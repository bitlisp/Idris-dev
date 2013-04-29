module IRTS.CodegenLLVM (codegenLLVM) where

import IRTS.Bytecode
import IRTS.Lang ( FType(..)
                 , PrimFn(..)
                 , LVar(..)
                 )
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Util.System
import Paths_idris

import LLVM.ST

import System.IO
import System.Directory (removeFile)
import System.FilePath ((</>))
import System.Process (rawSystem)
import System.Exit (ExitCode(..))
import System.Info (arch)
import Control.Monad
import Control.Monad.State
import Data.List
import Debug.Trace

opt :: String
opt = "-O3"

-- TODO: Perform optimization and assembly writing internally
codegenLLVM :: [(Name, SDecl)] ->
               String -> -- output file name
               OutputType ->
               IO ()
codegenLLVM defs out exec = do
  rtsBuf <- fmap (</> "llvm" </> "rts-" ++ arch ++ ".bc") getDataDir >>= createMemoryBufferWithContentsOfFile
  ctx <- getGlobalContext
  let mod = run ctx (codegen rtsBuf defs)
  case verifyModule mod of
    Just err -> ierror $ "Generated invalid module:\n" ++ show mod ++ "\n\n" ++ err
    Nothing ->
      case exec of
        Raw -> writeBC mod out
        Object -> buildObj mod out
        Executable ->
            withTmpFile $ \obj -> do
                          buildObj mod obj
                          exit <- rawSystem "gcc" [ obj, opt
                                                  , "-lm", "-lgc", "-lgmp"
                                                  , "-o", out
                                                  ]
                          when (exit /= ExitSuccess) $ ierror "FAILURE: Linking"
    where
      writeBC m dest
          = do writeBitcodeToFile m dest
               exit <- rawSystem "opt" ["-std-compile-opts", "-std-link-opts", opt, "-o", dest, dest]
               when (exit /= ExitSuccess) $ ierror "FAILURE: Bitcode optimization"
      buildObj m dest
          = withTmpFile $ \bitcode -> do
              writeBC m bitcode
              exit <- rawSystem "llc" ["--disable-fp-elim", "-filetype=obj", opt, "-o", dest, bitcode]
              when (exit /= ExitSuccess) $ ierror "FAILURE: Object file output"

      withTmpFile :: (FilePath -> IO a) -> IO a
      withTmpFile f = do
        (path, handle) <- tempfile
        hClose handle
        result <- f path
        removeFile path
        return result

data CGState c s = MkCGState { cgLocals :: [STValue c s]
                             , cgDepth :: Int
                             }

newtype ICG c s a = MkICG { unICG :: StateT (CGState c s) (CodeGen c s) a }

runICG :: [STValue c s] -> ICG c s a -> CodeGen c s a
runICG env (MkICG cg) = evalStateT cg $
                        MkCGState { cgLocals = reverse env
                                  , cgDepth = length env
                                  }

getUndefVal :: ICG c s (STValue c s)
getUndefVal = getUndef =<< getValTy

getNullVal :: ICG c s (STValue c s)
getNullVal = constPtrNull =<< getValTy

getValTy :: (Monad (m c s), MonadMG m) => m c s (STType c s)
getValTy = pointerType =<< getPrimTy "ctor"

getUnit :: ICG c s (STValue c s)
getUnit = do valTy <- getValTy
             unit <- getPrim "unit"
             buildPointerCast "" unit valTy

buildAlloc :: Bool -> STValue c s -> ICG c s (STValue c s)
buildAlloc atomic size = do alloc <- getPrim (if atomic then "GC_malloc_atomic" else "GC_malloc")
                            buildCall "" alloc [size]

instance Functor (ICG c s) where
    fmap f (MkICG x) = MkICG (fmap f x)

instance Monad (ICG c s) where
    (MkICG x) >>= f =
        MkICG (x >>= unICG . f)
    return = MkICG . return

instance MonadLLVM ICG where
    getContext = MkICG (lift getContext)
    liftLL = MkICG . lift . liftLL
    liftST = MkICG . lift . liftST

instance MonadMG ICG where
    liftMG = MkICG . lift . liftMG

instance MonadCG ICG where
    liftCG = MkICG . lift . liftCG

withVars :: [STValue c s] -> ICG c s a -> ICG c s a
withVars vs cg = do
  st <- MkICG get
  MkICG $ put st { cgLocals = reverse vs ++ cgLocals st
                 , cgDepth = length vs + cgDepth st
                 }
  result <- cg
  st' <- MkICG get
  unless (cgDepth st' == length vs + cgDepth st) $ ierror "Variable leak"
  MkICG $ put st' { cgLocals = drop (length vs) (cgLocals st')
                  , cgDepth = cgDepth st
                  }
  return result

findVar :: LVar -> ICG c s (STValue c s)
findVar (Glob name) = do
  global <- findGlobal (show name)
  case global of
    Just g -> return g
    Nothing -> ierror $ "Undefined global: " ++ show name
findVar (Loc level) = do
  st <- MkICG get
  return $ cgLocals st !! ((cgDepth st - 1) - level)

updateVar :: LVar -> STValue c s -> ICG c s ()
updateVar (Loc level) value = do
  st <- MkICG get
  MkICG . put $ st { cgLocals = replaceElt ((cgDepth st - 1) - level) value (cgLocals st) }
updateVar v _ = ierror $ "Unexpected non-local var in update: " ++ show v

replaceElt :: Int -> a -> [a] -> [a]
replaceElt _ val [] = error "replaceElt: Ran out of list"
replaceElt 0 val (x:xs) = val:xs
replaceElt n val (x:xs) = x : replaceElt (n-1) val xs

getEnv :: ICG c s [STValue c s]
getEnv = fmap cgLocals $ MkICG get

setEnv :: [STValue c s] -> ICG c s ()
setEnv e = do
  st <- MkICG get
  MkICG . put $ st { cgLocals = e
                   , cgDepth = length e
                   }

-- Given a set of branched environments containing potentially-updated
-- variables, construct and bind a single environment that refers to
-- the most up to date instance of every valuable, for use after the
-- branches merge
mergeEnvs :: [(STBasicBlock c s, [STValue c s])] -> ICG c s ()
mergeEnvs [] = return ()
mergeEnvs [(_, e)] = do
  st <- MkICG get
  MkICG . put $ st { cgLocals = e
                   , cgDepth = length e
                   }
mergeEnvs es = do
  let vars = transpose
             . map (\(block, env) -> map (\x -> (x, block)) env)
             $ es
  env <- forM vars $ \var ->
         case var of
           [] -> ierror "mergeEnvs: impossible"
           [(v, _)] -> return v
           vs@((v, _):_)
                  | all (== v) (map fst vs) -> return v
                  | otherwise ->
                      do name <- getValueName v
                         ty <- typeOf v
                         phi <- buildPhi name ty
                         addIncoming phi vs
                         return phi
  st <- MkICG get
  MkICG . put $ st { cgLocals = env
                   , cgDepth = length env
                   }

codegen :: MemoryBuffer -> [(Name, SDecl)] -> LLVM c s (STModule c s)
codegen rts defs = do
  m <- parseBitcode rts
  case m of
    Left err -> ierror $ "Failed to load RTS definitions:\n" ++ err
    Right mod -> runModuleGen mod (buildModule defs)

buildModule :: [(Name, SDecl)] -> ModuleGen c s (STModule c s)
buildModule defs = do
  let defs' = map snd defs
  buildPrimitives
  decls <- mapM toDecl defs'
  forM_ (zip decls defs') $ \(func, def) ->
      defineFunction func (toDef def)
  runMain <- findFunction (show (MN 0 "runMain"))
  case runMain of
    Nothing -> ierror "missing entry point"
    Just f -> buildMain f
  getModule

buildMain :: STValue c s -> ModuleGen c s (STValue c s)
buildMain entryPoint = do
  i32 <- intType 32
  argvTy <- intType 8 >>= pointerType >>= pointerType
  fty <- functionType i32 [i32, argvTy] False
  genFunction "main" fty $ do
                         buildGmpInit
                         call <- buildCall "" entryPoint []
                         setInstrCallConv call Fast
                         zero <- constInt i32 0 False
                         buildRet zero

buildGmpInit :: CodeGen c s ()
buildGmpInit = do
  setMem <- getPrim "__gmp_set_memory_functions"
  alloc <- getPrim "GC_malloc_atomic"
  realloc <- getPrim "gmp_realloc"
  free <- getPrim "gmp_free"
  buildCall "" setMem [alloc, realloc, free]
  return ()

toDecl :: SDecl -> ModuleGen c s (STValue c s)
toDecl (SFun name argNames _ e) = do
  valTy <- getValTy
  fty <- functionType valTy (replicate (length argNames) valTy) False
  func <- addFunction (show name) fty
  setLinkage func InternalLinkage
  setFuncCallConv func Fast
  addFuncAttrib func NoUnwindAttribute
  params <- getFunctionParams func
  forM_  (zip argNames params) $ \(argName, param) ->
      setValueName param (show argName)
  return func

toDef :: SDecl -> CodeGen c s ()
toDef (SFun _ _ _ body) = do
  params <- getParams
  result <- runICG params $ compile body
  unreachable <- isUnreachable result
  unless unreachable $ void $ buildRet result

-- TODO: Phi together env updates so branches don't screw with eachother
compile :: SExp -> ICG c s (STValue c s)
compile expr = do
  i8 <- intType 8
  i32 <- intType 32
  i64 <- intType 64
  valTy <- getValTy
  zero64 <- constInt i64 0 False
  zero32 <- constInt i32 0 False
  one <- constInt i32 1 False
  case expr of
    SV v -> findVar v
    SApp tailcall fname args ->
        do argVals <- mapM findVar args
           func <- liftMG $ findFunction (show fname)
           case func of
             Nothing -> ierror $ "Applying undefined function: " ++ show fname
             Just f ->
                 do call <- buildCall "" f argVals
                    setTailCall call tailcall
                    setInstrCallConv call Fast
                    return call
    SLet (Loc level) valueExpr body ->
        do value <- compile valueExpr
           withVars [value] $ compile body
    SLet (Glob name) _ _ -> ierror "Unexpected global name in let"
    SProj var index ->
        do idx <- constInt i64 (fromIntegral index) False
           val <- findVar var
           ptr <- buildInBoundsGEP "" val [zero64, one, idx]
           buildLoad (show index ++ "arg") ptr
    SUpdate var expr ->
        do value <- compile expr
           updateVar var value
           return value
    SCon tag name args -> mkCon tag =<< mapM findVar args
    SCase var alts ->
        do ctor <- findVar var
           let constAlts = filter (\a -> case a of { SConstCase {} -> True; _ -> False; }) alts
               conAlts   = filter (\a -> case a of { SConCase   {} -> True; _ -> False; }) alts
               defaultAction =
                   case find (\a -> case a of { SDefaultCase _ -> True; _ -> False; }) alts of
                     Just (SDefaultCase expr) -> compile expr
                     Nothing -> compile (SError "Inexhaustive case")
               altActions =
                   map (\a -> case a of
                                SConstCase _ e -> compile e
                                SConCase _ _ _ argNames e ->
                                    do args <- forM (zip argNames [0..]) $ \(name, index) ->
                                               do idx <- constInt i64 (fromIntegral index) False
                                                  argPtr <- buildInBoundsGEP "" ctor [zero64, one, idx]
                                                  buildLoad (show name) argPtr
                                       withVars args $ compile e)
                       (conAlts ++ constAlts)
           case constAlts of
             [] -> do tagPtr <- buildInBoundsGEP "" ctor [zero64, zero32]
                      tag <- buildLoad "tag" tagPtr
                      altTags <- forM conAlts $ \(SConCase _ tag _ _ _) ->
                                 constInt i32 (fromIntegral tag) False
                      buildMergingCase tag defaultAction (zip altTags altActions)
             SConstCase c _ : _ ->
                 do altVals <- mapM (\(SConstCase c _) -> compileConstUnboxed c) constAlts
                    valTy <- typeOf (head altVals)
                    boxTy <- pointerType =<< structType [i8, valTy] False
                    box <- buildPointerCast "" ctor boxTy
                    value <- buildLoad "value" =<< buildInBoundsGEP "" box [zero64, one]
                    case c of
                      Str _ -> do
                             strcmp <- getPrim "strcmp"
                             buildChainCase (\x y -> do
                                               r <- buildCall "" strcmp [x, y]
                                               buildICmp "" IntEQ r zero32)
                                            value defaultAction (zip altVals altActions)
                      BI _ -> do
                             mpzcmp <- getPrim "__gmpz_cmp"
                             buildChainCase (\x y -> do
                                                r <- buildCall "" mpzcmp [x, y]
                                                buildICmp "" IntEQ r zero32)
                                            value defaultAction (zip altVals altActions)
                      _ -> buildMergingCase value defaultAction (zip altVals altActions)
    SChkCase var alts ->
        case alts of
          [] -> ierror $ "Empty ChkCase: " ++ show expr
          _ -> do isVal <- buildIsVal =<< findVar var
                  buildIf valTy isVal (findVar var) (compile (SCase var alts))
    SConst c -> compileConst c
    SOp prim args ->
        do argVals <- mapM findVar args
           compilePrim prim argVals
    SForeign _ returnTy fname args ->
        do func <- liftMG $ ensureForeign fname returnTy (map fst args)
           argVals <- mapM (\(fty, var) -> findVar var >>= unbox fty) args
           result <- buildCall "" func argVals
           case returnTy of
             FUnit -> getUnit
             _ -> boxVal result
    SNothing -> getNullVal -- Could be undef, except sometimes erasure wipes out a 'return ()' which gets EVALed.
    SError msg ->
        do msgPtr <- buildGlobalStringPtr "errorMsg" (msg ++ "\n")
           putStr <- getPrim "putStr"
           call <- buildCall "" putStr [msgPtr]
           trap <- getPrim "llvm.trap"
           buildCall "" trap []
           buildUnreachable
    -- All elements are presently implemented
    -- x -> do m <- liftMG (getModule >>= showModule)
    --         ierror $ "Unimplemented IR element: " ++ show x ++ "\n\n"
    --               ++ "Module so far:\n" ++ m

ftyToNative :: (Monad (m c s), MonadLLVM m) => FType -> m c s (STType c s)
ftyToNative FInt    = intType 32
ftyToNative FChar   = intType 32
ftyToNative FString = intType 8 >>= pointerType
ftyToNative FPtr    = intType 8 >>= pointerType
ftyToNative FAny    = intType 8 >>= pointerType -- TODO: Verify correctness
ftyToNative FDouble = doubleType
ftyToNative FUnit   = voidType
--ftyToNative x       = ierror $ "Unimplemented foreign type: " ++ show x

ensureForeign :: String -> FType -> [FType] -> ModuleGen c s (STValue c s)
ensureForeign name returnTy argTys = do
  func <- findFunction name
  case func of
    Just f -> return f
    Nothing ->
        do nativeRet <- ftyToNative returnTy
           nativeArgs <- mapM ftyToNative argTys
           fty <- functionType nativeRet nativeArgs False
           addFunction name fty

compilePrim :: PrimFn -> [STValue c s] -> ICG c s (STValue c s)
compilePrim x args =
    case (x, args) of
      (LPlus,  [x,y]) -> bin FInt buildAdd x y
      (LMinus, [x,y]) -> bin FInt buildSub x y
      (LTimes, [x,y]) -> bin FInt buildMul x y
      (LAnd,   [x,y]) -> bin FInt buildAnd x y
      (LSHL,   [x,y]) -> bin FInt buildShl x y
      (LMod,   [x,y]) -> bin FInt buildSRem x y
      (LEq, [x,y]) -> icmp FInt IntEQ x y
      (LLt, [x,y]) -> icmp FInt IntSLT x y
      (LLe, [x,y]) -> icmp FInt IntSLE x y
      (LGt, [x,y]) -> icmp FInt IntSGT x y
      (LGe, [x,y]) -> icmp FInt IntSGE x y
      (LIntCh, [x]) -> return x
      (LChInt, [x]) -> return x
      (LIntBig, [x]) -> do
                     i <- unbox FInt x
                     i' <- buildSExt "" i =<< intType 64
                     f <- getPrim "__gmpz_init_set_si"
                     mpz <- getPrimTy "mpz"
                     mpz_t <- pointerType mpz
                     size <- sizeOf mpz
                     result <- buildAlloc False size
                     result' <- buildPointerCast "" result mpz_t
                     buildCall "" f [result', i']
                     boxVal result'
      (LBigInt, [x]) -> do
                     mpz_t <- pointerType =<< getPrimTy "mpz"
                     i32 <- intType 32
                     x' <- unbox' x mpz_t
                     f <- getPrim "__gmpz_get_si"
                     result <- buildCall "" f [x']
                     result' <- buildTrunc "" result i32
                     boxVal result'
      (LBigStr, [x]) -> do
                     mpz_t <- pointerType =<< getPrimTy "mpz"
                     i32 <- intType 32
                     zero <- constInt i32 0 True
                     nullStr <- constPtrNull =<< pointerType =<< intType 8
                     x' <- unbox' x mpz_t
                     f <- getPrim "__gmpz_get_str"
                     str <- buildCall "" f [nullStr, zero, x']
                     boxVal str
      (LBPlus, [x,y]) -> mpzOp "__gmpz_add" x y
      (LBMinus, [x,y]) -> mpzOp "__gmpz_sub" x y
      (LBTimes, [x,y]) -> mpzOp "__gmpz_mul" x y
      (LBDiv, [x,y]) -> mpzOp "__gmpz_fdiv_q" x y
      (LBMod, [x,y]) -> mpzOp "__gmpz_fdiv_r" x y
      (LBEq, [x,y]) -> mpzCmp IntEQ x y
      (LBLt, [x,y]) -> mpzCmp IntSLT x y
      (LBLe, [x,y]) -> mpzCmp IntSLE x y
      (LBGt, [x,y]) -> mpzCmp IntSGT x y
      (LBGe, [x,y]) -> mpzCmp IntSGE x y
      (LFPlus, [x,y]) -> bin FDouble buildFAdd x y
      (LFMinus, [x,y]) -> bin FDouble buildFSub x y
      (LFTimes, [x,y]) -> bin FDouble buildFMul x y
      (LFDiv, [x,y]) -> bin FDouble buildFDiv x y
      (LStrConcat, [x, y]) -> callPrim "strConcat" [(FString, x), (FString, y)]
      (LIntStr, [x]) -> callPrim "intStr" [(FInt, x)]
      (LStrInt, [x]) -> callPrim "strInt" [(FString, x)]
      (LStrEq, [x, y]) -> callPrim "strEq" [(FString, x), (FString, y)]
      (LStrCons, [x, y]) -> callPrim "strCons" [(FChar, x), (FString, y)]
      (LStrHead, [x]) -> callPrim "strHead" [(FString, x)]
      (LStrTail, [x]) -> callPrim "strTail" [(FString, x)]
      (LReadStr, [x]) -> callPrim "readStr" [(FPtr, x)]
      (LStdIn, []) -> boxVal =<< buildLoad "" =<< getPrim "stdin"
      _ -> ierror $ "Unimplemented primitive: " ++ show x ++ "("
                   ++ (intersperse ',' $ take (length args) ['a'..]) ++ ")"
    where
      icmp ty pred l r = do
        l' <- unbox ty l
        r' <- unbox ty r
        flag <- buildICmp "" pred l' r'
        i32 <- intType 32
        int <- buildZExt "" flag i32
        boxVal int

      bin ty f l r = do
        l' <- unbox ty l
        r' <- unbox ty r
        result <- f "" l' r'
        boxVal result

      mpzOp n l r = do
        mpz_t <- pointerType =<< getPrimTy "mpz"
        l' <- unbox' l mpz_t
        r' <- unbox' r mpz_t
        result <- buildMPZ
        f <- getPrim n
        buildCall "" f [result, l', r']
        boxVal result

      mpzCmp pred l r = do
        mpz <- getPrimTy "mpz"
        mpz_t <- pointerType mpz
        l' <- unbox' l mpz_t
        r' <- unbox' r mpz_t
        f <- getPrim "__gmpz_cmp"
        ord <- buildCall "" f [l', r']
        i32 <- intType 32
        zero <- constInt i32 0 True
        icmp FInt pred ord zero

buildMPZ :: ICG c s (STValue c s)
buildMPZ  = do
  mpz <- getPrimTy "mpz"
  mpz_t <- pointerType mpz
  size <- sizeOf mpz
  result <- buildAlloc False size
  result' <- buildPointerCast "" result mpz_t
  init <- getPrim "__gmpz_init"
  buildCall "" init [result']
  return result'

compileConst :: Const -> ICG c s (STValue c s)
compileConst c
    | elem c [ IType, BIType, FlType, ChType, StrType
             , B8Type, B16Type, B32Type, B64Type
             , PtrType, VoidType, Forgot
             ] = getNullVal -- Could be undef, except might get EVALed
    | otherwise = compileConstUnboxed c >>= boxVal

compileConstUnboxed :: Const -> ICG c s (STValue c s)
compileConstUnboxed (I   i) = intConst True  32 i
compileConstUnboxed (B8  i) = intConst False 8  i
compileConstUnboxed (B16 i) = intConst False 16 i
compileConstUnboxed (B32 i) = intConst False 32 i
compileConstUnboxed (B64 i) = intConst False 64 i
compileConstUnboxed (Str s) = buildGlobalStringPtr "strLit" s
compileConstUnboxed (Ch  c) = intConst False 32 (fromEnum c)
compileConstUnboxed (BI  i) = do
  mpz <- getPrimTy "mpz"
  mpz_t <- pointerType mpz
  size <- sizeOf mpz
  result <- buildAlloc False size
  result' <- buildPointerCast "" result mpz_t
  init <- getPrim "__gmpz_init_set_str"
  str <- buildGlobalStringPtr "bigIntLit" (show i)
  i32 <- intType 32
  base <- constInt i32 10 True
  buildCall "" init [result', str, base]
  return result'
compileConstUnboxed x = ierror $ "Unimplemented constant type: " ++ show x

intConst :: Integral a => Bool -> CUInt -> a -> ICG c s (STValue c s)
intConst signed width value = do
  ty <- intType width
  constInt ty (fromIntegral value) signed

-- Utility for debugging codegen
buildAssert :: STValue c s -> String -> ICG c s ()
buildAssert cond msg = do
  func <- getFunction
  true <- appendBasicBlock "assertTrue" func
  false <- appendBasicBlock "assertFalse" func
  buildCondBr cond true false
  positionAtEnd true
  compile (SError msg)
  positionAtEnd false

-- Non-constructor values have the tag MSB set
boxVal :: STValue c s -> ICG c s (STValue c s)
boxVal val = do
  valTy <- getValTy
  str <- showValue val
  i8 <- intType 8
  i32 <- intType 32
  i64 <- intType 64
  zero64 <- constInt i64 0 False
  zero32 <- constInt i32 0 False
  one <- constInt i32 1 False

  innerTy <- typeOf val
  kind <- typeKind innerTy

  -- str <- showValue val
  -- tystr <- showType innerTy
  -- trace ("Boxing " ++ str ++ " : " ++ tystr ++ ", a " ++ show kind) $ return ()
  -- case kind of
  --   PointerTypeKind ->
  --       do nullPtr <- constPtrNull innerTy
  --          isNull <- buildICmp "" IntEQ val nullPtr
  --          buildAssert p isNull "Boxed a null pointer"
  --   _ -> return ()

  const <- isConstant val
  case kind of
    VoidTypeKind -> getUnit
    _ -> do boxTy <- structType [i8, innerTy] False
            ptrTy <- pointerType boxTy
            size <- sizeOf boxTy
            mem <- buildAlloc (kind /= PointerTypeKind) size
            box <- buildPointerCast "box" mem ptrTy

            tagPtr <- buildInBoundsGEP "" box [zero64, zero32]
            tag <- constInt i8 (2^8 - 1) False
            buildStore tag tagPtr

            valPtr <- buildInBoundsGEP "" box [zero64, one]
            buildStore val valPtr
  
            buildPointerCast "" box valTy

unbox :: FType -> STValue c s -> ICG c s (STValue c s)
unbox FInt  v = intType 32 >>= unbox' v
unbox FChar v = intType 32 >>= unbox' v
unbox FString v = intType 8 >>= pointerType >>= unbox' v
unbox FPtr    v = intType 8 >>= pointerType >>= unbox' v
unbox FDouble v = doubleType >>= unbox' v
unbox FUnit v = return v

unbox' v ty = do
  i8 <- intType 8
  i32 <- intType 32
  i64 <- intType 64
  zero <- constInt i64 0 False
  one <- constInt i32 1 False
  boxTy <- structType [i8, ty] False
  ptrTy <- pointerType boxTy
  box <- buildPointerCast "box" v ptrTy
  valPtr <- buildInBoundsGEP "" box [zero, one]
  buildLoad "" valPtr

buildIsVal :: STValue c s -> ICG c s (STValue c s)
buildIsVal v = buildICmp "" IntEQ v =<< getNullVal

mkCon :: Int -> [STValue c s] -> ICG c s (STValue c s)
mkCon tag args = do
  valTy <- getValTy
  base <- constPtrNull valTy
  i64 <- intType 64
  i32 <- intType 32
  zero64 <- constInt i64 0 False
  zero32 <- constInt i32 0 False
  one <- constInt i32 1 False
  arity <- constInt i64 (fromIntegral (length args)) False
  offset <- constGEP base [zero64, one, arity]
  size <- constPtrToInt offset i64
  mem <- buildAlloc False size
  con <- buildPointerCast "" mem valTy
  tagPtr <- buildInBoundsGEP "" con [zero64, zero32]
  tagVal <- constInt i32 (fromIntegral tag) False
  buildStore tagVal tagPtr
  argsArray <- buildInBoundsGEP "" con [zero64, one]
  forM_ (zip [0..] args) $ \(index, val) ->
      do n <- constInt i64 index False
         ptr <- buildInBoundsGEP (show index ++ "arg") argsArray [zero64, n]
         buildStore val ptr
  pi8 <- pointerType =<< intType 8
  mem' <- buildPointerCast "" mem pi8
  neg1 <- constInt i64 (-1) True -- TODO: Replace with constant from LLVMABISizeOfType
  ivs <- getPrim "llvm.invariant.start"
  buildCall "" ivs [neg1, mem']
  return con

getPrim :: (Monad (m c s), MonadMG m) => String -> m c s (STValue c s)
getPrim name = do
  func <- findFunction name
  case func of
    Just f -> return f
    Nothing ->
        do glob <- findGlobal name
           case glob of
             Just g -> return g
             Nothing -> ierror $ "Missing primitive: " ++ name

callPrim :: String -> [(FType, STValue c s)] -> ICG c s (STValue c s)
callPrim name args = do
  func <- liftMG $ getPrim name
  args <- mapM (uncurry unbox) args
  result <- buildCall "" func args
  setInstrCallConv result Fast
  boxVal result

getPrimTy :: (Monad (m c s), MonadMG m) => String -> m c s (STType c s)
getPrimTy name = do
  ty <- findType name
  case ty of
    Just t -> return t
    Nothing -> ierror $ "Missing primitive type: " ++ name

buildPrimitives :: ModuleGen c s ()
buildPrimitives = do
  ctorTy <- structCreateNamed "ctor"
  i32 <- intType 32
  valTy <- pointerType ctorTy
  argsTy <- arrayType valTy 0
  structSetBody ctorTy [i32, argsTy] False -- Tag, args
  return ()

ierror :: String -> a
ierror msg = error $ "CodegenLLVM: INTERNAL ERROR: " ++ msg

-- Case that preserves local environment updates
buildMergingCase :: STValue c s -> ICG c s (STValue c s) -> [(STValue c s, ICG c s (STValue c s))]
                 -> ICG c s (STValue c s)
buildMergingCase value defaultCode alts = do
  initialEnv <- getEnv
  func <- getFunction
  defBlock <- appendBasicBlock "caseDefault" func
  switch <- buildSwitch value defBlock (fromIntegral (length alts))
  positionAtEnd defBlock
  defResult <- defaultCode
  defExit <- getInsertBlock
  defEnv <- getEnv
  results <- forM alts $ \(val, cg) ->
             do inBlock <- appendBasicBlock "caseAlt" func
                addCase switch val inBlock
                positionAtEnd inBlock
                setEnv initialEnv
                result <- cg
                outBlock <- getInsertBlock
                env <- getEnv
                return (result, outBlock, env)
  reachable <- filterM (\(r, _, _) -> fmap not $ isUnreachable r)
               ((defResult, defExit, defEnv):results)
  end <- appendBasicBlock "caseExit" func
  mapM_ (\(_, out, _) -> positionAtEnd out >> buildBr end) reachable
  positionAtEnd end
  case reachable of
    [] -> buildUnreachable
    (result, _, _):_ ->
        do ty <- typeOf result
           phi <- buildPhi "caseResult" ty
           addIncoming phi (map (\(result, outBlock, _) -> (result, outBlock))
                                reachable)
           mergeEnvs $ map (\(_, outBlock, env) -> (outBlock, env)) reachable
           return phi

-- As above, but with conditional branches based on a comparator instead of a switch. Slower but sometimes necessary.
buildChainCase :: (STValue c s -> STValue c s -> ICG c s (STValue c s))
               -> STValue c s -> ICG c s (STValue c s) -> [(STValue c s, ICG c s (STValue c s))]
               -> ICG c s (STValue c s)
buildChainCase comparator inspect defaultCode alts = do
  initialEnv <- getEnv
  func <- getFunction
  results <-
      forM alts $ \(val, cg) -> do
        eq <- comparator inspect val
        inBlock <- appendBasicBlock "chainCaseAlt" func
        elseBlock <- appendBasicBlock "chainCaseElse" func
        buildCondBr eq inBlock elseBlock
        positionAtEnd inBlock
        setEnv initialEnv
        result <- cg
        outBlock <- getInsertBlock
        env <- getEnv
        positionAtEnd elseBlock
        return (result, outBlock, env)
  defResult <- defaultCode
  defOut <- getInsertBlock
  defEnv <- getEnv
  reachable <- filterM (\(r, _, _) -> fmap not $ isUnreachable r)
               ((defResult, defOut, defEnv):results)
  end <- appendBasicBlock "chainCaseExit" func
  mapM_ (\(_, out, _) -> positionAtEnd out >> buildBr end) reachable
  positionAtEnd end
  case reachable of
    [] -> buildUnreachable
    (result, _, _):_ ->
        do ty <- typeOf result
           phi <- buildPhi "caseResult" ty
           addIncoming phi (map (\(result, outBlock, _) -> (result, outBlock)) reachable)
           mergeEnvs $ map (\(_, outBlock, env) -> (outBlock, env)) reachable
           return phi
