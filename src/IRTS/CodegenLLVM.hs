{-# LANGUAGE TypeOperators #-}
module IRTS.CodegenLLVM (codegenLLVM) where

import IRTS.Bytecode
import IRTS.Lang
import IRTS.Simplified
import IRTS.CodegenCommon
import Core.TT
import Util.System
import Paths_idris

import qualified LLVM.Wrapper.Core as L
import qualified LLVM.Wrapper.BitWriter as L
import qualified LLVM.Wrapper.Analysis as L

import System.IO
import System.Directory (removeFile)
import System.Process (rawSystem)
import System.Exit (ExitCode(..))
import Foreign.Ptr
import Control.Monad

codegenLLVM :: [(Name, SDecl)] ->
               String -> -- output file name
               OutputType -> -- generate executable if True, only .o if False
               IO ()
codegenLLVM defs out exec
    = L.withModule "" $ \m -> do
        prims <- declarePrimitives m
        decls <- mapM (toLLVMDecl prims m . snd) defs
        mapM (\f -> L.setLinkage f L.InternalLinkage) decls
        mapM_ (toLLVMDef prims m . snd) defs
        buildMain m (MN 0 "runMain")
        err <- L.verifyModule m
        case err of
          Nothing  -> case exec of
                        Raw -> L.printModuleToFile m out
                        Object -> buildObj m out
                        Executable ->
                            withTmpFile $ \obj -> do
                                  buildObj m obj
                                  rtsDir <- fmap (++ "/rts") getDataDir
                                  exit <- rawSystem "gcc" [ obj, "-O3"
                                                          , "-L" ++ rtsDir
                                                          , "-lidris_rts", "-lgmp", "-lpthread", "-lm"
                                                          , "-o", out
                                                          ]
                                  when (exit /= ExitSuccess) $ ierror "FAILURE: Linking"
          Just msg -> ierror msg
    where
      writeBc m dest
          = do L.writeBitcodeToFile m dest
               exit <- rawSystem "opt" ["-std-compile-opts", "-std-link-opts", "-O3", "-o", dest, dest]
               when (exit /= ExitSuccess) $ ierror "FAILURE: Bitcode optimization"
      buildObj m dest
          = withTmpFile $ \bitcode -> do
              writeBc m bitcode
              exit <- rawSystem "llc" ["-filetype=obj", "-O3", "-o", dest, bitcode]
              when (exit /= ExitSuccess) $ ierror "FAILURE: Object file output"

      withTmpFile :: (FilePath -> IO a) -> IO a
      withTmpFile f = do
        (path, handle) <- tempfile
        hClose handle
        result <- f path
        removeFile path
        return result

buildMain :: L.Module -> Name -> IO ()
buildMain m entryPoint
    = L.withBuilder $ \b -> do
        initVm <- L.addFunction m "init_vm"
                  $ L.functionType (L.pointerType L.int8Type 0) [L.int32Type, L.int64Type] False
        f <- L.addFunction m "main"
             $ L.functionType L.int32Type
                   [L.int32Type, L.pointerType (L.pointerType L.int8Type 0) 0] False
        bb <- L.appendBasicBlock f "entry"
        L.positionAtEnd b bb
        vm <- L.buildCall b initVm
              [L.constInt L.int32Type 4096000 True, L.constInt L.int64Type 2048000 True] ""
        maybeRunMain <- L.getNamedFunction m (llname entryPoint)
        case maybeRunMain of
          Just runMain -> do call <- L.buildCall b runMain [vm] ""
                             L.setInstructionCallConv call L.Fast
          Nothing -> ierror $ "missing entry point: " ++ (show entryPoint)
        L.buildRet b $ L.constInt L.int32Type 0 True
        return ()

data TypeID = ConTy | IntTy | FloatTy | StringTy | UnitTy | PtrTy
            deriving (Eq, Enum, Show)

data Prims = Prims { allocCon :: L.Value
                   , fprintf :: L.Value
                   , abort :: L.Value
                   , primReadStr :: L.Value
                   , primStdin :: L.Value
                   , primStdout :: L.Value
                   , primStderr :: L.Value
                   , primMkBigI :: L.Value
                   , primMkBigC :: L.Value
                   , primMkBigM :: L.Value
                   , primCastIntStr :: L.Value
                   , primCastStrInt :: L.Value
                   , primCastFloatStr :: L.Value
                   , primCastStrFloat :: L.Value
                   , primConcat :: L.Value
                   , primStrlt :: L.Value
                   , primStreq :: L.Value
                   , primStrlen :: L.Value
                   , primStrHead :: L.Value
                   , primStrTail :: L.Value
                   , primStrCons :: L.Value
                   , primStrIndex :: L.Value
                   , primStrRev :: L.Value
                   , primBigPlus :: L.Value
                   , primBigMinus :: L.Value
                   , primBigTimes :: L.Value
                   , primBigDivide :: L.Value
                   , primBigEq :: L.Value
                   , primBigLt :: L.Value
                   , primBigLe :: L.Value
                   , primBigGt :: L.Value
                   , primBigGe :: L.Value
                   , primCastIntBig :: L.Value
                   , primCastBigInt :: L.Value
                   , primCastStrBig :: L.Value
                   , primCastBigStr :: L.Value
                   , primFExp :: L.Value
                   , primFLog :: L.Value
                   , primFSin :: L.Value
                   , primFCos :: L.Value
                   , primFTan :: L.Value
                   , primFASin :: L.Value
                   , primFACos :: L.Value
                   , primFATan :: L.Value
                   , primFSqrt :: L.Value
                   , primFFloor :: L.Value
                   , primFCeil :: L.Value
                   , conTy :: L.Type
                   , valTy :: L.Type
                   }

declarePrimitives :: L.Module -> IO Prims
declarePrimitives m
    = do con <- L.structCreateNamed "constructor"
         val <- L.structCreateNamed "value"
         --                   Tag          Arity        Args
         L.structSetBody con [L.int32Type, L.int32Type, L.arrayType (L.pointerType val 0) 0] False
         --                   Type         Value
         L.structSetBody val [L.int32Type, con] False
         alloc <- L.addFunction m "allocCon"
                  $ L.functionType (L.pointerType val 0)
                        [L.pointerType L.int8Type 0, L.int32Type] False
         rstr <- L.addFunction m "idris_readStr"
                 $ L.functionType (L.pointerType val 0)
                       [L.pointerType L.int8Type 0, L.pointerType L.int8Type 0] False
         bigi <- L.addFunction m "MKBIGI"
                 $ L.functionType (L.pointerType val 0) [L.int32Type] False
         bigc <- L.addFunction m "MKBIGC"
                 $ L.functionType (L.pointerType val 0)
                       [L.pointerType L.int8Type 0, L.pointerType L.int8Type 0] False
         bigm <- L.addFunction m "MKBIGM"
                 $ L.functionType (L.pointerType val 0)
                       [L.pointerType L.int8Type 0, L.pointerType L.int8Type 0] False
         fpf <- L.addFunction m "fprintf"
                $ L.functionType L.int32Type [L.pointerType L.int8Type 0, L.pointerType L.int8Type 0] True
         abort' <- L.addFunction m "abort" $ L.functionType L.voidType [] False
         L.addFunctionAttr abort' L.NoReturnAttribute
         stdin'  <- L.addGlobal m (L.pointerType L.int8Type 0) "stdin"
         stdout' <- L.addGlobal m (L.pointerType L.int8Type 0) "stdout"
         stderr' <- L.addGlobal m (L.pointerType L.int8Type 0) "stderr"
         mapM_ (flip L.setLinkage L.ExternalLinkage) [stdin', stdout', stderr']
         let fpty = L.functionType L.doubleType [L.doubleType] False
         exp <- L.addFunction m "llvm.exp.f64" fpty
         log <- L.addFunction m "llvm.log.f64" fpty
         sin <- L.addFunction m "llvm.sin.f64" fpty
         cos <- L.addFunction m "llvm.cos.f64" fpty
         sqrt <- L.addFunction m "llvm.sqrt.f64" fpty
         floor <- L.addFunction m "llvm.floor.f64" fpty
         ceil <- L.addFunction m "ceil" fpty
         tan <- L.addFunction m "tan" fpty
         asin <- L.addFunction m "asin" fpty
         acos <- L.addFunction m "acos" fpty
         atan <- L.addFunction m "atan" fpty
         let bind name arity = do
               f <- L.addFunction m ("idris_" ++ name)
                    $ L.functionType (L.pointerType val 0)
                          ((L.pointerType L.int8Type 0)
                           : (replicate arity $ L.pointerType val 0)) False
               L.addFunctionAttr f L.NoUnwindAttribute
               return f
         cis <- bind "castIntStr" 1
         csi <- bind "castStrInt" 1
         cfs <- bind "castFloatStr" 1
         csf <- bind "castStrFloat" 1
         cnc <- bind "concat" 2
         slt <- bind "strlt" 2
         seq <- bind "streq" 2
         sln <- bind "strlen" 2
         shd <- bind "strHead" 1
         stl <- bind "strTail" 1
         stc <- bind "strCons" 2
         sti <- bind "strIndex" 2
         str <- bind "strRev" 1
         bip <- bind "bigPlus" 2
         bim <- bind "bigMinus" 2
         bit <- bind "bigTimes" 2
         bid <- bind "bigDivide" 2
         beq <- bind "bigEq" 2
         blt <- bind "bigLt" 2
         ble <- bind "bigLe" 2
         bgt <- bind "bigGt" 2
         bge <- bind "bigGe" 2
         cib <- bind "castIntBig" 1
         cbi <- bind "castBigInt" 1
         csb <- bind "castStrBig" 1
         cbs <- bind "castBigStr" 1
         return $ Prims { allocCon = alloc
                        , fprintf = fpf
                        , abort = abort'
                        , primReadStr = rstr
                        , primStdin = stdin'
                        , primStdout = stdout'
                        , primStderr = stderr'
                        , primMkBigI = bigi
                        , primMkBigC = bigc
                        , primMkBigM = bigm
                        , primCastIntStr = cis
                        , primCastStrInt = csi
                        , primCastFloatStr = cfs
                        , primCastStrFloat = csf
                        , primConcat = cnc
                        , primStrlt = slt
                        , primStreq = seq
                        , primStrlen = sln
                        , primStrHead = shd
                        , primStrTail = stl
                        , primStrCons = stc
                        , primStrIndex = sti
                        , primStrRev = str
                        , primBigPlus = bip
                        , primBigMinus = bim
                        , primBigTimes = bit
                        , primBigDivide = bit
                        , primBigEq = beq
                        , primBigLt = blt
                        , primBigLe = ble
                        , primBigGt = bgt
                        , primBigGe = bge
                        , primCastIntBig = cib
                        , primCastBigInt = cbi
                        , primCastStrBig = csb
                        , primCastBigStr = cbs
                        , primFExp = exp
                        , primFLog = log
                        , primFSin = sin
                        , primFCos = cos
                        , primFTan = tan
                        , primFASin = asin
                        , primFACos = acos
                        , primFATan = atan
                        , primFSqrt = sqrt
                        , primFFloor = floor
                        , primFCeil = ceil
                        , conTy = con
                        , valTy = val
                        }

idrFuncTy :: Prims -> Int -> L.Type
idrFuncTy p n = L.functionType (L.pointerType (valTy p) 0)
                ((L.pointerType L.int8Type 0)
                 : (replicate n $ L.pointerType (valTy p) 0))
                False

llname :: Name -> String
llname n = "_idris_" ++ (show n)

toLLVMDecl :: Prims -> L.Module -> SDecl -> IO L.Value
toLLVMDecl p m (SFun name args _ _)
    = do f <- L.addFunction m (llname name) $ idrFuncTy p $ length args
         L.setFunctionCallConv f L.Fast
         ps <- L.getParams f
         L.setValueName (head ps) "VM"
         mapM (uncurry L.setValueName) $ zip (tail ps) (map show args)
         return f


toLLVMDef :: Prims -> L.Module -> SDecl -> IO L.Value
toLLVMDef prims m (SFun name args _ exp)
    = L.withBuilder $ \b -> do
        f <- fmap (maybe (ierror "toLLVMDef: impossible") id) $ L.getNamedFunction m (llname name)
        bb <- L.appendBasicBlock f "entry"
        L.positionAtEnd b bb
        params <- L.getParams f
        value <- toLLVMExp prims m f b (head params) (tail params) exp
        unreachable <- L.isUnreachable value
        unless unreachable $ void $ L.buildRet b value
        broken <- L.verifyFunction f
        when broken $ do
          L.dumpValue f
          err <- L.verifyModule m
          case err of
            Just msg -> ierror $ "Broken function: " ++ msg
            Nothing -> ierror "toLLVMDef: impossible"
        return f

buildVal :: Prims -> L.Builder -> L.Value -> TypeID -> Int -> IO (L.Value, L.Value)
buildVal prims b vm tyid arity
    = do val <- L.buildCall b (allocCon prims) [vm, L.constInt L.int32Type (fromIntegral arity) True] ""
         ty <- L.buildStructGEP b val 0 "typePtr"
         L.buildStore b (L.constInt L.int32Type (fromIntegral $ fromEnum tyid) True) ty
         con <- L.buildStructGEP b val 1 "constructorPtr"
         return (val, con)

buildPrim :: Prims -> L.Builder -> L.Value -> TypeID -> IO (L.Value, L.Value)
buildPrim p b v t = buildVal p b v t 0

buildCon :: Prims -> L.Builder -> L.Value -> Int -> [L.Value] -> IO L.Value
buildCon prims b vm tag args
    = do (val, conPtr) <- buildVal prims b vm ConTy $ length args
         tagPtr <- L.buildStructGEP b conPtr 0 "tagPtr"
         L.buildStore b (L.constInt L.int32Type (fromIntegral tag) True) tagPtr
         arityPtr <- L.buildStructGEP b conPtr 1 "arityPtr"
         L.buildStore b (L.constInt L.int32Type (fromIntegral $ length args) True) arityPtr
         mapM (\(arg, idx) -> do
                 place <- L.buildInBoundsGEP b conPtr
                          [ L.constInt L.int32Type 0 True
                          , L.constInt L.int32Type 2 True
                          , L.constInt L.int32Type (fromIntegral idx) True
                          ] $ "arg" ++ (show idx)
                 L.buildStore b arg place) $ zip args [0..]
         return val

buildInt :: Prims -> L.Builder -> L.Value -> IO L.Value
buildInt prims b value
    = do shifted <- L.buildShl b value one ""
         tagged <- L.buildAdd b shifted one ""
         L.buildIntToPtr b tagged (L.pointerType (valTy prims) 0) ""
      where
        one = L.constInt L.int32Type 1 True

buildIsInt :: L.Builder -> L.Value -> IO L.Value
buildIsInt b v
    = do bits <- L.buildPtrToInt b v L.int32Type ""
         result <- L.buildAnd b bits (L.constInt L.int32Type 1 True) ""
         L.buildICmp b L.IntNE result (L.constInt L.int32Type 0 True) "isInt"

buildFloat :: Prims -> L.Builder -> L.Value -> L.Value -> IO L.Value
buildFloat prims b vm value
    = do (val, con) <- buildPrim prims b vm FloatTy
         floatPtr <- L.buildPointerCast b con (L.pointerType L.doubleType 0) ""
         L.buildStore b value floatPtr
         return val

buildPtr :: Prims -> L.Builder -> L.Value -> L.Value -> IO L.Value
buildPtr prims b vm value
    = do (val, con) <- buildPrim prims b vm PtrTy
         ptrPtr <- L.buildPointerCast b con (L.pointerType (L.pointerType L.int8Type 0) 0) ""
         L.buildStore b value ptrPtr
         return val

buildStr :: Prims -> L.Builder -> L.Value -> L.Value -> IO L.Value
buildStr prims b vm value
    = do (val, con) <- buildPrim prims b vm StringTy
         strPtr <- L.buildPointerCast b con (L.pointerType (L.pointerType L.int8Type 0) 0) ""
         L.buildStore b value strPtr
         return val

buildUnit :: Prims -> L.Builder -> L.Value -> IO L.Value
buildUnit p b vm = fmap fst $ buildPrim p b vm UnitTy

buildError :: Prims -> L.Builder -> String -> IO L.Value
buildError p b message
    = do fmt <- L.buildGlobalStringPtr b "%s" ""
         str <- L.buildGlobalStringPtr b message "errorMessage"
         stderr <- L.buildLoad b (primStderr p) ""
         L.buildCall b (fprintf p) [stderr, fmt, str] ""
         L.buildCall b (abort p) [] ""
         L.buildUnreachable b

buildCaseFail :: Prims -> L.Value -> IO L.BasicBlock
buildCaseFail prims f
    = L.withBuilder $ \b -> do
        bb <- L.appendBasicBlock f "caseFail"
        L.positionAtEnd b bb
        fname <- L.getValueName f
        buildError prims b $ "Inexhaustive case in " ++ fname
        return bb

buildAlt :: Prims -> L.Module -> L.Value -> L.Value -> [L.Value] -> L.Value -> L.BasicBlock -> L.BasicBlock ->
            SAlt -> IO (L.BasicBlock, L.Value)
buildAlt p m f vm s _ end entry (SDefaultCase body)
    = L.withBuilder $ \b -> do
        L.positionAtEnd b entry
        result <- toLLVMExp p m f b vm s body
        unreachable <- L.isUnreachable result
        unless unreachable $ void $ L.buildBr b end
        exit <- L.getInsertBlock b
        return (exit, result)
buildAlt p m f vm s _ end entry (SConstCase _ body)
    = L.withBuilder $ \b -> do
        L.positionAtEnd b entry
        result <- toLLVMExp p m f b vm s body
        unreachable <- L.isUnreachable result
        unless unreachable $ void $ L.buildBr b end
        exit <- L.getInsertBlock b
        return (exit, result)
buildAlt p m f vm s ctorPtr end entry (SConCase _ _ _ argNames body)
    = L.withBuilder $ \b -> do
        L.positionAtEnd b entry
        args <- mapM (\(name, idx) -> do
                        argPtr <- L.buildInBoundsGEP b ctorPtr
                                  [ L.constInt L.int32Type 0 True
                                  , L.constInt L.int32Type 2 True
                                  , L.constInt L.int32Type idx True
                                  ] ""
                        L.buildLoad b argPtr $ show name)
                     $ zip argNames [0..]
        result <- toLLVMExp p m f b vm (s ++ args) body
        unreachable <- L.isUnreachable result
        unless unreachable $ void $ L.buildBr b end
        exit <- L.getInsertBlock b
        return (exit, result)

foreignToC :: FType -> L.Type
foreignToC ty = case ty of
                  FInt -> L.int32Type
                  FUnit -> L.voidType
                  FDouble -> L.doubleType
                  FString -> L.pointerType L.int8Type 0
                  FPtr -> L.pointerType L.int8Type 0

idrToNative :: L.Builder -> FType -> L.Value -> IO L.Value
idrToNative b ty v
    = case ty of
        FInt -> do shifted <- L.buildPtrToInt b v L.int32Type ""
                   L.buildAShr b shifted (L.constInt L.int32Type 1 True) ""
        FAny -> return v
        _ -> do ctorPtr <- L.buildStructGEP b v 1 ""
                primPtr <- L.buildPointerCast b ctorPtr (L.pointerType (foreignToC ty) 0) ""
                L.buildLoad b primPtr ""

cToIdr :: Prims -> L.Builder -> FType -> L.Value -> L.Value -> IO L.Value
cToIdr prims b ty vm v
    = case ty of
        FInt  -> buildInt prims b v
        FChar -> buildInt prims b v
        FString -> buildStr   prims b vm v
        FDouble -> buildFloat prims b vm v
        FPtr    -> buildPtr   prims b vm v
        FUnit   -> buildUnit prims b vm
        FAny    -> return v

ensureBound :: L.Module -> String -> FType -> [FType] -> IO L.Value
ensureBound m name rty argtys
    = do maybef <- L.getNamedFunction m name
         case maybef of
           Nothing -> L.addFunction m name $ L.functionType (foreignToC rty) (map foreignToC argtys) False
           Just f -> return f

lookupVar :: L.Module -> [L.Value] -> LVar -> IO L.Value
lookupVar m s (Loc level) = return $ s !! level
lookupVar m s (Glob name)
    = do maybeVal <- L.getNamedGlobal m (show name)
         case maybeVal of
           Nothing -> ierror $ "Undefined global: " ++ (show name)
           Just val -> return val

toLLVMExp :: Prims ->
             L.Module ->  -- Current module
             L.Value ->   -- Current function
             L.Builder -> -- IR Cursor
             L.Value ->   -- VM pointer
             [L.Value] -> -- De Bruijn levels
             SExp ->      -- Expression to process
             IO L.Value
toLLVMExp p m f b vm s (SV v) = lookupVar m s v
-- TODO: Verify consistency of definition of tail call w/ LLVM
toLLVMExp p m f b vm s (SApp isTail name vars)
    = do maybeCallee <- L.getNamedFunction m (llname name)
         case maybeCallee of
           Nothing -> ierror $ "Undefined function: " ++ (show name)
           Just callee -> do
             args <- mapM (lookupVar m s) vars
             call <- L.buildCall b callee (vm:args) ""
             conv <- L.getFunctionCallConv callee
             L.setInstructionCallConv call conv
             L.setTailCall call isTail
             return call
toLLVMExp p m f b vm s (SLet name value body)
    = do v <- toLLVMExp p m f b vm s value
         case name of
           Glob n -> L.setValueName v (show name)
           Loc _  -> return ()
         toLLVMExp p m f b vm (s ++ [v]) body
toLLVMExp p m f b vm s (SCon tag _ vars)
    = mapM (lookupVar m s) vars >>= buildCon p b vm tag
toLLVMExp p m f b vm s (SCase var alts')
    = do let (alts, defaultAlt) =
                 foldl (\accum alt ->
                            case alt of
                              SDefaultCase exp -> (fst accum, Just alt)
                              _                -> (alt : fst accum, snd accum))
                       ([], Nothing) alts'
         let caseCount = case defaultAlt of
                           Just _  -> length alts - 1 -- Default case is treated specially
                           Nothing -> length alts
         value <- lookupVar m s var
         initialBlock <- L.getInsertBlock b
         switchBB <- case head alts of
                       SConCase _ _ _ _ _ ->
                           do bb <- L.appendBasicBlock f "switch"
                              L.positionAtEnd b bb
                              return $ Just bb
                       _ -> return Nothing
         ctorPtr <- L.buildStructGEP b value 1 ""
         altEntryBlocks <- mapM (\_ -> L.appendBasicBlock f "alt") alts
         endBlock <- L.appendBasicBlock f "endCase"
         builtAlts <- mapM (uncurry $ buildAlt p m f vm s ctorPtr endBlock) $ zip altEntryBlocks alts
         (defaultEntry, defaultExit, defaultVal) <-
             case defaultAlt of
               Just alt -> do defaultBlock <- L.appendBasicBlock f "default"
                              fmap (\(a, b) -> (defaultBlock, Just a, Just b))
                                $ buildAlt p m f vm s ctorPtr endBlock defaultBlock alt
               Nothing  -> do block <- buildCaseFail p f; return (block, Nothing, Nothing)
         let defSwitch value = do
               s <- L.buildSwitch b value defaultEntry (fromIntegral caseCount)
               mapM_ (uncurry $ L.addCase s)
                     $ map (\(alt, entry) -> case alt of
                                      SConCase _ ctorTag _ _ _ -> do
                                          (L.constInt L.int32Type (fromIntegral ctorTag) True, entry)
                                      SConstCase (I i) _ ->
                                          (L.constInt L.int32Type (fromIntegral i) True, entry)
                                      SConstCase _ _ -> ierror "Unimplemented case on non-int primitive")
                           $ zip alts altEntryBlocks
               return s
         case switchBB of
           Just switchBB ->
               do tagPtr <- L.buildStructGEP b ctorPtr 0 ""
                  tag <- L.buildLoad b tagPtr "tag"
                  defSwitch tag
                  L.positionAtEnd b initialBlock
                  isInt <- buildIsInt b value
                  L.buildCondBr b isInt defaultEntry switchBB
           Nothing -> idrToNative b FInt value >>= defSwitch
         L.positionAtEnd b endBlock
         phi <- L.buildPhi b (L.pointerType (valTy p) 0) "caseResult"
         results <- foldM (\accum (exit, value) -> do
                             unreachable <- L.isUnreachable value
                             return $ if unreachable then accum else (value, exit):accum)
                    [] builtAlts
         L.addIncoming phi results
         case (defaultExit, defaultVal) of
           (Just exit, Just val) ->
               do unreachable <- L.isUnreachable val
                  unless unreachable $ L.addIncoming phi [(val, exit)]
           _ -> return ()
         return phi
toLLVMExp p m f b vm s (SConst const)
    = case const of
        I i   -> buildInt p b $ L.constInt L.int32Type (fromIntegral i) True
        BI i | i < (2^30) -> L.buildCall b (primMkBigI p) [L.constInt L.int32Type (fromIntegral i) True] ""
             | otherwise  -> do str <- L.buildGlobalStringPtr b (show i) "bigIntLiteral"
                                L.buildCall b (primMkBigC p) [vm, str] ""
        Fl f  -> buildFloat p b vm $ L.constReal L.doubleType $ realToFrac f
        Ch c  -> buildInt p b $ L.constInt L.int32Type (fromIntegral $ fromEnum c) True
        Str s -> L.buildGlobalStringPtr b s "stringLiteral" >>= buildStr p b vm
        _ -> return $ L.getUndef $ L.pointerType (valTy p) 0 -- Type values are undefined
toLLVMExp p m f b vm s (SForeign lang ftype name args)
    = case lang of
        LANG_C -> do ffun <- ensureBound m name ftype $ map fst args
                     argVals <- mapM (\(fty, v) -> do
                                        idrVal <- lookupVar m s v
                                        idrToNative b fty idrVal)
                                     args
                     L.buildCall b ffun argVals "" >>= cToIdr p b ftype vm
toLLVMExp p m f b vm s (SOp prim vars)
    = do args <- mapM (lookupVar m s) vars
         let icmp op = do x <- idrToNative b FInt $ args !! 0
                          y <- idrToNative b FInt $ args !! 1
                          v <- L.buildICmp b op x y ""
                          bool <- L.buildZExt b v (foreignToC FInt) ""
                          cToIdr p b FInt vm bool
             fcmp op = do x <- idrToNative b FDouble $ args !! 0
                          y <- idrToNative b FDouble $ args !! 1
                          v <- L.buildFCmp b op x y ""
                          bool <- L.buildZExt b v (foreignToC FInt) ""
                          cToIdr p b FInt vm bool
             binOp ty f = do x <- idrToNative b ty $ args !! 0
                             y <- idrToNative b ty $ args !! 1
                             v <- f b x y ""
                             cToIdr p b ty vm v
             binPr prim = L.buildCall b (prim p) [vm, args !! 0, args !! 1] ""
             unPr prim  = L.buildCall b (prim p) [vm, args !! 0] ""
             fpPr prim  = do x <- idrToNative b FDouble $ args !! 0
                             L.buildCall b (primFExp p) [x] ""
         case prim of
           LPlus  -> binOp FInt L.buildAdd
           LMinus -> binOp FInt L.buildSub
           LTimes -> binOp FInt L.buildMul
           LDiv   -> binOp FInt L.buildSDiv
           LEq -> icmp L.IntEQ
           LLt -> icmp L.IntSLT
           LLe -> icmp L.IntSLE
           LGt -> icmp L.IntSGT
           LGe -> icmp L.IntSGE
           LFPlus  -> binOp FDouble L.buildFAdd
           LFMinus -> binOp FDouble L.buildFSub
           LFTimes -> binOp FDouble L.buildFMul
           LFDiv   -> binOp FDouble L.buildFDiv
           LFEq -> fcmp L.FPOEQ
           LFLt -> fcmp L.FPOLT
           LFLe -> fcmp L.FPOLE
           LFGt -> fcmp L.FPOGT
           LFGe -> fcmp L.FPOGE
           LBPlus     -> binPr primBigPlus
           LBMinus    -> binPr primBigMinus
           LBTimes    -> binPr primBigTimes
           LBDiv      -> binPr primBigDivide
           LBEq       -> binPr primBigEq
           LBLt       -> binPr primBigLt
           LBLe       -> binPr primBigLe
           LBGt       -> binPr primBigGt
           LBGe       -> binPr primBigGe
           LStrConcat -> binPr primConcat
           LStrLt     -> binPr primStrlt
           LStrEq     -> binPr primStreq
           LStrLen    -> binPr primStrlen
           LStrCons   -> binPr primStrCons
           LStrIndex  -> binPr primStrIndex
           LIntStr    -> unPr primCastIntStr
           LStrInt    -> unPr primCastStrInt
           LFloatStr  -> unPr primCastFloatStr
           LStrFloat  -> unPr primCastStrFloat
           LIntBig    -> unPr primCastIntBig
           LBigInt    -> unPr primCastBigInt
           LStrBig    -> unPr primCastStrBig
           LBigStr    -> unPr primCastBigStr
           LStrHead   -> unPr primStrHead
           LStrTail   -> unPr primStrTail
           LStrRev    -> unPr primStrRev
           LFExp      -> fpPr primFExp
           LFLog      -> fpPr primFLog
           LFSin      -> fpPr primFSin
           LFCos      -> fpPr primFCos
           LFTan      -> fpPr primFTan
           LFASin     -> fpPr primFASin
           LFACos     -> fpPr primFACos
           LFATan     -> fpPr primFATan
           LFSqrt     -> fpPr primFSqrt
           LFFloor    -> fpPr primFFloor
           LFCeil     -> fpPr primFCeil
           LPrintNum -> do fmt <- L.buildGlobalStringPtr b "%d" ""
                           num <- idrToNative b FInt $ args !! 0
                           stdout <- L.buildLoad b (primStdout p) ""
                           L.buildCall b (fprintf p) [stdout, fmt, num] ""
                           buildUnit p b vm
           LPrintStr -> do fmt <- L.buildGlobalStringPtr b "%s" ""
                           str <- idrToNative b FString $ args !! 0
                           stdout <- L.buildLoad b (primStdout p) ""
                           L.buildCall b (fprintf p) [stdout, fmt, str] ""
                           buildUnit p b vm
           LReadStr -> do ptrPtr <- L.buildStructGEP b (args !! 0) 1 ""
                          ptr <- idrToNative b FPtr $ args !! 0
                          L.buildCall b (primReadStr p) [vm, ptr] ""
           LIntFloat ->
               do x <- idrToNative b FInt $ args !! 0
                  f <- L.buildSIToFP b x L.doubleType ""
                  buildFloat p b vm f
           LFloatInt ->
               do x <- idrToNative b FDouble $ args !! 0
                  f <- L.buildFPToSI b x L.int32Type ""
                  buildFloat p b vm f
           LNoOp -> return $ L.getUndef $ L.pointerType (valTy p) 0
           _ -> fail $ "Unimplemented primitive operator: " ++ show prim
toLLVMExp p m f b vm s (SError message)
    = buildError p b message
toLLVMExp p m f b vm s (SProj var index)
    = do v <- lookupVar m s var
         p <- L.buildInBoundsGEP b v
              [ L.constInt L.int32Type 0 True
              , L.constInt L.int32Type 1 True
              , L.constInt L.int32Type 2 True
              , L.constInt L.int32Type (fromIntegral index) True
              ] ""
         L.buildLoad b p ""
toLLVMExp p _ _ _ _ _ SNothing = return $ L.getUndef $ L.pointerType (valTy p) 0

ierror :: String -> a
ierror msg = error $ "CodegenLLVM: INTERNAL ERROR: " ++ msg
