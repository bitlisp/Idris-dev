module IRTS.EscapeAnalysis
    -- ( EExp'(..)
    -- , EAlt(..)
    -- , EDecl(..)
    -- , markEscapes
    -- )
    where

import IRTS.Lang (LVar(..), FLang(..), FType(..), PrimFn(..))
import IRTS.Simplified
import Core.TT (Name(..), Const(..))
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Control.Applicative ((<$>), (<*>))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.ST
import Data.STRef

data EExp' a -- Parameter is used for capture annotations
    = EV LVar
    | EApp Bool Name [LVar]
    | ELet LVar (EExp' a) (EExp' a)
    | EUpdate LVar (EExp' a)
    | ECon a Int Name [LVar]
    | ECase LVar [EAlt' a]
    | EChkCase LVar [EAlt' a]
    | EProj LVar Int
    | EConst a Const
    | EForeign FLang FType String [(FType, LVar)]
    | EOp PrimFn [LVar]
    | ENothing -- erased value, will never be inspected
    | EError String
  deriving Show

data Escape = None -- Does not escape
            | Local -- Escapes into the return value
            | Global -- Escapes into global state
              deriving (Show, Eq)

type EExp = EExp' Escape
type FExp s = EExp' (Flag s)

data EAlt' a = EConCase Int Int Name [Name] (EExp' a)
             | EConstCase Const (EExp' a)
             | EDefaultCase (EExp' a)
  deriving Show

type EAlt = EAlt' Escape
type FAlt s = EAlt' (Flag s)

data EDecl' a = EFun Name [(a, Name)] Int (EExp' a)
  deriving Show

type EDecl = EDecl' Escape
type FDecl s = EDecl' (Flag s)

type Flag s = STRef s Escape

data Constraint a = ImpliesF a a
                  | ImpliesC a [Constraint a]
                    deriving (Eq, Show)

data EAEnv s = EAEnv { eaeVarFlags :: [Flag s]
                     , eaeFName :: Name
                     , eaeContext :: Map Name [Flag s]

                     -- if Nothing, current value unconditionally escapes
                     -- if Just var, current value escapes if the given var escapes
                     , eaeCurrentFlag :: Flag s
                     }

data EAOut s = EAOut { eaoLocalGiven :: [Flag s]
                     , eaoPossible :: [Constraint (Flag s)]
                     , eaoGlobalGiven :: [Flag s]
                     , eaoGlobalPossible :: [Constraint (Flag s)]
                     }

instance Monoid (EAOut s) where
    mempty = EAOut [] [] [] []
    mappend (EAOut es cs gs gcs) (EAOut es' cs' gs' gcs') =
        EAOut (es ++ es') (cs ++ cs') (gs ++ gs') (gcs ++ gcs')

type EA s = ReaderT (EAEnv s) (WriterT (EAOut s) (ST s))

liftST :: ST s a -> EA s a
liftST = lift . lift

runEA :: Map Name [Flag s] -> Name -> Flag s -> EA s a -> ST s (a, EAOut s)
runEA ctxt fname retflag ea =
    runWriterT (runReaderT ea (EAEnv { eaeVarFlags = case M.lookup fname ctxt of
                                                       Just n -> n
                                                       Nothing -> error "IRTS.EscapeAnalysis.runEA: impossible"
                                     , eaeContext = ctxt
                                     , eaeFName = fname
                                     , eaeCurrentFlag = retflag } ))

addConstraint :: Constraint (Flag s) -> EA s ()
addConstraint c = tell (EAOut [] [c] [] [])

addConstraints :: [Constraint (Flag s)] -> EA s ()
addConstraints cs = tell (EAOut [] cs [] [])

addRootEscape :: Flag s -> EA s ()
addRootEscape e = tell (EAOut [e] [] [] [])

addGlobalEscape :: Flag s -> EA s ()
addGlobalEscape e = tell (EAOut [] [] [e] [])

-- Constraints that are only triggered by globals
addGlobalConstraints :: [Constraint (Flag s)] -> EA s ()
addGlobalConstraints c = tell (EAOut [] [] [] c)

argFlags :: Name -> EA s [Flag s]
argFlags n = do
  ctxt <- fmap eaeContext ask
  case M.lookup n ctxt of
    Just fs -> return fs
    Nothing -> error $ "IRTS.EscapeAnalysis: Call to undefined function " ++ show n

argFlag :: Name -> Int -> EA s (Flag s)
argFlag func idx = fmap (!! idx) (argFlags func)

getCurrentFlag :: EA s (Flag s)
getCurrentFlag = fmap eaeCurrentFlag ask

definingVar :: EA s a -> EA s (Flag s, a)
definingVar x = do
  flag <- liftST (newSTRef None)
  ret <- local (\e -> e { eaeCurrentFlag = flag }) x
  return (flag, ret)

withVar :: LVar -> Flag s -> EA s a -> EA s a
withVar (Loc v) flag x = local (\e -> e { eaeVarFlags = eaeVarFlags e ++ [flag] }) x

getFlag :: LVar -> EA s (Flag s)
getFlag (Loc l) = do
  e <- ask
  return $ eaeVarFlags e !! l

freezeDecl :: FDecl s -> ST s EDecl
freezeDecl (EFun name args arity body) = do
  argEscapes <- mapM (readSTRef . fst) args
  body' <- freezeExp body
  return $ EFun name (zip argEscapes (map snd args)) arity body'

freezeExp :: FExp s -> ST s EExp
freezeExp (ELet var val body) = ELet var <$> freezeExp val <*> freezeExp body
freezeExp (EUpdate var e) = EUpdate var <$> freezeExp e
freezeExp (ECon flag tag name args) = do f <- readSTRef flag; return $ ECon f tag name args
freezeExp (ECase var alts) = ECase var <$> mapM freezeAlt alts
freezeExp (EChkCase var alts) = EChkCase var <$> mapM freezeAlt alts
freezeExp (EConst flag c) = EConst <$> readSTRef flag <*> return c
freezeExp (EV v) = return $ EV v
freezeExp (EApp tc n as) = return $ EApp tc n as
freezeExp (EProj v i) = return $ EProj v i
freezeExp (EForeign l r n as) = return $ EForeign l r n as
freezeExp (EOp op as) = return $ EOp op as
freezeExp ENothing = return ENothing
freezeExp (EError msg) = return $ EError msg

freezeAlt :: FAlt s -> ST s EAlt
freezeAlt (EConCase i j n ns e) = EConCase i j n ns <$> freezeExp e
freezeAlt (EConstCase c e) = EConstCase c <$> freezeExp e
freezeAlt (EDefaultCase e) = EDefaultCase <$> freezeExp e

analyzeDecls :: [SDecl] -> [EDecl]
analyzeDecls d = runST (mapM freezeDecl <=< markEscapes $ d)

-- Test decls
identity = SFun (UN "identity") [UN "x"] 1 (SV (Loc 0))
simpleLet = SFun (UN "nestedLet") [UN "x"] 1 (SLet (Loc 1) (SV (Loc 0)) (SV (Loc 1)))
double = SFun (UN "double") [UN "x"] 1 (SOp LPlus [Loc 0, Loc 0])
mutualOne = SFun (UN "mutualOne") [UN "x"] 1 (SApp True (UN "mutualTwo") [Loc 0])
mutualTwo = SFun (UN "mutualTwo") [UN "x"] 1 (SApp True (UN "mutualOne") [Loc 0])
mutualEscOne = SFun (UN "mutualOne") [UN "x"] 1 (SApp True (UN "mutualEscTwo") [Loc 0])
mutualEscTwo = SFun (UN "mutualTwo") [UN "x"] 1
               (SCase (Loc 0) [ SDefaultCase (SApp True (UN "mutualEscOne") [Loc 0])
                              , SConstCase (I 42) (SV (Loc 0))])

markEscapes :: [SDecl] -> ST s [FDecl s]
markEscapes decls = do
  ctxt <- forM decls (\(SFun name argNames arity body) ->
                          fmap ((,) name) (replicateM arity (newSTRef None)))
  results <- mapM (constrainDecl (M.fromList ctxt)) decls
  let (givens, constraints, givenGlobals, globalConstraints) =
          foldl (\(gacc, cacc, ggacc, gcacc) (_, EAOut g c gg gc) ->
                     (g ++ gacc, c ++ cacc, gg ++ ggacc, gc ++ gcacc)
                ) ([], [], [], []) results
      (localEsc, _) = solve ((map (snd . fst) results) ++ givens) constraints
      (globalEsc, _) = solve givenGlobals (globalConstraints ++ constraints)
  mapM (flip writeSTRef Local) (givens ++ localEsc)
  mapM (flip writeSTRef Global) (givenGlobals ++ globalEsc)
  return $ map (fst . fst) results

constrainDecl :: Map Name [Flag s] -> SDecl -> ST s ((FDecl s, Flag s), EAOut s)
constrainDecl ctxt (SFun name args arity body) = do
  retFlag <- newSTRef Local
  runEA ctxt name retFlag $ do
    body' <- constrain body
    afs <- argFlags name
    return (EFun name (zip afs args) arity body', retFlag)

solve :: Eq a => [a] -> [Constraint a] -> ([a], [Constraint a])
solve gs cs = case runState (runWriterT (mapM_ propagate gs)) cs of
                ((_, as), cs')
                    | cs == cs' -> (as, cs)
                    | otherwise -> let (as', cs'') = solve (as ++ gs) cs' in
                                   (as ++ as', cs'')

propagate :: Eq a => a -> WriterT [a] (State [Constraint a]) ()
propagate g = do
  cs <- get
  cs' <- foldM (\cs' c -> case resolve g c of
                            Nothing -> return (c:cs')
                            Just (Left x) -> tell [x] >> return cs'
                            Just (Right cs'') -> return (cs'' ++ cs')
               ) [] cs
  put cs'
  return ()

-- Does not recurse
resolve :: Eq a => a -> Constraint a -> (Maybe (Either a [Constraint a]))
resolve a (ImpliesF b c)
    | a == b = Just (Left c)
    | b == c = Just (Right [])
    | otherwise = Nothing
resolve a (ImpliesC b c)
    | a == b = Just (Right c)
    | otherwise = Nothing

constrain :: SExp -> EA s (FExp s)
constrain (SV var@(Loc _)) = do
  varFlag <- getFlag var
  cf <- getCurrentFlag
  addConstraint (ImpliesF cf varFlag)
  return $ EV var
constrain (SApp tc n args) = do
  argImplications <-
      forM (zip [0..] args) $ \(idx, arg) ->
          do vf <- getFlag arg
             af <- argFlag n idx
             return (ImpliesF af vf)
  addGlobalConstraints argImplications
  flag <- getCurrentFlag
  addConstraint (ImpliesC flag argImplications)
  return $ EApp tc n args
constrain (SLet var value body) = do
  (newFlag, value') <- definingVar (constrain value)
  body' <- withVar var newFlag (constrain body)
  return $ ELet var value' body'
constrain (SUpdate var e) = fmap (EUpdate var) (constrain e)
constrain (SCon tag name args) = do
  cf <- getCurrentFlag
  addConstraints =<< fmap (map (ImpliesF cf)) (mapM getFlag args)
  return $ ECon cf tag name args
constrain (SCase var alts) = fmap (ECase var) (mapM constrainAlts alts)
constrain (SChkCase var alts) = fmap (EChkCase var) (mapM constrainAlts alts)
constrain (SProj var idx) = return $ EProj var idx
constrain (SConst c) = do
  cf <- getCurrentFlag
  return $ EConst cf c
constrain (SForeign lang ret name args) = do -- TODO: Support capture annotations
  mapM_ (addGlobalEscape <=< getFlag . snd) args
  return $ EForeign lang ret name args
constrain (SOp op args) = do
  cf <- getCurrentFlag
  case primCaptures op of
    Global -> mapM_ (addGlobalEscape <=< getFlag) args -- Trivially escapes into global state
    Local -> addConstraints =<< mapM ((fmap (ImpliesF cf)) . getFlag) args
    None -> return ()
  return $ EOp op args
constrain SNothing = return ENothing
constrain (SError msg) = return $ EError msg

constrainAlts :: SAlt -> EA s (FAlt s)
constrainAlts (SConCase i j n ns body) = fmap (EConCase i j n ns) (constrain body)
constrainAlts (SConstCase c e) = fmap (EConstCase c) (constrain e)
constrainAlts (SDefaultCase e) = fmap EDefaultCase (constrain e)

-- Can a given primitive's argument's memory allocation end up as (part of) its return value?
primCaptures :: PrimFn -> Escape
primCaptures LPar = Local
primCaptures LStrTail = Local
primCaptures _ = None
