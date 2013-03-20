module IRTS.EscapeAnalysis
    -- ( EExp'(..)
    -- , EAlt(..)
    -- , EDecl(..)
    -- , markEscapes
    -- )
    where

import IRTS.Lang (LVar(..), FLang(..), FType(..), PrimFn(..))
import IRTS.Simplified
import Core.TT (Name, Const)
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
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

type EExp = EExp' Bool
type FExp s = EExp' (STRef s Bool)

data EAlt' a = EConCase Int Int Name [Name] (EExp' a)
             | EConstCase Const (EExp' a)
             | EDefaultCase (EExp' a)
  deriving Show

type EAlt = EAlt' Bool
type FAlt s = EAlt' (STRef s Bool)

data EDecl' a = EFun Name [(a, Name)] Int (EExp' a)
  deriving Show

type EDecl = EDecl' Bool
type FDecl s = EDecl' (STRef s Bool)

data Constraint a = ImpliesF a a
                  | ImpliesC a [Constraint a]
                    deriving (Eq, Show)

data EAEnv s = EAEnv { eaeVarFlags :: [STRef s Bool]
                     , eaeFName :: Name

                     -- if Nothing, current value unconditionally escapes
                     -- if Just var, current value escapes if the given var escapes
                     , eaeCurrentVar :: Maybe Int
                     }

initialEnv :: EAEnv s
initialEnv = EAEnv { eaeVarFlags = []
                   , eaeFName = error "IRTS.EscapeAnalysis: Function name not set"
                   , eaeCurrentVar = Nothing
                   }

data EAOut s = EAOut [STRef s Bool] [Constraint (STRef s Bool)]

instance Monoid (EAOut s) where
    mempty = EAOut [] []
    mappend (EAOut es cs) (EAOut es' cs') = EAOut (es ++ es') (cs ++ cs')

type EA s = ReaderT (EAEnv s) (WriterT (EAOut s) (StateT (IntMap (STRef s Bool)) (ST s)))

liftST :: ST s a -> EA s a
liftST = lift . lift . lift

runEA :: EA s a -> ST s (a, EAOut s)
runEA ea = evalStateT (runWriterT (runReaderT ea initialEnv)) IM.empty

addConstraint :: Constraint (STRef s Bool) -> EA s ()
addConstraint c = tell (EAOut [] [c])

addConstraints :: [Constraint (STRef s Bool)] -> EA s ()
addConstraints cs = tell (EAOut [] cs)

addRootEscape :: STRef s Bool -> EA s ()
addRootEscape e = tell (EAOut [e] [])

addEscape :: LVar -> EA s ()
addEscape v@(Loc l) = do f <- getFlag v; modify (IM.insert l f);
addEscape _ = return ()

dropEscape :: LVar -> EA s ()
dropEscape (Loc l) = modify (IM.delete l)
dropEscape _ = return ()

argFlag :: Name -> Int -> EA s (STRef s Bool)
argFlag func idx = do
  self <- fmap eaeFName ask
  case func == self of
    True -> getFlag (Loc idx)
    False -> liftST (newSTRef True) -- TODO

getEscape :: LVar -> EA s (Maybe (STRef s Bool))
getEscape (Loc l) = gets (IM.lookup l)

getCurrentVar :: EA s (Maybe LVar)
getCurrentVar = fmap (fmap Loc . eaeCurrentVar) ask

getCurrentFlag :: EA s (Maybe (STRef s Bool))
getCurrentFlag = do
  v <- getCurrentVar
  case v of
    Just v -> fmap Just (getFlag v)
    Nothing -> return Nothing

withNewVar :: LVar -> EA s a -> EA s a
withNewVar (Loc v) x = do
  flag <- liftST (newSTRef False)
  local (\e -> e { eaeCurrentVar = Just v
                 , eaeVarFlags = eaeVarFlags e ++ [flag]
                 }) x

getFlag :: LVar -> EA s (STRef s Bool)
getFlag (Loc l) = do
  e <- ask
  return $ eaeVarFlags e !! l

markEscapes :: SDecl -> ST s (FDecl s)
markEscapes (SFun name argNames arity body) = do
  ((body, argFlags), EAOut givens constraints) <-
      runEA $ do
        argFlags <- mapM (const (liftST (newSTRef False))) argNames
        body' <- local (\e -> e { eaeVarFlags = argFlags, eaeFName = name } ) (constrain body)
        return (body', argFlags)
  mapM (flip writeSTRef True) givens
  let (escaped, _) = solve givens constraints
  mapM (flip writeSTRef True) escaped
  return $ EFun name (zip argFlags argNames) arity body

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
  case cf of
    Just flag -> addConstraint (ImpliesF flag varFlag)
    Nothing -> addEscape var
  return $ EV var
constrain (SApp tc n args) = do
  argImplications <-
      forM (zip [0..] args) $ \(idx, arg) ->
          do vf <- getFlag arg
             af <- argFlag n idx
             return (ImpliesF af vf)
  cf <- getCurrentFlag
  case cf of
    Just flag -> addConstraint (ImpliesC flag argImplications)
    Nothing -> addConstraints argImplications
  return $ EApp tc n args
constrain (SLet var value body) = do
  value' <- withNewVar var (constrain value)
  body' <- constrain body
  varEscape <- getEscape var
  cf <- getCurrentFlag
  case (varEscape, cf) of
    (Nothing, _) -> return ()
    (Just varFlag, Just flag) -> addConstraint (ImpliesF flag varFlag)
    (Just varFlag, Nothing) -> addRootEscape varFlag
  dropEscape var
  return $ ELet var value' body'
constrain (SUpdate var e) = fmap (EUpdate var) (constrain e)
constrain (SCon tag name args) = do
  cf <- getCurrentFlag
  flag <- case cf of
            Just f -> return f
            Nothing -> liftST (newSTRef True) -- Trivially escapes, won't participate in resolution
  return $ ECon flag tag name args
constrain (SCase var alts) = fmap (ECase var) (mapM constrainAlts alts)
constrain (SChkCase var alts) = fmap (EChkCase var) (mapM constrainAlts alts)
constrain (SProj var idx) = return $ EProj var idx
constrain (SConst c) = do
  cf <- getCurrentFlag
  flag <- case cf of
            Just f -> return f
            Nothing -> liftST (newSTRef True) -- Trivially escapes, won't participate in resolution
  return $ EConst flag c
constrain (SForeign lang ret name args) = do -- TODO: Support capture annotations
  mapM_ (addEscape . snd) args
  return $ EForeign lang ret name args
constrain (SOp op args) = do
  when (primCaptures op) $
       do cf <- getCurrentFlag
          case cf of
            Just f -> addConstraints =<< mapM ((fmap (ImpliesF f)) . getFlag) args
            Nothing -> mapM_ (addRootEscape <=< getFlag) args
  return $ EOp op args
constrain SNothing = return ENothing
constrain (SError msg) = return $ EError msg

constrainAlts :: SAlt -> EA s (FAlt s)
constrainAlts (SConCase i j n ns body) = fmap (EConCase i j n ns) (constrain body)
constrainAlts (SConstCase c e) = fmap (EConstCase c) (constrain e)
constrainAlts (SDefaultCase e) = fmap EDefaultCase (constrain e)

-- Can a given primitive's argument's memory allocation end up as (part of) its return value?
primCaptures :: PrimFn -> Bool
primCaptures LPar = True
primCaptures LStrTail = True
primCaptures _ = False
