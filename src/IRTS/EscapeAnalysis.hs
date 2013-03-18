module IRTS.EscapeAnalysis where

import IRTS.Lang
import IRTS.Simplified
import Core.TT
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Control.Monad.State
import Control.Monad.Reader

data EExp = EV LVar
          | EApp Bool Name [LVar]
          | ELet LVar EExp EExp
          | EUpdate LVar EExp
          | ECon Bool Int Name [LVar] -- True if escapes
          | ECase LVar [EAlt]
          | EChkCase LVar [EAlt]
          | EProj LVar Int
          | EConst Bool Const -- True if escapes
          | EForeign FLang FType String [(FType, LVar)]
          | EOp PrimFn [LVar]
          | ENothing -- erased value, will never be inspected
          | EError String
  deriving Show

data EAlt = EConCase Int Int Name [Name] EExp
          | EConstCase Const EExp
          | EDefaultCase EExp
  deriving Show

-- Bool indicates capture
data EDecl = EFun Name [(Bool, Name)] Int EExp
  deriving Show

type EA = ReaderT Bool (State IntSet)

runEA :: EA x -> x
runEA ea = evalState (runReaderT ea False) IS.empty

escaping :: LVar -> EA Bool
escaping (Loc l) = do
  locs <- get
  return (IS.member l locs)
escaping _ = return False

escapes :: LVar -> EA ()
escapes (Loc l) = modify (IS.insert l)
escapes _ = return ()

markEscapes :: SDecl -> EDecl
markEscapes (SFun name argNames arity body) =
    runEA . local (const True) $ do
      body' <- markExpEscapes body
      argEscapes <- mapM (escaping . Loc) [0..arity]
      return $ EFun name (zip argEscapes argNames) arity body'

markExpEscapes :: SExp -> EA EExp
markExpEscapes (SV v@(Loc _)) = do
  thisEscapes <- ask
  when thisEscapes (escapes v)
  return $ EV v
markExpEscapes (SApp tc n args) = do
  thisEscapes <- ask
  when thisEscapes (mapM_ escapes args) -- TODO: Don't assume all arguments escape
  return $ EApp tc n args
markExpEscapes (SLet var value body) = do
  body' <- markExpEscapes body
  varEscapes <- escaping var
  value' <- local (const varEscapes) (markExpEscapes value)
  return $ ELet var value' body'
markExpEscapes (SUpdate var e) = fmap (EUpdate var) (markExpEscapes e)
markExpEscapes (SCon tag name args) = do
  thisEscapes <- ask
  when thisEscapes (mapM_ escapes args)
  return $ ECon thisEscapes tag name args
markExpEscapes (SCase var alts) = fmap (ECase var) (mapM markAltEscapes alts)
markExpEscapes (SChkCase var alts) = fmap (EChkCase var) (mapM markAltEscapes alts)
markExpEscapes (SProj var idx) = return $ EProj var idx
markExpEscapes (SConst c) = do
  thisEscapes <- ask
  return $ EConst thisEscapes c
markExpEscapes (SForeign lang ret name args) = do -- TODO: Support capture annotations
  mapM_ (escapes . snd) args
  return $ EForeign lang ret name args
markExpEscapes (SOp op args) = do
  thisEscapes <- ask
  when (thisEscapes && primCaptures op) (mapM_ escapes args)
  return $ EOp op args
markExpEscapes SNothing = return ENothing
markExpEscapes (SError msg) = return $ EError msg

markAltEscapes :: SAlt -> EA EAlt
markAltEscapes (SConCase i j n ns body) = fmap (EConCase i j n ns) (markExpEscapes body)
markAltEscapes (SConstCase c e) = fmap (EConstCase c) (markExpEscapes e)
markAltEscapes (SDefaultCase e) = fmap EDefaultCase (markExpEscapes e)

-- Can a given primitive's argument's memory allocation end up as (part of) its return value?
primCaptures :: PrimFn -> Bool
primCaptures LPar = True
primCaptures LStrTail = True
primCaptures _ = False
