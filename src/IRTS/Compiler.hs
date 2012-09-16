{-# LANGUAGE PatternGuards #-}

module IRTS.Compiler where

import IRTS.Lang
import IRTS.Defunctionalise
import IRTS.Simplified
import IRTS.CodegenCommon

import Idris.AbsSyntax
import Core.TT
import Core.Evaluate
import Core.CaseTree

import Control.Monad.State
import Data.List
import System.Process
import System.IO
import System.Directory
import System.Environment

import Paths_idris

genCode :: Codegen -> FilePath -> Term -> Idris ()
genCode codegen f tm
    = do checkMVs
         let tmnames = namesUsed (STerm tm)
         used <- mapM (allNames []) tmnames
         defsIn <- mkDecls tm (concat used)
         maindef <- irMain tm
         let defs = defsIn ++ [(MN 0 "runMain", maindef)]
         -- iputStrLn $ showSep "\n" (map show defs)
         let (nexttag, tagged) = addTags 0 (liftAll defs)
         let ctxtIn = addAlist tagged emptyContext
         let defuns = defunctionalise nexttag ctxtIn
         -- iputStrLn $ showSep "\n" (map show (toAlist defuns))
         let checked = checkDefs defuns (toAlist defuns)
         case checked of
           OK c -> do -- iputStrLn $ showSep "\n" (map show c)
                      liftIO $ codegen c f Executable [] "" NONE
           Error e -> fail $ show e
  where checkMVs = do i <- get
                      case idris_metavars i \\ primDefs of
                            [] -> return ()
                            ms -> fail $ "There are undefined metavariables: " ++ show ms
        inDir d h = do let f = d ++ "/" ++ h
                       ex <- doesFileExist f
                       if ex then return f else return h

irMain :: TT Name -> Idris LDecl
irMain tm = do i <- ir tm
               return $ LFun (MN 0 "runMain") [] (LForce i)

allNames :: [Name] -> Name -> Idris [Name]
allNames ns n | n `elem` ns = return []
allNames ns n = do i <- get
                   case lookupCtxt Nothing n (idris_callgraph i) of
                      [ns'] -> do more <- mapM (allNames (n:ns)) ns' 
                                  return (nub (n : concat more))
                      _ -> return [n]

mkDecls :: Term -> [Name] -> Idris [(Name, LDecl)]
mkDecls t used 
    = do i <- getIState
         let ds = filter (\ (n, d) -> n `elem` used || isCon d) $ ctxtAlist (tt_ctxt i)
         decls <- mapM build ds
         return decls

isCon (TyDecl _ _) = True
isCon _ = False

class ToIR a where
    ir :: a -> Idris LExp

build :: (Name, Def) -> Idris (Name, LDecl)
build (n, d)
    = do i <- getIState
         case lookup n (idris_scprims i) of
              Just (ar, op) -> 
                  let args = map (\x -> MN x "op") [0..] in
                      return (n, (LFun n (take ar args) 
                                         (LOp op (map (LV . Glob) (take ar args)))))
              _ -> do def <- mkLDecl n d
                      logLvl 3 $ "Compiled " ++ show n ++ " =\n\t" ++ show def
                      return (n, def)

declArgs args n (LLam xs x) = declArgs (args ++ xs) n x
declArgs args n x = LFun n args x 

mkLDecl n (Function tm _) = do e <- ir tm
                               return (declArgs [] n e)
mkLDecl n (CaseOp _ _ pats _ _ args sc) = do e <- ir (args, sc)
                                             return (declArgs [] n e)
mkLDecl n (TyDecl (DCon t a) _) = return $ LConstructor n (-1) a
mkLDecl n (TyDecl (TCon t a) _) = return $ LConstructor n (-1) a
mkLDecl n _ = return (LFun n [] (LError ("Impossible declaration " ++ show n)))

instance ToIR (TT Name) where 
    ir tm = ir' [] tm where
      ir' env tm@(App f a)
          | (P _ (UN "mkForeign") _, args) <- unApply tm
              = doForeign args
          | (P _ (UN "unsafePerformIO") _, [_, arg]) <- unApply tm
              = ir' env arg
          | (P _ (UN "lazy") _, [_, arg]) <- unApply tm
              = do arg' <- ir' env arg
                   return $ LLazyExp arg'
          | (P _ (UN "prim__IO") _, [v]) <- unApply tm
              = do v' <- ir' env v
                   return v'
          | (P _ (UN "io_bind") _, [_,_,v,k]) <- unApply tm
              = do v' <- ir' env v 
                   k' <- ir' env k
                   return (LApp False k' [LForce v'])
          | (P _ (UN "malloc") _, [_,size,t]) <- unApply tm
              = do size' <- ir' env size
                   t' <- ir' env t
                   return t' -- TODO $ malloc_ size' t'
          | (P _ (UN "trace_malloc") _, [_,t]) <- unApply tm
              = do t' <- ir' env t
                   return t' -- TODO
          | (P (DCon t a) n _, args) <- unApply tm
              = irCon env t a n args
          | (f, args) <- unApply tm
              = do f' <- ir' env f
                   args' <- mapM (ir' env) args
                   return (LApp False f' args')
      ir' env (P _ n _) = return $ LV (Glob n)
      ir' env (V i)     = return $ LV (Glob (env!!i))
      ir' env (Bind n (Lam _) sc)
          = do sc' <- ir' (n : env) sc
               return $ LLam [n] sc'
      ir' env (Bind n (Let _ v) sc)
          = do sc' <- ir' (n : env) sc
               v' <- ir' env v
               return $ LLet n v' sc'
      ir' env (Bind _ _ _) = return $ LConst (I 424242)
      ir' env (Constant c) = return $ LConst c
      ir' env _ = return $ LError "Impossible"

      irCon env t arity n args
        | length args == arity = buildApp env (LV (Glob n)) args
        | otherwise = let extra = satArgs (arity - length args) in
                          do sc' <- irCon env t arity n 
                                        (args ++ map (\n -> P Bound n undefined) extra)
                             return $ LLam extra sc'
        
      satArgs n = map (\i -> MN i "sat") [1..n]

      buildApp env e [] = return e
      buildApp env e xs = do xs' <- mapM (ir' env) xs
                             return $ LApp False e xs'

doForeign :: [TT Name] -> Idris LExp
doForeign (_ : fgn : args)
   | (_, (Constant (Str fgnName) : fgnArgTys : ret : [])) <- unApply fgn
        = let tys = getFTypes fgnArgTys
              rty = mkIty' ret in
              do args' <- mapM ir args
                 -- wrap it in a prim__IO
                 -- return $ con_ 0 @@ impossible @@ 
                 return $ LLazyExp $ LForeign LANG_C rty fgnName (zip tys args')
   | otherwise = fail "Badly formed foreign function call"

getFTypes :: TT Name -> [FType]
getFTypes tm = case unApply tm of
                 (nil, []) -> []
                 (cons, [ty, xs]) -> 
                    let rest = getFTypes xs in
                        mkIty' ty : rest

mkIty' (P _ (UN ty) _) = mkIty ty
mkIty' _ = FAny

mkIty "FInt"    = FInt
mkIty "FFloat"  = FDouble
mkIty "FChar"   = FChar
mkIty "FString" = FString
mkIty "FPtr"    = FPtr
mkIty "FUnit"   = FUnit

instance ToIR ([Name], SC) where
    ir (args, tree) = do logLvl 3 $ "Compiling " ++ show args ++ "\n" ++ show tree
                         tree' <- ir tree
                         return $ LLam args tree'

instance ToIR SC where
    ir (STerm t) = ir t
    ir (UnmatchedCase str) = return $ LError str
    ir (Case n alts) = do alts' <- mapM mkIRAlt alts
                          return $ LCase (LV (Glob n)) alts'
      where
        mkIRAlt (ConCase n t args rhs) 
             = do rhs' <- ir rhs
                  return $ LConCase (-1) n args rhs'
        mkIRAlt (ConstCase (I i) rhs)  
             = do rhs' <- ir rhs
                  return $ LConstCase (I i) rhs'
        mkIRAlt (ConstCase IType rhs) 
             = do rhs' <- ir rhs 
                  return $ LDefaultCase rhs'
        mkIRAlt (ConstCase c rhs)      
           = fail $ "Can only pattern match on integer constants (" ++ show c ++ ")"
        mkIRAlt (DefaultCase rhs)
           = do rhs' <- ir rhs
                return $ LDefaultCase rhs'





