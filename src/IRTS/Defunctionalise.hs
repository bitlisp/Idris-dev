module IRTS.Defunctionalise(module IRTS.Defunctionalise, 
                            module IRTS.Lang) where

import IRTS.Lang
import Core.TT

import Debug.Trace
import Data.Maybe
import Data.List

data DExp = DV LVar
          | DApp Bool Name [DExp] -- True = tail call
          | DLet Name DExp DExp -- name just for pretty printing
          | DProj DExp Int
          | DC Int Name [DExp]
          | DCase DExp [DAlt]
          | DConst Const
          | DForeign FLang FType String [(FType, DExp)]
          | DOp PrimFn [DExp]
          | DNothing -- erased value, can be compiled to anything since it'll never
                     -- be inspected
          | DError String
  deriving Eq

data DAlt = DConCase Int Name [Name] DExp
          | DConstCase Const DExp
          | DDefaultCase DExp
  deriving (Show, Eq)

data DDecl = DFun Name [Name] DExp -- name, arg names, definition
           | DConstructor Name Int Int -- constructor name, tag, arity
  deriving (Show, Eq)

type DDefs = Ctxt DDecl

defunctionalise :: Int -> LDefs -> DDefs 
defunctionalise nexttag defs 
     = let all = toAlist defs
           -- sort newcons so that EVAL and APPLY cons get sequential tags
           newcons = sortBy conord $ concatMap toCons (getFn all)
           eval = mkEval newcons
           app = mkApply newcons
           condecls = declare nexttag newcons in
           addAlist (eval : app : condecls ++ (map (addApps defs) all)) emptyContext
   where conord (n, _, _) (n', _, _) = compare n n'

getFn :: [(Name, LDecl)] -> [(Name, Int)]
getFn xs = mapMaybe fnData xs
  where fnData (n, LFun _ args _) = Just (n, length args) 
        fnData _ = Nothing

-- To defunctionalise:
--
-- 1 Create a data constructor for each function
-- 2 Create a data constructor for each underapplication of a function
-- 3 Convert underapplications to their corresponding constructors
-- 4 Create an EVAL function which calls the appropriate function for data constructors
--   created as part of step 1
-- 5 Create an APPLY function which adds an argument to each underapplication (or calls
--   APPLY again for an exact application)
-- 6 Wrap overapplications in chains of APPLY
-- 7 Wrap unknown applications (i.e. applications of local variables) in chains of APPLY
-- 8 Add explicit EVAL to case, primitives, and foreign calls

addApps :: LDefs -> (Name, LDecl) -> (Name, DDecl)
addApps defs o@(n, LConstructor _ t a) = (n, DConstructor n t a) 
addApps defs (n, LFun _ args e) = (n, DFun n args (aa args e))
  where
    aa :: [Name] -> LExp -> DExp
    aa env (LV (Glob n)) | n `elem` env = DV (Glob n)
                         | otherwise = aa env (LApp False (LV (Glob n)) [])
--     aa env e@(LApp tc (MN 0 "EVAL") [a]) = e
    aa env (LApp tc (LV (Glob n)) args)
       = let args' = map (aa env) args in
             case lookupCtxt Nothing n defs of
                [LConstructor _ i ar] -> DApp tc n args'
                [LFun _ as _] -> let arity = length as in
                                     fixApply tc n args' arity
                [] -> chainAPPLY (DV (Glob n)) args'
    aa env (LLazyApp n args)
       = let args' = map (aa env) args in
             case lookupCtxt Nothing n defs of
                [LConstructor _ i ar] -> DApp False n args'
                [LFun _ as _] -> let arity = length as in
                                     fixLazyApply n args' arity
                [] -> chainAPPLY (DV (Glob n)) args'
    aa env (LForce e) = eEVAL (aa env e)
    aa env (LLet n v sc) = DLet n (aa env v) (aa (n : env) sc)
    aa env (LCon i n args) = DC i n (map (aa env) args)
    aa env (LProj t i) = DProj (eEVAL (aa env t)) i
    aa env (LCase e alts) = DCase (eEVAL (aa env e)) (map (aaAlt env) alts)
    aa env (LConst c) = DConst c
    aa env (LForeign l t n args) = DForeign l t n (map (aaF env) args)
    aa env (LOp LFork args) = DOp LFork (map (aa env) args)
    aa env (LOp f args) = DOp f (map (eEVAL . (aa env)) args)
    aa env LNothing = DNothing
    aa env (LError e) = DError e

    aaF env (t, e) = (t, eEVAL (aa env e))

    aaAlt env (LConCase i n args e) = DConCase i n args (aa (args ++ env) e)
    aaAlt env (LConstCase c e) = DConstCase c (aa env e)
    aaAlt env (LDefaultCase e) = DDefaultCase (aa env e)

    fixApply tc n args ar 
        | length args == ar = DApp tc n args
        | length args < ar = DApp tc (mkUnderCon n (ar - length args)) args
        | length args > ar = chainAPPLY (DApp tc n (take ar args)) (drop ar args)

    fixLazyApply n args ar 
        | length args == ar = DApp False (mkFnCon n) args
        | length args < ar = DApp False (mkUnderCon n (ar - length args)) args
        | length args > ar = chainAPPLY (DApp False n (take ar args)) (drop ar args)
                                    
    chainAPPLY f [] = f
    chainAPPLY f (a : as) = chainAPPLY (DApp False (MN 0 "APPLY") [f, a]) as

eEVAL x = DApp False (MN 0 "EVAL") [x]

data EvalApply a = EvalCase a
                 | ApplyCase a
    deriving Show

-- For a function name, generate a list of
-- data constuctors, and whether to handle them in EVAL or APPLY

toCons :: (Name, Int) -> [(Name, Int, EvalApply DAlt)]
toCons (n, i) 
   = (mkFnCon n, i, 
        EvalCase (DConCase (-1) (mkFnCon n) (take i (genArgs 0))
                 (eEVAL (DApp False n (map (DV . Glob) (take i (genArgs 0)))))))
        : mkApplyCase n 0 i

mkApplyCase fname n ar | n == ar = []
mkApplyCase fname n ar 
        = let nm = mkUnderCon fname (ar - n) in
              (nm, n, ApplyCase (DConCase (-1) nm (take n (genArgs 0))
                              (DApp False (mkUnderCon fname (ar - (n + 1))) 
                                          (map (DV . Glob) (take n (genArgs 0) ++ 
                                                                   [MN 0 "arg"])))))
                            : mkApplyCase fname (n + 1) ar

mkEval :: [(Name, Int, EvalApply DAlt)] -> (Name, DDecl)
mkEval xs = (MN 0 "EVAL", DFun (MN 0 "EVAL") [MN 0 "arg"]
                             (mkBigCase (MN 0 "EVAL") 256 (DV (Glob (MN 0 "arg")))
                                 (mapMaybe evalCase xs ++
                                   [DDefaultCase (DV (Glob (MN 0 "arg")))])))
  where
    evalCase (n, t, EvalCase x) = Just x
    evalCase _ = Nothing

mkApply :: [(Name, Int, EvalApply DAlt)] -> (Name, DDecl)
mkApply xs = (MN 0 "APPLY", DFun (MN 0 "APPLY") [MN 0 "fn", MN 0 "arg"]
                             (mkBigCase (MN 0 "APPLY")
                                        256 (DApp False (MN 0 "EVAL")
                                            [DV (Glob (MN 0 "fn"))])
                                 (mapMaybe applyCase xs)))
  where
    applyCase (n, t, ApplyCase x) = Just x
    applyCase _ = Nothing


declare :: Int -> [(Name, Int, EvalApply DAlt)] -> [(Name, DDecl)]
declare t xs = dec' t xs [] where
   dec' t [] acc = reverse acc
   dec' t ((n, ar, _) : xs) acc = dec' (t + 1) xs ((n, DConstructor n t ar) : acc)


genArgs i = MN i "P_c" : genArgs (i + 1)

mkFnCon    n = MN 0 ("P_" ++ show n)
mkUnderCon n 0       = n
mkUnderCon n missing = MN missing ("U_" ++ show n)

instance Show DExp where
   show e = show' [] e where
     show' env (DV (Loc i)) = "var " ++ env!!i
     show' env (DV (Glob n)) = show n
     show' env (DApp _ e args) = show e ++ "(" ++
                                   showSep ", " (map (show' env) args) ++")"
     show' env (DLet n v e) = "let " ++ show n ++ " = " ++ show' env v ++ " in " ++
                               show' (env ++ [show n]) e
     show' env (DC i n args) = show n ++ ")" ++ showSep ", " (map (show' env) args) ++ ")"
     show' env (DProj t i) = show t ++ "!" ++ show i
     show' env (DCase e alts) = "case " ++ show' env e ++ " of {\n\t" ++
                                    showSep "\n\t| " (map (showAlt env) alts)
     show' env (DConst c) = show c
     show' env (DForeign lang ty n args)
           = "foreign " ++ n ++ "(" ++ showSep ", " (map (show' env) (map snd args)) ++ ")"
     show' env (DOp f args) = show f ++ "(" ++ showSep ", " (map (show' env) args) ++ ")"
     show' env (DError str) = "error " ++ show str
     show' env DNothing = "____"

     showAlt env (DConCase _ n args e) 
          = show n ++ "(" ++ showSep ", " (map show args) ++ ") => "
             ++ show' env e
     showAlt env (DConstCase c e) = show c ++ " => " ++ show' env e
     showAlt env (DDefaultCase e) = "_ => " ++ show' env e

-- Divide up a large case expression so that each has a maximum of
-- 'max' branches

mkBigCase cn max arg branches 
   | length branches <= max = DCase arg branches
   | otherwise = -- DCase arg branches -- until I think of something...
       -- divide the branches into groups of at most max (by tag),
       -- generate a new case and shrink, recursively
       let bs = sortBy tagOrd branches
           (all, def) = case (last bs) of
                    DDefaultCase t -> (init all, Just (DDefaultCase t))
                    _ -> (all, Nothing)
           bss = groupsOf max all
           cs = map mkCase bss in
           DCase arg branches

    where mkCase bs = DCase arg bs 

          tagOrd (DConCase t _ _ _) (DConCase t' _ _ _) = compare t t'
          tagOrd (DConstCase c _) (DConstCase c' _) = compare c c'
          tagOrd (DDefaultCase _) (DDefaultCase _) = EQ
          tagOrd (DConCase _ _ _ _) (DDefaultCase _) = LT
          tagOrd (DConCase _ _ _ _) (DConstCase _ _) = LT
          tagOrd (DConstCase _ _) (DDefaultCase _) = LT
          tagOrd (DDefaultCase _) (DConCase _ _ _ _) = GT
          tagOrd (DConstCase _ _) (DConCase _ _ _ _) = GT
          tagOrd (DDefaultCase _) (DConstCase _ _) = GT
          

groupsOf :: Int -> [DAlt] -> [[DAlt]]
groupsOf x [] = []
groupsOf x xs = let (batch, rest) = span (tagLT (x + tagHead xs)) xs in
                    batch : groupsOf x rest
  where tagHead (DConstCase (I i) _ : _) = i
        tagHead (DConCase t _ _ _ : _) = t
        tagHead (DDefaultCase _ : _) = -1 -- must be the end

        tagLT i (DConstCase (I j) _) = i < j
        tagLT i (DConCase j _ _ _) = i < j
        tagLT i (DDefaultCase _) = False

dumpDefuns :: DDefs -> String
dumpDefuns ds = showSep "\n" $ map showDef (toAlist ds)
  where showDef (x, DFun fn args exp) 
            = show fn ++ "(" ++ showSep ", " (map show args) ++ ") = \n\t" ++
              show exp ++ "\n"
        showDef (x, DConstructor n t a) = "Constructor " ++ show n ++ " " ++ show t


