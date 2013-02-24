module Language.Reflection

TTName : Type
TTName = String -- needs to capture namespaces too...

data TT = Var TTName
        | Lam TTName TT TT
        | Pi  TTName TT TT
        | Let TTName TT TT TT
        | App TTName TT TT

data Tactic = Try Tactic Tactic
            | GoalType TTName Tactic -- only run if the goal has the right type
            | Refine TTName
            | Seq Tactic Tactic
            | Trivial
            | Solve
            | Exact TT -- not yet implemented

