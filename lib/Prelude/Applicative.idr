module Prelude.Applicative

import Builtins

---- Applicative functors/Idioms

infixl 2 <$> 

class Applicative (f : Set -> Set) where 
    pure  : a -> f a
    (<$>) : f (a -> b) -> f a -> f b 


