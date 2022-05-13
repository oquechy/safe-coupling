-----------------------------------------------------------------
-- | Relational Specifications for PrM Primitives -------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM.Relational.TCB.Spec where 

import Monad.PrM 
import Monad.PrM.Lift 
import Monad.PrM.Predicates
import Monad.PrM.Relational.Rules

import Data.Dist

{-@ pureSpec :: Eq a => p:(a -> a -> Bool) 
                    -> x1:a -> x2:a -> {_:()|p x1 x2} 
                    -> {lift p (ppure x1) (ppure x2)} @-}
pureSpec :: Eq a => (a -> a -> Bool) -> a -> a -> () -> ()
pureSpec p x1 x2 px = pureT Inf p x1 x2 px ()

{-@ assume bindSpec :: (Eq a, Eq b) => p:(b -> b -> Bool) -> q:(a -> a -> Bool) 
                    -> e1:PrM a -> f1:(a -> PrM b) 
                    -> e2:PrM a -> f2:(a -> PrM b) 
                    -> {_:()|lift q e1 e2} 
                    -> (x1:a -> {x2:a|q x1 x2} -> {lift p (f1 x1) (f2 x2)})
                    -> {lift p (bind e1 f1) (bind e2 f2)} @-}
bindSpec :: (Eq a, Eq b) => (b -> b -> Bool) -> (a -> a -> Bool) -> 
              PrM a -> (a -> PrM b) -> PrM a -> (a -> PrM b) -> 
              () ->
              (a -> a -> ()) -> 
              ()
bindSpec _ _ _ _ _ _ _ _ = ()

{-@ assume bernoulliSpec :: p:Prob -> {q:Prob| leDoubleP p q}
                         ->  {lift leDoubleP (bernoulli p) (bernoulli q)} @-}
bernoulliSpec :: Prob -> Prob -> ()
bernoulliSpec _ _ = ()

{-@ assume liftSpec :: Eq a => e:PrM a -> {lift eqP e e} @-}
liftSpec :: Eq a => PrM a -> ()
liftSpec _ = ()


{-@ assume liftTrue :: Eq a => e1:PrM a -> e2:PrM a -> {lift trueP e1 e2} @-}
liftTrue :: Eq a => PrM a -> PrM a -> ()
liftTrue _ _ = ()