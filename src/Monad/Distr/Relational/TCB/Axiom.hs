-----------------------------------------------------------------
-- | Relational Specifications for Distr Primitives -------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.Distr.Relational.TCB.Axiom where 

import Monad.Distr 
import Monad.Distr.Predicates

{-@ assume pureAxiom :: p:(a -> b -> Bool) 
                    -> x1:a -> x2:b -> {_:_|p x1 x2} 
                    -> {lift p (ppure x1) (ppure x2)} @-}
pureAxiom :: (a -> b -> Bool) -> a -> b -> () -> ()
pureAxiom _ _ _ _ = ()

{-@ assume bindAxiom :: p:(b -> b -> Bool) -> q:(a -> a -> Bool) 
                    -> e1:Distr a -> f1:(a -> Distr b) 
                    -> e2:Distr a -> f2:(a -> Distr b) 
                    -> {_:()|lift q e1 e2} 
                    -> (x1:a -> {x2:a|q x1 x2} -> {lift p (f1 x1) (f2 x2)})
                    -> {lift p (bind e1 f1) (bind e2 f2)} @-}
bindAxiom :: (b -> b -> Bool) -> (a -> a -> Bool) -> 
              Distr a -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> 
              () ->
              (a -> a -> ()) -> 
              ()
bindAxiom _ _ _ _ _ _ _ _ = ()

{-@ assume bernoulliAxiom :: p:Prob -> {q:Prob| leDoubleP p q}
                         ->  {lift leDoubleP (bernoulli p) (bernoulli q)} @-}
bernoulliAxiom :: Prob -> Prob -> ()
bernoulliAxiom _ _ = ()

{-@ assume liftAxiom :: e:Distr a -> {lift eqP e e} @-}
liftAxiom :: Distr a -> ()
liftAxiom _ = ()

{-@ assume liftTrue :: e1:Distr a -> e2:Distr a -> {lift trueP e1 e2} @-}
liftTrue :: Distr a -> Distr a -> ()
liftTrue _ _ = ()