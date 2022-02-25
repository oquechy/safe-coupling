-----------------------------------------------------------------
-- | Relational Specifications for Distr Primitives -------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.Distr.Relational.TCB.Spec where 

import Monad.Distr 
import Monad.Distr.Predicates

{-@ assume pureSpec :: p:(a -> b -> Bool) 
                    -> x1:a -> x2:b -> {_:_|p x1 x2} 
                    -> {lift p (ppure x1) (ppure x2)} @-}
pureSpec :: (a -> b -> Bool) -> a -> b -> () -> ()
pureSpec _ _ _ _ = ()

{-@ assume bindSpec :: p:(b -> b -> Bool) -> q:(a -> a -> Bool) 
                    -> e1:Distr a -> f1:(a -> Distr b) 
                    -> e2:Distr a -> f2:(a -> Distr b) 
                    -> {_:()|lift q e1 e2} 
                    -> (x1:a -> {x2:a|q x1 x2} -> {lift p (f1 x1) (f2 x2)})
                    -> {lift p (bind e1 f1) (bind e2 f2)} @-}
bindSpec :: (b -> b -> Bool) -> (a -> a -> Bool) -> 
              Distr a -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> 
              () ->
              (a -> a -> ()) -> 
              ()
bindSpec _ _ _ _ _ _ _ _ = ()

{-@ assume bernoulliSpec :: p:Prob -> {q:Prob| leDoubleP p q}
                         ->  {lift leDoubleP (bernoulli p) (bernoulli q)} @-}
bernoulliSpec :: Prob -> Prob -> ()
bernoulliSpec _ _ = ()

{-@ assume liftSpec :: e:Distr a -> {lift eqP e e} @-}
liftSpec :: Distr a -> ()
liftSpec _ = ()


{-@ assume liftTrue :: e1:Distr a -> e2:Distr a -> {lift trueP e1 e2} @-}
liftTrue :: Distr a -> Distr a -> ()
liftTrue _ _ = ()