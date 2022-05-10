-----------------------------------------------------------------
-- | Relational Specifications for PrM Primitives -------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.PrM.Relational.TCB.Spec where 

import Monad.PrM 
import Monad.PrM.Predicates

{-@ assume pureSpec :: p:(a -> b -> Bool) 
                    -> x1:a -> x2:b -> {_:()|p x1 x2} 
                    -> {lift p (ppure x1) (ppure x2)} @-}
pureSpec :: (a -> b -> Bool) -> a -> b -> () -> ()
pureSpec _ _ _ _ = ()

{-@ assume bindSpec :: p:(b -> b -> Bool) -> q:(a -> a -> Bool) 
                    -> e1:PrM a -> f1:(a -> PrM b) 
                    -> e2:PrM a -> f2:(a -> PrM b) 
                    -> {_:()|lift q e1 e2} 
                    -> (x1:a -> {x2:a|q x1 x2} -> {lift p (f1 x1) (f2 x2)})
                    -> {lift p (bind e1 f1) (bind e2 f2)} @-}
bindSpec :: (b -> b -> Bool) -> (a -> a -> Bool) -> 
              PrM a -> (a -> PrM b) -> PrM a -> (a -> PrM b) -> 
              () ->
              (a -> a -> ()) -> 
              ()
bindSpec _ _ _ _ _ _ _ _ = ()

{-@ assume bernoulliSpec :: p:Prob -> {q:Prob| leDoubleP p q}
                         ->  {lift leDoubleP (bernoulli p) (bernoulli q)} @-}
bernoulliSpec :: Prob -> Prob -> ()
bernoulliSpec _ _ = ()

{-@ assume liftSpec :: e:PrM a -> {lift eqP e e} @-}
liftSpec :: PrM a -> ()
liftSpec _ = ()


{-@ assume liftTrue :: e1:PrM a -> e2:PrM a -> {lift trueP e1 e2} @-}
liftTrue :: PrM a -> PrM a -> ()
liftTrue _ _ = ()