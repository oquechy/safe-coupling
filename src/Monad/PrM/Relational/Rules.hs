{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM.Relational.Rules where 

import Data.Dist
import Monad.PrM
import Monad.PrM.Lift
import Monad.PrM.Predicates

{-@ reflect boundBy @-}
boundBy :: KBound a -> a -> a -> Bool
boundBy Inf _ _ = True
boundBy (K d k) x1 x2 = dist d x1 x2 <= k

{-@ pureT :: k:KBound a -> p:(a -> a -> Bool) -> x1:a -> x2:a 
          -> {px:()|p x1 x2 && boundBy k x1 x2} 
          -> {klift k p (ppure x1) (ppure x2)} @-}
pureT :: KBound a -> (a -> a -> Bool) -> a -> a -> () -> () 
pureT Inf _ _ _ _ = ()
pureT _ _ _ _ _ = ()

{- unifT :: Eq a => k:KBound a -> {xs:[a]|0 < len xs} -> {klift k eqP (unif xs) (unif xs)} @-}
unifT :: KBound a -> [a] -> ()
unifT _ _ = ()
unifT Inf [_] = ()
unifT Inf (_:xs@(_:_)) = unifT Inf xs
unifT k [_] = ()
unifT k (_:xs@(_:_)) = unifT k xs
