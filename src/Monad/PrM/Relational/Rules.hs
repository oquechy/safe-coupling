-----------------------------------------------------------------
-- | Relational Rules as in the safe-coupling paper -------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Monad.PrM.Relational.TCB.Rules where 

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

