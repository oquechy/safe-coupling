-----------------------------------------------------------------
-- | Monad Laws for the PrM monad -----------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.PrM.Laws where 

import Monad.PrM

{-@ assume leftId :: x:a -> f:(a -> PrM b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> PrM b) -> ()
leftId _ _ = ()


