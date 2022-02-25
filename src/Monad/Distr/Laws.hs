-----------------------------------------------------------------
-- | Monad Laws for the Distr monad -----------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.Distr.Laws where 

import Monad.Distr

{-@ assume leftId :: x:a -> f:(a -> Distr b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> Distr b) -> ()
leftId _ _ = ()
