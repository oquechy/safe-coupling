-----------------------------------------------------------------
-- | Monad Laws for the PrM monad -----------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.PrM.Laws where 

import Monad.PrM

{-@ assume leftId :: x:a -> f:(a -> PrM b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> PrM b) -> ()
leftId _ _ = ()

{-@ assume commutative :: e:PrM a -> u:PrM b -> f:(a -> b -> PrM c) 
                -> {bind e (seqBind u f)
                      = bind u (seqBind e (flip f))} @-}
commutative :: PrM a -> PrM b -> (a -> b -> PrM c) -> ()
commutative _ _ _ = ()
