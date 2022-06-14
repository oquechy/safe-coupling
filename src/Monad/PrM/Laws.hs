-----------------------------------------------------------------
-- | Monad Laws for the PrM monad -----------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.PrM.Laws where 

import Monad.PrM

{-@ assume leftId :: x:a -> f:(a -> PrM b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> PrM b) -> ()
leftId _ _ = ()

{-@ assume assoc :: x:PrM a -> g:(a -> PrM b) -> f:(b -> PrM c) 
                 -> { bind (bind x g) f = bind x (composeBind g f) } @-}
assoc :: PrM a -> (a -> PrM b) -> (b -> PrM c) -> ()
assoc _ _ _ = ()

{-@ assume commutative :: e:PrM a -> u:PrM b -> f:(a -> b -> PrM c) 
                -> {bind e (seqBind u f)
                      = bind u (seqBind e (flip f))} @-}
commutative :: PrM a -> PrM b -> (a -> b -> PrM c) -> ()
commutative _ _ _ = ()

{-@ assume ext :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:() | f x == g x}) -> {f == g } @-} 
ext :: (a -> b) -> (a -> b) -> (a -> ()) -> () 
ext _ _ _ = () 