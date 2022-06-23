-----------------------------------------------------------------
-- | Laws for the Distr monad -----------------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.Distr.Laws where 

import Monad.Distr

-----------------------------------------------------------------
-- | Monad's Left Identity --------------------------------------
-----------------------------------------------------------------

{-@ assume leftId :: x:a -> f:(a -> Distr b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> Distr b) -> ()
leftId _ _ = ()

-----------------------------------------------------------------
-- | Commutativity of Probabilistic Monad [Staton'17] -----------
-----------------------------------------------------------------

{-@ assume commutative :: e:Distr a -> u:Distr b -> f:(a -> b -> Distr c) 
                -> {bind e (seqBind u f)
                      = bind u (seqBind e (flip f))} @-}
commutative :: Distr a -> Distr b -> (a -> b -> Distr c) -> ()
commutative _ _ _ = ()

-----------------------------------------------------------------
-- | Function Extensionality ------------------------------------
-----------------------------------------------------------------

{-@ assume extDouble :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:() | f x == g x}) -> {f == g } @-} 
extDouble :: (a -> b) -> (a -> b) -> (a -> ()) -> () 
extDouble _ _ _ = ()

