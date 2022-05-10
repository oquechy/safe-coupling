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

{-@ assume choiceBind :: p:Prob -> e1:PrM a -> e2:PrM a -> f:(a -> PrM b) 
                      -> {choice p (bind e1 f) (bind e2 f) = bind (choice p e1 e2) f} @-}
choiceBind :: Prob -> PrM a -> PrM a -> (a -> PrM b) -> ()
choiceBind _ _ _ _ = ()

{-@ assume extDouble :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:() | f x == g x}) -> {f == g } @-} 
extDouble :: (a -> b) -> (a -> b) -> (a -> ()) -> () 
extDouble _ _ _ = () 