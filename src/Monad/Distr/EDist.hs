-----------------------------------------------------------------
-- | Expected Distance as a desigared type class ----------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Monad.Distr.EDist where 

import Monad.Distr 
import Data.List 
import Prelude hiding (max)


-----------------------------------------------------------------
-- | class Dist a -----------------------------------------------
-----------------------------------------------------------------
data EDist a = EDist { 
    edist    :: Distr a -> Distr a -> Double 
  , maxEdist :: Distr a -> Distr a -> Double 
  , edistEq  :: Distr a -> () 
  , maxProp  :: Distr a -> Distr a -> ()
  }

{-@ data EDist a = EDist { 
    edist    :: Distr a -> Distr a -> {v:Double | 0.0 <= v } 
  , maxEdist :: Distr a -> Distr a -> {v:Double | 0.0 <= v } 
  , edistEq  :: a:Distr a -> { edist a a = 0}
  , maxProp  :: x:Distr a -> y:Distr a -> { edist x y <= maxEdist x y }
  } @-}

-----------------------------------------------------------------
-- | instance EDist a => EDist (List a) ---------------------------
-----------------------------------------------------------------
-- TODO: prove the proof obligations 

{-@ reflect eDistList @-}
eDistList ::  EDist a -> List (Distr a) -> List (Distr a) -> Double
eDistList _ Nil _ = 0 
eDistList _ _ Nil = 0 
eDistList ed (Cons x xs) (Cons y ys) 
  = max (edist ed x y) (eDistList ed xs ys)


