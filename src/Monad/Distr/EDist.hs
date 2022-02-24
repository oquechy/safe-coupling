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

{-@ measure Monad.Distr.EDist.expDist :: Distr a -> Distr a -> Double @-}
{-@ assume expDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == Monad.Distr.EDist.expDist x1 x2 } @-}
expDist :: Distr a -> Distr a -> Double
expDist _ _ = 0


{-@ measure expDistList :: List (Distr a) -> List (Distr b) -> Double @-}
{-@ assume expDistList :: xs1:List (Distr a) -> xs2:List (Distr a) -> {v:Double | v == expDistList xs1 xs2 } @-}
expDistList :: List (Distr a) -> List (Distr a) -> Double
expDistList Nil _ = 0 
expDistList _ Nil = 0 
expDistList (Cons x xs) (Cons y ys) = max (expDist x y) (expDistList xs ys)

{-@ assume maxExpDistLemma :: x1:Distr a -> x2:Distr a -> { expDist x1 x2 <=  maxExpDist x1 x2 } @-}
maxExpDistLemma :: Distr a -> Distr a -> ()
maxExpDistLemma _ _ = ()

{-@ measure maxExpDist :: Distr a -> Distr a -> Double @-}
{-@ assume maxExpDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == maxExpDist x1 x2 } @-}
maxExpDist :: Distr a -> Distr a -> Double
maxExpDist _ _ = 0


{-@ assume expDistEq :: x1:Distr a -> {x2:Distr a | x1 = x2 } -> {expDist x1 x2 = 0} @-}
expDistEq :: Distr a -> Distr a -> ()
expDistEq _ _ = ()