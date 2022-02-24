-----------------------------------------------------------------
-- | Distance as a desugared type class -------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Data.Dist where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators
import Misc.ProofCombinators
import Data.List

-----------------------------------------------------------------
-- | class Dist a -----------------------------------------------
-----------------------------------------------------------------
data Dist a = Dist { 
    dist           :: a -> a -> Double 
  , distEq         :: a -> () 
  , triangularIneq :: a -> a -> a -> ()
  , symmetry       :: a -> a -> ()
  , absEq          :: a -> a -> ()
  }


{-@ data Dist a = Dist { 
    dist           :: a -> a -> {v:Double | 0.0 <= v } 
  , distEq         :: a:a -> {dist a a = 0}
  , triangularIneq :: x:a -> y:a -> z:a -> {dist x z <= dist x y + dist y z}
  , symmetry       :: a:a -> b:a -> {dist a b = dist b a}
  , absEq          :: x:a -> y:a -> {dist x y == dist y x}
  } @-}



-- TODO: define this 
-- distFun :: Dist b -> Dist (a -> b)


-----------------------------------------------------------------
-- | instance Dist Double ---------------------------------------
-----------------------------------------------------------------

{-@ reflect distDouble@-}
distDouble :: Dist Double
distDouble = Dist distD distEqD triangularIneqD symmetryD absEqDouble

{-@ ple distEqD @-}
{-@ reflect distEqD @-}
distEqD :: Double -> ()
{-@ distEqD :: x:Double -> {distD x x == 0 } @-}
distEqD _ = () 


{-@ ple absEqDouble @-}
{-@ reflect absEqDouble @-}
absEqDouble :: Double -> Double -> ()
{-@ absEqDouble :: x:Double -> y:Double -> {distD x y == distD y x } @-}
absEqDouble _ _ = () 

{-@ ple triangularIneqD @-}
{-@ reflect triangularIneqD @-}
{-@ triangularIneqD :: a:Double -> b:Double -> c:Double -> { distD a c <= distD a b + distD b c} @-}
triangularIneqD :: Double -> Double -> Double -> ()
triangularIneqD _ _ _ = ()

{-@ ple symmetryD @-}
{-@ reflect symmetryD @-}
{-@ symmetryD :: a:Double -> b:Double -> {distD a b = distD b a} @-}
symmetryD :: Double -> Double -> () 
symmetryD _ _ = ()

{-@ reflect distD @-}
{-@ distD :: Double -> Double -> {d:Double | 0.0 <= d } @-}
distD :: Double -> Double -> Double 
distD x y = if x <= y then y - x else x - y 

-----------------------------------------------------------------
-- | instance Dist a => Dist (List a) ---------------------------
-----------------------------------------------------------------
-- TODO: prove the proof obligations 

{-@ reflect distList @-}
{-@ distList :: Dist a -> List a -> List a -> {d:Double | 0 <= d } @-}
distList :: Dist a -> List a -> List a -> Double
distList d Nil _ = 0
distList d _ Nil = 0
distList d (Cons x xs) (Cons y ys) = max (dist d x y) (distList d xs ys)


-----------------------------------------------------------------
-- | Linearity on Doubles 
-- | Does not type check forall a, so cannot just get axiomatized
-----------------------------------------------------------------

{-@ ple linearity @-}
{-@ linearity :: k:{Double | 0 <= k } -> l:Double -> a:Double -> b:Double 
                     -> { distD (k * a + l) (k * b + l) = k * distD a b} @-}
linearity :: Double -> Double -> Double -> Double -> ()
linearity k l a b
  | a <= b    = assert (k * a + l <= k * b + l) 
  | otherwise = assert (distD (k * a + l) (k * b + l) == k * distD a b)

