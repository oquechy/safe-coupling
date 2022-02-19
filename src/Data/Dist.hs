{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Data.Dist
  ( distList
  , distEq
  , triangularIneqD
  , symmetryD
  , absEqDouble 
  , linearity
  , Dist (..)
  , distDouble
  , distD
  )
where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators
import Misc.ProofCombinators
import Data.List

-- class Dist 
data Dist a = Dist { 
    dist :: a -> a -> Double 
  , triangularIneq :: a -> a -> a -> ()
  , symmetry       :: a -> a -> ()
  , absEq          :: a -> a -> ()
  }



{-@ data Dist a = Dist { 
    dist :: a -> a -> Double 
  , triangularIneq :: a:a -> b:a -> c:a -> {dist a c <= dist a b + dist b c}
  , symmetry       :: a:a -> b:a -> {dist a b = dist b a}
  , absEq          :: x:a -> y:a -> {dist x y == dist y x}
  } @-}



{-@ reflect distDouble@-}
distDouble :: Dist Double
distDouble = Dist distD triangularIneqD symmetryD absEqDouble

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
distD :: Double -> Double -> Double 
distD x y = if x <= y then y - x else x - y 

{- measure Data.Dist.dist :: a -> a -> Double @-}
{- assume dist :: x1:a -> x2:a -> {v:Double | v == Data.Dist.dist x1 x2 && v >= 0} @-}
-- dist :: a -> a -> Double
-- dist _ _ = 0

{-@ reflect distList @-}
{-@ distList :: Dist a -> List a -> List a -> {d:Double | 0 <= d } @-}
distList :: Dist a -> List a -> List a -> Double
distList d Nil _ = 0
distList d _ Nil = 0
distList d (Cons x xs) (Cons y ys) = max (dist d x y) (distList d xs ys)

{-@ assume distEq :: d:Dist a -> x:a -> y:a -> {x = y <=> dist d x y = 0} @-} 
distEq :: Dist a -> a -> a -> () 
distEq _ _ _ = ()

{-@ ple linearity @-}
{-@ linearity :: k:{Double | 0 <= k } -> l:Double -> a:Double -> b:Double 
                     -> { distD (k * a + l) (k * b + l) = k * distD a b} @-}
linearity :: Double -> Double -> Double -> Double -> ()
linearity k l a b
  | a <= b    = assert (k * a + l <= k * b + l) ? ()
  | otherwise = () 

