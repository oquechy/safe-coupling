{-@ LIQUID "--reflection" @-}

module Data.Dist
  ( dist
  , distList
  , distEq
  , symmetry
  , triangularIneq
  , linearity
  )
where

import Prelude hiding (max)

import Data.List

{-@ measure Data.Dist.dist :: a -> a -> Double @-}
{-@ assume dist :: x1:a -> x2:a -> {v:Double | v == Data.Dist.dist x1 x2 && v >= 0} @-}
dist :: a -> a -> Double
dist _ _ = 0

{-@ reflect distList @-}
{-@ distList :: List a -> List a -> {d:Double | 0 <= d } @-}
distList :: List a -> List a -> Double
distList Nil _ = 0
distList _ Nil = 0
distList (Cons x xs) (Cons y ys) = max (dist x y) (distList xs ys)

{-@ assume distEq :: x:a -> y:a -> {x = y <=> dist x y = 0} @-} 
distEq :: a -> a -> () 
distEq _ _ = ()

{-@ assume triangularIneq :: a:a -> b:a -> c:a -> {dist a c <= dist a b + dist b c} @-}
triangularIneq :: a -> a -> a -> ()
triangularIneq _ _ _ = ()

{-@ assume symmetry :: a:a -> b:a -> {dist a b = dist b a} @-}
symmetry :: a -> a -> ()
symmetry _ _ = ()

{-@ assume linearity :: k:_ -> l:_ -> a:_ -> b:_ -> {dist (k * a + l) (k * b + l) = k * dist a b} @-}
linearity :: Double -> Double -> Double -> Double -> ()
linearity _ _ _ _ = ()