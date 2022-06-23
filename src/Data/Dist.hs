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
  , identity         :: a -> () 
  , trinequality :: a -> a -> a -> ()
  , symmetry       :: a -> a -> ()
  }


{-@ data Dist a = Dist { 
    dist           :: a -> a -> {v:Double | 0.0 <= v } 
  , identity         :: a:a -> {dist a a == 0}
  , trinequality :: x:a -> y:a -> z:a -> {dist x z <= dist x y + dist y z}
  , symmetry       :: a:a -> b:a -> {dist a b = dist b a}
  } @-}

-- TODO: define this 
-- distFun :: Dist b -> Dist (a -> b)

-----------------------------------------------------------------
-- | instance Dist Double ---------------------------------------
-----------------------------------------------------------------

{-@ reflect distDouble@-}
distDouble :: Dist Double
distDouble = Dist distD identityD trinequalityD symmetryD

{-@ ple identityD @-}
{-@ reflect identityD @-}
identityD :: Double -> ()
{-@ identityD :: x:Double -> {distD x x == 0 } @-}
identityD _ = () 

{-@ ple trinequalityD @-}
{-@ reflect trinequalityD @-}
{-@ trinequalityD :: a:Double -> b:Double -> c:Double -> { distD a c <= distD a b + distD b c} @-}
trinequalityD :: Double -> Double -> Double -> ()
trinequalityD _ _ _ = ()

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
-- Note the proof obligations hold, but this is not a real metric
-- since the two lists should have the same len
-- The following cannot type check 
-- listDist :: Dist a -> Dist (List a)
-- listDist d = Dist (distList d) (distListEq d) (distListTri d) (distListSym d)

{-@ type ListEq a XS = {ys:List a | llen ys == llen XS } @-}
{-@ reflect distList @-}
{-@ distList :: Dist a -> x:List a -> y:ListEq a {x} 
                       -> {d:Double | 0 <= d } @-}
distList :: Dist a -> List a -> List a -> Double
distList d Nil _ = 0
distList d _ Nil = 0
distList d (Cons x xs) (Cons y ys) = max (dist d x y) (distList d xs ys)

{-@ ple distListEq @-}
{-@ distListEq :: d:Dist a -> x:List a -> { distList d x x == 0 } @-}
distListEq :: Dist a -> List a -> ()
distListEq d Nil = () 
distListEq d (Cons x xs) = identity d x ? distListEq d xs

{-@ ple distListSym @-}
{-@ distListSym :: d:Dist a -> x:List a -> y:ListEq a {x} -> { distList d x y == distList d y x } @-}
distListSym :: Dist a -> List a -> List a -> ()
distListSym d Nil _ = () 
distListSym d _ Nil = () 
distListSym d (Cons x xs) (Cons y ys) = symmetry d x y ? distListSym d xs ys


{-@ ple distListTri @-}
{-@ distListTri :: d:Dist a -> x:List a -> y:ListEq a {x} -> z:ListEq a {x}
                -> { distList d x z <= distList d x y + distList d y z } @-}
distListTri :: Dist a -> List a -> List a -> List a -> ()
distListTri d x@Nil y z = assert (distList d x z <= distList d x y + distList d y z)
distListTri d x y z@Nil = assert (distList d x z <= distList d x y + distList d y z)
distListTri d (Cons x xs) (Cons y ys) (Cons z zs) 
  = trinequality d x y z ? distListTri d xs ys zs 

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

