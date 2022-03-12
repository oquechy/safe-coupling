-----------------------------------------------------------------
-- | Reflected Predicates (required for lifting) ----------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}

module Monad.PrM.Predicates where 

import Data.Dist 
import Data.List 

{-@ reflect trueP @-}
trueP :: a -> a -> Bool 
trueP _ _ = True 

{-@ reflect bounded @-}
{-@ bounded :: Double -> x:List Double -> ListEq Double {x} -> Bool @-}
bounded :: Double -> List Double -> List Double -> Bool
bounded m v1 v2 = distList distDouble v1 v2 <= m && llen v1 == llen v2

{-@ reflect boundedD @-}
boundedD :: Dist a -> Double -> a -> a -> Bool
boundedD d m v1 v2 = dist d v1 v2 <= m

{-@ reflect bounded' @-}
bounded' :: Double -> Double -> Double -> Bool
bounded' m x1 x2 = distD x1 x2 <= m

{-@ reflect eqP @-}
eqP :: Eq a => a -> a -> Bool
eqP = (==)


{-@ reflect leDoubleP @-}
{-@ leDoubleP :: x:Double -> y:Double -> {v:Bool|v <=> (x <= y)} @-}
leDoubleP :: Double -> Double -> Bool
leDoubleP x y = x <= y

{-@ reflect impP @-}
{-@ impP :: x:Bool -> y:Bool -> {v:Bool|v <=> (x => y)} @-}
impP :: Bool -> Bool -> Bool
impP True False = False
impP _    _     = True

{-@ reflect leIntP @-}
{-@ leIntP :: x:Int -> y:Int -> {v:Bool|v <=> (x <= y)} @-}
leIntP :: Int -> Int -> Bool
leIntP x y = x <= y

-- Properties on Predicates 
{-@ ple boundedNil @-}
{-@ boundedNil :: {m:_|0 <= m} -> {bounded m Nil Nil} @-}
boundedNil :: Double -> ()
boundedNil _ = ()
