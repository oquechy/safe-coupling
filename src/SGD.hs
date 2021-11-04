{-@ LIQUID "--reflection"     @-}

module SGD where 

import           Prelude  hiding ( head, tail, sum)
import           Monad.Distr 
import           Data.Dist 

{-@ type StepSize = {v:Double | 0.0 <= v } @-}
type StepSize = Double
{-@ data StepSizes = SSEmp | SS StepSize StepSizes @-}
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint| 1 < lend v && 1 < len v } @-}
type DataSet = Set DataPoint
type DataDistr = Distr DataPoint


{-@ reflect sgd @-}
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> ss:StepSizes -> LossFunction 
       -> Distr Weight / [ sslen ss, 0 ] @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp    _ = ppure w0
sgd zs w0 (SS α a) f = 
  choice (one / lend zs)
         (bind uhead (sgdRecUpd zs w0 α a f))
         (bind utail (sgdRecUpd zs w0 α a f)) 
 where
  uhead = ppure (head zs)
  utail = unif (tail zs)


{-@ reflect sgdRecUpd @-}
{-@ sgdRecUpd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> StepSize -> ss:StepSizes -> LossFunction 
       -> DataPoint -> Distr Weight / [ sslen ss, 1 ] @-}
sgdRecUpd :: DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataPoint -> Distr Weight
sgdRecUpd zs w0 α a f z = bind (sgd zs w0 a f) (pureUpdate z α f)

{-@ reflect pureUpdate @-}
{-@ pureUpdate :: DataPoint -> StepSize -> LossFunction -> Weight -> Distr Weight @-}
pureUpdate :: DataPoint -> StepSize -> LossFunction -> Weight -> Distr Weight 
pureUpdate zs a f = ppure . update zs a f


{-@ measure SGD.update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight @-}
{-@ update :: x1:DataPoint -> x2:StepSize -> x3:LossFunction -> x4:Weight 
           -> {v:Weight | v = SGD.update x1 x2 x3 x4 } @-}
update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight
update _ w _ _ = w


-------------------------------------------------------------------------------
-- | Helper Definitions -------------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v } @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs


{-@ reflect one @-}
{-@ one :: {v:Double| v = 1.0 } @-}
one :: Double
one = 1



{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ measure sslen @-}
sslen :: StepSizes -> Int 
{-@ sslen :: StepSizes -> Nat @-}
sslen SSEmp = 0 
sslen (SS _ ss) = 1 + sslen ss 