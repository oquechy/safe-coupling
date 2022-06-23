{-@ LIQUID "--reflection"     @-}

module SGD.SGD where 

import           Prelude  hiding ( head, tail, sum)
import           Monad.Distr 
import           Data.Dist 
import           Data.List 
import           Data.Derivative

-------------------------------------------------------------------------------
-- | Executable code ----------------------------------------------------------
-------------------------------------------------------------------------------

{-@ type StepSize = {v:Double | 0.0 <= v } @-}
type StepSize = Double
{-@ data StepSizes = SSEmp | SS StepSize StepSizes @-}
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint| 1 < lend v && 1 < len v} @-}
type DataSet = Set DataPoint
type DataDistr = Distr DataPoint


{-@ reflect sgd @-}
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> ss:StepSizes -> LossFunction 
       -> Distr Weight / [ sslen ss, 0 ] @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp    _ = ppure w0
sgd zs w0 (SS alpha a) f = 
  choice (1.0 / lend zs)
         (bind uhead (sgdRecUpd zs w0 alpha a f))
         (bind utail (sgdRecUpd zs w0 alpha a f)) 
 where
  uhead = ppure (head zs)
  utail = unif (tail zs)


{-@ reflect sgdRecUpd @-}
{-@ sgdRecUpd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> StepSize -> ss:StepSizes -> LossFunction 
       -> DataPoint -> Distr Weight / [ sslen ss, 1 ] @-}
sgdRecUpd :: DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataPoint -> Distr Weight
sgdRecUpd zs w0 alpha a f z = bind (sgd zs w0 a f) (pureUpdate z alpha f)

{-@ reflect pureUpdate @-}
{-@ pureUpdate :: DataPoint -> StepSize -> LossFunction -> Weight -> Distr Weight @-}
pureUpdate :: DataPoint -> StepSize -> LossFunction -> Weight -> Distr Weight 
pureUpdate zs a f = ppure . update zs a f


{-@ measure SGD.SGD.update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight @-}
{-@ update :: x1:DataPoint -> x2:StepSize -> x3:LossFunction -> x4:Weight 
           -> {v:Weight | v = SGD.SGD.update x1 x2 x3 x4 } @-}
update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight
update z alpha f w = w - alpha * (grad (f z) w) 


-------------------------------------------------------------------------------
-- | Helper Definitions -------------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure sslen @-}
sslen :: StepSizes -> Int 
{-@ sslen :: StepSizes -> Nat @-}
sslen SSEmp = 0 
sslen (SS _ ss) = 1 + sslen ss