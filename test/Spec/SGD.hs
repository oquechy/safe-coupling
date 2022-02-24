module Spec.SGD where

import           Test.HUnit                     ( assertEqual
                                                , (@?)
                                                , (@?=)
                                                , Assertion
                                                )
import           Numeric.Probability.Distribution
                                                ( decons )
import           Spec.Utils

import           SGD.SGD                            

{-@ loss :: DataPoint -> {ws:[Weight]|len ws = 1} -> Dbl @-}
loss :: DataPoint -> Weight -> Double
loss (x, y) w = (y - x + w) ^ 2

dp :: DataPoint
dp = (0, 1)

ss :: StepSizes
ss = SS 0.5 (SS 0.5 (SS 0.5 (SS 0.5 SSEmp)))

unit_sgd :: Assertion
unit_sgd = w @?= (-1)
  where [(w, 1)] = clean $ decons $ sgd (replicate 4 dp) 1 ss loss
