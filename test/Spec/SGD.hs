module Spec.SGD where

import           Test.HUnit                     ( assertEqual
                                                , (@?)
                                                , (@?=)
                                                , Assertion
                                                )
import           SGD                            

{-@ loss :: DataPoint -> {ws:[Weight]|len ws = 1} -> Dbl @-}
loss :: DataPoint -> [Weight] -> Double
loss (x, y) [ws] = (y - x + ws) ^ 2

dp :: DataPoint
dp = (0, 1)

unit_gd :: Assertion
unit_gd = do
  w @?= (-1)
  where [w] = sgd (replicate 4 dp) [1] 0.5 loss
