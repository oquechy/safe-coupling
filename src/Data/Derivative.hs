module Data.Derivative where

-- TODO: find implementation, e.g. Numeric.AD
grad :: (Double -> Double) -> (Double -> Double)
grad f x = 2 * x + 2 
