module Spec.Bins where

import           Test.HUnit                     ( assertEqual
                                                , (@?)
                                                , (@?=)
                                                , Assertion
                                                )
import           Data.Sort                      ( sort )
import           Numeric.Probability.Distribution
                                         hiding ( map )
import           Spec.Utils

import           Monad.Distr
import           Bins.Bins

p, q :: Double
p    = 0.5
q    = 0.625

coupling :: Double -> Double -> Distr (Bool, Bool)
coupling p q =
  fromFreqs [((True, True), p), ((False, True), q - p), ((False, False), 1 - q)]

mockbins :: Distr (Bool, Bool) -> Int -> Distr (Int, Int)
mockbins _ 0 = return (0, 0)
mockbins c n = do
  (xl, xr) <- c
  (yl, yr) <- mockbins c (n - 1)
  return (yl + toInt xl, yr + toInt xr)
  where toInt x = if x then 1 else 0

binsIter1 = sort [ ((1, 1), p)
                 , ((0, 1), q - p)
                 , ((0, 0), 1 - q)
                 ]

binsIter2 = sort [ ((2, 2), p ^ 2)
                 , ((1, 2), 2 * p * (q - p))
                 , ((1, 1), 2 * p * (1 - q))
                 , ((0, 2), (q - p) ^ 2)
                 , ((0, 1), 2 * (q - p) * (1 - q))
                 , ((0, 0), (1 - q) ^ 2)
                 ]

unit_mockbins_1_it :: Assertion
unit_mockbins_1_it =
  bins @?= binsIter1
 where
  bins = clean $ decons $ mockbins (coupling p q) 1

unit_mockbins_2_it :: Assertion
unit_mockbins_2_it = 
  bins @?= binsIter2
 where
  bins = clean $ decons $ mockbins (coupling p q) 2
  
unit_bins_1_it :: Assertion
unit_bins_1_it = do
  resl @?= clean (map (\((a, _), p) -> (fromIntegral a, p)) binsIter1)
  resr @?= clean (map (\((_, b), p) -> (fromIntegral b, p)) binsIter1)
 where
  resl = clean $ decons $ bins p 1
  resr = clean $ decons $ bins q 1

unit_bins_2_it :: Assertion
unit_bins_2_it = do
  resl @?= clean (map (\((a, _), p) -> (fromIntegral a, p)) binsIter2)
  resr @?= clean (map (\((_, b), p) -> (fromIntegral b, p)) binsIter2)
 where
  resl = clean $ decons $ bins p 2
  resr = clean $ decons $ bins q 2
  
unit_exp_dist_mockbins :: Assertion
unit_exp_dist_mockbins =
  expDist == fromIntegral n * (q - p)
    @? "want: E[dist (bins p n) (bins q n)] <= n * (q - p), got: " ++  show expDist
 where
  n       = 10
  bins    = mockbins (coupling p q) n
  dist    = fmap (\(a, b) -> fromIntegral (b - a)) bins
  expDist = expected dist

