{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module ApplicativeBins.Theorem where

import           Monad.PrM
import           Data.Dist

import           Monad.PrM.Relational.TCB.EDist
import           ApplicativeBins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ binsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble 
             -> {dist (kant distDouble) (bins p n) (bins q n) <= n * (q - p)} / [n] @-}
binsDist :: Prob -> Prob -> Double -> ()
binsDist p q n | n < 1.0 
  = pureDist distDouble 0 0 
  ? assert (0 <= n) 
  ? assert (0 <= (q - p)) 
  ? assert (dist (kant distDouble) (bins p n) (bins q n) <= n * (q - p)) 
binsDist p q n
  =   liftA2Dist d d d 1 ((n - 1) * (q - p)) 1 (q - p) 0
          plus (bins p (n - 1)) (bernoulli p) 
          plus (bins q (n - 1)) (bernoulli q)
          (binsDist p q (n - 1))
          (bernoulliDist d p q)
          plusDist
  where d = distDouble

{-@ plusDist :: x1:Double -> y1:Double -> x2:Double -> y2:Double 
             -> {distD (plus x1 y1) (plus x2 y2) <= distD x1 x2 + distD y1 y2} @-}
plusDist :: Double -> Double -> Double -> Double -> ()
plusDist _ _ _ _ = ()