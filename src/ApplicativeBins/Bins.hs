{-@ LIQUID "--reflection"     @-}

module ApplicativeBins.Bins where

import           Monad.PrM 
import           Data.Dist

{-@ type PDouble = {v:Double | 0 <= v } @-}

{-@ reflect bins @-}
{-@ bins :: p:Prob -> n:PDouble -> PrM {d:Double | 0 <= d && d <= n } / [n] @-}
bins :: Double -> Double -> PrM Double
bins _ n | n < 1.0 = ppure 0
bins p n = liftA2 plus (bins p (n - 1)) (bernoulli p)
