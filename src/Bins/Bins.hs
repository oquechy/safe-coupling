{-@ LIQUID "--reflection"     @-}

module Bins.Bins where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , max
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                , uncurry
                                                )

{-@ type PDouble = {v:Double | 0 <= v } @-}

{-@ reflect bins @-}
{-@ bins :: p:Prob -> n:PDouble -> Distr {d:Double | 0 <= d && d <= n } / [n] @-}
bins :: Double -> Double -> Distr Double
bins _ n | n < 1.0 = ppure 0
bins p n = bind (bins p (n - 1)) (addBernoulli p (n - 1))

-- bins = liftA2 (+) (bins p (n - 1)) (bernoulli p)

{-@ reflect addBernoulli @-}
{-@ addBernoulli :: Prob -> n:PDouble -> {d:Double | 0 <= d && d <= n } -> Distr {d:Double | 0 <= d && d <= n + 1 } @-}
addBernoulli :: Double -> Double -> Double -> Distr Double
addBernoulli p n x = bind (bernoulli p) (ppure . plus x)

{-@ reflect plus @-}
{-@ plus :: x:Double -> y:Double -> {d:Double | d = x + y } @-} 
plus :: Double -> Double -> Double 
plus x y = x + y 