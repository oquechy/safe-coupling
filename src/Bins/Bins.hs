{-@ LIQUID "--reflection"     @-}

module Bins.Bins where

import           Monad.PrM
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

{-@ type NBool = {v:Int | 0 <= v && v <= 1} @-}
type NBool = Int 
{-@ type NDouble = {v:Double | 0 <= v && v <= 1} @-}
type NDouble = Double 
{-@ type PDouble = {v:Double | 0 <= v } @-}

{-@ reflect bins @-}
{-@ bins :: p:Prob -> n:PDouble -> PrM {d:Double | 0 <= d && d <= n } / [n] @-}
bins :: Double -> Double -> PrM Double
bins _ n | n < 1.0 = ppure 0
bins p n = bind (bins p (n - 1)) (addBernoulli p (n - 1))

{-@ reflect addBernoulli @-}
{-@ addBernoulli :: Prob -> n:PDouble -> {d:Double | 0 <= d && d <= n } -> PrM {d:Double | 0 <= d && d <= n + 1 } @-}
addBernoulli :: Double -> Double -> Double -> PrM Double
addBernoulli p n x = bind (bernoulli p) (ppure . plus x)
