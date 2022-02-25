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

{-@ type NBool = {v:Int | 0 <= v && v <= 1} @-}
type NBool = Int 
{-@ type NDouble = {v:Double | 0 <= v && v <= 1} @-}
type NDouble = Double 
{-@ type PDouble = {v:Double | 0 <= v } @-}

{-@ reflect bins @-}
{-@ bins :: p:Prob -> n:PDouble -> Distr {d:Double | 0 <= d && d <= n } / [n] @-}
bins :: Double -> Double -> Distr Double
bins _ n | n < 1.0 = ppure 0
bins p n = bind (bins p (n-1)) (binsRec p (n - 1))




{-@ reflect binsRec @-}
{-@ binsRec :: Prob -> n:PDouble -> {d:Double | 0 <= d && d <= n } -> Distr {d:Double | 0 <= d && d <= n + 1 } / [n, 1] @-}
binsRec :: Double -> Double -> Double -> Distr Double
binsRec p n x = bind (bernoulli p) (ppure . plus x)

{-@ reflect plus @-}
{-@ plus :: x:Double -> y:Double -> {d:Double | d = x + y } @-} 
plus :: Double -> Double -> Double 
plus x y = x + y 



{- 

{-@ reflect bins' @-}
{-@ bins' :: Prob -> Prob -> n:Double -> Distr Double / [n, 0] @-}
bins' :: Double -> Double -> Double -> Distr Double
bins' _ q n | n < 1.0 = ppure 0
bins' p q n = bind (bernoulli p) (binsRec q (n - 1))

{-@ reflect incCond @-}
{-@ incCond :: Double -> Double -> Distr Double @-}
incCond :: Double -> Double -> Distr Double
incCond x y = ppure (y + x)
-}

