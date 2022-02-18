{-@ LIQUID "--reflection"     @-}

module Bins where

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

{-@ reflect bins @-}
{-@ bins :: Prob -> n:Nat -> Distr Int / [n, 0] @-}
bins :: Double -> Int -> Distr Int
bins _ 0 = ppure 0
bins p n = bind (bernoulli p) (binsRec p (n - 1))

{-@ reflect binsRec @-}
{-@ binsRec :: Prob -> n:Nat -> Bool -> Distr Int / [n, 1] @-}
binsRec :: Double -> Int -> Bool -> Distr Int
binsRec p n x = bind (bins p n) (incCond x)

{-@ reflect incCond @-}
incCond :: Bool -> Int -> Distr Int
incCond x y = ppure (y + if x then 1 else 0)