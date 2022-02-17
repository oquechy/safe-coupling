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
{-@ bins :: Prob -> n:Int -> Distr Int / [n, 0] @-}
bins :: Double -> Int -> Distr Int
bins _ 0 = ppure 0
bins p n = bind (bernoulli p) (binsRec p (n - 1))

{-@ reflect binsRec @-}
{-@ binsRec :: Prob -> n:Int -> Bool -> Distr Int / [n, 1] @-}
binsRec :: Double -> Int -> Bool -> Distr Int
binsRec p n x = bind (bins p n) (incCond x)

{-@ reflect incCond @-}
incCond :: Bool -> Int -> Distr Int
incCond x y = ppure (y + if x then 1 else 0)

{-@ reflect leP @-}
leP :: Int -> Int -> Bool
leP = (<=)

{-@ relationalbins :: p:Prob -> q:Prob -> n:Int 
                   -> {p <= q => lift leP (bins p n) (bins q n)} @-}
relationalbins :: Double -> Double -> Int -> ()
relationalbins _ _ 0 = liftPure leP 0 0 ()
relationalbins p q n 
    = liftBind leP leP 
               (bernoulli p) (binsRec p (n - 1))
               (bernoulli q) (binsRec q (n - 1))
               (relationalbernoulli p q)
               (\x1 x2 -> 
                    liftBind leP leP
                         (bins p (n - 1)) (incCond x1)
                         (bins q (n - 1)) (incCond x2)
                         (relationalbins p q (n - 1))
                         (\y1 y2 -> 
                             liftPure (y1 + if x1 then 1 else 0)
                                      (y2 + if x2 then 1 else 0)
                                      ()))

