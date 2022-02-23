{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.Theorem where

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

import           Bins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ relationalinccond :: x1:Bool -> {x2:Bool|impP x1 x2} -> y1:Int -> {y2:Int|leIntP y1 y2} 
                      -> {lift leIntP (incCond x1 y1) (incCond x2 y2)} @-}
relationalinccond :: Bool -> Bool -> Int -> Int -> ()
relationalinccond x1 x2 y1 y2 = liftPure leIntP
                                         (y1 + if x1 then 1 else 0)
                                         (y2 + if x2 then 1 else 0)
                                         ()
                                
{-@ relationalbinsrec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Nat -> x1:Bool -> {x2:Bool|impP x1 x2}
                      -> {lift leIntP (binsRec p n x1) (binsRec q n x2)} / [n, 1] @-}
relationalbinsrec :: Double -> Double -> Int -> Bool -> Bool -> ()
relationalbinsrec p q n x1 x2
    = liftBind leIntP leIntP
        (bins p n) (incCond x1)
        (bins q n) (incCond x2)
        (relationalbins p q n)
        (relationalinccond x1 x2)
 
{-@ relationalbins :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Nat 
                   -> {lift leIntP (bins p n) (bins q n)} / [n, 0] @-}
relationalbins :: Double -> Double -> Int -> ()
relationalbins p q 0 
    = liftPure leIntP 0 0 ()
relationalbins p q n 
    = liftBind leIntP impP
               (bernoulli p) (binsRec p (n - 1))
               (bernoulli q) (binsRec q (n - 1))
               (relationalbernoulli p q)
               (relationalbinsrec p q (n - 1))
        

