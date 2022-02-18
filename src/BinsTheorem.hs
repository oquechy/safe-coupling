{-@ LIQUID "--reflection"     @-}

module BinsTheorem where

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

import           Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ lePIncCond :: x1:Bool -> x2:Bool -> {_:()|impP x1 x2} -> y1:Int -> y2:Int -> {_:()|leIntP y1 y2} 
               -> {leIntP (y1 + if x1 then 1 else 0) (y2 + if x2 then 1 else 0)} @-}
lePIncCond :: Bool -> Bool -> () -> Int -> Int -> () -> ()
lePIncCond x1@True x2 imp y1 y2 le 
    =   y1 + (if x1 then 1 else 0)
    === y1 + 1
        ? le
    =<= y2 + 1
        ? imp
    === y2 + (if x2 then 1 else 0)
    *** QED
lePIncCond x1@False x2 imp y1 y2 le 
    =   y1 + (if x1 then 1 else 0)
    === y1
        ? le
    =<= y2
    =<= y2 + (if x2 then 1 else 0)
    *** QED

{-@ relationalinccond :: x1:Bool -> {x2:Bool|impP x1 x2} -> y1:Int -> {y2:Int|leIntP y1 y2} 
                      -> {lift leIntP (incCond x1 y1) (incCond x2 y2)} @-}
relationalinccond :: Bool -> Bool -> Int -> Int -> ()
relationalinccond x1 x2 y1 y2 = liftPure leIntP
                                         (y1 + if x1 then 1 else 0)
                                         (y2 + if x2 then 1 else 0)
                                         (lePIncCond x1 x2 () y1 y2 ())
                                    ? (incCond x1 y1 === ppure (y1 + if x1 then 1 else 0) *** QED)
                                    ? (incCond x2 y2 === ppure (y2 + if x2 then 1 else 0) *** QED)

{-@ relationalbinsrec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Nat -> x1:Bool -> {x2:Bool|impP x1 x2}
                      -> {lift leIntP (binsRec p n x1) (binsRec q n x2)} / [n, 1] @-}
relationalbinsrec :: Double -> Double -> Int -> Bool -> Bool -> ()
relationalbinsrec p q n x1 x2
    = liftBind leIntP leIntP
        (bins p n) (incCond x1)
        (bins q n) (incCond x2)
        (relationalbins p q n)
        (relationalinccond x1 x2)
            ? (binsRec p n x1 === bind (bins p n) (incCond x1) *** QED)
            ? (binsRec q n x2 === bind (bins q n) (incCond x2) *** QED)

{-@ relationalbins :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Nat 
                   -> {lift leIntP (bins p n) (bins q n)} / [n, 0] @-}
relationalbins :: Double -> Double -> Int -> ()
relationalbins p q n@0 
    = liftPure leIntP 0 0 (lePEq 0)
        ? (bins p n === ppure 0 *** QED)
        ? (bins q n === ppure 0 *** QED)
relationalbins p q n 
    = liftBind leIntP impP
               (bernoulli p) (binsRec p (n - 1))
               (bernoulli q) (binsRec q (n - 1))
               (relationalbernoulli p q)
               (relationalbinsrec p q (n - 1))
        ? (bins p n === bind (bernoulli p) (binsRec p (n - 1)) *** QED)
        ? (bins q n === bind (bernoulli q) (binsRec q (n - 1)) *** QED)
        

