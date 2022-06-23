{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.TheoremSpec where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Monad.Distr.Predicates
import           Monad.Distr.Relational.TCB.Axiom 
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Relational.Theorems
import           Bins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ ppurePlusSpec :: x1:Double -> {x2:Double|x1 <= x2} -> y1:Double -> {y2:Double|leDoubleP y1 y2} 
                      -> {lift leDoubleP ((ppure . (plus x1)) (y1)) ((ppure . (plus x2)) (y2))} @-}
ppurePlusSpec :: Double -> Double -> Double -> Double -> ()
ppurePlusSpec x1 x2 y1 y2 = pureAxiom leDoubleP
                                         (plus y1 x1)
                                         (plus y2 x2)
                                         ()
                                
{-@ addBernoulliSpec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double -> x1:Double -> {x2:Double| x1 <= x2}
                      -> {lift leDoubleP (addBernoulli p n x1) (addBernoulli q n x2)} / [n, 1] @-}
addBernoulliSpec :: Double -> Double -> Double -> Double -> Double -> ()
addBernoulliSpec p q n x1 x2
    = bindAxiom leDoubleP leDoubleP
        (bernoulli p) (ppure . plus x1)
        (bernoulli q) (ppure . plus x2)
        (bernoulliAxiom p q)
        (ppurePlusSpec x1 x2)
 
{-@ binsSpec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double 
             -> {lift leDoubleP (bins p n) (bins q n)} / [n, 0] @-}
binsSpec :: Double -> Double -> Double -> ()
binsSpec p q n | n < 1  
    = pureAxiom leDoubleP 0 0 ()
binsSpec p q n 
    = bindAxiom leDoubleP leDoubleP
               (bins p (n - 1)) (addBernoulli p (n - 1))
               (bins q (n - 1)) (addBernoulli q (n - 1))
               (binsSpec p q (n - 1))
               (addBernoulliSpec p q (n - 1))
