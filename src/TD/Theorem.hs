{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Theorem where 

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Monad.Distr.Predicates


import           TD.Lemmata.Relational.Act
import           TD.Lemmata.Relational.Iterate

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


{-@ td0Spec :: n:Nat -> l:Nat -> t:TransitionOf l -> {v1:_|llen v1 = l} -> v2:SameLen v1 -> 
        {lift (bounded (pow k n * (distList distDouble v1 v2))) (td0 n v1 t) (td0 n v2 t)} @-}
td0Spec :: Int -> Int -> Transition -> ValueFunction -> ValueFunction -> ()
td0Spec n l t v1 v2 
    = iterateSpec (distList distDouble v1 v2) k n l (act l t) (actSpec l t) v1 v2 
