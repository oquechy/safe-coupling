{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.TD0 where 

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Lemmata.Relational.Act
import           Lemmata.Relational.Iterate

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators
import Misc.ProofCombinators


{-@ relationaltd0 :: n:Nat -> l:Nat -> t:TransitionOf l -> {v1:_|llen v1 = l} -> v2:SameLen v1 -> 
        {lift (bounded (pow k n * (distList v1 v2))) (td0 n v1 t) (td0 n v2 t)} @-}
relationaltd0 :: Int -> Int -> Transition -> ValueFunction -> ValueFunction -> ()
relationaltd0 n l t v1 v2 
    = relationaliterate (distList v1 v2) k n v1 v2 (act l t) (relationalact l t) 
