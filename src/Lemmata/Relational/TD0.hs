{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.TD0 where 

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Lemmata.Relational.Act
import           Lemmata.Relational.Iterate

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationaltd0 :: n:Nat -> t:_ -> v1:_ -> v2:_ -> 
        {lift (bounded (pow k n * (distList v1 v2))) (td0 n t v1) (td0 n t v2)} @-}
relationaltd0 :: Int -> Transition -> ValueFunction -> ValueFunction -> ()
relationaltd0 n t v1 v2 
    = relationaliterate (distList v1 v2) k n (act t) (relationalact t) v1 v2 
