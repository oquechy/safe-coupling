{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Theorem where 

import           Monad.PrM
import           Monad.PrM.Lift
import           Data.Dist
import           Data.List

import           Monad.PrM.Predicates


import           TD.Lemmata.Relational.Act
import           TD.Lemmata.Relational.Iterate

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


{-@ relationaltd0 :: n:Nat -> l:Nat -> t:TransitionOf l -> {v1:ValueFunction|len v1 = l} -> v2:SameLen v1 -> 
        {lift (bounded (pow k n * (distList distDouble v1 v2))) (td0 n v1 t) (td0 n v2 t)} @-}
relationaltd0 :: Int -> Int -> Transition -> ValueFunction -> ValueFunction -> ()
relationaltd0 n l t v1 v2 
    = relationaliterate (distList distDouble v1 v2) k n l (act l t) (relationalact l t) v1 v2 
