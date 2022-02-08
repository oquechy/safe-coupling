{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Update where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators

{-@ relationalupdate :: v1:_ -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> r:_ ->
                        {dist (update v1 i j r) (update v2 i j r) 
                            <= k * max (dist (at v1 i) (at v2 i)) (dist (at v1 j) (at v2 j))} @-}
relationalupdate :: ValueFunction -> ValueFunction -> State -> State -> Reward -> ()
relationalupdate v1 v2 i j r 
    =   dist (update v1 i j r) (update v2 i j r)
    === dist ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
             ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   triangularIneq ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
                           ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                           ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
    =<= dist ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
             ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
             + dist ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                    ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   linearity (1 - α) (α * (r + γ * v1 `at` j)) (v1 `at` i) (v2 `at` i)
    =<= (1 - α) * dist (v1 `at` i) (v2 `at` i)
             + dist ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                    ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   linearity (α * γ) ((1 - α) * v2 `at` i + α * r) (v1 `at` j) (v2 `at` j)
    =<= (1 - α) * dist (v1 `at` i) (v2 `at` i)
        + α * γ * dist (v1 `at` j) (v2 `at` j)
    =<= k * max (dist (v1 `at` i) (v2 `at` i)) (dist (v1 `at` j) (v2 `at` j))
    *** QED
