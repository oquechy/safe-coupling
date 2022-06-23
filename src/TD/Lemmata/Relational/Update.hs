{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple"            @-}

module TD.Lemmata.Relational.Update where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators

{-@ updateSpec :: v1:_ -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> r:_ ->
                        {distD (update v1 i j r) (update v2 i j r) 
                            <= k * max (distD (at v1 i) (at v2 i)) (distD (at v1 j) (at v2 j))} @-}
updateSpec :: ValueFunction -> ValueFunction -> State -> State -> Reward -> ()
updateSpec v1 v2 i j r 
    =   distD (update v1 i j r) (update v2 i j r)
    === distD ((1 - alpha) * v1 `at` i + alpha * (r + gamma * v1 `at` j))
             ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v2 `at` j))
        ?   trinequality distDouble
                           ((1 - alpha) * v1 `at` i + alpha * (r + gamma * v1 `at` j))
                           ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v1 `at` j))
                           ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v2 `at` j))
    =<= distD ((1 - alpha) * v1 `at` i + alpha * (r + gamma * v1 `at` j))
             ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v1 `at` j))
             + distD ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v1 `at` j))
                    ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v2 `at` j))
        ?   linearity (1 - alpha) (alpha * (r + gamma * v1 `at` j)) (v1 `at` i) (v2 `at` i)
    =<= (1 - alpha) * distD (v1 `at` i) (v2 `at` i)
             + distD ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v1 `at` j))
                     ((1 - alpha) * v2 `at` i + alpha * (r + gamma * v2 `at` j))
        ?   linearity (alpha * gamma) ((1 - alpha) * v2 `at` i + alpha * r) (v1 `at` j) (v2 `at` j)
    =<= (1 - alpha) * distD (v1 `at` i) (v2 `at` i)
        + alpha * gamma * distD (v1 `at` j) (v2 `at` j)
    =<= k * max (distD (v1 `at` i) (v2 `at` i)) (distD (v1 `at` j) (v2 `at` j))
    *** QED
