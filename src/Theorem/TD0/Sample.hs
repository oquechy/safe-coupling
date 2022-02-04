{-@ LIQUID "--reflection"     @-}

module Theorem.TD0.Sample where

import           Data.Dist
import           Data.List
import           Monad.Distr
import           TD0
import           Language.Haskell.Liquid.ProofCombinators

{-@ relationalsample :: m:_ -> t:_ -> i:_ -> v1:_ -> v2:_ ->  
                        {bounded m v1 v2 => lift (bounded' (k * m)) (sample t v1 i) (sample t v2 i)} @-}
relationalsample :: Double -> Transition -> State -> ValueFunction -> ValueFunction -> ()
relationalsample = undefined
