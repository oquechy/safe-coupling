{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Act where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationalact :: t:_ -> m:_ -> v1:_ -> v2:_ -> 
                    {bounded m v1 v2 => lift (bounded (k * m)) (act t v1) (act t v2)} @-}
relationalact :: Transition -> Double -> ValueFunction -> ValueFunction -> ()
relationalact t m v1 v2 
    =   undefined
    -- relationalmapM m k 
    --         (sample t v1) (range 0 (llen v1)) 
    --         (sample t v2) (range 0 (llen v2)) 
    --         (relationalsample m t v1 v2)