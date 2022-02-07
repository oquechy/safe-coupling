{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Act where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           Lemmata.Relational.MapM
import           Lemmata.Relational.Sample

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationalact :: t:_ -> m:{_|0 <= m} -> v1:_ -> {v2:_|llen v1 = llen v2} -> 
                    {bounded m v1 v2 => lift (bounded (k * m)) (act (llen v1) t v1) (act (llen v2) t v2)} @-}
relationalact :: Transition -> Double -> ValueFunction -> ValueFunction -> ()
relationalact t m v1 v2 | bounded m v1 v2 
    = relationalmapM (k * m)
            (sample v1 t) (range 0 (llen v1)) 
            (sample v2 t) (range 0 (llen v2)) 
            (relationalsample m t v1 v2)
relationalact _ _ _ _ = ()