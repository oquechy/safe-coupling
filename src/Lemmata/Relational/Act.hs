{-@ LIQUID "--reflection"     @-}
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



{-@ relationalact :: l:Nat -> t:TransitionOf l -> m:{_|0 <= m} -> v1:{_ | llen v1 == l} 
                  -> {v2:_|llen v2 = l} 
                  -> {bounded m v1 v2 => lift (bounded (k * m)) (act l t v1) (act l t v2)} @-}
relationalact :: Int -> Transition -> Double -> ValueFunction -> ValueFunction -> ()
relationalact _ t m v1 v2 | bounded m v1 v2 
    = relationalmapM (k * m)
            (sample v1 t) (sample v2 t) 
            (range 0 (llen v1)) 
            (relationalsample m (llen v1) t v1 v2)
relationalact _ _ _ _ _ = ()