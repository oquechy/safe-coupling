{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Lemmata.Relational.Act where 

import           Monad.PrM
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           Monad.PrM.Predicates
import           Monad.PrM.Relational.Theorems (mapMSpec)

import           TD.Lemmata.Relational.Sample

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators



{-@ relationalact :: l:Nat -> t:TransitionOf l -> m:{Double|0 <= m} -> v1:{ValueFunction | len v1 == l} 
                  -> {v2:ValueFunction|len v2 = l} 
                  -> {bounded m v1 v2 => lift (bounded (k * m)) (act l t v1) (act l t v2)} @-}
relationalact :: Int -> Transition -> Double -> ValueFunction -> ValueFunction -> ()
relationalact _ t m v1 v2 | bounded m v1 v2 
    = mapMSpec (k * m)
            (sample v1 t) (sample v2 t) 
            (range 0 (len v1)) 
            (relationalsample m (len v1) t v1 v2)
relationalact _ _ _ _ _ = ()