{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Iterate where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (iterate)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationaliterate :: m:{_|0 <= m} -> {k:_|k >= 0} -> n:Nat -> f:_ -> 
                            (m:{_|0 <= m} -> x1:_ -> x2:{List Double | llen x1 == llen x2} -> {bounded m x1 x2 => lift (bounded (k * m)) (f x1) (f x2)}) ->
                            x1:_ -> {x2:_|llen x1 == llen x2 && bounded m x1 x2} -> 
                            {lift (bounded (pow k n * m)) (iterate n f x1) (iterate n f x2)} @-}
relationaliterate :: Double -> Double -> Int -> (List Double -> Distr (List Double)) ->
                        (Double -> List Double -> List Double -> ()) -> List Double -> List Double -> ()
relationaliterate m k n _ _ x1 x2 | n <= 0
    =   liftPure (bounded (pow k n * m)) x1 x2 ()
relationaliterate m k n f lemma x1 x2
    =   liftBind (bounded (pow k n * m)) (bounded (k * m)) 
                 (f x1) (iterate (n - 1) f)
                 (f x2) (iterate (n - 1) f)
                 (lemma m x1 x2)
                 undefined
                --  (relationaliterate (k * m) k (n - 1) f lemma)
            
