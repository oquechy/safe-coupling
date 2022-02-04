{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Iterate where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationaliterate :: m:_ -> {k:_|k >= 0} -> n:Nat -> f:_ -> 
                            (m:_ -> x1:_ -> x2:_ -> {bounded m x1 x2 => lift (bounded (k * m)) (f x1) (f x2)}) ->
                            x1:_ -> x2:_ -> 
                            {bounded m x1 x2 => lift (bounded (pow k n * m)) (iterate n f x1) (iterate n f x2)} @-}
relationaliterate :: Double -> Double -> Int -> (List Double -> Distr (List Double)) ->
                        (Double -> List Double -> List Double -> ()) -> List Double -> List Double -> ()
relationaliterate m k n _ _ x1 x2 | n <= 0
    =   undefined
        -- liftPure (bounded (pow k n * m)) x1 x2  
            -- ? (distList x1 x2 
            --     =<= m
            --     =<= pow k n * m
            --     *** QED)
relationaliterate m k n f lemma x1 x2
    =   undefined
        -- liftBind (bounded (pow k n * m)) (bounded (k * m)) 
        --          (f x1) (iterate (n - 1) f)
        --          (f x2) (iterate (n - 1) f)
        --          (relationaliterate (k * m) k (n - 1) f lemma)
        --     ? lemma m x1 x2
