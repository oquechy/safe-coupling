{-@ LIQUID "--reflection"     @-}

module Theorem.TD0.TD0 where

import           Data.Dist
import           Data.List
import           Monad.Distr

import          Theorem.TD0.Act

import           TD0

import           Language.Haskell.Liquid.ProofCombinators

{-@ relationaltd0 :: n:Nat -> t:_ -> v1:_ -> v2:_ -> 
        {lift (bounded (pow k n * (distList v1 v2))) (td0 n t v1) (td0 n t v2)} @-}
relationaltd0 :: Int -> Transition -> ValueFunction -> ValueFunction -> ()
relationaltd0 n t v1 v2 
    = relationaliterate (distList v1 v2) k n (act t) (relationalact t) v1 v2
        ? (distList v1 v2 
            =<= distList v1 v2
            *** QED)

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
