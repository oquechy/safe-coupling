{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Sample where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, uncurry)

import           Lemmata.Relational.Update

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators

{- 
{-@ lemma :: m:_ -> v1:_ -> {v2:_|bounded m v1 v2} -> i:_ -> t1:_ -> {t2:_|eqP t1 t2} -> 
                {lift (bounded' (m * k)) (ppure (uncurry (update v1 i) t1)) (ppure (uncurry (update v2 i) t2))} @-}
lemma :: Double -> ValueFunction -> ValueFunction -> State -> (State, Reward) -> (State, Reward) -> ()
lemma m v1 v2 i (j1, r1) (j2, r2) = 
    liftPure (bounded' (max (dist (at v1 i) (at v2 i)) (dist (at v1 j1) (at v2 j2))))
                (update v1 i j1 r1) (update v2 i j2 r2) 
                (dist (update v1 i j1 r1) (update v2 i j2 r2)
                    === dist (update v1 i j1 r1) (update v2 i j1 r1)
                        ? relationalupdate v1 v2 i j1 r1
                    =<= k * max (dist (at v1 i) (at v2 i)) (dist (at v1 j1) (at v2 j1))
                        ? (max (dist (at v1 i) (at v2 i)) (dist (at v1 j1) (at v2 j2))
                            =<= distList v1 v2 
                            =<= m
                            *** QED)
                    =<= k * m
                        *** QED)
-}
{-@ relationalsample :: m:_ -> t:_ -> v1:_ -> v2:_ -> i:_ ->  
                        {bounded m v1 v2 => lift (bounded' (k * m)) (sample t v1 i) (sample t v2 i)} @-}
relationalsample :: Double -> Transition -> ValueFunction -> ValueFunction -> State -> ()
relationalsample m t v1 v2 i | bounded m v1 v2 
    = liftBind (bounded' (k * m)) eqP
               (t `at` i) (ppure `o` (uncurry (update v1 i)))
               (t `at` i) (ppure `o` (uncurry (update v2 i)))
               (liftEq (t `at` i))
               undefined -- (lemma m v1 v2 i)
relationalsample _ _ _ _ _ = ()