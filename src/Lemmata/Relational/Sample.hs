{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Sample where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, uncurry)

import           Lemmata.Relational.Update

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

-- TODO: listLemma will be unnecessary when `at` is reflected
{-@ listLemma :: v1:_ -> v2:_ -> i:_ -> {dist (at v1 i) (at v2 i) <= distList v1 v2} @-}
listLemma :: ValueFunction -> ValueFunction -> State -> ()
listLemma = undefined

{-@ maxLemma :: v1:_ -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> 
                    {max (dist (at v1 i) (at v2 i)) (dist (at v1 j) (at v2 j)) <= distList v1 v2 } @-}
maxLemma :: ValueFunction -> ValueFunction -> State -> State -> ()
maxLemma v1 v2 i j 
    =   max (dist (at v1 i) (at v2 i)) (dist (at v1 j) (at v2 j)) 
        ? listLemma v1 v2 i
    =<= max (distList v1 v2) (dist (at v1 j) (at v2 j))
        ? listLemma v1 v2 j
    =<= max (distList v1 v2) (distList v1 v2)
    =<= distList v1 v2
    *** QED

{-@ updateLemma :: v1:_ -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> r:_ -> 
                    {dist (update v1 i j r) (update v2 i j r) <= k * distList v1 v2} @-}
updateLemma :: ValueFunction -> ValueFunction -> State -> State -> Reward -> ()
updateLemma v1 v2 i j r
    =   dist (update v1 i j r) (update v2 i j r)
        ? relationalupdate v1 v2 i j r
    =<= k * max (dist (at v1 i) (at v2 i)) (dist (at v1 j) (at v2 j))
        ? maxLemma v1 v2 i j
    =<= k * distList v1 v2
    *** QED

{-@ ignore pureUpdateLemma @-}
{-@ pureUpdateLemma :: m:_ -> v1:_ -> {v2:_|bounded m v1 v2 && llen v1 = llen v2} -> i:StateOf v1 -> t1:(StateOf v1, Reward) -> {t2:(StateOf v1, Reward)|eqP t1 t2} -> 
                {lift (bounded' (m * k)) (ppure (uncurry (update v1 i) t1)) (ppure (uncurry (update v2 i) t2))} @-}
pureUpdateLemma :: Double -> ValueFunction -> ValueFunction -> State -> (State, Reward) -> (State, Reward) -> ()
pureUpdateLemma m v1 v2 i (j1, r1) (j2, r2) = 
    liftPure (bounded' (max (dist (at v1 i) (at v2 i)) (dist (at v1 j1) (at v2 j2))))
                (update v1 i j1 r1) (update v2 i j2 r2) 
                (updateLemma v1 v2 i j1 r1)

{-@ ignore relationalsample@-}
-- INDEXING NV SHOULD FIX 

{-@ relationalsample :: m:_ -> t:_ -> {v1:_|llen t = llen v1} -> {v2:_|llen t = llen v2} -> i:StateOf t ->  
                        {bounded m v1 v2 => lift (bounded' (k * m)) (sample v1 t i) (sample v2 t i)} @-}
relationalsample :: Double -> Transition -> ValueFunction -> ValueFunction -> State -> ()
relationalsample m t v1 v2 i | bounded m v1 v2 
    = liftBind (bounded' (k * m)) eqP
               (t `at` i) (ppure `o` (uncurry (update v1 i)))
               (t `at` i) (ppure `o` (uncurry (update v2 i)))
               (liftEq (t `at` i))
               (pureUpdateLemma m v1 v2 i)
relationalsample _ _ _ _ _ = ()
