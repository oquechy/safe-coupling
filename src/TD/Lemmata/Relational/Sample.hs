{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Lemmata.Relational.Sample where 

import           Monad.PrM
import           Data.Dist
import           Data.List
import           Prelude hiding (max, uncurry)

import           Monad.PrM.Relational.TCB.Spec 
import           Monad.PrM.Predicates      
import           Monad.PrM.Lift      

import           TD.Lemmata.Relational.Update

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ listLemma :: v1:ValueFunction -> v2:SameLen v1 -> i:StateOf v1 
              -> {distD (at v1 i) (at v2 i) <= distList distDouble v1 v2} @-}
listLemma :: ValueFunction -> ValueFunction -> State -> ()
listLemma [] v2 i = ()
listLemma v1 [] i = ()
listLemma (x:xs) (y:ys) 0 = ()
listLemma (x:xs) (y:ys) i = listLemma xs ys (i - 1)

{-@ maxLemma :: v1:ValueFunction -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> 
                    {max (distD (at v1 i) (at v2 i)) (distD (at v1 j) (at v2 j)) <= distList distDouble v1 v2 } @-}
maxLemma :: ValueFunction -> ValueFunction -> State -> State -> ()
maxLemma v1 v2 i j 
    =   max (distD (at v1 i) (at v2 i)) (distD (at v1 j) (at v2 j)) 
        ? listLemma v1 v2 i
    =<= max (distList distDouble v1 v2) (distD (at v1 j) (at v2 j))
        ? listLemma v1 v2 j
    =<= max (distList distDouble v1 v2) (distList distDouble v1 v2)
    =<= distList distDouble v1 v2
    *** QED

{-@ updateLemma :: v1:ValueFunction -> v2:SameLen v1 -> i:StateOf v1 -> j:StateOf v1 -> r:Reward -> 
                    {distD (update v1 i j r) (update v2 i j r) <= k * distList distDouble v1 v2} @-}
updateLemma :: ValueFunction -> ValueFunction -> State -> State -> Reward -> ()
updateLemma v1 v2 i j r
    =   distD (update v1 i j r) (update v2 i j r)
        ? relationalupdate v1 v2 i j r
    =<= k * max (distD (at v1 i) (at v2 i)) (distD (at v1 j) (at v2 j))
        ? maxLemma v1 v2 i j
    =<= k * distList distDouble v1 v2
    *** QED

{-@ uncurryLemma :: {m:Double|0 <= m} -> v1:ValueFunction -> v2:SameLen v1 -> {_:()|bounded m v1 v2} -> i:StateOf v1 
                 -> t1:(StateOf v1, Reward) -> {t2:(StateOf v1, Reward)|t1 = t2}
                 -> {bounded' (k * m) (uncurry (update v1 i) t1) (uncurry (update v2 i) t2)} @-}
uncurryLemma :: Double -> ValueFunction -> ValueFunction -> () -> State 
             -> (State, Reward) -> (State, Reward) 
             -> ()
uncurryLemma m v1 v2 b i t1@(j1, r1) t2@(j2, r2) 
    =   distD (uncurry (update v1 i) t1) (uncurry (update v2 i) t2)
    === distD (uncurry (update v1 i) t1) (uncurry (update v2 i) t1)
    === distD (update v1 i j1 r1) (update v2 i j1 r1)
        ? updateLemma v1 v2 i j1 r1
    =<= k * distList distDouble v1 v2
        ? b
    =<= k * m
    *** QED

{-@ pureUpdateLemma :: {m:Double|0 <= m} -> v1:ValueFunction -> v2:SameLen v1 -> {_:()|bounded m v1 v2} -> i:StateOf v1 
                    -> t1:(StateOf v1, Reward) -> {t2:(StateOf v1, Reward)|eqP t1 t2} 
                    -> {lift (bounded' (k * m)) ((o ppure (uncurry (update v1 i))) (t1)) ((o ppure (uncurry (update v2 i))) (t2))} @-}
pureUpdateLemma :: Double -> ValueFunction -> ValueFunction -> () -> State -> (State, Reward) -> (State, Reward) -> ()
pureUpdateLemma m v1 v2 b i t1@(j1, r1) t2@(j2, r2) = 
    pureSpec (bounded' (k * m))
                (uncurry (update v1 i) t1) (uncurry (update v2 i) t2)
                (uncurryLemma m v1 v2 b i t1 t2)
        

{-@ relationalsample :: {m:Double|0 <= m} -> n:Nat -> t:TransitionOf n -> {v1:ValueFunction|len t = len v1 && len v1 == n } -> {v2:ValueFunction|len t = len v2} 
                     -> i:StateOf t 
                     -> {bounded m v1 v2 => lift (bounded' (k * m)) (sample v1 t i) (sample v2 t i)} @-}
relationalsample :: Double -> Int ->  Transition -> ValueFunction -> ValueFunction -> State -> ()
relationalsample m n t v1 v2 i | bounded m v1 v2 
    = bindSpec (bounded' (k * m)) eqP
               (t `at` i) (ppure `o` (uncurry (update v1 i)))
               (t `at` i) (ppure `o` (uncurry (update v2 i)))
               (liftSpec (t `at` i))
               (pureUpdateLemma m v1 v2 () i)
relationalsample _ _ _ _ _ _ = ()