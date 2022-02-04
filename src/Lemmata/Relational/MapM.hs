{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.MapM where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationalmapM :: m:_ -> k:_ -> f1:_ -> v1:_ -> f2:_ -> v2:_ -> 
                        (x1:_ -> {x2:_|dist x1 x2 <= m} -> {lift (bounded' (k * m)) (f1 x1) (f2 x2)}) ->
                        {lift (bounded (k * m)) (mapM f1 v1) (mapM f2 v2)} @-}
relationalmapM :: Double -> Double -> (Double -> Distr Double) -> List Double -> (Double -> Distr Double) -> List Double -> 
                    (Double -> Double -> ()) -> ()

relationalmapM m k f1 v1 f2 v2 _
    = undefined 

{-     
relationalmapM m k _ v1 _ Nil _
    =   liftPure (bounded (k * m)) v1 Nil
relationalmapM m k _ Nil _ v2 _
    =   liftPure (bounded (k * m)) Nil v2
-- mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))
relationalmapM m k f1 v1 f2 (Cons i is) lemma = undefined
    -- =   liftBind (bounded (k * m)) trueP
    --         (f1 i1) (cons (mapM f is2))
    --         (\i1 i2 -> 
    --             distList (cons (mapM f xs1) x1) (cons (mapM f xs2) x2)) 
    --             =<= k * m
    --             *** QED)

-}