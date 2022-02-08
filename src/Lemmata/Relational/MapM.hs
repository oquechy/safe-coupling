{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.MapM where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ boundedNil :: {m:_|0 <= m} -> {true} @-}
boundedNil :: Double -> ()
boundedNil _ = ()

{-@ relationalmapM :: {m:_|0 <= m} -> f1:(a -> Distr Double) -> is1:List a -> 
                        f2:(a -> Distr Double) -> {is2:List a|is1 = is2} -> 
                        (i:a -> {lift (bounded' m) (f1 i) (f2 i)}) ->
                        {lift (bounded m) (mapM f1 is1) (mapM f2 is2)} @-}
relationalmapM :: Double -> (a -> Distr Double) -> List a -> (a -> Distr Double) -> List a -> 
                    (a -> ()) -> ()
-- mapM _ Nil = ppure Nil
relationalmapM m f1 Nil f2 Nil _
    =   undefined
        -- liftPure (bounded (k * m)) Nil Nil (boundedNil (k * m))
-- mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))
relationalmapM m f1 (Cons i1 is1) f2 (Cons i2 is2) lemma = undefined
    -- =   liftBind (bounded (k * m)) (bounded' (k * m))
    --         (f1 i1) (cons (mapM f1 is2))
    --         (f2 i2) (cons (mapM f2 is2))
    --         (lemma i1 i2)
    --         undefined
            -- (\r1 r2 -> 
            --     liftBind (bounded (k * m)) (bounded (k * m))
            --              (mapM f1 is1) (ppure `o` (Cons r1))
            --              (mapM f2 is2) (ppure `o` (Cons r2))
            --              (relationalmapM m k f1 is1 f2 is2 lemma)
            --              (\rs1 rs2 -> 
            --                 liftPure (bounded (k * m)) (Cons r1 rs1) (Cons r2 rs2) ()))
            


-- {-@ consbounded :: m:Double -> x1:Distr Double -> xs1:Distr (List Double) -> {x2:Distr Double|bounded' m x1 x2} -> {xs2:Distr (List Double)|bounded m xs1 xs2} -> 
--                     {bounded m (consM x1 xs1) (consM x2 xs2)} @-}
-- consbounded :: Double -> Distr Double -> Distr (List Double) -> Distr Double -> Distr (List Double) -> ()
-- consbounded = undefined
