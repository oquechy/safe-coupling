{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.MapM where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ consLemma :: m:_ -> r1:_ -> rs1:_ -> {r2:_|bounded' m r1 r2} -> {rs2:_|llen rs1 = llen rs2 && bounded m rs1 rs2} 
              -> {bounded m (Cons r1 rs1) (Cons r2 rs2)} @-}
consLemma :: Double -> Double -> List Double -> Double -> List Double -> ()
consLemma m r1 rs1 r2 rs2 = ()

{-@ relationalmapM :: {m:_|0 <= m} 
                   -> f1:(a -> Distr Double) -> f2:(a -> Distr Double) 
                   -> is:List a
                   -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)}) 
                   -> {lift (bounded m) (mapM f1 is) (mapM f2 is)} @-}
relationalmapM :: Double -> (a -> Distr Double) -> (a -> Distr Double) -> List a 
               -> (a -> ()) 
               -> ()
relationalmapM m f1 f2 is@Nil lemma
    =   liftPure (bounded m) Nil Nil (boundedNil m)
relationalmapM m f1 f2 (Cons i is) lemma 
    =   liftBind (bounded m) (bounded' m)
            (f1 i) (cons (llen is) (mapM f1 is))
            (f2 i) (cons (llen is) (mapM f2 is))
            (lemma i)
            (\r1 r2 -> 
                liftBind (bounded m) (bounded m)
                         (mapM f1 is) (ppure `o` (consDouble r1))
                         (mapM f2 is) (ppure `o` (consDouble r2))
                         (relationalmapM m f1 f2 is lemma)
                         (\rs1 rs2 -> 
                            liftPure (bounded m) 
                                     (Cons r1 rs1) (Cons r2 rs2) 
                                     (consLemma m r1 rs1 r2 rs2)))