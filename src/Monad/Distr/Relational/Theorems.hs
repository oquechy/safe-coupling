-----------------------------------------------------------------
-- | Proved Theorems for Relational Properties: mapMSpec   ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Monad.Distr.Relational.Theorems where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM)

import           Monad.Distr.Relational.TCB.Spec 
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Predicates

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


-------------------------------------------------------
-- | bindDistEq when the bind args are BijCoupling  ---
-------------------------------------------------------

{-@ predicate BijCoupling X Y = X = Y @-}
{-@ bindDistEq :: d:Dist b -> m:Double 
               -> f1:(a -> Distr b) -> e1:Distr a 
               -> f2:(a -> Distr b) -> e2:{Distr a | BijCoupling e1 e2 } 
               -> (x:a -> { dist (kant d) (f1 x) (f2 x) <= m}) 
               -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDistEq :: Eq a => Dist b -> Double -> (a -> Distr b) -> Distr a -> (a -> Distr b) ->  Distr a ->  (a -> ()) -> ()
bindDistEq d m f1 e1 f2 e2 lemma = 
  bindDist d m eqP f1 e1 f2 (e2 `const` liftSpec e2) 
          (makeTwoArg d m f1 f2 lemma)
   
{-@ makeTwoArg :: d:Dist b -> m:Double -> f1:(a -> Distr b) -> f2:(a -> Distr b)
        -> (x:a -> {v:() | dist (kant d) (f1 x) (f2 x) <= m}) 
        -> (x:a -> y:{a | eqP x y} -> { dist (kant d) (f1 x) (f2 y) <= m}) @-} 
makeTwoArg :: Dist b -> Double -> (a -> Distr b) -> (a -> Distr b) -> (a -> ())
    -> (a -> a -> ())
makeTwoArg d m f1 f2 lemma x y = lemma x  

-------------------------------------------------------
-- | mapM Spec ----------------------------------------
-------------------------------------------------------

{-@ mapMSpec :: {m:_|0 <= m} 
                   -> f1:(a -> Distr Double) -> f2:(a -> Distr Double) 
                   -> is:List a
                   -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)}) 
                   -> {lift (bounded m) (mapM f1 is) (mapM f2 is)} / [llen is, 0] @-}
mapMSpec :: Double -> (a -> Distr Double) -> (a -> Distr Double) -> List a 
               -> (a -> ()) 
               -> ()
mapMSpec m f1 f2 is@Nil lemma
    = pureSpec (bounded m) Nil Nil (boundedNil m)
mapMSpec m f1 f2 (Cons i is) lemma 
    = bindSpec (bounded m) (bounded' m)
            (f1 i) (cons (llen is) (mapM f1 is))
            (f2 i) (cons (llen is) (mapM f2 is))
            (lemma i)
            (consBindLemma m f1 f2 is lemma)

{-@ consLemma :: m:_ -> r1:_ -> rs1:_ -> {r2:_|bounded' m r1 r2} -> {rs2:_|llen rs1 = llen rs2 && bounded m rs1 rs2} 
              -> {bounded m (Cons r1 rs1) (Cons r2 rs2)} @-}
consLemma :: Double -> Double -> List Double -> Double -> List Double -> ()
consLemma m r1 rs1 r2 rs2 = ()

{-@ consBindLemma :: {m:_|0 <= m} -> f1:_ -> f2:_ -> is:_ 
                  -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)})
                  -> r1:_ 
                  -> {r2:_|bounded' m r1 r2}
                  -> {lift (bounded m) 
                           ((cons (llen is) (mapM f1 is)) (r1)) 
                           ((cons (llen is) (mapM f2 is)) (r2))} / [llen is, 1] @-}
consBindLemma :: Double -> (a -> Distr Double) -> (a -> Distr Double) 
              -> List a 
              -> (a -> ()) 
              -> Double -> Double
              -> ()
consBindLemma m f1 f2 is lemma r1 r2
    = bindSpec (bounded m) (bounded m)
                         (mapM f1 is) (ppure `o` (consDouble r1))
                         (mapM f2 is) (ppure `o` (consDouble r2))
                         (mapMSpec m f1 f2 is lemma) 
                         (pureLemma m r1 r2 f1 f2 is) 

{-@ pureLemma :: {m:_|0 <= m} 
           -> r1:_ -> {r2:_|bounded' m r1 r2}  
           -> f1:_ -> f2:_ -> is:_ 
           -> rs1:_ -> rs2:{_|bounded m rs1 rs2}
           -> {lift (bounded m) (o ppure (consDouble r1) rs1)
                                (o ppure (consDouble r2) rs2)} @-}
pureLemma :: Double -> Double -> Double -> (a -> Distr Double) -> (a -> Distr Double) 
       -> List a -> List Double -> List Double -> () 
pureLemma m r1 r2 f1 f2 is rs1 rs2 = pureSpec (bounded m) 
                                     (Cons r1 rs1) (Cons r2 rs2) 
                                     (consLemma m r1 rs1 r2 rs2)

