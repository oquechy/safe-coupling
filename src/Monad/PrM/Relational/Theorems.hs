-----------------------------------------------------------------
-- | Proved Theorems for Relational Properties: mapMSpec   ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Monad.PrM.Relational.Theorems where 

import           Monad.PrM
import           Monad.PrM.Lift
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM, const)

import           Monad.PrM.Relational.TCB.Spec 
import           Monad.PrM.Relational.TCB.EDist
import           Monad.PrM.Predicates

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


-------------------------------------------------------
-- | bindDistEq when the bind args are BijCoupling  ---
-------------------------------------------------------

{-@ predicate BijCoupling X Y = X = Y @-}
{-@ bindDistEq :: Eq a => d:Dist b -> m:Double 
               -> f1:(a -> PrM b) -> e1:PrM a 
               -> f2:(a -> PrM b) -> e2:{PrM a | BijCoupling e1 e2 } 
               -> (x:a -> { dist (kant d) (f1 x) (f2 x) <= m}) 
               -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDistEq :: Eq a => Dist b -> Double -> (a -> PrM b) -> PrM a -> (a -> PrM b) ->  PrM a ->  (a -> ()) -> ()
bindDistEq d m f1 e1 f2 e2 lemma = 
  bindDist d m eqP f1 e1 f2 (e2 `const` liftSpec e2) 
          (makeTwoArg d m f1 f2 lemma)
   
{-@ makeTwoArg :: Eq a => d:Dist b -> m:Double -> f1:(a -> PrM b) -> f2:(a -> PrM b)
        -> (x:a -> {v:() | dist (kant d) (f1 x) (f2 x) <= m}) 
        -> (x:a -> y:{a | eqP x y} -> { dist (kant d) (f1 x) (f2 y) <= m}) @-} 
makeTwoArg :: Eq a => Dist b -> Double -> (a -> PrM b) -> (a -> PrM b) -> (a -> ())
    -> (a -> a -> ())
makeTwoArg d m f1 f2 lemma x y = lemma x  

-------------------------------------------------------
-- | mapM Spec ----------------------------------------
-------------------------------------------------------

{-@ lazy mapMSpec @-}
{-@ mapMSpec :: {m:Double|0 <= m} 
                   -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) 
                   -> xs:[a]
                   -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)}) 
                   -> {lift (bounded m) (mapM f1 xs) (mapM f2 xs)} / [len xs, 0] @-}
mapMSpec :: Double -> (a -> PrM Double) -> (a -> PrM Double) -> List a 
               -> (a -> ()) 
               -> ()
mapMSpec m f1 f2 is@[] lemma 
    = pureSpec (bounded m) nilDouble nilDouble (boundedNil m)
mapMSpec m f1 f2 is'@(i:is) lemma
    = bindSpec (bounded m) (bounded' m)
            (f1 i) (consM (len is) (mapM f1 is))
            (f2 i) (consM (len is) (mapM f2 is))
            (lemma i)
            (consBindLemma m f1 f2 is lemma)

{-@ consLemma :: m:Double -> r1:Double -> rs1:List Double -> {r2:Double|bounded' m r1 r2} 
              -> {rs2:List Double|len rs1 = len rs2 && bounded m rs1 rs2} 
              -> {bounded m (consDouble r1 rs1) (consDouble r2 rs2)} @-}
consLemma :: Double -> Double -> List Double -> Double -> List Double -> ()
consLemma m r1 rs1 r2 rs2 = ()

{-@ lazy consBindLemma @-}
{-@ consBindLemma :: {m:Double|0 <= m} -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) 
                  -> xs:[a] 
                  -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)})
                  -> r1:Double
                  -> {r2:Double|bounded' m r1 r2}
                  -> {lift (bounded m) 
                           ((consM (len xs) (mapM f1 xs)) (r1)) 
                           ((consM (len xs) (mapM f2 xs)) (r2))} / [len xs, 1] @-}
consBindLemma :: Double -> (a -> PrM Double) -> (a -> PrM Double) 
              -> [a] 
              -> (a -> ()) 
              -> Double -> Double
              -> ()
consBindLemma m f1 f2 is lemma r1 r2
    = bindSpec (bounded m) (bounded m)
                         (mapM f1 is) (ppure `o` (consDouble r1))
                         (mapM f2 is) (ppure `o` (consDouble r2))
                         (mapMSpec m f1 f2 is lemma)
                         (pureLemma m r1 r2 f1 f2 is)

{-@ pureLemma :: {m:Double|0 <= m} 
           -> r1:Double -> {r2:Double|bounded' m r1 r2}  
           -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) -> is:List a 
           -> rs1:List Double -> rs2:{List Double|bounded m rs1 rs2}
           -> {lift (bounded m) (o ppure (consDouble r1) rs1)
                                (o ppure (consDouble r2) rs2)} @-}
pureLemma :: Double -> Double -> Double -> (a -> PrM Double) -> (a -> PrM Double) 
       -> List a -> List Double -> List Double -> () 
pureLemma m r1 r2 f1 f2 is rs1 rs2 | len rs1 == len rs2 
    = pureSpec (bounded m) 
        (consDouble r1 rs1) (consDouble r2 rs2) 
        (consLemma m r1 rs1 r2 rs2)
pureLemma m r1 r2 f1 f2 is rs1 rs2 = ()

{-@ boundedNil :: {m:Double|0 <= m} -> {bounded m nilDouble nilDouble} @-}
boundedNil :: Double -> ()
boundedNil _ = ()
