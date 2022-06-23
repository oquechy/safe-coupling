{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.TheoremDist where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( flip )

import           Monad.Distr.Predicates
import           Monad.Distr.Laws
import           Monad.Distr.Relational.TCB.Axiom 
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Relational.Theorems
import           Bins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators 

-----------------------------------------------------------------
-- | Proof ------------------------------------------------------
-----------------------------------------------------------------

{-@ plusDist :: y:Double -> x1:Double -> x2:Double 
             -> {distD (plus y x1) (plus y x2) = distD x1 x2} @-}
plusDist :: Double -> Double -> Double -> ()
plusDist _ _ _ = ()

{-@ addBernoulliDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble -> {y:PDouble|y <= n}
             -> {dist (kant distDouble) (addBernoulli p n y) (addBernoulli q n y) <= q - p} @-}
addBernoulliDist :: Prob -> Prob -> Double -> Double -> ()
addBernoulliDist p q n y
  =   dist (kant distDouble) (addBernoulli p n y) (addBernoulli q n y)
        ? pureBindDist distDouble distDouble
                 0
                 (plus y) (bernoulli p)
                 (plus y) (bernoulli q)
                 (plusDist y)
  =<= dist (kant distDouble) (bernoulli p) (bernoulli q)
     ? (bernoulliDist distDouble p q)
     ? assert (distD 1.0 0.0 == 1.0)
     ? assert (distD 1 0 * (q-p) == q-p)
  =<= distD 1 0 * (q -p)
  =<=  q - p
  *** QED

{-@ binsDistL :: p:Prob -> {q:Prob|p <= q} -> {n:PDouble|1 <= n}
             -> {dist (kant distDouble) (bins n p) (gbins p q n) <= q - p} @-}
binsDistL :: Prob -> Prob -> Double -> ()
binsDistL p q n 
  = bindDistEq distDouble 
               (q - p)
               (addBernoulli p (n - 1)) (bins (n - 1) p)
               (addBernoulli q (n - 1)) (bins (n - 1) p)
               (addBernoulliDist p q (n - 1))

{-@ addBinsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble -> x:Double 
                -> {dist (kant distDouble) 
                         (seqBind (bins n p) (flip (pure2 plus)) x)
                         (seqBind (bins n q) (flip (pure2 plus)) x)
                          <= n * (q - p)} / [n, 2] @-}
addBinsDist ::  Prob -> Prob -> Double -> Double -> ()
addBinsDist p q n x 
  =   dist (kant distDouble) 
           (seqBind (bins n p) (flip (pure2 plus)) x)
           (seqBind (bins n q) (flip (pure2 plus)) x)
  === dist (kant distDouble) 
           (bind (bins n p) (flip (pure2 plus) x))
           (bind (bins n q) (flip (pure2 plus) x))
      ? flipPlus x 
  === dist (kant distDouble) 
           (bind (bins n p) (ppure . (plus x)))
           (bind (bins n q) (ppure . (plus x)))
        ? pureBindDist distDouble distDouble
                       0
                       (plus x) (bins n p)
                       (plus x) (bins n q)
                       (plusDist x)
  =<= dist (kant distDouble) (bins n p) (bins n q)
       ? binsDist p q n 
  =<=  n * (q - p) 
  *** QED

{-@ addBernoulliEq :: n:{Double | 0 <= n - 1 } -> p:Prob -> q:Prob 
                   -> {addBernoulli q (n - 1) == seqBind (bernoulli q) (pure2 plus)} @-}
addBernoulliEq :: Double -> Double -> Double -> () 
addBernoulliEq n p q 
  = extDouble (addBernoulli q (n - 1)) (seqBind (bernoulli q) (pure2 plus)) 
              (addBernoulliEq' n p q)

{-@ addBernoulliEq' :: n:{Double | 0 <= n - 1 } -> p:Prob -> q:Prob 
                    -> x:{Double | 0 <= x && x <= n - 1 }
                   -> {addBernoulli q (n - 1) x == seqBind (bernoulli q) (pure2 plus) x} @-}
addBernoulliEq' :: Double -> Double -> Double -> Double -> () 
addBernoulliEq' n p q x
  =   addBernoulli q (n - 1) x 
  === bind (bernoulli q) (ppure . plus x)
       ? extDouble (ppure . plus x) (pure2 plus x) (
           \z -> (ppure . plus x) z  === pure2 plus x z *** QED 
       )
  === bind (bernoulli q) (pure2 plus x)
  === bind (bernoulli q) (pure2 plus x)
  === seqBind (bernoulli q) (pure2 plus) x
  *** QED 

{-@ binsDistR :: p:Prob -> {q:Prob|p <= q} -> {n:PDouble|1 <= n} 
              -> {dist (kant distDouble) (gbins p q n) (bins n q) <= (n - 1) * (q - p)} 
              / [n, 0] @-}
binsDistR ::Prob -> Prob -> Double -> ()
binsDistR p q n 
  =   dist (kant d) (gbins p q n) (bins n q)
      ? addBernoulliEq n p q 
      ? assert (gbins p q n == bind (bins (n - 1) p) (seqBind (bernoulli q) (pure2 plus)))
      ? assert (bins n q == bind (bins (n - 1) q) (seqBind (bernoulli q) (pure2 plus)))
  === dist (kant d) 
           (bind (bins (n - 1) p) (seqBind (bernoulli q) (pure2 plus))) 
           (bind (bins (n - 1) q) (seqBind (bernoulli q) (pure2 plus)))
      ? commutative (bins (n - 1) p) (bernoulli q) (pure2 plus)
      ? commutative (bins (n - 1) q) (bernoulli q) (pure2 plus)
  === dist (kant d) 
           (bind (bernoulli q) (seqBind (bins (n - 1) p) (flip (pure2 plus)))) 
           (bind (bernoulli q) (seqBind (bins (n - 1) q) (flip (pure2 plus))))
        ? bindDistEq d
                     ((n - 1) * (q - p))
                     (seqBind (bins (n - 1) p) (flip (pure2 plus))) (bernoulli q)
                     (seqBind (bins (n - 1) q) (flip (pure2 plus))) (bernoulli q)
                     (addBinsDist p q (n - 1))
  =<= (n - 1) * (q - p)
  *** QED
    where d = distDouble 

{-@ binsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble 
             -> {dist (kant distDouble) (bins n p) (bins n q) <= n * (q - p)} 
             / [n, 1] @-}
binsDist :: Prob -> Prob -> Double -> ()
binsDist p q n | n < 1.0 
  = pureDist distDouble 0 0 
  ? assert (0 <= n) 
  ? assert (0 <= (q - p)) 
  ? assert (dist (kant distDouble) (bins n p) (bins n q) <= n * (q - p)) 
binsDist p q n
  =   dist (kant d) (bins n p) (bins n q)
      ? trinequality (kant d) (bins n p) (gbins p q n) (bins n q)
      ? assert (dist (kant d) (bins n p) (bins n q) 
                   <= dist (kant d) (bins n p) (gbins p q n)
                    + dist (kant d) (gbins p q n) (bins n q))
  =<= dist (kant d) (bins n p) (gbins p q n)
        + dist (kant d) (gbins p q n) (bins n q)  
      ? binsDistL p q n
  =<= q - p
        + dist (kant d) (gbins p q n) (bins n q)  
      ? binsDistR p q n
  =<= q - p + (n - 1) * (q - p)
  =<= n * (q - p)
  *** QED
  where d = distDouble

{-@ reflect gbins @-}
{-@ gbins :: Prob -> Prob -> n:Double -> Distr Double @-}
gbins :: Double -> Double -> Double -> Distr Double
gbins _ q n | n < 1.0 = ppure 0
gbins p q n = bind (bins (n - 1) p) (addBernoulli q (n - 1))

{-@ flipPlus :: x:Double -> {(flip (pure2 plus) x) == (ppure . (plus x))} @-}
flipPlus :: Double -> () 
flipPlus x = extDouble (flip (pure2 plus) x) (ppure . (plus x)) (flipPlus' x)

{-@ flipPlus' :: x:Double -> y:Double -> {(flip (pure2 plus) x y) == (ppure . (plus x)) (y)} @-}
flipPlus' :: Double -> Double -> () 
flipPlus' _ _ = ()

