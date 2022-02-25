{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.Theorem where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( flip )

import           Monad.Distr.Predicates
import           Monad.Distr.Relational.TCB.Spec 
import           Monad.Distr.Relational.TCB.EDist
import           Bins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{- 
{-@ relationalinccond :: x1:Double -> {x2:Double|x1 <= x2} -> y1:Double -> {y2:Double|leDoubleP y1 y2} 
                      -> {lift leDoubleP (incCond x1 y1) (incCond x2 y2)} @-}
relationalinccond :: Double -> Double -> Double -> Double -> ()
relationalinccond x1 x2 y1 y2 = pureSpec leDoubleP
                                         (y1 + x1)
                                         (y2 + x2)
                                         ()
                                
{-@ relationalbinsrec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double -> x1:Double -> {x2:Double| x1 <= x2}
                      -> {lift leDoubleP (addBernoulli p n x1) (addBernoulli q n x2)} / [n, 1] @-}
relationalbinsrec :: Double -> Double -> Double -> Double -> Double -> ()
relationalbinsrec p q n x1 x2
    = bindSpec leDoubleP leDoubleP
        (bins p n) (incCond x1)
        (bins q n) (incCond x2)
        (binsSpec p q n)
        (relationalinccond x1 x2)
 
{-@ binsSpec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double 
             -> {lift leDoubleP (bins p n) (bins q n)} / [n, 0] @-}
binsSpec :: Double -> Double -> Double -> ()
binsSpec p q n | n < 1  
    = pureSpec leDoubleP 0 0 ()
binsSpec p q n 
    = bindSpec leDoubleP leDoubleP
               (bernoulli p) (addBernoulli p (n - 1))
               (bernoulli q) (addBernoulli q (n - 1))
               (bernoulliSpec p q)
               (relationalbinsrec p q (n - 1))

-}

{-@ plusDist :: y:Double -> x1:Double -> x2:Double -> {distD (plus y x1) (plus y x2) = distD x1 x2} @-}
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
  *** QED

{-@ binsDistL :: p:Prob -> {q:Prob|p <= q} -> {n:PDouble|1 <= n}
             -> {dist (kant distDouble) (bins p n) (bins' p q n) <= q - p} @-}
binsDistL :: Prob -> Prob -> Double -> ()
binsDistL p q n 
  = bindDistEq distDouble 
               (q - p)
               (addBernoulli p (n - 1)) (bins p (n - 1))
               (addBernoulli q (n - 1)) (bins p (n - 1))
               (addBernoulliDist p q (n - 1))

{-@ addBinsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble -> x:Double 
                -> {dist (kant distDouble) 
                         (seqBind (bins p n) (flip (pure2 plus)) x)
                         (seqBind (bins q n) (flip (pure2 plus)) x)
                          <= n * (q - p)} @-}
addBinsDist :: Prob -> Prob -> Double -> Double -> ()
addBinsDist p q n x 
  =   dist (kant distDouble) 
           (seqBind (bins p n) (flip (pure2 plus)) x)
           (seqBind (bins q n) (flip (pure2 plus)) x)
  === dist (kant distDouble) 
           (bind (bins p n) (flip (pure2 plus) x))
           (bind (bins q n) (flip (pure2 plus) x))
  === dist (kant distDouble) 
           (bind (bins p n) (ppure . (plus x)))
           (bind (bins q n) (ppure . (plus x)))
        ? pureBindDist distDouble distDouble
                       (n * (q - p))
                       (plus x) (bins p n)
                       (plus x) (bins q n)
                       (plusDist x)
  =<= n * (q - p)
  *** QED

{-@ reflect pure2 @-}
pure2 :: (a -> b -> c) -> a -> b -> Distr c
pure2 f a b = ppure (f a b)

{-@ binsDistR :: p:Prob -> {q:Prob|p <= q} -> {n:PDouble|1 <= n} 
             -> {dist (kant distDouble) (bins' p q n) (bins q n) <= (n - 1) * (q - p)} @-}
binsDistR :: Prob -> Prob -> Double -> ()
binsDistR p q n 
  =   dist (kant distDouble) (bins' p q n) (bins q n)
      ? assume (bins' p q n == bind (bins p (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
      ? assume (bins q n == bind (bins q (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
  === dist (kant distDouble) 
           (bind (bins p (n - 1)) (seqBind (bernoulli q) (pure2 plus))) 
           (bind (bins q (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
      ? commutative (bins p (n - 1)) (bernoulli q) (pure2 plus)
      ? commutative (bins q (n - 1)) (bernoulli q) (pure2 plus)
  === dist (kant distDouble) 
           (bind (bernoulli q) (seqBind (bins p (n - 1)) (flip (pure2 plus)))) 
           (bind (bernoulli q) (seqBind (bins q (n - 1)) (flip (pure2 plus))))
        ? bindDistEq distDouble
                     ((n - 1) * (q - p))
                     (seqBind (bins p (n - 1)) (flip (pure2 plus))) (bernoulli q)
                     (seqBind (bins q (n - 1)) (flip (pure2 plus))) (bernoulli q)
                     (addBinsDist p q (n - 1))
  =<= (n - 1) * (q - p)
  *** QED

{-@ binsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble 
             -> {dist (kant distDouble) (bins p n) (bins q n) <= n * (q - p)} @-}
binsDist :: Prob -> Prob -> Double -> ()
binsDist p q n | n < 1 = pureDist distDouble 0 0
binsDist p q n
  =   dist (kant distDouble) (bins p n) (bins q n)
      ? triangularIneq (kant distDouble) (bins p n) (bins' q p n) (bins q n)
      ? assume (dist (kant distDouble) (bins p n) (bins q n) 
                  <= dist (kant distDouble) (bins p n) (bins' p q n)
                      + dist (kant distDouble) (bins' p q n) (bins q n))
  =<= dist (kant distDouble) (bins p n) (bins' p q n)
        + dist (kant distDouble) (bins' p q n) (bins q n)  
      ? binsDistL p q n
  =<= q - p
        + dist (kant distDouble) (bins' p q n) (bins q n)  
      ? binsDistR p q n
  =<= q - p + (n - 1) * (q - p)
  === n * (q - p)
  *** QED

{-@ reflect bins' @-}
{-@ bins' :: Prob -> Prob -> n:Double -> Distr Double @-}
bins' :: Double -> Double -> Double -> Distr Double
bins' _ q n | n < 1.0 = ppure 0
bins' p q n = bind (bins p (n - 1)) (addBernoulli q (n - 1))

-- LV TODO: move to Monad.Distr I think?
{-@ reflect seqBind @-}
seqBind :: Distr b -> (a -> b -> Distr c) -> a -> Distr c
seqBind u f x = bind u (f x)

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

{-@ assume commutative :: e:Distr a -> u:Distr b -> f:(a -> b -> Distr c) 
                -> {bind e (seqBind u f)
                      = bind u (seqBind e (flip f))} @-}
commutative :: Distr a -> Distr b -> (a -> b -> Distr c) -> ()
commutative _ _ _ = ()
