{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.Theorem where

import           Monad.PrM
import           Monad.PrM.Laws
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( flip )

import           Monad.PrM.Predicates
import           Monad.PrM.Relational.TCB.Spec 
import           Monad.PrM.Relational.TCB.EDist
import           Monad.PrM.Relational.Theorems
import           Bins.Bins

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ relationalinccond :: x1:Double -> {x2:Double|x1 <= x2} -> y1:Double -> {y2:Double|leDoubleP y1 y2} 
                      -> {lift leDoubleP ((ppure . (plus x1)) (y1)) ((ppure . (plus x2)) (y2))} @-}
relationalinccond :: Double -> Double -> Double -> Double -> ()
relationalinccond x1 x2 y1 y2 = pureSpec leDoubleP
                                         (plus y1 x1)
                                         (plus y2 x2)
                                         ()
                                
{-@ relationalbinsrec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double -> x1:Double -> {x2:Double| x1 <= x2}
                      -> {lift leDoubleP (addBernoulli p n x1) (addBernoulli q n x2)} / [n, 1] @-}
relationalbinsrec :: Double -> Double -> Double -> Double -> Double -> ()
relationalbinsrec p q n x1 x2
    = bindSpec leDoubleP leDoubleP
        (bernoulli p) (ppure . plus x1)
        (bernoulli q) (ppure . plus x2)
        (bernoulliSpec p q)
        (relationalinccond x1 x2)
 
{-@ binsSpec :: p:Prob -> {q:Prob|leDoubleP p q} -> n:Double 
             -> {lift leDoubleP (bins p n) (bins q n)} / [n, 0] @-}
binsSpec :: Double -> Double -> Double -> ()
binsSpec p q n | n < 1  
    = pureSpec leDoubleP 0 0 ()
binsSpec p q n 
    = bindSpec leDoubleP leDoubleP
               (bins p (n - 1)) (addBernoulli p (n - 1))
               (bins q (n - 1)) (addBernoulli q (n - 1))
               (binsSpec p q (n - 1))
               (relationalbinsrec p q (n - 1))

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
                          <= n * (q - p)} / [n, 2] @-}
addBinsDist ::  Prob -> Prob -> Double -> Double -> ()
addBinsDist p q n x 
  =   dist (kant distDouble) 
           (seqBind (bins p n) (flip (pure2 plus)) x)
           (seqBind (bins q n) (flip (pure2 plus)) x)
  === dist (kant distDouble) 
           (bind (bins p n) (flip (pure2 plus) x))
           (bind (bins q n) (flip (pure2 plus) x))
      ? flipPlus x 
  === dist (kant distDouble) 
           (bind (bins p n) (ppure . (plus x)))
           (bind (bins q n) (ppure . (plus x)))
        ? pureBindDist distDouble distDouble
                       0
                       (plus x) (bins p n)
                       (plus x) (bins q n)
                       (plusDist x)
  =<= dist (kant distDouble) (bins p n) (bins q n)
       ? binsDist p q n 
  =<=  n * (q - p) 
  *** QED

{-@ reflect pure2 @-}
pure2 :: (a -> b -> c) -> a -> b -> PrM c
pure2 f a b = ppure (f a b)

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
              -> {dist (kant distDouble) (bins' p q n) (bins q n) <= (n - 1) * (q - p)} 
              / [n, 0] @-}
binsDistR ::Prob -> Prob -> Double -> ()
binsDistR p q n 
  =   dist (kant d) (bins' p q n) (bins q n)
      ? addBernoulliEq n p q 
      ? assert (bins' p q n == bind (bins p (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
      ? assert (bins q n == bind (bins q (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
  === dist (kant d) 
           (bind (bins p (n - 1)) (seqBind (bernoulli q) (pure2 plus))) 
           (bind (bins q (n - 1)) (seqBind (bernoulli q) (pure2 plus)))
      ? commutative (bins p (n - 1)) (bernoulli q) (pure2 plus)
      ? commutative (bins q (n - 1)) (bernoulli q) (pure2 plus)
  === dist (kant d) 
           (bind (bernoulli q) (seqBind (bins p (n - 1)) (flip (pure2 plus)))) 
           (bind (bernoulli q) (seqBind (bins q (n - 1)) (flip (pure2 plus))))
        ? bindDistEq d
                     ((n - 1) * (q - p))
                     (seqBind (bins p (n - 1)) (flip (pure2 plus))) (bernoulli q)
                     (seqBind (bins q (n - 1)) (flip (pure2 plus))) (bernoulli q)
                     (addBinsDist p q (n - 1))
  =<= (n - 1) * (q - p)
  *** QED
    where d = distDouble 

{-@ binsDist :: p:Prob -> {q:Prob|p <= q} -> n:PDouble 
             -> {dist (kant distDouble) (bins p n) (bins q n) <= n * (q - p)} 
             / [n, 1] @-}
binsDist :: Prob -> Prob -> Double -> ()
binsDist p q n | n < 1.0 
  = pureDist distDouble 0 0 
  ? assert (0 <= n) 
  ? assert (0 <= (q - p)) 
  ? assert (dist (kant distDouble) (bins p n) (bins q n) <= n * (q - p)) 
binsDist p q n
  =   dist (kant d) (bins p n) (bins q n)
      ? triangularIneq (kant d) (bins p n) (bins' p q n) (bins q n)
      ? assert (dist (kant d) (bins p n) (bins q n) 
                   <= dist (kant d) (bins p n) (bins' p q n)
                    + dist (kant d) (bins' p q n) (bins q n))
  =<= dist (kant d) (bins p n) (bins' p q n)
        + dist (kant d) (bins' p q n) (bins q n)  
      ? binsDistL p q n
  =<= q - p
        + dist (kant d) (bins' p q n) (bins q n)  
      ? binsDistR p q n
  =<= q - p + (n - 1) * (q - p)
  =<= n * (q - p)
  *** QED
  where d = distDouble

{-@ reflect bins' @-}
{-@ bins' :: Prob -> Prob -> n:Double -> PrM Double @-}
bins' :: Double -> Double -> Double -> PrM Double
bins' _ q n | n < 1.0 = ppure 0
bins' p q n = bind (bins p (n - 1)) (addBernoulli q (n - 1))

{-@ flipPlus :: x:Double -> {(flip (pure2 plus) x) == (ppure . (plus x))} @-}
flipPlus :: Double -> () 
flipPlus x = extDouble (flip (pure2 plus) x) (ppure . (plus x)) (flipPlus' x)

{-@ flipPlus' :: x:Double -> y:Double -> {(flip (pure2 plus) x y) == (ppure . (plus x)) (y)} @-}
flipPlus' :: Double -> Double -> () 
flipPlus' _ _ = ()

{-@ assume extDouble :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:() | f x == g x}) -> {f == g } @-} 
extDouble :: (a -> b) -> (a -> b) -> (a -> ()) -> () 
extDouble _ _ _ = () 
