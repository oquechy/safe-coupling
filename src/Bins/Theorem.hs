{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Bins.Theorem where

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude                 hiding ( map
                                                , max
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                , uncurry
                                                )
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
                      -> {lift leDoubleP (binsRec p n x1) (binsRec q n x2)} / [n, 1] @-}
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
               (bernoulli p) (binsRec p (n - 1))
               (bernoulli q) (binsRec q (n - 1))
               (bernoulliSpec p q)
               (relationalbinsrec p q (n - 1))

-}

{-



m <-> (n-1) (q - p)


Theorem :  edist (bins p n) (bins q n) <= n * (q - p)
IH :       edist (bins p (n-1)) (bins q (n-1)) <= (n-1) * (q - p)

We need 
           lift (\y1 y2 -> distD y1 y2 <=  (n-1) (q - p)) (bins p (n-1)) (bins q (n-1))

unlift :: (Distr a -> Distr a -> Bool) -> a -> a -> Bool 

axiom :: expDist e1 e2 <= m => unli


W so that 
  lift W (bins p (n-1)) (bins q (n-1)) <=> edist (bins p (n-1)) (bins q (n-1)) <= (n-1) * (q - p)
  unlift W x1 x2 = dist x1 x2 <= (n-1) * (q - p)






edist e1 e2 <= m => lift (\x1 x2 -> dist x1 x2 <= m) e1 e2


lift pred (bins p (n-1)) (bins q (n-1)) <- LEFT 





pred p q n y1 y2 = distD y1 y2 <= (n-1) (q - p)


P y1 y2 <=> distD y1 y2 <=  (n-1) (q - p)

y1:Double -> y2:{Double | distD y1 y2 <= m}

edist d 
 binsRec p (n - 1) y1 
 binsRec q (n - 1) y2 
<= 
(q - p) + m


edist d 
 bind (bins p (n-1)) (binsRec p (n - 1))
 bind (bins p (n-1)) (binsRec p (n - 1))
<= 

-}
{- 
{-@ binsDistRec :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n }  
                -> m:Double -> y1:Double -> y2:{Double | distD y1 y2 <= m}  
                -> {edist d (binsRec p n y1) (binsRec q n y2) <= (q - p) + m }  @-}
binsDistRec :: EDist Double -> Double -> Double -> Double -> Double -> Double -> Double -> ()
binsDistRec d p q n m y1 y2
    = assume (edist d (bernoulli p) (bernoulli q) <= q - p) ? 
      pureBindDist distDouble distDouble d d m 
                   (plus y1) (bernoulli p) 
                   (plus y2) (bernoulli q)
                   (lemma p q n m y1 y2) 

{-@ lemma :: p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
          -> m:Double -> y1:Double -> y2:{Double | distD y1 y2 <= m}
          -> x1:Double -> x2:Double -> { distD (plus y1 x1) (plus y2 x2) <= distD x1 x2 + m} @-}
lemma :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> () 
lemma = undefined 
-}
{- 

{-@ binsDist :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
             -> {edist d (bins p n) (bins q n) <=  n * (q - p) } / [n, 0] @-}
binsDist :: EDist Double -> Double -> Double -> Double -> ()
binsDist d p q n | n < 1 = pureDist d distDouble 0 0 
binsDist d p q n
  =    edist d (bins p n) (bins q n) 
  === edist d (bind (bernoulli p) (binsRec p (n - 1))) 
              (bind (bernoulli q) (binsRec p (n - 1))) 
  === edist d (bind (bernoulli p) (binsRec p (n - 1))) 
              (bind (bernoulli q) (binsRec p (n - 1))) 
  =<=  n * (q - p)  
  *** QED 



{-@ binsDist :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
             -> {edist d (bins p n) (bins q n) <=  n * (q - p) } / [n, 0] @-}
binsDist :: EDist Double -> Double -> Double -> Double -> ()
binsDist d p q n | n < 1 = pureDist d distDouble 0 0 ?  
binsDist d p q n 
  = triangularIneqAss d 
       (bins p n)
       (bins' p q n)
       (bins q n)
  ? binsDist1 d p q (n - 1)
  ? binsDist2 d p q n
  ? assert (edist d (bins p n) (bins q n) <= edist d (bins p n) (bins' p q n) + edist d (bins' p q n) (bins q n))
  ? assert (edist d (bins p n) (bins' p q n) <= (n - 1) * (q - p))
  ? assert (edist d (bins' p q n) (bins q n) <=  (q - p))
  ? assert (edist d (bins p n) (bins q n) <= (n-1) * (q-p) + (q-p) )
  ? assert (edist d (bins p n) (bins q n) <= n * (q - p))
  


{-@ binsDist1 :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
             -> {edist d (bins p n) (bins' p q n) <= n * (q - p) } / [n, 0] @-}
binsDist1 :: EDist Double -> Double -> Double -> Double -> ()
binsDist1 d p q n | n < 1 
  = pureDist d distDouble 0 0 
  ? assert (edist d (bins p n) (bins' p q n) <= distD 0 0 )
  ? assert (distD 0 0 == 0 )
  ? assert (0 <= n )
  ? assert (0 <= q - p)
  ? assert (0 <= n * (q - p))
binsDist1 d p q n
  = assert (bins p n    == bind (bernoulli p) (binsRec p (n-1))) 
  ? assert (bins' p q n == bind (bernoulli p) (binsRec q (n-1))) 
  ? bindDistEq d (n * (q - p)) 
         (binsRec p (n-1)) (bernoulli p) (binsRec q (n-1)) (bernoulli p)
         (binsDist1Helper d p q (n-1))

{-@ binsDist1Helper :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
             -> x:Double
             -> {edist d (binsRec p n x) (binsRec q n x) <= (n+1) * (q - p) } / [n, 0] @-}
binsDist1Helper :: EDist Double -> Double -> Double -> Double -> Double -> ()
binsDist1Helper d p q n x
  = bindDist d ((n+1) * (q - p)) ???
            (incCond x) (bins p n) (incCond x) (bins q n)
            (binsDist1Helper1 d p q n x y1 y2)
        

 {-@ binsDist1Helper1 :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double | 0 <= n } 
             -> x:Double -> y1:Double -> y2:Double 
             -> {edist d (incCond x y1) (incCond x y2) <= (n+1) * (q - p) } / [n, 0] @-}
binsDist1Helper1 :: EDist Double -> Double -> Double -> Double -> Double -> ()
binsDist1Helper1 d p q n x y1 y2
  = edist d (incCond x y1) (incCond x y2) 
  === distD (x + y1) (x + y2)
  === distD y1 y2


{-@ binsDist2 :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:{Double  | 1 < n }
             -> {edist d (bins' p q n) (bins q n) <=  (q - p) } / [n, 0] @-}
binsDist2 :: EDist Double -> Double -> Double -> Double -> ()
binsDist2 d p q n | n < 1 
  = pureDist d distDouble 0 0 
binsDist2 d p q n
  = liftTrue (bernoulli p) (bernoulli q) ? 
    assert (bins' p q n == bind (bernoulli p) (binsRec q (n - 1)))? 
    assert (bins    q n == bind (bernoulli q) (binsRec q (n - 1)))? 
    bindDist d (q - p) trueP 
         (binsRec q (n - 1)) (bernoulli p) (binsRec q (n - 1)) (bernoulli q)
         (binsDist2Lemma d p q n)

{-@ binsDist2Lemma :: d:EDist Double -> p:Prob -> {q:Prob|leDoubleP p q} -> n:Double 
                   -> x1:Double -> x2:Double 
                   -> {edist d (binsRec q (n - 1) x1) (binsRec q (n - 1) x2) <= 0 } / [n, 0] @-}
binsDist2Lemma :: EDist Double -> Double -> Double -> Double -> Double -> Double -> ()
binsDist2Lemma  d p q n x1 x2 = undefined 

{-@ assume triangularIneqAss :: d:EDist a -> x:Distr a -> y:Distr a -> z:Distr a 
                      -> {edist d x z <= edist d x y + edist d y z} @-}
triangularIneqAss :: EDist a -> Distr a -> Distr a -> Distr a -> () 
triangularIneqAss _ _ _ _ = () 

-}