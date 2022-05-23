{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM.Relational.Rules where 

import Data.Dist
import Monad.PrM
import Monad.PrM.Lift
import Monad.PrM.Predicates

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

import Prelude hiding (pi, fst, snd, map, uncurry, all, const)

{-@ reflect boundBy @-}
boundBy :: KBound a -> a -> a -> Bool
boundBy Inf _ _ = True
boundBy (K d k) x1 x2 = dist d x1 x2 <= k

{-@ pureT :: Eq a => k:KBound a -> p:(a -> a -> Bool) -> x1:a -> x2:a 
          -> {px:()|p x1 x2}
          -> {bx:()|boundBy k x1 x2} 
          -> {klift k p (ppure x1) (ppure x2)} @-}
pureT :: Eq a => KBound a -> (a -> a -> Bool) -> a -> a -> () -> () -> () 
pureT Inf _ _ _ _ _ = ()
pureT _ _ _ _ _ _ = ()

{-@ assume piBij :: Eq a => e:PrM a -> {pi fst (bij2 e e) = e && pi snd (bij2 e e) == e} @-}
piBij :: Eq a => PrM a -> ()
piBij e = assume (pi fst (bij2 e e) == e && pi snd (bij2 e e) == e)

{-@ assume edistBij :: d:Dist a -> e:PrM a -> {edist d (bij2 e e) = 0} @-}
edistBij :: Dist a -> PrM a -> ()
edistBij d e = ()

{-@ unifT :: Eq a => k:KBound a -> {xs:[a]|0 < len xs} -> {klift k eqP (unif xs) (unif xs)} @-}
unifT :: Eq a => KBound a -> [a] -> ()
unifT Inf xs@[_] = ()
unifT Inf xs@(_:xs'@(_:_))
    = piBij e
    ? assume (pi fst (bij2 e e) == e && pi snd (bij2 e e) == e)
    ? assume (all (uncurry eqP) (map fst mu))
    where
        e = unif xs
        mu = bij2 e e
unifT (K d k) xs@[x]
    =   distEq d x
unifT b@(K d k) xs@(_:xs'@(_:_)) 
    = assume (pi fst (bij2 e e) == e) 
    ? assume (pi snd (bij2 e e) == e) 
    ? assume (all (uncurry eqP) (map fst mu))
    ? edistBij d e
    where
        e = unif xs
        mu = bij2 e e

{-@ assume bernT :: k:KBound Double -> x1:Prob -> x2:Prob -> {_:()|x1 <= x2} -> {klift k (between 0 1) (bernoulli x1) (bernoulli x2)} @-}
bernT :: KBound Double -> Prob -> Prob -> () -> ()
bernT _ _ _ _ = ()

{-@ assume choiceT :: Eq a => m:KBound a -> p:(a -> a -> Bool)
                   -> q:Prob
                   -> k:KBound a
                   -> x1:PrM a -> x2:PrM a 
                   -> {_:()|klift k p x1 x2} 
                   -> l:KBound a
                   -> y1:PrM a -> y2:PrM a
                   -> {_:()|klift l p y1 y2}
                   -> {klift m p (choice q x1 y1) (choice q x2 y2)} @-}
choiceT :: Eq a => KBound a -> (a -> a -> Bool) -> Prob 
        -> KBound a -> PrM a -> PrM a -> ()
        -> KBound a -> PrM a -> PrM a -> ()
        -> ()
choiceT _ _ _ _ _ _ _ _ _ _ _ = ()

{-@ assume bindT :: (Eq a, Eq b) => m:KBound b -> p:(b -> b -> Bool)
                 -> k:KBound a -> q:(a -> a -> Bool)
                 -> e1:PrM a -> e2:PrM a 
                 -> {_:()|klift k q e1 e2}
                 -> l:KBound b
                 -> f1:(a -> PrM b) -> f2:(a -> PrM b)
                 -> (x1:a -> x2:a -> {_:()|q x1 x2} -> {klift l p (f1 x1) (f2 x2)})
                 -> {klift m p (bind e1 f1) (bind e2 f2)} @-}
bindT :: (Eq a, Eq b) => KBound b -> (b -> b -> Bool)
      -> KBound a -> (a -> a -> Bool)
      -> PrM a -> PrM a 
      -> ()
      -> KBound b
      -> (a -> PrM b) -> (a -> PrM b)
      -> (a -> a -> () -> ())
      -> ()
bindT _ _ _ _ _ _ _ _ _ _ _ = ()

{-@ assume fmapT :: (Eq a, Eq b) => m:KBound b -> p:(b -> b -> Bool) 
                 -> k:KBound a -> q:(a -> a -> Bool) 
                 -> e1:PrM a -> e2:PrM a 
                 -> {_:()|klift k q e1 e2} 
                 -> l:KBound b 
                 -> f1:(a -> b) -> f2:(a -> b)
                 -> (x1:a -> x2:a -> {_:()|q x1 x2} -> {p (f1 x1) (f2 x2) && boundBy l (f1 x1) (f2 x2)})
                 -> {klift m p (fmap f1 e1) (fmap f2 e2)} @-}
fmapT :: (Eq a, Eq b) => KBound b -> (b -> b -> Bool) -> KBound a -> (a -> a -> Bool)
      -> PrM a -> PrM a -> () -> KBound b -> (a -> b) -> (a -> b)
      -> (a -> a -> () -> ())
      -> ()
fmapT m p k q e1 e2 ehyp l f1 f2 fhyp | klift k q e1 e2
    = bindT m p k q e1 e2 ehyp l (ppure `o` f1) (ppure `o` f2) (fmapLemma l p q f1 f2 fhyp)
fmapT m p k q e1 e2 ehyp l f1 f2 fhyp = ()

{-@ fmapLemma :: Eq b => l:KBound b 
              -> p:(b -> b -> Bool)
              -> q:(a -> a -> Bool)
              -> f1:(a -> b) -> f2:(a -> b)
              -> (x1:a -> x2:a -> {_:()|q x1 x2} -> {p (f1 x1) (f2 x2) && boundBy l (f1 x1) (f2 x2)})
              -> x1:a -> x2:a -> {_:()|q x1 x2} -> {klift l p (o ppure f1 x1) (o ppure f2 x2)} @-}
fmapLemma :: Eq b => KBound b -> (b -> b -> Bool) -> (a -> a -> Bool) 
          -> (a -> b) -> (a -> b) -> (a -> a -> () -> ()) 
          -> a -> a -> () -> ()
fmapLemma l p q f1 f2 fhyp x1 x2 xhyp
    =   klift l p ((ppure . f1) x1) ((ppure . f2) x2)
    === klift l p (ppure (f1 x1)) (ppure (f2 x2))
        ? pureT l p (f1 x1) (f2 x2) (fhyp x1 x2 xhyp) (fhyp x1 x2 xhyp)
    === True
    *** QED