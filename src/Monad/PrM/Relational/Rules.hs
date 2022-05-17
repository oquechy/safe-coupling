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

{-@ pureT :: k:KBound a -> p:(a -> a -> Bool) -> x1:a -> x2:a 
          -> {px:()|p x1 x2}
          -> {bx:()|boundBy k x1 x2} 
          -> {klift k p (ppure x1) (ppure x2)} @-}
pureT :: KBound a -> (a -> a -> Bool) -> a -> a -> () -> () -> () 
pureT Inf _ _ _ _ _ = ()
pureT _ _ _ _ _ _ = ()

{-@ assume piBij :: Eq a => e:PrM a -> {pi fst (bij2 e e) = e && pi snd (bij2 e e) == e} @-}
piBij :: Eq a => PrM a -> ()
piBij e = assume (pi fst (bij2 e e) == e && pi snd (bij2 e e) == e)

{-@ assume edistBij :: d:Dist a -> e:PrM a -> {edist d (bij2 e e) = 0} @-}
edistBij :: Dist a -> PrM a -> ()
edistBij d e = ()

{-assume  @-}

{-@ unifT :: Eq a => k:KBound a -> {xs:[a]|0 < len xs} -> {klift k eqP (unif xs) (unif xs)} @-}
unifT :: Eq a => KBound a -> [a] -> ()
unifT Inf xs@[_] = ()
unifT Inf xs@(_:xs'@(_:_))
    = piBij e
    ? assert (pi fst (bij2 e e) == e && pi snd (bij2 e e) == e)
    ? assume (all (uncurry eqP) (map fst mu))
    where
        e = unif xs
        mu = bij2 e e
unifT (K d k) xs@[x]
    =   distEq d x
unifT b@(K d k) xs@(_:xs'@(_:_)) 
    = (pi fst (bij2 e e) 
        ? piBij e
        === e
        *** QED) 
    ? (pi snd (bij2 e e) 
        ? piBij e
        === e
        *** QED)
    ? assume (all (uncurry eqP) (map fst mu))
    ? edistBij d e
    where
        e = unif xs
        mu = bij2 e e