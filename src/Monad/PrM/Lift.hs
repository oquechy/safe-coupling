{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM.Lift where

import Data.Dist
import Monad.PrM

import Prelude hiding ( fst
                      , snd
                      , pi
                      , map
                      , uncurry
                      , id
                      , all 
                      , Maybe(..)
                      )

{-@ reflect lift @-}
{-@ lift :: Eq a => (a -> a -> Bool) -> PrM a -> PrM a -> Bool @-}
lift :: Eq a => (a -> a -> Bool) -> PrM a -> PrM a -> Bool
lift p e1 e2 = snd (plift (Inf e1) p e1 e2)

{-@ measure Monad.PrM.Lift.kant :: Dist a -> Dist (PrM a) @-}
{-@ assume kant :: d:Dist a -> {dd:Dist (PrM a) | dd = Monad.PrM.Lift.kant d } @-}
kant :: Dist a -> Dist (PrM a)
kant = undefined 

{-@ reflect edist @-} 
edist :: Dist a -> PrM (a, a) -> Double
edist d mu = expect (uncurry (dist d)) mu

data KBound a = Inf (PrM a) | K (Dist a) Double

{-@ reflect coupling @-}
coupling :: Eq a => KBound a -> (a -> a -> Bool) -> PrM a -> PrM a -> PrM (a, a) -> Bool
coupling (Inf _) p e1 e2 mu 
    = pi fst mu == e1 && pi snd mu == e2 
    && all (uncurry p) (map fst mu) 
coupling (K d k) p e1 e2 mu 
    = pi fst mu == e1 && pi snd mu == e2 
    && all (uncurry p) (map fst mu) 
    && edist d mu <= k

{-@ reflect pi @-}
pi :: ((a, b) -> c) -> PrM (a, b) -> PrM c
pi f = map (bimap f id)

{-@ reflect elift @-}
{-@ elift :: Eq a => KBound a -> (a -> a -> Bool) -> PrM a -> PrM a 
          -> (PrM a -> PrM a -> PrM (a, a)) -> (PrM (a, a), Bool) @-}
elift :: Eq a => KBound a -> (a -> a -> Bool) -> PrM a -> PrM a
      -> (PrM a -> PrM a -> PrM (a, a)) -> (PrM (a, a), Bool)
elift dk p e1 e2 f = (mu, coupling dk p e1 e2 mu)
    where mu = f e1 e2

{-@ reflect plift @-}
{-@ plift :: Eq a => KBound a -> (a -> a -> Bool) -> PrM a -> PrM a -> (PrM (a, a), Bool) @-}
plift :: Eq a => KBound a -> (a -> a -> Bool) -> PrM a -> PrM a -> (PrM (a, a), Bool)
plift k p e1 e2 = elift k p e1 e2 bij2

{-@ reflect bij2 @-}
{- assume bij2 :: e1:PrM a -> e2:PrM b -> {mu:PrM (a, b)|(pi fst mu == e1) && (pi snd mu == e2)} @-}
bij2 :: PrM a -> PrM a -> PrM (a, a)
bij2 [] _          = []
bij2 _ []          = []
bij2 ((x, p):xs) ((y, q):ys) | p <= q = ((x, y), p):bij2 xs ((y, q - p):ys)
bij2 ((x, p):xs) ((y, q):ys) = ((x, y), q):bij2 xs ((y, p - q):ys)