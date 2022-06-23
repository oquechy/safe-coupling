-----------------------------------------------------------------
-- | Implementation of the Distr monad as a wrapper  ------------
-- | This module includes only executable code       ------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
module Monad.Distr where 

import Data.Dist 
import Data.List hiding (all) 

import Prelude hiding (max, mapM)
import Numeric.Probability.Distribution hiding (Cons, cons)

{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

type Distr a = T Prob a

{-@ measure Monad.Distr.bind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume bind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = bind x1 x2 } @-}
bind :: Distr a -> (a -> Distr b) -> Distr b
bind = (>>=)

{-@ measure Monad.Distr.ppure :: a -> Distr a @-}
{-@ ppure :: x:a -> {v:Distr a | v = Monad.Distr.ppure x } @-}
ppure :: a -> Distr a
ppure = pure 

{-@ ignore choice @-}
{-@ measure Monad.Distr.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice p x y = cond (fromFreqs [(True, p), (False, 1 - p)]) x y

{-@ measure Monad.Distr.bernoulli :: Prob -> Distr Double @-}
{-@ assume bernoulli :: p:Prob -> {v:Distr {n:Double | 0 <= n && n <= 1}| v == bernoulli p } @-}
bernoulli :: Prob -> Distr Double
bernoulli p = fromFreqs [(1, p), (0, 1 - p)]


{-@ reflect unif @-}
{-@ unif :: {xs:[a]|0 < len xs} -> Distr a @-}
unif :: [a] -> Distr a
unif [a]    = ppure a
unif (x:xs) = choice (1 `mydiv` fromIntegral (len xs + 1)) (ppure x) (unif xs)

{-@ measure Monad.Distr.lift :: (a -> b -> Bool) -> Distr a -> Distr b -> Bool @-}
{-@ assume lift :: p1:(a -> b -> Bool) -> x1:Distr a -> x2:Distr b 
                -> {v:Bool | v == Monad.Distr.lift p1 x1 x2 } @-}
lift :: (a -> b -> Bool) -> Distr a -> Distr b -> Bool
lift p e1 e2 = and (fst <$> (decons act))
  where act = do x <- e1 
                 y <- e2
                 return (p x y)

-----------------------------------------------------------------
-- | mapM: Standard monadic mapM instantiated for LH limitations  
-----------------------------------------------------------------

{-@ reflect mapM @-}
{-@ mapM :: (a -> Distr Double) -> xs:List a -> Distr ({ys:List Double| llen ys = llen xs }) @-}
mapM :: (a -> Distr Double) -> List a -> Distr (List Double)
mapM _ []         = ppureDouble []
mapM f (x:xs) = bind (f x) (cons (llen xs) (mapM f xs))

-----------------------------------------------------------------
-- | Helper Definitions for Reflection 
-----------------------------------------------------------------

{-@ reflect len @-}
len :: [a] -> Int
len [] = 0
len (_:xs) = 1 + len xs

{-@ reflect mydiv @-}
{-@ mydiv :: Double -> {i:Double | i /= 0 } -> Double @-}
mydiv :: Double -> Double -> Double
mydiv x y = x / y 

{-@ reflect ppureDouble @-}
{-@ ppureDouble :: xs:List Double -> Distr ({v:List Double | llen v == llen xs}) @-}
ppureDouble :: List Double -> Distr (List Double)
ppureDouble x = ppure x 

{-@ reflect cons @-}
{-@ cons :: n:Nat -> Distr ({xs:List Double | llen xs == n}) -> Double -> Distr ({v:List Double | llen v = n + 1}) @-}
cons :: Int -> Distr (List Double) -> Double -> Distr (List Double)
cons n xs x = bind xs (ppure `o` (consDouble x))

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect seqBind @-}
seqBind :: Distr b -> (a -> b -> Distr c) -> a -> Distr c
seqBind u f x = bind u (f x)

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

{-@ reflect pure2 @-}
pure2 :: (a -> b -> c) -> a -> b -> Distr c
pure2 f a b = ppure (f a b)