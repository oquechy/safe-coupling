-----------------------------------------------------------------
-- | Implementation of the PrM monad as a wrapper  ------------
-- | This module includes only executable code       ------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
module Monad.PrM where 

import Data.Dist 
import Data.List hiding (all) 

import Prelude hiding (max, mapM)
import Numeric.Probability.Distribution hiding (Cons, cons)

{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

type PrM a = T Prob a

{-@ measure Monad.PrM.bind :: PrM a -> (a -> PrM b) -> PrM b @-}
{-@ assume bind :: x1:PrM a -> x2:(a -> PrM b) -> {v:PrM b | v = bind x1 x2 } @-}
bind :: PrM a -> (a -> PrM b) -> PrM b
bind = (>>=)

{-@ measure Monad.PrM.ppure :: a -> PrM a @-}
{-@ ppure :: x:a -> {v:PrM a | v = Monad.PrM.ppure x } @-}
ppure :: a -> PrM a
ppure = pure 

{-@ measure Monad.PrM.liftA2 :: (a -> b -> c) -> PrM a -> PrM b -> PrM c @-}
{-@ liftA2 :: f:(a -> b -> c) -> x:PrM a -> y:PrM b -> {v:PrM c | v = Monad.PrM.liftA2 f x y} @-}
liftA2 :: (a -> b -> c) -> PrM a -> PrM b -> PrM c
liftA2 f a b = do x <- a
                  y <- b
                  ppure (f x y)

{-@ reflect fmap @-}
fmap :: (a -> b) -> PrM a -> PrM b
fmap f a = bind a (ppure . f)

{-@ measure Monad.PrM.choice :: Prob -> PrM a -> PrM a -> PrM a @-}
{-@ assume choice :: x1:Prob -> x2:PrM a -> x3:PrM a -> {v:PrM a | v == choice x1 x2 x3 } @-}
choice :: Prob -> PrM a -> PrM a -> PrM a
choice p x y = cond (fromFreqs [(True, p), (False, 1 - p)]) x y

{-@ measure Monad.PrM.bernoulli :: Prob -> PrM Double @-}
{-@ assume bernoulli :: p:Prob -> {v:PrM {n:Double | 0 <= n && n <= 1}| v == bernoulli p } @-}
bernoulli :: Prob -> PrM Double
bernoulli p = fromFreqs [(1, p), (0, 1 - p)]

{-@ reflect unif @-}
{-@ unif :: {xs:[a]|0 < len xs} -> PrM a @-}
unif :: [a] -> PrM a
unif [a]    = ppure a
unif l@(x:xs) = choice (1 `mydiv` lend l) (ppure x) (unif xs)

{-@ measure Monad.PrM.lift :: (a -> b -> Bool) -> PrM a -> PrM b -> Bool @-}
{-@ assume lift :: p1:(a -> b -> Bool) -> x1:PrM a -> x2:PrM b 
                -> {v:Bool | v == Monad.PrM.lift p1 x1 x2 } @-}
lift :: (a -> b -> Bool) -> PrM a -> PrM b -> Bool
lift p e1 e2 = and (fst <$> (decons act))
  where act = do x <- e1 
                 y <- e2
                 return (p x y)

-----------------------------------------------------------------
-- | mapM: Standard monadic mapM instantiated for LH limitations  
-----------------------------------------------------------------

{-@ reflect mapM @-}
{-@ mapM :: (a -> PrM Double) -> xs:List a -> PrM ({ys:List Double| llen ys = llen xs }) @-}
mapM :: (a -> PrM Double) -> List a -> PrM (List Double)
mapM _ Nil         = ppureDouble Nil
mapM f (Cons x xs) = bind (f x) (cons (llen xs) (mapM f xs))

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
{-@ ppureDouble :: xs:List Double -> PrM ({v:List Double | llen v == llen xs}) @-}
ppureDouble :: List Double -> PrM (List Double)
ppureDouble x = ppure x 

{-@ reflect cons @-}
{-@ cons :: n:Nat -> PrM ({xs:List Double | llen xs == n}) -> Double -> PrM ({v:List Double | llen v = n + 1}) @-}
cons :: Int -> PrM (List Double) -> Double -> PrM (List Double)
cons n xs x = bind xs (ppure `o` (consDouble x))

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect seqBind @-}
seqBind :: PrM b -> (a -> b -> PrM c) -> a -> PrM c
seqBind u f x = bind u (f x)

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

{-@ reflect lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v } @-}
lend :: [a] -> Double
lend xs = fromIntegral (len xs)
