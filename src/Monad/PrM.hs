{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM where

import Data.Dist
import Data.List

import           Prelude                 hiding ( id
                                                , fmap
                                                , map
                                                , mapM
                                                , concatMap
                                                , uncurry
                                                , (++)
                                                , foldr
                                                , sum
                                                , (>>=)
                                                , return
                                                , const
                                                , all
                                                , concat
                                                , reverse
                                                , fst
                                                , and
                                                )

{-@ type PrM a = [(a, Double)] @-}
type PrM a = [(a, Double)]

{-@ type Prob = {v:Double|0 <= v && v <= 1} @-}
type Prob = Double

{-@ reflect bind' @-}
bind' :: (a -> PrM b) -> a -> Double -> [(b, Double)]
bind' f x p = map (bimap id (mul p)) (f x)

{-@ reflect bind @-}
{-@ bind :: PrM a -> (a -> PrM b) -> PrM b @-}
bind :: PrM a -> (a -> PrM b) -> PrM b
bind a f = concatMap (uncurry (bind' f)) a

{-@ infixl >>= @-}
{-@ reflect >>= @-}
(>>=) :: PrM a -> (a -> PrM b) -> PrM b
(>>=) = bind

{-@ reflect ppure @-}
{-@ ppure :: a -> PrM a @-}
ppure :: a -> PrM a
ppure x = [(x, 1)]

{-@ reflect return @-}
return :: a -> PrM a
return = ppure

{-@ reflect fmap @-}
fmap :: (a -> b) -> PrM a -> PrM b
fmap f a = bind a (ppure . f)

{-@ reflect lift' @-}
lift' :: (a -> b -> c) -> PrM b -> a -> Double -> [(c, Double)]
lift' f b x p = map (bimap (f x) (mul p)) b

{-@ reflect liftA2 @-}
liftA2 :: (a -> b -> c) -> PrM a -> PrM b -> PrM c
liftA2 f a b = concat (map (uncurry (lift' f b)) a)

{-@ reflect ap @-}
ap :: PrM (a -> b) -> PrM a -> PrM b
ap = liftA2 id

{-@ infixl >> @-}
{-@ reflect >> @-}
(>>) :: PrM a -> PrM b -> PrM b
a >> b = a >>= (const b)

{-@ reflect choice @-}
choice :: Prob -> PrM a -> PrM a -> PrM a
choice p a b = map (bimap id (mul p)) a ++ map (bimap id (mul (1 - p))) b

{-@ reflect bernoulli @-}
{-@ bernoulli :: Prob -> PrM {v:Double| v = 0 || v = 1} @-}
bernoulli :: Prob -> PrM Double
bernoulli p = [(1, p), (0, 1 - p)]

{-@ reflect unif @-}
{-@ unif :: {xs:[a]|0 < len xs} -> PrM a @-}
unif :: [a] -> PrM a
unif [  a     ] = ppure a
unif l@(x : xs) = choice (1 `mydiv` lend l) (ppure x) (unif xs)

{-@ reflect expect @-}
expect :: (a -> Double) -> PrM a -> Double
expect f [] = 0
expect f ((x,p):xs) = f x * p + expect f xs

-----------------------------------------------------------------
-- | mapM: Standard monadic mapM instantiated for LH limitations  
-----------------------------------------------------------------

{-@ reflect mapM @-}
{-@ mapM :: (a -> PrM Double) -> xs:List a -> PrM ({ys:List Double| len ys = len xs }) @-}
mapM :: (a -> PrM Double) -> List a -> PrM (List Double)
mapM _ []       = ppure nilDouble
mapM f (x : xs) = bind (f x) (consM (len xs) (mapM f xs))

-----------------------------------------------------------------
-- | Helper Definitions for Reflection 
-----------------------------------------------------------------

{-@ reflect sum @-}
sum :: [Double] -> Double
sum [] = 0
sum (x:xs) = x + sum xs

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f i []       = i
foldr f i (x : xs) = f x (foldr f i xs)

{-@ reflect concatMap @-}
concatMap :: (a -> [b]) -> [a] -> [b]
concatMap _ []       = []
concatMap f (x : xs) = f x ++ concatMap f xs

{-@ reflect mul @-}
mul :: Double -> Double -> Double
mul = (*)

{-@ reflect plus @-}
plus :: Double -> Double -> Double
plus = (+)

{-@ reflect id @-}
id :: a -> a
id x = x

{-@ reflect map @-}
map :: (a -> b) -> [a] -> [b]
map _ []       = []
map f (x : xs) = f x : map f xs

{-@ reflect concat @-}
concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) = x ++ concat xs

{-@ reflect bimap @-}
bimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
bimap f g (x, y) = (f x, g y)

{-@ reflect mydiv @-}
{-@ mydiv :: Double -> {i:Double | i /= 0 } -> Double @-}
mydiv :: Double -> Double -> Double
mydiv x y = x / y

{-@ reflect const @-}
const :: a -> b -> a
const x _ = x

{-@ reflect consM @-}
{-@ consM :: n:Nat -> PrM ({xs:List Double | len xs == n}) -> Double -> PrM ({v:List Double | len v = n + 1}) @-}
consM :: Int -> PrM (List Double) -> Double -> PrM (List Double)
consM n xs x = bind xs (ppure `o` (consDouble x))

{-@ reflect cons @-}
{-@ cons :: a -> xs:[a] -> {ys:[a]|len ys = len xs + 1} @-}
cons :: a -> [a] -> [a]
cons = (:)

{-@ reflect consDouble @-}
{-@ consDouble :: Double -> xs:[Double] -> {ys:[Double]|len ys = len xs + 1} @-}
consDouble :: Double -> [Double] -> [Double]
consDouble = (:)

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

{-@ reflect uncurry @-}
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

{-@ infixr ++ @-}
{-@ reflect ++ @-}
(++) :: [a] -> [a] -> [a]
[]       ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse = reverse' []

{-@ reflect reverse' @-}
reverse' :: [a] -> [a] -> [a]
reverse' acc [] = acc
reverse' acc (x : xs) = reverse' (x : acc) xs

{-@ reflect pure2 @-}
pure2 :: (a -> b -> c) -> a -> b -> PrM c
pure2 f a b = ppure (f a b)

{-@ reflect and @-}
and :: Bool -> Bool -> Bool
and = (&&)

{-@ reflect all @-}
all :: (a -> Bool) -> [a] -> Bool
all _ [] = True
all f (x:xs) = f x && all f xs

{-@ reflect fst @-}
fst :: (a, b) -> a
fst (a, _) = a

{-@ reflect snd @-}
snd :: (a, b) -> b
snd (_, b) = b

{-@ reflect nilDouble @-}
nilDouble :: [Double]
nilDouble = []
