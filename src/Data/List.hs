{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , max
                                                , zipWith
                                                , all
                                                , foldr
                                                , elem
                                                )


{-@ type SameLen L = {v:_|len v = len L} @-}
{-@ type ListN N = {v:_|len v = N} @-}

type List a = [a]

{-@ reflect consDouble @-}
{-@ consDouble :: Double -> xs:List Double -> {v:List Double | len v == len xs + 1  } @-}
consDouble :: Double -> List Double -> List Double 
consDouble x xs = x:xs

{-@ reflect cons' @-}
{-@ cons' :: a -> xs:List a -> {v:List a | len v == len xs + 1 && 1 <= len v} @-}
cons' :: a -> List a -> List a 
cons' x xs = x:xs

{-@ reflect nilDouble @-}
{-@ nilDouble :: {v:List Double|len v = 0} @-}
nilDouble :: List Double 
nilDouble = []

{-@ measure len @-}
{-@ len :: List a -> Nat @-}
len :: List a -> Int
len []         = 0
len (_:xs) = 1 + len xs

{-@ type Idx V = {i:Int | 0 <= i && i < len V} @-}

{-@ reflect at @-}
{-@ at :: xs:List a -> Idx xs -> a @-}
at :: List a -> Int -> a
at (x:_) i | i == 0 = x
at (_:xs) i         = at xs (i - 1)

{-@ reflect range @-}
{-@ range :: i:Nat -> l:Nat -> {v:List {j:Nat|j < i + l}|len v = l} / [l] @-}
range :: Int -> Int -> List Int
range _ 0   = []
range i len = i : (range (i + 1) (len - 1))

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {ys:List b|len ys = len xs} @-}
map :: (a -> b) -> List a -> List b
map f []         = []
map f (x:xs) = (f x) : (map f xs)

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith _ []         _             = []
zipWith _ _           []           = []
zipWith f (x:xs) (x':xs') = (f x x') : (zipWith f xs xs')

all :: List Bool -> Bool
all []         = True
all (x:xs) = x && all xs

{-@ reflect max @-}
max :: Double -> Double -> Double
max a b = if a < b then b else a

{-@ reflect pow @-}
{-@ pow :: {v:Double|v >= 0} -> i:Nat -> {v:Double|v >= 0} / [i] @-}
pow :: Double -> Int -> Double
pow x 0 = 1
pow x i = x * pow x (i - 1)

{-@ reflect ap @-}
ap :: List (a -> b) -> List a -> List b
ap _ [] = []
ap [] _ = []
ap (f:fs) (x:xs) = (f x) : (ap fs xs)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z [] = z                  
foldr f z (x:xs) = f x (foldr f z xs)

{-@ reflect lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v} @-}
lend :: [a] -> Double
lend xs = fromIntegral (len xs)

{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1} @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
elem x []                  = False
elem x (x' : xs) | x == x' = True
elem x (_ : xs)            = elem x xs

{-@ reflect isPermutation @-}
{-@ isPermutation :: Eq a => xs:[a] -> ys:[a] -> {v:Bool|v => (len xs = len ys)} @-}
isPermutation :: Eq a => [a] -> [a] -> Bool
isPermutation [] []                     = True
isPermutation _ []                      = False
isPermutation [] _                      = False
isPermutation (x : xs) xs' | elem x xs' = isPermutation xs (xs' \\ x)
isPermutation _ _                       = False

{-@ infix \\ @-}
{-@ reflect \\ @-}
{-@ (\\) :: Eq a => xs:[a] -> x:a -> {v:[a]|elem x xs => len v = len xs - 1} @-}
(\\) :: Eq a => [a] -> a -> [a]
[] \\ x | elem x []             = []
[] \\ x                         = []
(x : xs) \\ x' | x == x'        = xs
xs@(x : xs') \\ x' | elem x' xs = x : (xs' \\ x')
(x : xs') \\ x'                 = x : (xs' \\ x')

