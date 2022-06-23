{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , max
                                                , zipWith
                                                , all
                                                , foldr
                                                )


{-@ type SameLen L = {v:_|llen v = llen L} @-}
{-@ type ListN N = {v:_|llen v = N} @-}

type List a = [a]

{-@ reflect consDouble @-}
{-@ consDouble :: Double -> xs:List Double -> {v:List Double | llen v == llen xs + 1  } @-}
consDouble :: Double -> List Double -> List Double 
consDouble x xs = x:xs

{-@ reflect nilDouble @-}
{-@ nilDouble :: {v:List Double|llen v = 0} @-}
nilDouble :: List Double 
nilDouble = []

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen []         = 0
llen (_:xs) = 1 + llen xs

{-@ type Idx V = {i:Int | 0 <= i && i < llen V} @-}

{-@ reflect at @-}
{-@ at :: xs:List a -> Idx xs -> a @-}
at :: List a -> Int -> a
at (x:_) i | i == 0 = x
at (_:xs) i         = at xs (i - 1)

{-@ reflect range @-}
{-@ range :: i:Nat -> len:Nat -> {v:List {j:Nat|j < i + len}|llen v = len} / [len] @-}
range :: Int -> Int -> List Int
range _ 0   = []
range i len = i : (range (i + 1) (len - 1))

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {ys:List b|llen ys = llen xs} @-}
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

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v } @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs
