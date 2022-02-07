{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , max
                                                , zipWith
                                                , all
                                                , foldr
                                                )


data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil         = 0
llen (Cons _ xs) = 1 + llen xs

{-@ type Idx V = {i:Int | 0 <= i && i < llen V} @-}

{-@ reflect at @-}
{-@ at :: xs:List a -> Idx xs -> a @-}
at :: List a -> Int -> a
at (Cons x _) i | i == 0 = x
at (Cons _ xs) i         = at xs (i - 1)

{-@ reflect range @-}
{-@ range :: i:Nat -> len:Nat -> {v:List {j:Nat|j < i + len}|llen v = len} / [len] @-}
range :: Int -> Int -> List Int
range _ 0   = Nil
range i len = Cons i (range (i + 1) (len - 1))

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {ys:List b|llen ys = llen xs} @-}
map :: (a -> b) -> List a -> List b
map f Nil         = Nil
map f (Cons x xs) = Cons (f x) (map f xs)

zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith _ Nil         _             = Nil
zipWith _ _           Nil           = Nil
zipWith f (Cons x xs) (Cons x' xs') = Cons (f x x') (zipWith f xs xs')

all :: List Bool -> Bool
all Nil         = True
all (Cons x xs) = x && all xs

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
ap _ Nil = Nil
ap Nil _ = Nil
ap (Cons f fs) (Cons x xs) = Cons (f x) (ap fs xs)

{-@ reflect zip3With @-}
zip3With :: (a -> b -> c -> d) -> List a -> List b -> List c -> List d
zip3With _ Nil _ _ = Nil
zip3With _ _ Nil _ = Nil
zip3With _ _ _ Nil = Nil
zip3With f (Cons a as) (Cons b bs) (Cons c cs) = Cons (f a b c) (zip3With f as bs cs)

{-@ zip4 :: as:List a -> {bs:List b|llen bs = llen as} -> {cs:List c|llen cs = llen as} -> {ds:List d|llen ds = llen as} -> List (a, b, c, d) @-}
zip4 :: List a -> List b -> List c -> List d -> List (a, b, c, d)
zip4 Nil Nil Nil Nil = Nil
zip4 (Cons a as) (Cons b bs) (Cons c cs) (Cons d ds) = Cons (a, b, c, d) (zip4 as bs cs ds)

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z Nil = z                  
foldr f z (Cons x xs) = f x (foldr f z xs)
