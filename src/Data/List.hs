{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , zipWith
                                                , all
                                                )


data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

{-@ measure llen @-}
llen :: List a -> Int
llen Nil         = 0
llen (Cons _ xs) = 1 + llen xs

{-@ reflect at @-}
{-@ at :: xs:List a -> {i:Nat| i < llen xs} -> a @-}
at :: List a -> Int -> a
at (Cons x _ ) 0 = x
at (Cons _ xs) i = at xs (i - 1)

{-@ reflect range @-}
{-@ range :: i:Nat -> len:Nat -> List {j:Nat|j < i + len} / [len] @-}
range :: Int -> Int -> List Int
range _ 0   = Nil
range i len = Cons i (range (i + 1) (len - 1))

{-@ reflect map @-}
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
