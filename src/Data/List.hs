{-@ LIQUID "--reflection"     @-}

module Data.List where

import Prelude hiding (map)

data List a = Nil | Cons a (List a)

{-@ measure llen @-}
llen :: List a -> Int
llen Nil = 0
llen (Cons _ xs) = 1 + llen xs

{-@ reflect at @-}
{-@ at :: xs:List a -> {i:Nat| i < llen xs} -> a @-}
at :: List a -> Int -> a
at (Cons x _ ) 0 = x
at (Cons _ xs) i = at xs (i - 1)

{-@ reflect range @-}
{-@ range :: i:Nat -> List {j:Nat|j <= i} / [i + 1] @-}
range :: Int -> List Int
range 0 = Cons 0 Nil
range i = Cons i (range (i - 1))

{-@ reflect map @-}
map :: (a -> b) -> List a -> List b
map f Nil = Nil
map f (Cons x xs) = Cons (f x) (map f xs)