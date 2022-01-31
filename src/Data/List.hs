{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , zipWith
                                                , all
                                                )


data List a = Nil | Cons a (List a)
    deriving (Eq, Show)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil         = 0
llen (Cons _ xs) = 1 + llen xs

{-@ measure Data.List.at :: List a -> Int -> a @-}
{-@ assume at :: xs:List a -> i:Int -> {v:a|v = Data.List.at xs i} @-}
at :: List a -> Int -> a
at Nil _                 = undefined
at (Cons x _) i | i <= 0 = x
at (Cons _ xs) i         = at xs (i - 1)


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
