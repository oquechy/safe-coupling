module Data.List where

data List a = Nil | Cons a (List a)

{-@ measure llen @-}
llen :: List a -> Int
llen Nil = 0
llen (Cons _ xs) = 1 + llen xs

{-@ at :: xs:List a -> {i:Nat|i < llen xs} -> a @-}
at :: List a -> Int -> a
at (Cons x _) 0 = x
at (Cons _ xs) i = at xs (i - 1)
