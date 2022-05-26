{-@ LIQUID "--reflection"     @-}

module Data.List where

import           Prelude                 hiding ( map
                                                , max
                                                , zipWith
                                                , all
                                                , foldr
                                                , elem
                                                )

{-@ type SameLen L = {v:List Double|len v = len L} @-}
{-@ type ListN N = {v:List Double|len v = N} @-}

type List a = [a]

-- {-@ reflect consDouble @-}
-- {-@ consDouble :: Double -> xs:List Double -> {v:List Double | len v == len xs + 1  } @-}
-- consDouble :: Double -> List Double -> List Double 
-- consDouble = (:)

{-@ reflect cons @-}
{-@ cons :: a -> xs:[a] -> {v:[a]|len v = len xs + 1} @-}
cons :: a -> [a] -> [a]
cons = (:)

{-@ measure len @-}
{-@ len :: List a -> Nat @-}
len :: List a -> Int
len []     = 0
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
range i len = i : range (i + 1) (len - 1)

-- {-@ reflect map @-}
-- {-@ map :: (a -> b) -> xs:List a -> {ys:List b|len ys = len xs} @-}
-- map :: (a -> b) -> List a -> List b
-- map f Nil         = Nil
-- map f (Cons x xs) = Cons (f x) (map f xs)

{-@ reflect max @-}
max :: Double -> Double -> Double
max a b = if a < b then b else a

-- zipWith :: (a -> b -> c) -> List a -> List b -> List c
-- zipWith _ Nil         _             = Nil
-- zipWith _ _           Nil           = Nil
-- zipWith f (Cons x xs) (Cons x' xs') = Cons (f x x') (zipWith f xs xs')



-- all :: List Bool -> Bool
-- all Nil         = True
-- all (Cons x xs) = x && all xs

{-@ reflect pow @-}
{-@ pow :: {v:Double|v >= 0} -> i:Nat -> {v:Double|v >= 0} / [i] @-}
pow :: Double -> Int -> Double
pow x 0 = 1
pow x i = x * pow x (i - 1)

-- {-@ reflect ap @-}
-- ap :: List (a -> b) -> List a -> List b
-- ap _ Nil = Nil
-- ap Nil _ = Nil
-- ap (Cons f fs) (Cons x xs) = Cons (f x) (ap fs xs)

{-@ reflect sort @-}
{-@ sort :: Ord a => xs:[a] -> {v:[a]|len xs = len v} @-}
sort :: Ord a => [a] -> [a]
sort [] = []
sort (x:xs) = insert x (sort xs)

{-@ reflect insert @-}
{-@ insert :: Ord a => a -> xs:[a] -> {v:[a]|len v = len xs + 1} @-}
insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:xs) | x <= y = x:y:xs
insert x (y:xs) = y : insert x xs

{-@ reflect elem @-}
elem :: Eq a => a -> [a] -> Bool
elem x []                  = False
elem x (x' : xs) | x == x' = True
elem x (_ : xs)            = elem x xs

{-@ reflect isPermutation @-}
{-@ isPermutation :: Eq a => xs:[a] -> {ys:[a]|len xs = len ys} -> Bool @-}
isPermutation :: Eq a => [a] -> [a] -> Bool
isPermutation [] []                     = True
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

{-@ reflect diff1 @-}
{-@ diff1 :: Eq a => {xs:[a]|1 <= len xs} -> {ys:[a]|len ys = len xs} 
          -> (x::a, y::a, zs::[a], Bool) @-}
diff1 :: Eq a => [a] -> [a] -> (a, a, [a], Bool)
diff1 xs@(x:xs') ys@(y:ys') 
    = (x, y, zs, isPermutation (cons x zs) xs && isPermutation (cons y zs) ys)    
    where zs = xs'