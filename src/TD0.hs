{-@ LIQUID "--reflection"     @-}

module TD0 where

-- import           Monad.Implemented.Distr
import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , max
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                , uncurry
                                                )


type State = Int
type Action = Int
type Reward = Double

type PolicyMap = List (Distr Action)
type RewardFunction = List (Action -> Distr Reward)
type TransitionFunction = List (Action -> Distr State)

type Transition = List (Distr (State, Reward))
type ValueFunction = List Reward
type DistrValueFunction = Distr (List Reward)

lq_required :: List Int -> ()
lq_required _ = ()

-- {-@ reflect iterate @-}
-- {-@ iterate :: Nat -> (b -> b) -> b -> b @-}
-- iterate :: Int -> (b -> b) -> b -> b
-- iterate 0 _ b = b 
-- iterate n f b = iterate (n - 1) f (f b)

{-@ reflect td0 @-}
{-@ td0 :: Nat -> _ -> _ -> _ @-} 
td0 :: Int -> Transition -> ValueFunction -> DistrValueFunction
td0 n t v = iterate n (act t) v

{-@ reflect foldM @-}
foldM :: (b -> a -> Distr b) -> List a -> b -> Distr b
foldM _ Nil z = ppure z
foldM f (Cons x xs) z = bind (f z x) (foldM f xs)

{-@ reflect cons @-}
cons :: Distr (List a) -> a -> Distr (List a)
cons xs x = bind xs (ppure `o` (Cons x))

{-@ reflect purecons @-}
purecons :: a -> List a -> Distr (List a)
purecons x xs = ppure (Cons x xs)

{-@ reflect mapM @-}
mapM :: (a -> Distr Double) -> List a -> Distr (List Double)
mapM _ Nil = ppureDouble Nil
mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))

{-@ reflect ppureDouble @-}
ppureDouble :: List Double -> Distr (List Double)
ppureDouble x = ppure x 

-- flipConst :: (b -> Distr b) -> b -> a -> Distr b

{-@ reflect iterate @-}
iterate :: Int -> (b -> Distr b) -> b -> Distr b
iterate n _ x | n <= 0 = ppure x
iterate n f x = bind (f x) (iterate (n - 1) f)

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect act @-}
act :: Transition -> ValueFunction -> DistrValueFunction
act t v = mapM (sample t v) (range 0 (llen v)) 

{-@ reflect uncurry @-}
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

{-@ reflect sample @-}
sample :: Transition -> ValueFunction -> State -> Distr Reward
sample t v i = bind (t `at` i) (ppure `o` (uncurry (update v i)))

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 0.2
α = 0.5
k = 1 - α + α * γ

{-@ reflect update @-}
update :: ValueFunction -> State -> State -> Reward -> Reward
update v i j r = (1 - α) * (v `at` i) + α * (r + γ * v `at` j)


