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

{-@ type StateOf V = Idx V @-}
type State = Int
type Action = Int
type Reward = Double

type PolicyMap = List (Distr Action)
type RewardFunction = List (Action -> Distr Reward)
type TransitionFunction = List (Action -> Distr State)

{-@ type TransitionOf N = {v:List (Distr ({i:State|0 <= i && i < N}, Reward))| llen v = N} @-}
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
{-@ td0 :: Nat -> v:_ -> TransitionOf (llen v) -> _ @-} 
td0 :: Int -> ValueFunction -> Transition -> DistrValueFunction
td0 n v t = iterate n (act (llen v) t) v

{-@ reflect cons @-}
cons :: Distr (List a) -> a -> Distr (List a)
cons xs x = bind xs (ppure `o` (Cons x))

{-@ reflect mapM @-}
{-@ mapM :: (a -> Distr Double) -> xs:List a -> Distr {ys:_|llen ys = llen xs} @-}
mapM :: (a -> Distr Double) -> List a -> Distr (List Double)
mapM _ Nil = ppure Nil
mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))

{-@ reflect iterate @-}
iterate :: Int -> (b -> Distr b) -> b -> Distr b
iterate n _ x | n <= 0 = ppure x
iterate n f x = bind (f x) (iterate (n - 1) f)

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect act @-}
{-@ act :: n:Nat -> TransitionOf n -> {v:_|llen v = n} -> Distr {v':_|llen v' = llen v} @-}
act :: Int -> Transition -> ValueFunction -> DistrValueFunction
act n t v = mapM (sample v t) (range 0 (llen v)) 

{-@ reflect uncurry @-}
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

{-@ reflect sample @-}
{-@ sample :: v:_ -> TransitionOf (llen v) -> StateOf v -> _ @-}
sample :: ValueFunction -> Transition -> State -> Distr Reward
sample v t i = bind (t `at` i) (ppure `o` (uncurry (update v i)))

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 0.2
α = 0.5
k = 1 - α + α * γ

{-@ reflect update @-}
{-@ update :: v:_ -> StateOf v -> StateOf v -> _ -> _ @-}
update :: ValueFunction -> State -> State -> Reward -> Reward
update v i j r = (1 - α) * (v `at` i) + α * (r + γ * v `at` j)


