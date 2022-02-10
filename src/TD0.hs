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

{-@ reflect td0 @-}
{-@ td0 :: Nat -> v:ValueFunction -> TransitionOf (llen v) -> DistrValueFunction @-} 
td0 :: Int -> ValueFunction -> Transition -> DistrValueFunction
td0 n v t = iterate n (llen v) (act (llen v) t) v

{-@ reflect cons @-}
{-@ cons :: n:Nat -> Distr ({xs:List Double | llen xs == n}) -> Double -> Distr ({v:List Double | llen v = n + 1}) @-}
cons :: Int -> Distr (List Double) -> Double -> Distr (List Double)
cons n xs x = bind xs (ppure `o` (consDouble x))

{-@ reflect mapM @-}
{-@ mapM :: (a -> Distr Double) -> xs:List a -> Distr ({ys:List Double| llen ys = llen xs }) @-}
mapM :: (a -> Distr Double) -> List a -> Distr (List Double)
mapM _ Nil = ppureDouble Nil
mapM f (Cons x xs) = bind (f x) (cons (llen xs) (mapM f xs))

{-@ reflect iterate @-}
{-@ iterate :: n:Nat -> l:Nat -> (v:{ValueFunction | llen v == l} -> Distr ({v':ValueFunction|llen v' = llen v})) -> 
                v:{ValueFunction | llen v == l}  -> Distr ({v':ValueFunction|llen v' = llen v}) @-}
iterate :: Int -> Int -> (ValueFunction -> DistrValueFunction) -> ValueFunction -> DistrValueFunction
iterate n l _ x | n <= 0 = ppure x
iterate n l f x = bind (f x) (iterate (n - 1) l f)

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect act @-}
{-@ act :: n:Nat -> TransitionOf n -> v:{ValueFunction|llen v == n} 
        -> Distr {v':ValueFunction|llen v' = llen v} @-}
act :: Int -> Transition -> ValueFunction -> DistrValueFunction
act n t v = mapM (sample v t) (range 0 (llen v)) 

{-@ reflect uncurry @-}
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

{-@ reflect sample @-}
{-@ sample :: v:ValueFunction -> TransitionOf (llen v) -> StateOf v -> Distr Reward @-}
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
{-@ update :: v:ValueFunction -> StateOf v -> StateOf v -> Reward -> Reward @-}
update :: ValueFunction -> State -> State -> Reward -> Reward
update v i j r = (1 - α) * (v `at` i) + α * (r + γ * v `at` j)

