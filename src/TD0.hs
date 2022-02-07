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
td0 n v t = iterate n (act (llen v) t) v

{-@ reflect cons @-}
cons :: Distr (List a) -> a -> Distr (List a)
cons xs x = bind xs (ppure `o` (Cons x))

{-@ reflect ppureDouble @-}
ppureDouble :: List Double -> Distr (List Double)
ppureDouble x = ppure x 

{-@ reflect mapM @-}
{-@ mapM :: (a -> Distr Double) -> xs:List a -> Distr ({ys:List Double|llen ys = llen xs}) @-}
mapM :: (a -> Distr Double) -> List a -> Distr (List Double)
mapM _ Nil = ppureDouble Nil
mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))

{-@ reflect iterate @-}
{-@ iterate :: Int -> (v:ValueFunction -> Distr ({v':ValueFunction|llen v' = llen v})) -> 
                v:ValueFunction -> Distr ({v':ValueFunction|llen v' = llen v}) @-}
iterate :: Int -> (ValueFunction -> DistrValueFunction) -> ValueFunction -> DistrValueFunction
iterate n _ x | n <= 0 = ppure x
iterate n f x = bind (f x) (iterate (n - 1) f)

{-@ reflect o @-}
o :: (b -> c) -> (a -> b) -> a -> c
o g f x = g (f x)

{-@ reflect act @-}
{-@ act :: n:Nat -> TransitionOf n -> {v:ValueFunction|llen v = n} -> Distr {v':ValueFunction|llen v' = llen v} @-}
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
-- 

