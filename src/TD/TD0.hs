{-@ LIQUID "--reflection"     @-}

module TD.TD0 where

-- import           Monad.Implemented.PrM
import           Monad.PrM
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

{-@ type TransitionOf N = {v:List (PrM ({i:State|0 <= i && i < N}, Reward))| llen v = N} @-}
type Transition = List (PrM (State, Reward))
type ValueFunction = List Reward
type PrMValueFunction = PrM (List Reward)

lq_required :: List Int -> ()
lq_required _ = ()

{-@ reflect td0 @-}
{-@ td0 :: Nat -> v:ValueFunction -> TransitionOf (llen v) -> PrMValueFunction @-} 
td0 :: Int -> ValueFunction -> Transition -> PrMValueFunction
td0 n v t = iterate n (llen v) (act (llen v) t) v



{-@ reflect iterate @-}
{-@ iterate :: n:Nat -> l:Nat -> (v:{ValueFunction | llen v == l} -> PrM ({v':ValueFunction|llen v' = llen v})) -> 
                v:{ValueFunction | llen v == l}  -> PrM ({v':ValueFunction|llen v' = llen v}) @-}
iterate :: Int -> Int -> (ValueFunction -> PrMValueFunction) -> ValueFunction -> PrMValueFunction
iterate n l _ x | n <= 0 = ppure x
iterate n l f x = bind (f x) (iterate (n - 1) l f)



{-@ reflect act @-}
{-@ act :: n:Nat -> TransitionOf n -> v:{ValueFunction|llen v == n} 
        -> PrM {v':ValueFunction|llen v' = llen v} @-}
act :: Int -> Transition -> ValueFunction -> PrMValueFunction
act n t v = mapM (sample v t) (range 0 (llen v)) 

{-@ reflect uncurry @-}
uncurry :: (a -> b -> c) -> (a, b) -> c
uncurry f (a, b) = f a b

{-@ reflect sample @-}
{-@ sample :: v:ValueFunction -> TransitionOf (llen v) -> StateOf v -> PrM Reward @-}
sample :: ValueFunction -> Transition -> State -> PrM Reward
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

