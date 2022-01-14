{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module TD where
-- https://dl.acm.org/doi/pdf/10.1145/3434333

import           Monad.Distr
import           Data.Dist
import           Data.List

type State = Int
type Action = Int
type Reward = Double

type PolicyMap = State -> Distr Action
type RewardFunction = State -> Action -> Distr Reward
type TransitionFunction = State -> Action -> Distr State
-- TODO: make it a list
type ValueFunction = List Reward

{-@ reflect pow @-}
{-@ pow :: Double -> Nat -> Double @-}
pow :: Double -> Int -> Double
pow x 0 = 1
pow x i = x * pow x (i - 1)

{-@ thm :: n:_ -> s:_ -> π:_ -> r:_ -> p:_ -> v1:_ -> v2:_ -> 
        {dist (td0 n s π r p v2) (td0 n s π r p v1) <= pow k n * dist v1 v2} @-}
thm :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> ()
thm n s π r p v1 v2 | n <= 0 = ()
thm n s π r p v1 v2 = undefined

{-@ reflect td0 @-}
td0 :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> Distr ValueFunction
td0 n _ _ _ _ v | n <= 0 = ppure v
td0 n s π r p v          = bind (act s π r p v Nil) (td0 (n - 1) s π r p)

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 1
α = 0.5
k = 1 - α + α * γ

{- relational act ~ act :: i1:State -> π1:PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction 
                            ~ i2:State -> π1:PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction
                            ~~ true => true => true => true => true => true => true @-}

{-@ measure TD.act :: State -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction @-}
act :: State -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction
act i _ _ _ _ w | i <= 0 = ppure w
act i π r p v w = bind (π i) (\a -> 
                    bind (r i a) (\rw -> 
                        bind (p i a) (\j -> 
                            act (i - 1) π r p v (Cons ((1 - α) * v `at` i + α * (rw + γ * v `at` j)) w))))