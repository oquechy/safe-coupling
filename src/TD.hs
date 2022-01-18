{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module TD where
-- https://dl.acm.org/doi/pdf/10.1145/3434333

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Language.Haskell.Liquid.ProofCombinators

{-@ type State = Nat @-}
type State = Int
type Action = Int
type Reward = Double

type PolicyMap = State -> Distr Action
type RewardFunction = State -> Action -> Distr Reward
type TransitionFunction = State -> Action -> Distr State
-- TODO: make it a list
type ValueFunction = List Reward

lq_required :: List Int -> ()
lq_required _ = ()

{-@ reflect pow @-}
{-@ pow :: {v:Double|v >= 0} -> Nat -> {v:Double|v >= 0} @-}
pow :: Double -> Int -> Double
pow x 0 = 1
pow x i = x * pow x (i - 1)

{-@ thm :: n:Nat -> s:_ -> π:_ -> r:_ -> p:_ -> v1:_ -> v2:_ -> 
        {expDist (td0 n s π r p v1) (td0 n s π r p v2) <= pow k n * dist v1 v2} @-}
thm :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> ()
thm n s π r p v1 v2 | n <= 0 
    =   expDist (td0 n s π r p v1) (td0 n s π r p v2)
        ? relationalppure v1 v2
    === dist v1 v2
    === pow k n * dist v1 v2
    *** QED
thm n s π r p v1 v2
    =   expDist (td0 n s π r p v1) (td0 n s π r p v2)
        ? expDistBindP 0 (\v1' v2' -> True)
                      (td0 (n - 1) s π r p) (act s π r p v1 Nil) 
                      (td0 (n - 1) s π r p) (act s π r p v2 Nil)
                      (lemma n s π r p)
    =<= pow k n * dist v1 v2
    *** QED

{-@ lemma :: {n:Nat| n > 0} -> s:_ -> π:_ -> r:_ -> p:_ -> v1:_ -> v2:_ -> {expDist (td0 (n - 1) s π r p v1) (td0 (n - 1) s π r p v2) <= 0} @-}
lemma :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> ()
lemma n s π r p v1 v2
    =   expDist (td0 (n - 1) s π r p v1) (td0 (n - 1) s π r p v2) 
        ? thm (n - 1) s π r p v1 v2
    =<= pow k (n - 1) * dist v1 v2
    =<= pow k n * dist v1 v2
    *** QED

{-@ reflect td0 @-}
{-@ td0 :: Nat -> i:Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> Distr ValueFunction @-}
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

{-@ measure TD.act :: i:State -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction @-}
act :: State -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> Distr ValueFunction
act i _ _ _ _ w | i <= 0 = ppure w
act i π r p v w = bind (π i) (\a -> 
                    bind (r i a) (\rw -> 
                        bind (p i a) (\j -> 
                            act (i - 1) π r p v (Cons ((1 - α) * v `at` i + α * (rw + γ * v `at` j)) w))))