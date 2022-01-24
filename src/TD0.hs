{-@ LIQUID "--skip-module"     @-}

module TD0 where

import           Monad.Implemented.Distr
-- import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                )

import           Language.Haskell.Liquid.ProofCombinators

type State = Int
type Action = Int
type Reward = Double

type PolicyMap = State -> Distr Action
type RewardFunction = State -> Action -> Distr Reward
type TransitionFunction = Int -> State -> Action -> Distr State
type ValueFunction = List Reward
type DistrValueFunction = List (Distr Reward)

lq_required :: List Int -> ()
lq_required _ = ()

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z Nil = z                  
foldr f z (Cons x xs) = f x (foldr f z xs)

td0 :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> DistrValueFunction
td0 n s π r p v = foldr (\i v -> act i π r p v) (map ppure v) (range n) 


inj :: DistrValueFunction -> Distr ValueFunction
inj Nil = ppure Nil
inj (Cons x xs) = 
  bind x        (\v -> 
  bind (inj xs) (\vs -> 
  ppure (Cons v vs))) 


act :: State -> PolicyMap -> RewardFunction -> TransitionFunction -> DistrValueFunction -> DistrValueFunction
act i _ _ _ v | i <= 0 = v
act i π r p v          = map (\i -> bind (inj v) (\v' -> sample π r p v' i)) (range i)
    
sample :: PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> State -> Distr Reward
sample π r p v i = bind (π i) (sample' r p v i)
        
sample' :: RewardFunction -> TransitionFunction -> ValueFunction -> State -> Action -> Distr Reward
sample' r p v i a = bind (r i a) (sample'' p v i a)

sample'' :: TransitionFunction -> ValueFunction -> State -> Action -> Reward -> Distr Reward
sample'' p v i a rw = bind (p (llen v) i a) (update v i rw) 

γ, α :: Double
γ = 0.9
α = 0.5

update :: ValueFunction -> State -> Reward -> State -> Distr Reward
update v i rw j = ppure ((1 - α) * v `at` i + α * (rw + γ * v `at` j))

