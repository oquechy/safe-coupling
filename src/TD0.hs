{-@ LIQUID "--reflection"     @-}

module TD0 where

-- import           Monad.Implemented.Distr
import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                )


type State = Int
type Action = Int
type Reward = Double

type PolicyMap = List (Distr Action)
type RewardFunction = List (Action -> Distr Reward)
type TransitionFunction = List (Action -> Distr State)
type ValueFunction = List Reward
type DistrValueFunction = List (Distr Reward)

lq_required :: List Int -> ()
lq_required _ = ()

{-@ reflect foldr @-}
foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ z Nil = z                  
foldr f z (Cons x xs) = f x (foldr f z xs)

{-@ reflect iterate @-}
{-@ iterate :: Nat -> (b -> b) -> b -> b @-}
iterate :: Int -> (b -> b) -> b -> b
iterate 0 f b = f b 
iterate n f b = f (iterate (n - 1) f b) 

{-@ reflect td0 @-}
{-@ td0 :: Nat -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> DistrValueFunction @-}
td0 :: Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> DistrValueFunction
td0 n π r p v = iterate n (act π r p) (map ppure v)

{-@ measure TD0.inj :: DistrValueFunction -> Distr ValueFunction @-}
{-@ assume inj :: v:DistrValueFunction -> {v':Distr ValueFunction|v' = TD0.inj v} @-}
inj :: DistrValueFunction -> Distr ValueFunction
inj Nil = ppure Nil
inj (Cons x xs) = 
  bind x        (\v -> 
  bind (inj xs) (\vs -> 
  ppure (Cons v vs))) 

{-@ reflect act @-}
act :: PolicyMap -> RewardFunction -> TransitionFunction -> DistrValueFunction -> DistrValueFunction
act π r p v = map (local π r p v) (range 0 (llen v))
    
{-@ reflect local @-}
local :: PolicyMap -> RewardFunction -> TransitionFunction -> DistrValueFunction -> State -> Distr Reward
local π r p v i = bind (inj v) (sample π r p i)

{-@ reflect sample @-}
sample :: PolicyMap -> RewardFunction -> TransitionFunction -> State -> ValueFunction -> Distr Reward
sample π r p i v = bind (π `at` i) (sample' r p v i)

{-@ reflect sample' @-}
sample' :: RewardFunction -> TransitionFunction -> ValueFunction -> State -> Action -> Distr Reward
sample' r p v i a = bind ((r `at` i) a) (sample'' p v i a)

{-@ reflect sample'' @-}
sample'' :: TransitionFunction -> ValueFunction -> State -> Action -> Reward -> Distr Reward
sample'' p v i a rw = bind ((p `at` i) a) (update v i rw) 

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 0.2
α = 0.5
k = 1 - α + α * γ

{-@ reflect update @-}
update :: ValueFunction -> State -> Reward -> State -> Distr Reward
update v i rw j = ppure ((1 - α) * v `at` i + α * (rw + γ * v `at` j))

