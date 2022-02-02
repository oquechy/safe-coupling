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
iterate 0 _ b = b 
iterate n f b = iterate (n - 1) f (f b)

{-@ reflect td0 @-}
{- td0 :: Nat -> π:_ -> {r:_|llen r = llen π} -> {p:_|llen p = llen π} -> {v:_|llen v = llen π} -> {v':_|true} @-} 
{-@ td0 :: Nat -> _ -> _ -> _ -> _ -> _ @-} 
td0 :: Int -> PolicyMap -> RewardFunction -> TransitionFunction -> DistrValueFunction -> DistrValueFunction
td0 n π r p v = iterate n (act π r p) v

{-@ reflect act @-}
{- act :: π:_ -> {r:_|llen r = llen π} -> {p:_|llen p = llen π} -> {v:_|llen v = llen π} -> {v':_|llen v' = llen π} @-}
act :: PolicyMap -> RewardFunction -> TransitionFunction -> DistrValueFunction -> DistrValueFunction
act π r p v = ap (zip3With (sample v) π r p) v

{-@ reflect sample @-}
sample :: DistrValueFunction -> Distr Action -> (Action -> Distr Reward) -> (Action -> Distr State) -> Distr Reward -> Distr Reward
sample v a r j rw = bind a (sample' v r j rw)

{-@ reflect sample' @-}
sample' :: DistrValueFunction -> (Action -> Distr Reward) -> (Action -> Distr State) -> Distr Reward -> Action -> Distr Reward
sample' v r j rw a = bind (r a) (sample'' v j rw a)

{-@ reflect sample'' @-}
sample'' :: DistrValueFunction -> (Action -> Distr State) -> Distr Reward -> Action -> Reward -> Distr Reward
sample'' v j rw a r = bind (j a) (sample''' v rw r)

{-@ reflect sample''' @-}
sample''' :: DistrValueFunction -> Distr Reward -> Reward -> State -> Distr Reward
sample''' v rw r j = bind rw (sample'''' v r j)

{-@ reflect sample'''' @-}
sample'''' :: DistrValueFunction -> Reward -> State -> Reward -> Distr Reward
sample'''' v r j rw = bind (v `at` j) (update r rw)

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 0.2
α = 0.5
k = 1 - α + α * γ

{-@ reflect update @-}
update :: Reward -> Reward -> Reward -> Distr Reward
update r rw rw' = ppure ((1 - α) * rw + α * (r + γ * rw'))


