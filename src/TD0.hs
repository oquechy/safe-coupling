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

{-@ measure TD0.foldM :: (b -> a -> Distr b) -> b -> List a -> Distr b @-}
{-@ assume foldM :: f:(b -> a -> Distr b) -> z:b -> xs:List a -> {v:Distr b|v == TD0.foldM f z xs} @-}
foldM :: (b -> a -> Distr b) -> b -> List a -> Distr b
foldM _ z Nil = ppure z
foldM _ _ _ = undefined

-- flipConst :: (b -> Distr b) -> b -> a -> Distr b

{-@ measure TD0.iterate :: Nat -> (b -> Distr b) -> b -> Distr b @-}
{-@ assume iterate :: n:Nat -> f:(b -> Distr b) -> x:b -> {v:Distr b|v == TD0.iterate n f x} @-}
iterate :: Int -> (b -> Distr b) -> b -> Distr b
iterate n _ x | n <= 0 = ppure x
iterate n f x = bind (f x) (iterate (n - 1) f)

{-@ reflect act @-}
act :: Transition -> ValueFunction -> DistrValueFunction
act t v = foldM (sample t v) Nil (range 0 (llen v))

{-@ reflect sample @-}
sample :: Transition -> ValueFunction -> ValueFunction -> State -> DistrValueFunction
sample t v w i = bind (t `at` i) (cons (update v i) w)

{-@ reflect cons @-}
cons :: (State -> Reward -> Reward) -> ValueFunction -> (State, Reward) -> DistrValueFunction
cons u w (i, r) = ppure (Cons (u i r) w)

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


