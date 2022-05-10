{-@ LIQUID "--reflection"     @-}

module ApplicativeTD.TD0 where

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

{-@ type TransitionOf N = {v:List (PrM ({i:State|0 <= i && i < N}, Reward))| len v = N} @-}
type Transition = List (PrM (State, Reward))
type ValueFunction = List Reward
type PrMValueFunction = List (PrM Reward)

lq_required :: List Int -> ()
lq_required _ = ()

{-@ reflect td0 @-}
{- td0 :: Nat -> v:ValueFunction -> TransitionOf (len v) -> PrMValueFunction @-} 
td0 :: Int -> List Reward -> Transition -> List (PrM Reward)
td0 n v t = iterate n (len v) (act (len v) t) (map ppure v)

{-@ reflect iterate @-}
{- iterate :: n:Nat -> l:Nat -> (v:{PrMValueFunction | len v == l} -> PrM ({v':ValueFunction|len v' = len v})) -> 
                v:{PrMValueFunction | len v == l}  -> PrM ({v':PrMValueFunction|len v' = len v}) @-}
iterate :: Int -> Int -> (PrMValueFunction -> PrMValueFunction) -> PrMValueFunction -> PrMValueFunction
iterate n l _ x | n <= 0 = x
iterate n l f x = iterate (n - 1) l f (f x)

{-@ reflect act @-}
{- act :: n:Nat -> TransitionOf n -> v:{PrMValueFunction|len v == n} 
        -> PrM {v':ValueFunction|len v' = len v} @-}
act :: Int -> Transition -> PrMValueFunction -> PrMValueFunction
act n t v = map (sample v t) (range 0 (len v)) 



{-@ reflect sample @-}
{- sample :: v:PrMValueFunction -> TransitionOf (len v) -> StateOf v -> PrM Reward @-}
sample :: PrMValueFunction -> Transition -> State -> PrM Reward
sample v t i = bind (t `at` i) (uncurry (liftUpdate v i))

{-@ reflect liftUpdate @-}
liftUpdate :: PrMValueFunction -> State -> State -> Reward -> PrM Reward 
liftUpdate v i j r = liftA2 (update r) (v `at` i) (v `at` j)

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}
γ, α, k :: Double
γ = 0.2
α = 0.5
k = 1 - α + α * γ

{-@ reflect update @-}
{-@ update :: Reward -> Reward -> Reward -> Reward @-}
update :: Reward -> Reward -> Reward -> Reward
update r a b = (1 - α) * a + α * (r + γ * b)

