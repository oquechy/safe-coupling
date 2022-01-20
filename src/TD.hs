{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}

module TD where
-- https://dl.acm.org/doi/pdf/10.1145/3434333

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , repeat
                                                )

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
type DistrValueFunction = List (Distr Reward)

lq_required :: List Int -> ()
lq_required _ = ()

{-@ test :: i:State -> {v:ValueFunction|i < llen v} -> {j:State|j < llen v} @-}
test :: State -> ValueFunction -> State
test i v = i

{-@ reflect pow @-}
{-@ pow :: {v:Double|v >= 0} -> Nat -> {v:Double|v >= 0} @-}
pow :: Double -> Int -> Double
pow x 0 = 1
pow x i = x * pow x (i - 1)

-- distFun :: f:(a -> b) -> g:(a -> b) -> {max_a [dist (f a) (g a)]}

-- expDistList :: f:(a -> Distr b) -> g:(a -> Distr b) -> {max_a [dist (f a) (g a)]}

{-@ thm :: n:Nat -> s:_ -> π:_ -> r:_ -> p:_ -> v1:_ -> v2:_ -> 
        {expDist (td0 n s π r p v1) (td0 n s π r p v2) <= pow k n * dist v1 v2} @-}
thm :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> ()
thm n s π r p v1 v2 | n <= 0 
    =   undefined
{-        
        expDistList (td0 n s π r p v1) (td0 n s π r p v2)
        ? relationalppure v1 v2
    === dist v1 v2
    === pow k n * dist v1 v2
    *** QED -}
thm n s π r p v1 v2
    =   undefined
{-        
        expDist (td0 n s π r p v1) (td0 n s π r p v2)
        ? axiomSampleLift arg1 arg2 
        ? expDistBindP m (sampleP arg1 arg2)
                      (td0 (n - 1) s π r p) arg1
                      (td0 (n - 1) s π r p) arg2
                      (lemma n s π r p v1 v2 m)
        ? assert (expDist (bind arg1 (td0 (n - 1) s π r p) ) (bind arg2 (td0 (n - 1) s π r p) ) <= (pow k (n-1) * expDist arg1 arg2))
    =<= pow k (n-1) * expDist arg1 arg2
         ? relationalAct s π r p v1 v2
         ? assert (expDist (act s π r p v1) (act s π r p v2) <= k * (dist v1 v2))
    =<= pow k n * dist v1 v2 
    *** QED -}
    where 
    arg1 = act s π r p v1 
    arg2 = act s π r p v2 
    -- m    = pow k (n-1) * expDist arg1 arg2
    -- m' = pow k (n-1) * expDist (act s π r p v1) (act s π r p v2)



 {-@ relationalAct :: s:_ -> π:_ -> r:_ -> p:_ -> v1:_ -> v2:_ 
                   -> { expDist (act s π r p v1) (act s π r p v2) <= k * (dist v1 v2) } @-}   
relationalAct :: Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> () 
relationalAct = undefined 


{- sampled (act ...) v1 -}


{-@ assert :: b:{Bool | b} -> () @-}
assert :: Bool -> () 
assert _ = () 


{-@ reflect trueP @-}
trueP :: a -> a -> Bool 
trueP _ _ = True 



{-@ measure TD.sampled :: Distr a ->  a -> Bool @-}
{-@ assume sampled :: a:Distr a ->  v:a -> {b:Bool | b <=> TD.sampled a v } @-} 
sampled :: Distr a ->  a -> Bool 
sampled _ _ = undefined  

{-@ reflect sampleP @-}
sampleP :: Distr a -> Distr a ->  a -> a -> Bool 
sampleP e1 e2 x1 x2 = sampled e1 x1 && sampled e2 x2  


{-@ assume axiomSampleLift :: x:Distr a -> y:Distr a -> { lift (sampleP x y) x y == True } @-}
axiomSampleLift :: Distr a -> Distr a -> () 
axiomSampleLift _ _ = ()

{-@ assume axiomTrueLift :: x:Distr a -> y:Distr a -> { lift trueP x y == True } @-}
axiomTrueLift :: Distr a -> Distr a -> () 
axiomTrueLift _ _ = () 

{-@ lemma :: {n:Nat| n > 0} -> s:_ -> π:_ -> r:_ -> p:_ 
          -> v1:_ 
          -> v2:_ 
          -> m:{Double | m == pow k (n-1) * expDist (act s π r p v1) (act s π r p v2) } 
          -> x1:ValueFunction 
          -> x2:{ValueFunction | sampleP (act s π r p v1) (act s π r p v2) x1 x2 }
          -> {expDist (td0 (n - 1) s π r p x1) (td0 (n - 1) s π r p x2) <= m} @-}
lemma :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction ->  ValueFunction -> ValueFunction -> Double ->  ValueFunction -> ValueFunction -> ()
--           -> x2:{ValueFunction | sampled (act s π r p v1) x1 && sampled (act s π r p v2) x2 }

lemma n s π r p v1 v2 = undefined 
{- 
    =   expDist (td0 (n - 1) s π r p v1) (td0 (n - 1) s π r p v2) 
        ? thm (n - 1) s π r p v1 v2
    =<= pow k (n - 1) * dist v1 v2
    *** QED
-}

repeat :: Int -> (ValueFunction -> DistrValueFunction) -> ValueFunction -> DistrValueFunction
repeat = undefined

{-@ reflect td0 @-}
{-@ td0 :: Nat -> i:State -> _ -> _ -> _ -> {v:ValueFunction|i < llen v} -> DistrValueFunction @-}
td0 :: Int -> Int -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> DistrValueFunction
td0 n _ _ _ _ v | n <= 0 = map ppure v
td0 n s π r p v          = act s π r p v

{-@ reflect γ @-}
{-@ reflect α @-}
{-@ reflect k @-}

γ, α, k :: Double

γ = 0.9
α = 0.5

{-@ k :: {k:Double|k < 1} @-}
k = 1 - α + α * γ

-- {-@ forall i < len w1. espDist (w1 i) (w2 i) < k * dist (v1 i) (v2 i) @-}

{-@ reflect act @-}
{-@ act :: i:State -> _ -> _ -> _ -> {v:_|i < llen v} -> DistrValueFunction @-}
act :: State -> PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> DistrValueFunction
act i _ _ _ v | i <= 0 = map ppure v
act i π r p v          = map (sample π r p v) (range i)
    
{-@ relationalf :: π:_ -> r:_ -> p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> 
                    {expDist (sample π r p v1 i) (sample π r p v2 i) <= k * dist (at v1 i) (at v2 i)} @-}
relationalf :: PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> State -> ()
relationalf π r p v1 v2 i
    =   expDist (sample π r p v1 i) (sample π r p v2 i) 
    === expDist (bind (π i) (sample' r p v1 i)) (bind (π i) (sample' r p v2 i))
        ?   expDistBind m (sample' r p v1 i) (π i)
                          (sample' r p v2 i) (π i)
                          (lemma1 r p v1 v2 i)
    =<= m
    *** QED
  where m = k * dist (v1 `at` i) (v2 `at` i)

{-@ lemma1 :: r:_ -> p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> 
                a:_ -> {expDist (sample' r p v1 i a) (sample' r p v2 i a) <= k * dist (at v1 i) (at v2 i)} @-}
lemma1 :: RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> State -> Action -> ()
lemma1 r p v1 v2 i a 
    =   expDist (sample' r p v1 i a) (sample' r p v2 i a)
    === expDist (bind (r i a) (sample'' p v1 i a)) (bind (r i a) (sample'' p v2 i a))
        ?   expDistBind m (sample'' p v1 i a) (r i a)
                          (sample'' p v2 i a) (r i a)
                          (lemma2 p v1 v2 i a)
    =<= m
    *** QED
  where m = k * dist (at v1 i) (at v2 i)

{-@ lemma2 :: p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> a:_ ->
                rw:_ -> {expDist (sample'' p v1 i a rw) (sample'' p v2 i a rw) <= k * dist (at v1 i) (at v2 i)} @-}
lemma2 :: TransitionFunction -> ValueFunction -> ValueFunction -> State -> Action -> Reward -> ()
lemma2 p v1 v2 i a rw 
    =   expDist (sample'' p v1 i a rw) (sample'' p v2 i a rw)
    === expDist (bind (p i a) (update v1 i rw)) (bind (p i a) (update v2 i rw))
        ?   expDistBind m (update v1 i rw) (p i a)
                          (update v2 i rw) (p i a)
                          (lemma3 v1 v2 i a rw)
    =<= m
    *** QED
  where m = k * dist (at v1 i) (at v2 i)

{-@ lemma3 :: v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> a:_ -> rw:_ -> 
                {j:State|j < llen v1} -> {expDist (update v1 i rw j) (update v2 i rw j) <= k * dist (at v1 i) (at v2 i)} @-}
lemma3 :: ValueFunction -> ValueFunction -> State -> Action -> Reward -> State -> ()
lemma3 v1 v2 i a rw j 
    =   expDist (update v1 i rw j) (update v2 i rw j)
    === expDist (ppure ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))) 
                (ppure ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j)))
        ? expDistPure ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))
                      ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j))
    === dist ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))
             ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j))
    =<= k * dist (at v1 i) (at v2 i)
    *** QED

{-@ reflect sample @-}
{-@ sample :: _ -> _ -> _ -> v:_ -> {i:State|i < llen v} -> _ @-}
sample :: PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> State -> Distr Reward
sample π r p v i = bind (π i) (sample' r p v i)
        
{-@ reflect sample' @-}
{-@ sample' :: _ -> _ -> v:_ -> {i:State|i < llen v} -> _ -> _ @-}
sample' :: RewardFunction -> TransitionFunction -> ValueFunction -> State -> Action -> Distr Reward
sample' r p v i a = bind (r i a) (sample'' p v i a)

{-@ reflect sample'' @-}
{-@ sample'' :: _ -> v:ValueFunction -> {i:State|i < llen v} -> _ -> _ -> _ @-}
sample'' :: TransitionFunction -> ValueFunction -> State -> Action -> Reward -> Distr Reward
sample'' p v i a rw = bind (p i a) (update v i rw)
            
{-@ reflect update @-}
{-@ update :: v:_ -> {i:State|i < llen v} -> _ -> {j:State|j < llen v} -> _ @-}
update :: ValueFunction -> State -> Reward -> State -> Distr Reward
update v i rw j = ppure ((1 - α) * v `at` i + α * (rw + γ * v `at` j))

