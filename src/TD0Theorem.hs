{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple"      @-}

module TD0Theorem where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Prelude                 hiding ( map
                                                , max
                                                , iterate
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                )

import           Language.Haskell.Liquid.ProofCombinators
import           Monad.Distr 
import           Data.Dist 
import           TD0

{-@ relationaltd0 :: n:Nat -> t:_ -> v1:_ -> v2:_ -> 
        {lift (bounded (pow k n * (distList v1 v2))) (td0 n t v1) (td0 n t v2)} @-}
relationaltd0 :: Int -> Transition -> ValueFunction -> ValueFunction -> ()
relationaltd0 n t v1 v2 
    = relationaliterate (distList v1 v2) k n (act t) (relationalact t) v1 v2 

{-@ relationaliterate :: m:_ -> {k:_|k >= 0} -> n:Nat -> f:_ -> 
                            (m:_ -> x1:_ -> x2:_ -> {bounded m x1 x2 => lift (bounded (k * m)) (f x1) (f x2)}) ->
                            x1:_ -> x2:_ -> 
                            {bounded m x1 x2 => lift (bounded (pow k n * m)) (iterate n f x1) (iterate n f x2)} @-}
relationaliterate :: Double -> Double -> Int -> (List Double -> Distr (List Double)) ->
                        (Double -> List Double -> List Double -> ()) -> List Double -> List Double -> ()
relationaliterate m k n _ _ x1 x2 | n <= 0
    =   undefined
        -- liftPure (bounded (pow k n * m)) x1 x2  
            -- ? (distList x1 x2 
            --     =<= m
            --     =<= pow k n * m
            --     *** QED)
relationaliterate m k n f lemma x1 x2
    =   undefined
        -- liftBind (bounded (pow k n * m)) (bounded (k * m)) 
        --          (f x1) (iterate (n - 1) f)
        --          (f x2) (iterate (n - 1) f)
        --          (relationaliterate (k * m) k (n - 1) f lemma)
        --     ? lemma m x1 x2
            

-- {-@ relationaliterate :: n:Nat -> {k:_|k > 0} -> f:_ -> v1:_ -> v2:_ -> 
--                             (v1':_ -> v2':_ -> {expDistList (f v1') (f v2') <= k * expDistList v1' v2'}) ->
--                             {expDistList (iterate n f v1) (iterate n f v2) <= pow k n * expDistList v1 v2} @-}
-- relationaliterate :: Int -> Double -> (DistrValueFunction -> DistrValueFunction) -> DistrValueFunction -> DistrValueFunction -> 
--                         (DistrValueFunction -> DistrValueFunction -> ()) -> ()
-- relationaliterate 0 k f v1 v2 relf
--     =   expDistList (iterate 0 f v1) (iterate 0 f v2) 
--     === expDistList v1 v2
--     =<= pow k 0 * expDistList v1 v2
--     *** QED
-- relationaliterate n k f v1 v2 relf
--     =   expDistList (iterate n f v1) (iterate n f v2) 
--     === expDistList (iterate (n - 1) f (f v1)) (iterate (n - 1) f (f v2)) 
--         ? relationaliterate (n - 1) k f (f v1) (f v2) relf
--     =<= pow k (n - 1) * expDistList (f v1) (f v2)
--         ? relf v1 v2
--     =<= k * pow k (n - 1) * expDistList v1 v2
--     === pow k n * expDistList v1 v2
--     *** QED

{-@ reflect shrinks @-}
shrinks :: Transition -> Double -> ValueFunction -> ValueFunction -> Bool
shrinks t k v1' v2' = dist (act t v1') (act t v2') <= k * dist v1' v2'

{-@ reflect bounded @-}
bounded :: Double -> ValueFunction -> ValueFunction -> Bool
bounded m v1' v2' = distList v1' v2' <= m

{-@ reflect bounded' @-}
bounded' :: Double -> Double -> Double -> Bool
bounded' m x1 x2 = dist x1 x2 <= m

-- consM :: 
-- consM = undefined

-- {-@ consbounded :: m:Double -> x1:Distr Double -> xs1:Distr (List Double) -> {x2:Distr Double|bounded' m x1 x2} -> {xs2:Distr (List Double)|bounded m xs1 xs2} -> 
--                     {bounded m (consM x1 xs1) (consM x2 xs2)} @-}
-- consbounded :: Double -> Distr Double -> Distr (List Double) -> Distr Double -> Distr (List Double) -> ()
-- consbounded = undefined

{-@ relationalmapM :: m:_ -> k:_ -> f1:_ -> v1:_ -> f2:_ -> v2:_ -> 
                        (x1:_ -> {x2:_|dist x1 x2 <= m} -> {lift (bounded' (k * m)) (f1 x1) (f2 x2)}) ->
                        {lift (bounded (k * m)) (mapM f1 v1) (mapM f2 v2)} @-}
relationalmapM :: Double -> Double -> (Double -> Distr Double) -> List Double -> (Double -> Distr Double) -> List Double -> 
                    (Double -> Double -> ()) -> ()
-- mapM _ Nil = ppure Nil
relationalmapM m k _ v1 _ Nil _
    =   liftPure (bounded (k * m)) v1 Nil
relationalmapM m k _ Nil _ v2 _
    =   liftPure (bounded (k * m)) Nil v2
-- mapM f (Cons x xs) = bind (f x) (cons (mapM f xs))
relationalmapM m k f1 v1 f2 (Cons i is) lemma = undefined
    -- =   liftBind (bounded (k * m)) trueP
    --         (f1 i1) (cons (mapM f is2))
    --         (\i1 i2 -> 
    --             distList (cons (mapM f xs1) x1) (cons (mapM f xs2) x2)) 
    --             =<= k * m
    --             *** QED)

{-@ relationalact :: t:_ -> m:_ -> v1:_ -> v2:_ -> 
                    {bounded m v1 v2 => lift (bounded (k * m)) (act t v1) (act t v2)} @-}
relationalact :: Transition -> Double -> ValueFunction -> ValueFunction -> ()
relationalact t m v1 v2 
    =   undefined
    -- relationalmapM m k 
    --         (sample t v1) (range 0 (llen v1)) 
    --         (sample t v2) (range 0 (llen v2)) 
    --         (relationalsample m t v1 v2)

-- {-@ reflect shrinks @-}
-- shrinks :: Double -> List (Distr a -> Distr b) -> List (Distr a -> Distr b) -> Distr a -> Distr a -> Bool
-- shrinks _ Nil _ _ _ = True
-- shrinks _ _ Nil _ _ = True
-- shrinks k (Cons f fs) (Cons f' fs') x x' = expDist (f x) (f' x') < k * expDist x x' && shrinks k fs fs' x x'

-- {-@ relationalap :: fs1:_ -> xs1:_ ->
--                     fs2:_ -> xs2:_ ->
--                     (x1:_ -> x2:_ -> {shrinks k fs1 fs2 x1 x2}) ->
--                     {expDistList (ap fs1 xs1) (ap fs2 xs2) <= k * expDistList xs1 xs2} @-}
-- relationalap :: List (a -> b) -> List a -> List (a -> b) -> List a -> (a -> a -> ()) -> ()
-- relationalap xs1 xs2 f = undefined

{-@ relationalsample :: m:_ -> t:_ -> i:_ -> v1:_ -> v2:_ ->  
                        {bounded m v1 v2 => lift (bounded' (k * m)) (sample t v1 i) (sample t v2 i)} @-}
relationalsample :: Double -> Transition -> State -> ValueFunction -> ValueFunction -> ()
relationalsample = undefined

-- maybe bounded m*k w1 w2 => lift (bounded m*k) ...
-- {-@ relationalcons :: m:_ -> u1:_ -> w1:_ -> u2:_ -> w2:_ -> p:(j:_, r:_) ->
--                         {dist (u1 (fst p) (snd p)) (u2 (fst p) (snd p)) <= m && bounded m w1 w2 => 
--                             lift (bounded m) (cons u1 w1 p) (cons u2 w2 p)} @-}
-- relationalcons :: Double -> (State -> Reward -> Reward) -> ValueFunction -> 
--                             (State -> Reward -> Reward) -> ValueFunction -> 
--                             (State, Reward) -> ()
-- relationalcons = undefined

{-@ relationalupdate :: m:_ -> v1:_ -> v2:_ -> i:_ -> j:_ -> r:_ ->
                        {dist (update v1 i j r) (update v2 i j r) 
                            <= k * max (dist (at v1 i) (at v2 i)) (dist (at v1 j) (at v2 j))} @-}
relationalupdate :: Double -> ValueFunction -> ValueFunction -> State -> State -> Reward -> ()
relationalupdate m v1 v2 i j r 
    =   dist (update v1 i j r) (update v2 i j r)
    === dist ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
             ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   triangularIneq ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
                           ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                           ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
    =<= dist ((1 - α) * v1 `at` i + α * (r + γ * v1 `at` j))
             ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
             + dist ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                    ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   linearity (1 - α) (α * (r + γ * v1 `at` j)) (v1 `at` i) (v2 `at` i)
    =<= (1 - α) * dist (v1 `at` i) (v2 `at` i)
             + dist ((1 - α) * v2 `at` i + α * (r + γ * v1 `at` j))
                    ((1 - α) * v2 `at` i + α * (r + γ * v2 `at` j))
        ?   linearity (α * γ) ((1 - α) * v2 `at` i + α * r) (v1 `at` j) (v2 `at` j)
    =<= (1 - α) * dist (v1 `at` i) (v2 `at` i)
        + α * γ * dist (v1 `at` j) (v2 `at` j)
    =<= k * max (dist (v1 `at` i) (v2 `at` i)) (dist (v1 `at` j) (v2 `at` j))
    *** QED

-- {-@ relationalsample'''' :: v1:_ -> v2:_ -> r:_ -> j:_ -> rw1:_ -> rw2:_ -> 
--                             {expDist (sample'''' v1 r j rw1) (sample'''' v2 r j rw2) 
--                                 <= k * max (dist rw1 rw2) (expDist (at v1 j) (at v2 j))} @-}
-- relationalsample'''' :: DistrValueFunction -> DistrValueFunction -> Reward -> State -> Reward -> Reward -> ()
-- relationalsample'''' v1 v2 r j rw1 rw2 
--     =   expDist (sample'''' v1 r j rw1) (sample'''' v2 r j rw2) 
--         ? expDistBindP m (\rw1' rw2' -> dist rw1' rw2' <= expDist (at v1 j) (at v2 j))
--             (update r rw1) (at v1 j)
--             (update r rw2) (at v2 j)
--             (\rw1' rw2' -> 
--                 expDist (update r rw1 rw1') (update r rw2 rw2')
--                     ? relationalupdate r rw1 rw2
--                 =<= k * max (dist rw1 rw2) (dist rw1' rw2')
--                 *** QED)
--     =<= m
--     *** QED    
--     where m = k * max (dist rw1 rw2) (expDist (at v1 j) (at v2 j))

-- {-{-@ relationalmap :: xs1:_ -> {xs2:_|llen xs2 = llen xs1} -> f:_ -> 
--                         (x1:_ -> x2:_ -> {expDist (f x1) (f x2) <= k * expDist x1 x2}) ->
--                         {expDistList (map f xs1) (map f xs2) <= k * expDistList xs1 xs2} @-}
-- relationalmap :: List a -> List a -> (a -> b) -> (a -> a -> ()) -> ()
-- relationalmap xs1 xs2 f = undefined
-- -}

-- {-}
-- {-@ relationalsample :: π:_ -> r:_ -> p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> 
--                     {expDist (sample π r p i v1) (sample π r p i v2) <= k * dist (at v1 i) (at v2 i)} @-}
-- relationalsample :: PolicyMap -> RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> State -> ()
-- relationalsample π r p v1 v2 i
--     =   expDist (sample π r p i v1) (sample π r p i v2) 
--     === expDist (bind (π `at` i) (sample' r p v1 i)) (bind (π `at` i) (sample' r p v2 i))
--         ?   expDistBind m (sample' r p v1 i) (π `at` i)
--                           (sample' r p v2 i) (π `at` i)
--                           (lemma1 r p v1 v2 i)
--     =<= m
--     *** QED
--   where m = k * dist (v1 `at` i) (v2 `at` i)

-- {-@ lemma1 :: r:_ -> p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> 
--                 a:_ -> {expDist (sample' r p v1 i a) (sample' r p v2 i a) <= k * dist (at v1 i) (at v2 i)} @-}
-- lemma1 :: RewardFunction -> TransitionFunction -> ValueFunction -> ValueFunction -> State -> Action -> ()
-- lemma1 r p v1 v2 i a 
--     =   expDist (sample' r p v1 i a) (sample' r p v2 i a)
--     === expDist (bind ((r `at` i) a) (sample'' p v1 i a)) (bind ((r `at` i) a) (sample'' p v2 i a))
--         ?   expDistBind m (sample'' p v1 i a) ((r `at` i) a)
--                           (sample'' p v2 i a) ((r `at` i) a)
--                           (lemma2 p v1 v2 i a)
--     =<= m
--     *** QED
--   where m = k * dist (at v1 i) (at v2 i)

-- {-@ lemma2 :: p:_ -> v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> a:_ ->
--                 rw:_ -> {expDist (sample'' p v1 i a rw) (sample'' p v2 i a rw) <= k * dist (at v1 i) (at v2 i)} @-}
-- lemma2 :: TransitionFunction -> ValueFunction -> ValueFunction -> State -> Action -> Reward -> ()
-- lemma2 p v1 v2 i a rw 
--     =   expDist (sample'' p v1 i a rw) (sample'' p v2 i a rw)
--     === expDist (bind ((p `at` i) a) (update v1 i rw)) (bind ((p `at` i) a) (update v2 i rw))
--         ?   expDistBind m (update v1 i rw) ((p `at` i) a)
--                           (update v2 i rw) ((p `at` i) a)
--                           (lemma3 v1 v2 i a rw)
--     =<= m
--     *** QED
--   where m = k * dist (at v1 i) (at v2 i)

-- {-@ lemma3 :: v1:_ -> {v2:_|llen v1 = llen v2} -> {i:State|i < llen v1} -> a:_ -> rw:_ -> 
--                 {j:State|j < llen v1} -> {expDist (update v1 i rw j) (update v2 i rw j) <= k * dist (at v1 i) (at v2 i)} @-}
-- lemma3 :: ValueFunction -> ValueFunction -> State -> Action -> Reward -> State -> ()
-- lemma3 v1 v2 i a rw j 
--     =   expDist (update v1 i rw j) (update v2 i rw j)
--     === expDist (ppure ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))) 
--                 (ppure ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j)))
--         ? expDistPure ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))
--                       ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j))
--     === dist ((1 - α) * v1 `at` i + α * (rw + γ * v1 `at` j))
--              ((1 - α) * v2 `at` i + α * (rw + γ * v2 `at` j))
--         ?   triangularIneq -- | a + b - c - d | <= | a - c| + | b - d |
--                            -- | a + b | <= | a | + | b |
--     =<= dist ((1 - α) * v1 `at` i) ((1 - α) * v2 `at` i) 
--         + dist (α * (rw + γ * v1 `at` j)) (α * (rw + γ * v2 `at` j))
--         ?   linearity
--     === (1 - α) * dist (v1 `at` i) (v2 `at` i)
--         + α * γ * dist (v1 `at` j) (v2 `at` j)
--         ?   distLTMax
--     =<= (1 - α + α * γ) * maxDist v1 v2
--     === k * maxDist v1 v2
    
--     *** QED
-- -}