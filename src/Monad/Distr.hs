{-@ LIQUID "--reflection" @-}


module Monad.Distr where 

import Data.Dist (dist)

type Distr a = a

{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ measure expDist :: Distr a -> Distr a -> Double @-}
{-@ assume expDist :: x1:_ -> x2:_ -> {v:Double | v == dist x1 x2 } @-}
expDist :: Distr a -> Distr a -> Double
expDist _ _ = 0


-- TODO: CHABGE 

{-@ measure maxExpDist :: Distr a -> Distr a -> Double @-}
{-@  assume maxExpDist :: x1:_ -> x2:_ -> {v:Double | v == maxExpDist x1 x2 && v == 0 } @-}
maxExpDist :: Distr a -> Distr a -> Double
maxExpDist _ _ = 0

-------------------------------------------------------------------------------
-- | Relational Specifications ------------------------------------------------
-------------------------------------------------------------------------------

{-@ assume relationalpbind :: e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        { dist (pbind e1 f1) (pbind e2 f2) == dist (f1 e1) (f2 e2)  } @-}
relationalpbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b) -> ()
relationalpbind = undefined

{-@ assume relationalqbind :: e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
         { dist (qbind e1 f1) (qbind e2 f2) == dist (f1 e1) (f2 e2)  } @-}
relationalqbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b)  ->  ()
relationalqbind = undefined

{-@ assume relationalppure :: x1:a -> x2:a 
                    -> { dist (ppure x1) (ppure x2) = dist x1 x2 } @-}
relationalppure :: a -> a -> () 
relationalppure _ _ = () 

{-@ assume relationalchoice :: p:Prob -> e1:Distr a -> e1':Distr a 
        ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
        ->  { dist (choice p e1 e1') (choice q e2 e2') <= p * (dist e1 e2) + (1.0 - p) * (dist e1' e2')} @-}
relationalchoice :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
relationalchoice _ _ _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | (Non) Implementations ----------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure Monad.Distr.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume pbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ measure Monad.Distr.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume qbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined



{-@ measure Monad.Distr.ppure :: a -> Distr a @-}
{-@ ppure :: x:a -> {v:Distr a | v = Monad.Distr.ppure x } @-}
ppure :: a -> Distr a
ppure x = undefined

{-@ measure Monad.Distr.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

{-@ measure Monad.Distr.unif :: zs:[a] -> Distr a @-}
{-@ assume unif :: x:[a] -> {v:Distr a | v == unif x } @-}
unif :: [a] -> Distr a
unif _ = undefined
