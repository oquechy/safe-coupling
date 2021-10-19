{-@ LIQUID "--reflection" @-}


module Monad.Distr where 

import Data.Dist 
type Distr a = a
{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ assume relationalpbind :: e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        { dist (pbind e1 f1) (pbind e2 f2) = dist (f1 e1) (f2 e2) } @-}
relationalpbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b) -> ()
relationalpbind = undefined

{-@ assume relationalqbind :: e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
        { dist (qbind e1 f1) (qbind e2 f2) = dist (f1 e1) (f2 e2)} @-}
relationalqbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b)  ->  ()
relationalqbind = undefined

{-@ measure SGDu.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume pbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ measure SGDu.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume qbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ assume relationalppure :: x1:a -> x2:a 
                    -> { expDist (ppure x1) (ppure x2) = dist x1 x2 } @-}
relationalpure :: a -> a -> () 
relationalchoice _ _ = () 

{-@ measure Monad.Distr.ppure :: a -> Distr a @-}
{-@ ppure :: x:a -> {v:Distr a | v = ppure x } @-}
ppure :: a -> Distr a
ppure x = x

{-@ measure SGDu.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x