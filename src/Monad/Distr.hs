{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"     @-}

module Monad.Distr where 

import Data.Dist (dist, distList)
import Data.List 

import Prelude hiding (max)

data Distr a = Distr a

{-@ reflect bounded @-}
bounded :: Double -> List Double -> List Double -> Bool
bounded m v1' v2' = distList v1' v2' <= m

{-@ reflect bounded' @-}
bounded' :: Double -> Double -> Double -> Bool
bounded' m x1 x2 = dist x1 x2 <= m

{-@ boundedNil :: {m:_|0 <= m} -> {bounded m Nil Nil} @-}
boundedNil :: Double -> ()
boundedNil _ = ()

{-@ reflect eqP @-}
eqP :: Eq a => a -> a -> Bool
eqP = (==)

-- TODO: replace with BijCoupling
{-@ assume liftEq :: e:Distr a -> {lift eqP e e} @-}
liftEq :: Distr a -> ()
liftEq _ = ()

{-@ assume liftPure :: p:(a -> b -> Bool) 
                    -> x1:a -> x2:b -> {_:_|p x1 x2} 
                    -> {lift p (ppure x1) (ppure x2)} @-}
liftPure :: (a -> b -> Bool) -> a -> b -> () -> ()
liftPure _ _ _ _ = ()

{-@ reflect ppureDouble @-}
{-@ ppureDouble :: xs:List Double -> Distr ({v:List Double | llen v == llen xs}) @-}
ppureDouble :: List Double -> Distr (List Double)
ppureDouble x = ppure x 

--              (x1:_ -> {x2:_|q x1 x2} -> {lift p (f1 x1) (f2 x2)}) ->
{-@ assume liftBind :: p:(b -> b -> Bool) -> q:(a -> a -> Bool) -> 
                e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) ->   
                {_:()|lift q e1 e2} ->
                (x1:a -> {x2:a|q x1 x2} -> {true}) ->
                {lift p (bind e1 f1) (bind e2 f2)} @-}
liftBind :: (b -> b -> Bool) -> (a -> a -> Bool) -> 
              Distr a -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> 
              () ->
              (a -> a -> ()) -> 
              ()
liftBind _ _ _ _ _ _ _ _ = ()

{-@ measure Monad.Distr.lift :: (a -> b -> Bool) -> Distr a -> Distr b -> Bool @-}
{-@ assume lift :: p1:(a -> b -> Bool) -> x1:Distr a -> x2:Distr b -> {v:Bool | v == Monad.Distr.lift p1 x1 x2} @-}
lift :: (a -> b -> Bool) -> Distr a -> Distr b -> Bool
lift p e1 e2 = True

{-@ reflect trueP @-}
trueP :: a -> a -> Bool 
trueP _ _ = True 

  {- do
      x1 <- e1
      x2 <- e2
      return (p x1 x2) -}

{-@ assume expDistPure :: x1:a -> x2:a -> {expDist (ppure x1) (ppure x2) = dist x1 x2} @-}
expDistPure :: a -> a -> ()
expDistPure _ _ = ()

{-@ assume expDistEq :: x1:Distr a -> {x2:Distr a | x1 = x2 } -> {expDist x1 x2 = 0} @-}
expDistEq :: Distr a -> Distr a -> ()
expDistEq _ _ = ()


-- CHECK IF THIS IS CORRECT 
{-@ ple relUnitBindTry @-}
{-@ assume relUnitBindTry :: m:Double 
                          -> f1:(a -> b) -> e1:Distr a 
                          -> f2:(a -> b) -> e2:Distr a 
                          -> (x1:a -> x2:a -> { dist (f1 x1) (f2 x2) <= dist x1 x2 + m}) 
                          -> { expDist (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= expDist e1 e2 + m } @-}
relUnitBindTry :: Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
relUnitBindTry m f1 e1 f2 e2 t = () --  maxExpDistLemma e1 e2 `const` relUnitBind m f1 e1 f2 e2 t


{-@ assume relUnitBind :: m:Double 
                          -> f1:(a -> b) -> e1:Distr a 
                          -> f2:(a -> b) -> e2:Distr a 
                          -> (x1:a -> x2:a -> { dist (f1 x1) (f2 x2) <= dist x1 x2 + m}) 
                          -> { expDist (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= maxExpDist e1 e2 + m } @-}
relUnitBind :: Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
relUnitBind _ _ _ _ _ _ = ()



{-@ assume expDistBind :: m:Double 
                          -> f1:(a -> Distr b) -> e1:Distr a 
                          -> f2:(a -> Distr b) -> e2:{Distr a | BijCoupling e1 e2 } 
                          -> (x:a -> { expDist (f1 x) (f2 x) <= m}) 
                          -> { expDist (bind e1 f1) (bind e2 f2) <= m } @-}
expDistBind :: Double -> (a -> Distr b) -> Distr a -> (a -> Distr b) ->  Distr a ->  (a -> ()) -> ()
expDistBind _ _ _ _ _ _ = ()

{-@ assume expDistBindP :: m:Double -> p:(a -> a -> Bool )
                -> f1:(a -> Distr b) -> e1:Distr a 
                -> f2:(a -> Distr b) -> e2:{Distr a | lift p e1 e2 } 
                -> lemma:(x1:a -> {x2:a|p x1 x2} -> { expDist (f1 x1) (f2 x2) <= m}) 
                -> { expDist (bind e1 f1) (bind e2 f2) <= m } @-}
expDistBindP :: Double -> (a -> a -> Bool) -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> Distr a -> (a -> a -> ()) -> ()
expDistBindP _ _ _ _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | (Non) Definitions --------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate BijCoupling X Y = true @-}

{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ assume maxExpDistLemma :: x1:Distr a -> x2:Distr a -> { expDist x1 x2 <=  maxExpDist x1 x2 } @-}
maxExpDistLemma :: Distr a -> Distr a -> ()
maxExpDistLemma _ _ = ()

{-@ measure maxExpDist :: Distr a -> Distr a -> Double @-}
{-@ assume maxExpDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == maxExpDist x1 x2 } @-}
maxExpDist :: Distr a -> Distr a -> Double
maxExpDist _ _ = 0


{-@ measure Monad.Distr.expDist :: Distr a -> Distr a -> Double @-}
{-@ assume expDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == Monad.Distr.expDist x1 x2 } @-}
expDist :: Distr a -> Distr a -> Double
expDist _ _ = 0

{-@ measure expDistList :: List (Distr a) -> List (Distr b) -> Double @-}
{-@ assume expDistList :: xs1:List (Distr a) -> xs2:List (Distr a) -> {v:Double | v == expDistList xs1 xs2 } @-}
expDistList :: List (Distr a) -> List (Distr a) -> Double
expDistList Nil _ = 0 
expDistList _ Nil = 0 
expDistList (Cons x xs) (Cons y ys) = max (expDist x y) (expDistList xs ys)

-------------------------------------------------------------------------------
-- | Relational Specifications ------------------------------------------------
-------------------------------------------------------------------------------
{-@ assume relationalppure :: x1:a -> x2:a 
                    -> { dist (ppure x1) (ppure x2) = dist x1 x2 } @-}
relationalppure :: a -> a -> () 
relationalppure _ _ = () 

{-@ assume leftId :: x:a -> f:(a -> Distr b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> Distr b) -> ()
leftId _ _ = ()

{-@ assume relationalchoice :: p:Prob -> e1:Distr a -> e1':Distr a 
        ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
        ->  { dist (choice p e1 e1') (choice q e2 e2') <= p * (dist e1 e2) + (1.0 - p) * (dist e1' e2')} @-}
relationalchoice :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
relationalchoice _ _ _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | (Non) Implementations ----------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure Monad.Distr.bind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume bind :: forall <p :: a -> Bool>.x1:Distr a<p> -> x2:(a<p> -> Distr b) -> {v:Distr b | v = bind x1 x2 } @-}
bind :: Distr a -> (a -> Distr b) -> Distr b
bind = undefined

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
