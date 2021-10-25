{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{- LIQUID "--ple"            @-}

module Theorem where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Data.Functor.Identity
import           Language.Haskell.Liquid.ProofCombinators
import           Monad.Distr 
import           Data.Dist 


{-@ type StepSize = {v:Double | 0.0 <= v } @-}
type StepSize = Double
{-@ data StepSizes = SSEmp | SS StepSize StepSizes @-}
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint| 0 < len v && 0.0 < lend v } @-}
type DataSet = Set DataPoint
type DataDistr = Distr DataPoint



{-@ assume relationalupdatep :: z1:DataPoint -> α1:StepSize -> f1:LossFunction -> ws1:Weight -> 
                          z2:DataPoint -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> ws2:Weight -> 
                            {dist (update z1 α1 f1 ws1) (update z2  α2 f2 ws2) = dist ws1 ws2 + 2.0 * α1} @-}
relationalupdatep :: DataPoint -> StepSize -> LossFunction -> Weight -> DataPoint -> StepSize -> LossFunction -> Weight -> ()
relationalupdatep _ _ _ _ _ _ _ _ = ()

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double| 0.0 <= v } @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ measure Theorem.update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight @-}
update :: DataPoint -> StepSize -> LossFunction -> Weight -> Weight
update _ w _ _ = w

{-@ reflect one @-}
{-@ one :: {v:Double| v = 1.0 } @-}
one :: Double
one = 1

{-@ assume relationalupdateq :: z1:DataPoint -> ws1:Weight -> α1:StepSize -> f1:LossFunction -> 
                                  {z2:DataPoint|z1 = z2} -> ws2:Weight -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} -> 
                                    {dist (update z1 α1 f1 ws1) (update z2 α2 f2 ws2) = dist ws1 ws2} @-}
relationalupdateq ::  DataPoint -> Weight -> StepSize -> LossFunction -> DataPoint -> Weight -> StepSize -> LossFunction -> ()
relationalupdateq = undefined


{-@ reduce :: p:Double -> ws1:Weight -> ws2:Weight -> {p * dist ws1 ws2 + (1 - p) * dist ws1 ws2 = dist ws1 ws2} @-}
reduce :: Double -> Weight -> Weight -> ()
reduce _ _ _ = ()

{-@ reflect sum @-}
{-@ sum :: StepSizes -> {v:StepSize | 0.0 <= v } @-}
sum :: StepSizes -> Double
sum SSEmp       = 0
sum (SS a as) = a + sum as

{-@ reflect estab @-}
{-@ estab :: DataSet -> StepSizes -> {v:Double | 0.0 <= v} @-}
estab :: DataSet -> StepSizes -> Double
estab zs as = 2.0 / (lend zs) * sum as

{-@ ple estabEmp @-}
estabEmp :: DataSet -> () 
{-@ estabEmp :: zs:DataSet -> {estab zs SSEmp == 0.0} @-}
estabEmp zs = 
      estab zs SSEmp 
  === 2.0 / (lend zs) * sum SSEmp
  *** QED 

{-@ ple estabconsR @-}
{-@ measure Theorem.estabconsR  :: DataSet -> StepSize -> StepSizes -> ()  @-}
{-@ estabconsR :: zs:{DataSet | lend zs /= 0} -> x:StepSize -> xs:StepSizes 
                    -> { estab zs (SS x xs) == 2.0 * x * (one / lend zs) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  ==. 2.0 / (lend zs) * sum (SS x xs)
  ==. 2.0 * x * (one / lend zs) + estab zs xs 
  *** QED 


{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ measure sslen @-}
sslen :: StepSizes -> Int 
{-@ sslen :: StepSizes -> Nat @-}
sslen SSEmp = 0 
sslen (SS _ ss) = 1 + sslen ss 

-- {-@ reflect upd @-}
-- {-@ upd :: zs:{DataSet | 1 < len zs  && 1 < lend zs } -> Weight -> StepSize -> ss:StepSizes -> LossFunction -> DataPoint 
--        -> Distr Weight / [ sslen ss, 1 ] @-}
-- upd ::  DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataPoint -> Distr Weight
-- upd zs w0 α a f z' = update z' w0 α f (sgd zs  a f)

{-
a1 ~ a2 | true
f1 ~ f2 | forall x1 x2. expDist (r1 x1) (r2 x2) <= deltaneq
f1 ~ f2 | forall x. expDist (r1 x) (r2 x) <= deltaeq
___________________________________________________________
bind a1 f1 ~ bind a2 f2 | 1/|S| deltaneq + |S|-1/|S| deltaeq 
-}

{-
a1 ~ a2 | true
f1 ~ f2 | forall ws1 ws2. expDist (f1 ws1) (f2 ws2) <=
     dist ws1 ws2 + estab zs1 α1
___________________________________________________________
             bind a1 f1 ~ bind a2 f2 | 1/|S| deltaneq 
                                      + |S|-1/|S| deltaeq 
-}

{-@ reflect sgdRecUpd @-}
{-@ sgdRecUpd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> StepSize -> ss:StepSizes -> LossFunction 
       -> DataPoint -> Distr Weight / [ sslen ss, 1 ] @-}
sgdRecUpd :: DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataPoint -> Distr Weight
sgdRecUpd zs w0 α a f z = bind (sgd zs w0 a f) (ppure . update z α f)

{-@ reflect sgd @-}
{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> ss:StepSizes -> LossFunction 
       -> Distr Weight / [ sslen ss, 0 ] @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp    _ = ppure w0
sgd zs w0 (SS α a) f = 
  choice (one / lend zs)
         (bind uhead (sgdRecUpd zs w0 α a f))
         (bind utail (sgdRecUpd zs w0 α a f)) -- `rconst` estabconsR zs α a
 where
  uhead = ppure (head zs)
  utail = unif (tail zs)


{-@ reflect rconst @-}
rconst :: a -> b -> a 
rconst x _ = x 


distZero :: Distr a -> Distr a -> ()
{-@ assume distZero :: x1:Distr a -> x2:{Distr a | x1 == x2 } ->  {expDist x1 x2 == 0 }  @-}
distZero _ _ = () 

{-@ assume maxExpDistLess :: m:_ -> f1:_ -> f2:_ -> (x1:_ -> x2:_ -> {expDist (f1 x1) (f2 x2) <= m}) -> { maxExpDist f1 f2 <= m } @-}
maxExpDistLess :: Double -> (a -> Distr b) -> (a -> Distr b) -> (a -> a -> ()) -> ()
maxExpDistLess _ _ _ _ = ()

{-@ assume maxExpDistEqLess :: m:_ -> f1:_ -> f2:_ -> 
                (x:_ -> {expDist (f1 x) (f2 x) <= m}) -> 
                { maxExpDistEq f1 f2 <= m } @-}
maxExpDistEqLess :: Double -> (a -> Distr b) -> (a -> Distr b) -> (a -> a -> ()) -> ()
maxExpDistEqLess _ _ _ _ = ()

{-@ ple thm @-}
{-@ thm :: zs1:{DataSet | 1 < lend zs1 && 1 < len zs1 } -> ws1:Weight -> α1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | 1 < lend zs2 && 1 < len zs2 && lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {α2:StepSizes| α2 = α1} -> {f2:LossFunction|f1 = f2} -> 
            { expDist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= dist ws1 ws2 + estab zs1 α1} @-}
thm :: DataSet -> Weight -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
thm zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2 =
  expDist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    === expDist (ppure ws1) (ppure ws2)
        ? relationalppure ws1 ws2
    === dist ws1 ws2
        ? estabEmp zs1 
    === dist ws1 ws2 + estab zs1 α1
    *** QED 

thm zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 =
  expDist (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    -- === expDist
    --       (choice (one / lend zs1) (pbind uhead1 sgdRec1) (qbind utail1 sgdRec1) `rconst` estabconsR zs1 α1 a1)
    --       (choice (one / lend zs2) (pbind uhead2 sgdRec2) (qbind utail2 sgdRec2) `rconst` estabconsR zs2 α2 a2)
    === expDist
          (choice (one / lend zs1) (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
          (choice (one / lend zs2) (bind uhead2 sgdRec2) (bind utail2 sgdRec2))
    ?   relationalchoice (one / lend zs1) (bind uhead1 sgdRec1) (bind utail1 sgdRec1)
                         (one / lend zs2) (bind uhead2 sgdRec2) (bind utail2 sgdRec2)

    =<= (one / lend zs1) * (expDist (bind uhead1 sgdRec1) (bind uhead2 sgdRec2)) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   leftId (head zs1) sgdRec1 
        ?   leftId (head zs2) sgdRec2 

    =<= (one / lend zs1) * (expDist (sgdRec1 (head zs1)) (sgdRec2 (head zs2))) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
    
    =<= (one / lend zs1) * (expDist (bind (sgd zs1 ws1 a1 f1) pureUpd1) 
                                    (bind (sgd zs2 ws2 a2 f2) pureUpd2)) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   relationalbind (sgd zs1 ws1 a1 f1) pureUpd1 (sgd zs2 ws2 a2 f2) pureUpd2
        
    =<= (one / lend zs1) * (expDist (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2) + maxExpDist pureUpd1 pureUpd2) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   thm zs1 ws1 a1 f1 zs2 ws2 a2 f2

    =<= (one / lend zs1) * (dist ws1 ws2 + estab zs1 a1 + maxExpDist pureUpd1 pureUpd2) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   maxExpDistLess (2 * α1) pureUpd1 pureUpd2 (\ws1' ws2' -> 
              expDist (pureUpd1 ws1') (pureUpd2 ws2')
                  ? expDistPure (update (head zs1) α1 f1 ws1') (update (head zs2) α2 f2 ws2')
              === dist (update (head zs1) α1 f1 ws1') (update (head zs2) α2 f2 ws2')
                  ? relationalupdatep (head zs1) α1 f1 ws1' (head zs2) α2 f2 ws2'
              =<= 2 * α1 
              *** QED)

    =<= (one / lend zs1) * (dist ws1 ws2 + estab zs1 a1 + 2 * α1) 
        + (1 - (one / lend zs1)) * (expDist (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   relationalbind utail1 sgdRec1 utail2 sgdRec2

    =<= (one / lend zs1) * (dist ws1 ws2 + estab zs1 a1 + 2 * α1) 
        + (1 - (one / lend zs1)) * (expDist utail1 utail2 + maxExpDist sgdRec1 sgdRec2)
        ?   expDistEq utail1 utail2

    =<= (one / lend zs1) * (dist ws1 ws2 + estab zs1 a1 + 2 * α1) 
        + (1 - (one / lend zs1)) * (maxExpDist sgdRec1 sgdRec2)
        ?   maxExpDistLess (dist ws1 ws2 + estab zs1 a1) sgdRec1 sgdRec2 (\z1 z2 ->
              expDist (sgdRec1 z1) (sgdRec2 z2)
                  ? relationalbind (sgd zs1 ws1 a1 f1) (ppure . update z1 α1 f1)
                                   (sgd zs2 ws2 a2 f2) (ppure . update z2 α2 f2)
              =<= expDist (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
                  + maxExpDist (ppure . update z1 α1 f1) (ppure . update z2 α2 f2)
                  ? thm zs1 ws1 a1 f1 zs2 ws2 a2 f2
              =<= dist ws1 ws2 + estab zs1 a1 + maxExpDist (ppure . update z1 α1 f1) (ppure . update z2 α2 f2)
              =<= estab zs1 a1
              *** QED)

    =<= (one / lend zs1) * (dist ws1 ws2 + estab zs1 a1 + 2 * α1) 
            + (1 - (one / lend zs1)) * (dist ws1 ws2 + estab zs1 a1)

    =<= dist ws1 ws2 + 2.0 * α1 * (one / lend zs1) + estab zs1 a1
        ?   estabconsR zs1 α1 a1
                            
    =<= dist ws1 ws2 + estab zs1 (SS α1 a1)
    =<= dist ws1 ws2 + estab zs1 as1
    *** QED 
 where
  pureUpd1 = ppure . update (head zs1) α1 f1
  pureUpd2 = ppure . update (head zs2) α2 f2
  sgdRec1 = sgdRecUpd zs1 ws1 α1 a1 f1
  sgdRec2 = sgdRecUpd zs2 ws2 α2 a2 f2
  uhead1 = ppure (head zs1)
  utail1 = unif (tail zs1)
  uhead2 = ppure (head zs2)
  utail2 = unif (tail zs2)
thm zs1 ws1 _ f1 zs2 ws2 _ f2 = ()