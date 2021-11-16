{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}
{-@ LIQUID "--no-termination" @-}


module SGDr where

import           Prelude                 hiding ( head
                                                , tail
                                                )
import           Data.Functor.Identity
import           Language.Haskell.Liquid.ProofCombinators

{-@ infix : @-}
{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ type StepSize = {v:Double | 0.0 <= v } @-}
type StepSize = Double
{-@ data StepSizes = SSEmp | SS StepSize StepSizes @-}
data StepSizes = SSEmp | SS StepSize StepSizes
type DataPoint = (Double, Double)
type Weight = Double
type LossFunction = DataPoint -> Weight -> Double

type Set a = [a]
{-@ type DataSet = {v:Set DataPoint| 1 < len v && 1.0 < lend v } @-}
type DataSet = Set DataPoint
type Distr a = a
type DataDistr = Distr DataPoint

{-@ measure dist :: a -> a -> Double @-}
{-@ assume dist :: x1:_ -> x2:_ -> {v:Double | v == dist x1 x2 } @-}
dist :: a -> a -> Double
dist _ _ = 0

{-@ assume relational choice ~ choice 
        :: p:_ -> e1:_ -> e1':_ -> _
         ~ q:_ -> e2:_ -> e2':_ -> _
        ~~ p = q => true => true => 
            dist (r1 p e1 e1') (r2 q e2 e2') <= p * (dist e1 e2) + (1 - p) * (dist e1' e2') @-}

{-@ choice :: Prob -> Distr a -> Distr a -> Distr a @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

unif :: DataSet -> DataDistr
unif = undefined

{-@ reflect rconst @-}
rconst :: a -> b -> a 
rconst x _ = x

{-@ relational rconst ~ rconst :: a1:_ -> b1:_ -> _
                                ~ a2:_ -> b2:_ -> _ 
                               ~~ r1 a1 b1 = a1 && r2 a2 b2 = a2 @-}

{-@ assume relational update ~ update 
      :: z1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
       ~ z2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
      ~~ true => true => α1 = α2 => f1 = f2 => 
          dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) = dist ws1 ws2 @-}

{-@ assume relational update ~ update 
      :: z1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
       ~ z2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
      ~~ z1 = z2 => true => α1 = α2 => f1 = f2 => 
          dist (r1 z1 ws1 α1 f1) (r2 z2 ws2 α2 f2) = dist ws1 ws2 @-}

update :: DataPoint -> Weight -> StepSize -> LossFunction -> Weight
update = undefined

{-@ reflect one @-}
{-@ one :: {v:Double|v = 1} @-}
one :: Double
one = 1

{-@ measure lend @-}
{-@ lend :: xs:[a] -> {v:Double|v >= 0} @-}
lend :: [a] -> Double
lend []       = 0
lend (_ : xs) = 1 + lend xs

{-@ assume relational pbind ~ pbind :: e1:_ -> f1:_ -> _
                                     ~ e2:_ -> f2:_ -> _
                                    ~~ true => true =>
                                          dist (r1 e1 f1) (r2 e2 f2) = dist (f1 e1) (f2 e2) @-}

{-@ assume relational qbind ~ qbind :: e1:_ -> f1:_ -> _
                                     ~ e2:_ -> f2:_ -> _
                                    ~~ e1 = e2 => true =>
                                          dist (r1 e1 f1) (r2 e2 f2) = dist (f1 e1) (f2 e2) @-}

pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ reflect ppure @-}
ppure :: a -> Distr a
ppure x = x

{-@ reflect head @-}
{-@ head :: {xs:[a] | len xs > 0 } -> a @-}
head :: [a] -> a
head (z : _) = z

{-@ reflect tail @-}
{-@ tail :: {xs:[a] | len xs > 0 } -> {v:[a] | len v == len xs - 1 && lend v == lend xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : zs) = zs

{-@ sgd :: zs:{DataSet | 1 < len zs && 1 < lend zs } -> Weight -> StepSizes -> LossFunction -> Distr Weight @-}
sgd :: DataSet -> Weight -> StepSizes -> LossFunction -> Distr Weight
sgd _  w0 SSEmp      _ = let lemma = undefined in ppure w0
sgd zs w0 (SS a α) f   = choice (one / lend zs)
                             (pbind uhead upd)
                             (qbind utail upd) 
                             `rconst` (
                                    dist (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
                                    ==. (one / lend zs1) * (dist (updWs1 uhead1) (updWs2 uhead2)) 
                                          + (one - (one / lend zs1)) * (dist (qbind utail1 updWs1) (qbind utail2 updWs2))
                                    ==. (one / lend zs1) * (dist ws1 ws2) 
                                                + (one - (one / lend zs1)) * (dist (updWs1 utail1) (updWs2 utail2)) 
                             )
 where
  upd z' = sgd zs (update z' w0 a f) α f
  uhead = unif [head zs]
  uhead2 = uhead
  uhead1 = uhead
  updWs1 = upd
  updWs2 = upd
  utail = unif (tail zs)
  utail1 = utail
  utail2 = utail
  zs1 = zs 
  zs2 = zs 
  f1 = f 
  f2 = f 
  a1 = a
  a2 = a
  ws1 = w0
  ws2 = w0
  α1 = α
  α2 = α

{-@ relational sgd ~ sgd :: zs1:_ -> ws1:_ -> α1:_ -> f1:_ -> _ 
                            ~ zs2:_ -> ws2:_ -> α2:_ -> f2:_ -> _
                           ~~ 1 < SGDr.lend zs1 && 1 < len zs1 && 1 < SGDr.lend zs2 && 1 < len zs2 
                                && SGDr.lend zs1 ==SGDr.lend zs2 && SGDr.tail zs1 = SGDr.tail zs2 =>
                                  true => α2 = α1 => f1 = f2 => 
                                    SGDr.dist (r1 zs1 ws1 α1 f1) (r2 zs2 ws2 α2 f2) <= SGDr.dist ws1 ws2
@-}
