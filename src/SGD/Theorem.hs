{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple-local"      @-}

module SGD.Theorem where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Language.Haskell.Liquid.ProofCombinators

import           Misc.ProofCombinators

import           Monad.Distr 
import           Monad.Distr.Laws
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Relational.Theorems
import           Data.Dist 
import           Data.List 
import           SGD.DataPointDist
import           SGD.SGD 

-----------------------------------------------------------------
-- | Assumptions ------------------------------------------------
-----------------------------------------------------------------

{-@ measure SGD.Theorem.lip :: Double @-}
{-@ assume lip :: {v:Double|SGD.Theorem.lip = v && v >= 0 } @-}
lip :: Double
lip = 10

{-@ assume bounded :: d:Dist Double -> z1:DataPoint -> alpha1:StepSize -> f1:LossFunction 
                             -> z2:DataPoint -> {alpha2:StepSize|alpha1 = alpha2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 alpha1 f1 ws1) (update z2  alpha2 f2 ws2) = dist d ws1 ws2 + 2.0 * lip * alpha1 } @-}
bounded :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
bounded _ _ _ _ _ _ _ _ _ = ()


{-@ assume contractive :: d:Dist Double -> z1:DataPoint -> alpha1:StepSize -> f1:LossFunction 
                             -> {z2:DataPoint|z1 = z2} -> {alpha2:StepSize|alpha1 = alpha2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 alpha1 f1 ws1) (update z2  alpha2 f2 ws2) = dist d ws1 ws2} @-}
contractive :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
contractive = undefined

-----------------------------------------------------------------
-- | Proof ------------------------------------------------------
-----------------------------------------------------------------

{-@ reflect sum @-}
{-@ sum :: StepSizes -> {v:StepSize | 0.0 <= v } @-}
sum :: StepSizes -> Double
sum SSEmp       = 0
sum (SS a as) = a + sum as

{-@ reflect estab @-}
{-@ estab :: DataSet -> StepSizes -> {v:Double | 0.0 <= v} @-}
estab :: DataSet -> StepSizes -> Double
estab zs as = 2.0 * lip / (lend zs) * sum as

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
                    -> { estab zs (SS x xs) == 2.0 * lip * x * (mydiv 1.0 (lend zs)) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  === 2.0 * lip / (lend zs) * sum (SS x xs)
  === 2.0 * lip * x * (1.0 / lend zs) + estab zs xs 
  === 2.0 * lip * x * (mydiv 1.0 (lend zs)) + estab zs xs 
  *** QED 

{-@ ple sgdDist @-}
{-@ sgdDist :: d:Dist Double 
        -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]|1 <= len zs}
        -> {zs1:DataSet|isPermutation (cons' x zs) zs1} -> ws1:Weight -> as1:StepSizes -> f1:LossFunction 
        -> {zs2:DataSet|isPermutation (cons' y zs) zs2} -> ws2:Weight -> {as2:StepSizes|as2 = as1} 
        -> {f2:LossFunction|f1 = f2}
        -> {dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2) <= dist d ws1 ws2 + estab zs1 as1} / [sslen as1, 0]@-}
sgdDist :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] 
    -> DataSet -> Weight -> StepSizes -> LossFunction 
    -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
sgdDist d x y zs zs1 ws1 alpha1@SSEmp f1 zs2 ws2 alpha2@SSEmp f2 =
  dist (kant d) (sgd zs1 ws1 alpha1 f1) (sgd zs2 ws2 alpha2 f2)
    === dist (kant d) (ppure ws1) (ppure ws2)
        ? pureDist d ws1 ws2
    =<= dist d ws1 ws2
        ? estabEmp zs1 
    =<= dist d ws1 ws2 + estab zs1 alpha1
    *** QED 

sgdDist d x y zs zs1 ws1 as1@(SS alpha1 a1) f1 zs2 ws2 as2@(SS alpha2 a2) f2 
    = dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    === dist (kant d) (bind (unif zs1) sgdRec1) 
                      (bind (unif zs2) sgdRec2)
        ?   unifPermut distDataPoint xs zs1 
    === dist (kant d) (bind (unif xs) sgdRec1) 
                      (bind (unif zs2) sgdRec2)
        ?   unifPermut distDataPoint ys zs2
    === dist (kant d) (bind (unif (cons' x zs)) sgdRec1) 
                      (bind (unif (cons' y zs)) sgdRec2)
        ?   unifChoice x zs 
        ?   assert (unif (cons' x zs) == choice (mydiv 1.0 (lend (cons' x zs))) (ppure x) (unif zs))
        ?   unifChoice y zs
        ?   assert (unif (cons' y zs) == choice (mydiv 1.0 (lend (cons' y zs))) (ppure y) (unif zs))
    === dist (kant d) (bind (choice (1.0 `mydiv` lend (cons' x zs)) uhead1 utail1) sgdRec1)
                      (bind (choice (1.0 `mydiv` lend (cons' y zs)) uhead2 utail2) sgdRec2)
    === dist (kant d)
            (bind (choice p uhead1 utail1) sgdRec1)
            (bind (choice p uhead2 utail2) sgdRec2)
        ? choiceBind p uhead1 utail1 sgdRec1
    === dist (kant d)
            (choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
            (bind (choice p uhead2 utail2) sgdRec2)
        ? choiceBind p uhead2 utail2 sgdRec2
    === dist (kant d)
          (choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
          (choice p (bind uhead2 sgdRec2) (bind utail2 sgdRec2))
        ?   choiceDist d p (bind uhead1 sgdRec1) (bind utail1 sgdRec1)
                         p (bind uhead2 sgdRec2) (bind utail2 sgdRec2)
        ? assert (dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2) 
              == dist (kant d)
          (choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
          (choice p (bind uhead2 sgdRec2) (bind utail2 sgdRec2)))
    =<= p * (dist (kant d) (bind uhead1 sgdRec1) (bind uhead2 sgdRec2)) 
            + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   sgdDistNeq d x y zs zs1 ws1 zs2 ws2 alpha1 a1 f1
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * alpha1) 
            + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   sgdDistEq d x y zs zs1 ws1 zs2 ws2 alpha1 a1 f1
        ? assert (alpha1 == alpha2)
       ? assert (dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 alpha1 a1 f1)) 
                               (bind (unif zs) (sgdRecUpd zs2 ws2 alpha1 a1 f1))  
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 alpha1 a1 f1)) 
                               (bind (unif zs) (sgdRecUpd zs2 ws2 alpha2 a2 f2))  
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2)
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (0.0 <= 1.0 - p )
       ? assert (
           p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * alpha1) 
            + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
          <= 
           p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * alpha1) 
            + (1.0 - p) * (dist d ws1 ws2 + estab zs1 a1)   
       )
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * alpha1) 
            + (1.0 - p) * (dist d ws1 ws2 + estab zs1 a1)
    =<= dist d ws1 ws2 + 2.0 * lip * alpha1 * p + estab zs1 a1
        ?   permutLen xs zs1
        ?   assert (lend zs1 == lend (cons' x zs))
        ?   estabconsR zs1 alpha1 a1
    =<= dist d ws1 ws2 + estab zs1 (SS alpha1 a1)
    =<= dist d ws1 ws2 + estab zs1 as1
    *** QED
 where
  p = 1.0 `mydiv` lend (cons' x zs)
  pureUpd1 = pureUpdate x alpha1 f1
  pureUpd2 = pureUpdate y alpha2 f2
  sgdRec1 = sgdRecUpd zs1 ws1 alpha1 a1 f1
  sgdRec2 = sgdRecUpd zs2 ws2 alpha2 a2 f2
  uhead1 = ppure x
  utail1 = unif zs
  uhead2 = ppure y
  utail2 = unif zs
  xs = cons' x zs
  ys = cons' y zs
sgdDist _ _ _ d zs1 ws1 _ f1 zs2 ws2 _ f2 = ()

{-@ ple sgdDistNeq @-}
{-@ sgdDistNeq :: d:Dist Double -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
           -> {zs1:DataSet|isPermutation (cons' x zs) zs1}
           -> ws1:Weight
           -> {zs2:DataSet|isPermutation (cons' y zs) zs2}
           -> ws2:Weight 
           -> alpha:StepSize -> alphas:StepSizes -> f:LossFunction 
           -> { dist (kant d) (bind (ppure x) (sgdRecUpd zs1 ws1 alpha alphas f)) 
                              (bind (ppure y) (sgdRecUpd zs2 ws2 alpha alphas f)) 
                <= dist d ws1 ws2 + estab zs1 alphas + 2.0 * lip * alpha} / [sslen alphas, 1] @-}
sgdDistNeq :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> ()
sgdDistNeq d x y zs zs1 ws1 zs2 ws2 alpha alphas f
    =   dist (kant d) (bind (ppure x) (sgdRecUpd zs1 ws1 alpha alphas f)) 
                      (bind (ppure y) (sgdRecUpd zs2 ws2 alpha alphas f))
    === dist (kant d) (bind (ppure x) sgdRec1) 
                      (bind (ppure y) sgdRec2)
        ?   leftId x sgdRec1 
        ?   leftId y sgdRec2 
    === dist (kant d) (sgdRec1 x) (sgdRec2 y)
    === dist (kant d) (bind (sgd zs1 ws1 alphas f) pureUpd1) 
                      (bind (sgd zs2 ws2 alphas f) pureUpd2)
        ?   pureUpdateEq x alpha f
        ?   pureUpdateEq y alpha f
    === dist (kant d) (bind (sgd zs1 ws1 alphas f) (ppure . update x alpha f)) 
                      (bind (sgd zs2 ws2 alphas f) (ppure . update y alpha f))
        ?   pureBindDist d d (2.0 * lip * alpha) (update x alpha f) (sgd zs1 ws1 alphas f) 
                                       (update y alpha f) (sgd zs2 ws2 alphas f) 
                                       (bounded d x alpha f y alpha f)
    =<= dist (kant d) (sgd zs1 ws1 alphas f) (sgd zs2 ws2 alphas f) + 2.0 * lip * alpha
        ?   sgdDist d x y zs zs1 ws1 alphas f zs2 ws2 alphas f
    =<= dist d ws1 ws2 + estab zs1 alphas + 2.0 * lip * alpha
    *** QED
    where   
        pureUpd1 = pureUpdate x alpha f
        pureUpd2 = pureUpdate y alpha f
        sgdRec1 = sgdRecUpd zs1 ws1 alpha alphas f
        sgdRec2 = sgdRecUpd zs2 ws2 alpha alphas f
        uhead1 = ppure x
        uhead2 = ppure y

{-@ ple sgdDistEq @-}
{-@ sgdDistEq :: d:Dist Double -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
          -> {zs1:DataSet|isPermutation (cons' x zs) zs1}
          -> ws1:Weight
          -> {zs2:DataSet|isPermutation (cons' y zs) zs2}
          -> ws2:Weight
          -> alpha:StepSize -> alphas:StepSizes -> f:LossFunction 
          -> { dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 alpha alphas f)) 
                              (bind (unif zs) (sgdRecUpd zs2 ws2 alpha alphas f)) 
                <= dist d ws1 ws2 + estab zs1 alphas } / [sslen alphas, 2] @-}
sgdDistEq :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> ()
sgdDistEq d x y zs zs1 ws1 zs2 ws2 alpha alphas f 
    =   dist (kant d) (bind (unif zs) sgdRec1) 
                      (bind (unif zs) sgdRec2)
        ?   bindDistEq d (dist d ws1 ws2 + estab zs1 alphas) 
                       sgdRec1 utail sgdRec2 utail
                       (lemma d x y zs zs1 ws1 alpha alphas f zs2 ws2 alpha alphas f)
    =<= dist d ws1 ws2 + estab zs1 alphas
    *** QED
    where
        sgdRec1 = sgdRecUpd zs1 ws1 alpha alphas f
        sgdRec2 = sgdRecUpd zs2 ws2 alpha alphas f
        utail = unif zs

{-@ lemma :: d:Dist Double
          -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
          -> {zs1:DataSet|isPermutation (cons' x zs) zs1}
          -> ws1:Weight
          -> alpha1:StepSize -> a1:StepSizes -> f1:LossFunction
          -> {zs2:DataSet|isPermutation (cons' y zs) zs2}
          -> ws2:Weight -> alpha2:{StepSize|alpha1 = alpha2} -> {a2:StepSizes|a2 = a1} -> f2:{LossFunction|f1 = f2} 
          -> z:DataPoint 
          -> {dist (kant d) (sgdRecUpd zs1 ws1 alpha1 a1 f1 z) (sgdRecUpd zs2 ws2 alpha2 a2 f2 z) <= dist d ws1 ws2 + estab zs1 a1} / [sslen a1, 1] @-}
lemma :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSize ->  StepSizes -> LossFunction -> DataPoint -> ()
lemma d x y zs zs1 ws1 alpha1 a1 f1 zs2 ws2 alpha2 a2 f2 z = 
  dist (kant d) (sgdRecUpd zs1 ws1 alpha1 a1 f1 z) (sgdRecUpd zs2 ws2 alpha2 a2 f2 z)
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (pureUpdate z alpha1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (pureUpdate z alpha2 f2))
        ? pureUpdateEq z alpha1 f1
        ? pureUpdateEq z alpha2 f2
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (ppure . update z alpha1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (ppure . update z alpha2 f2))
        ?   pureBindDist d d 0 (update z alpha1 f1) (sgd zs1 ws1 a1 f1)
                               (update z alpha2 f2) (sgd zs2 ws2 a2 f2) 
                               (contractive d z alpha1 f1 z alpha2 f2)
    =<= dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
        ?   sgdDist d x y zs zs1 ws1 a1 f1 zs2 ws2 a2 f2
    =<= dist d ws1 ws2 + estab zs1 a1
    *** QED

{-@ assume pureUpdateEq :: zs:DataPoint -> a:StepSize -> f:LossFunction
               -> {pureUpdate zs a f == ppure . update zs a f} @-}
pureUpdateEq :: DataPoint -> StepSize -> LossFunction -> ()
pureUpdateEq zs a f = () 
