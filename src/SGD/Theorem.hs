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
import           Monad.Distr.Relational.Theorems (bindDistEq)
import           Data.Dist 
import           Data.List 
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
                    -> { estab zs (SS x xs) == 2.0 * lip * x * (1.0 / lend zs) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  === 2.0 * lip / (lend zs) * sum (SS x xs)
  === 2.0 * lip * x * (1.0 / lend zs) + estab zs xs 
  *** QED 

{-@ ple sgdDist @-}
{-@ sgdDist :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> alpha1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {alpha2:StepSizes| alpha2 = alpha1} -> {f2:LossFunction|f1 = f2} -> 
            { dist (kant d) (sgd zs1 ws1 alpha1 f1) (sgd zs2 ws2 alpha2 f2) <= dist d ws1 ws2 + estab zs1 alpha1} / [sslen alpha1, 0]@-}
sgdDist :: Dist Double -> DataSet -> Weight -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
sgdDist d zs1 ws1 alpha1@SSEmp f1 zs2 ws2 alpha2@SSEmp f2 =
  dist (kant d) (sgd zs1 ws1 alpha1 f1) (sgd zs2 ws2 alpha2 f2)
    === dist (kant d) (ppure ws1) (ppure ws2)
        ? pureDist d ws1 ws2
    === dist d ws1 ws2
        ? estabEmp zs1 
    === dist d ws1 ws2 + estab zs1 alpha1
    *** QED 

sgdDist d zs1 ws1 as1@(SS alpha1 a1) f1 zs2 ws2 as2@(SS alpha2 a2) f2 =
  dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    === dist (kant d)
          (choice (one / lend zs1) (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
          (choice (one / lend zs2) (bind uhead2 sgdRec2) (bind utail2 sgdRec2))
    ?   choiceDist d (one / lend zs1) (bind uhead1 sgdRec1) (bind utail1 sgdRec1)
                   (one / lend zs2) (bind uhead2 sgdRec2) (bind utail2 sgdRec2)

    =<= (one / lend zs1) * (dist (kant d) (bind uhead1 sgdRec1) (bind uhead2 sgdRec2)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   leftId (head zs1) sgdRec1 
        ?   leftId (head zs2) sgdRec2 

    =<= (one / lend zs1) * (dist (kant d) (sgdRec1 (head zs1)) (sgdRec2 (head zs2))) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
    
    =<= (one / lend zs1) * (dist (kant d) (bind (sgd zs1 ws1 a1 f1) pureUpd1) 
                                    (bind (sgd zs2 ws2 a2 f2) pureUpd2)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ? pureUpdateEq (head zs1) alpha1 f1
        ? pureUpdateEq (head zs2) alpha2 f2

    =<= (one / lend zs1) * (dist (kant d) (bind (sgd zs1 ws1 a1 f1) (ppure . (update (head zs1) alpha1 f1))) 
                                    (bind (sgd zs2 ws2 a2 f2) (ppure . (update (head zs2) alpha2 f2)))) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

        ?   pureBindDist d d (2 * lip * alpha1) (update (head zs1) alpha1 f1) (sgd zs1 ws1 a1 f1) 
                                    (update (head zs2) alpha2 f2) (sgd zs2 ws2 a2 f2) 
                                    (bounded d (head zs1) alpha1 f1 (head zs2) alpha2 f2) 
        
    =<= (one / lend zs1) * (dist (kant d) (sgd zs1 ws1 a1 f1)  
                                    (sgd zs2 ws2 a2 f2) + (2.0 * lip * alpha1)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

         ? sgdDist d zs1 ws1 a1 f1 zs2 ws2 a2 f2
         ? assert (dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2) <= dist d ws1 ws2 + estab zs1 a1)
    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * alpha1)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ? bindDistEq d (dist d ws1 ws2 + estab zs1 a1) sgdRec1 utail1 sgdRec2 utail2
                     (lemma d zs1 ws1 alpha1 a1 f1 zs2 ws2 alpha2 a2 f2)
        ? assert (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2) <= dist d ws1 ws2 + estab zs1 a1)
        ? assert (0 <= (1 - (one / lend zs1)))
        ? multHelper ((one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * alpha1))) (1 - (one / lend zs1)) 
                 (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
                 (dist d ws1 ws2 + estab zs1 a1)
    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * alpha1)) 
        + (1 - (one / lend zs1)) * (dist d ws1 ws2 + estab zs1 a1)

    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * alpha1)) 
            + (1 - (one / lend zs1)) * (dist d ws1 ws2 + estab zs1 a1)

    =<= dist d ws1 ws2 + 2.0 * lip * alpha1 * (one / lend zs1) + estab zs1 a1
        ?   estabconsR zs1 alpha1 a1
                            
    =<= dist d ws1 ws2 + estab zs1 (SS alpha1 a1)
    =<= dist d ws1 ws2 + estab zs1 as1
    *** QED
 where
  pureUpd1 = pureUpdate (head zs1) alpha1 f1
  pureUpd2 = pureUpdate (head zs2) alpha2 f2
  sgdRec1 = sgdRecUpd zs1 ws1 alpha1 a1 f1
  sgdRec2 = sgdRecUpd zs2 ws2 alpha2 a2 f2
  uhead1 = ppure (head zs1)
  utail1 = unif (tail zs1)
  uhead2 = ppure (head zs2)
  utail2 = unif (tail zs2)
  one = 1.0
sgdDist d zs1 ws1 _ f1 zs2 ws2 _ f2 = ()

{-@ multHelper :: a:Double -> b:{Double | 0 <= b} -> c:Double -> d:{Double | c <= d } 
               -> { a + b * c <= a + b * d }  @-}
multHelper :: Double -> Double -> Double -> Double -> () 
multHelper _ _ _ _ = ()

{-@ lemma :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> alpha1:StepSize -> a1:StepSizes -> f1:LossFunction -> 
             zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
             ws2:Weight -> alpha2:{StepSize | alpha1 = alpha2} -> {a2:StepSizes| a2 = a1} -> f2:{LossFunction|f1 = f2} ->  
             z:DataPoint -> 
             {dist (kant d) (sgdRecUpd zs1 ws1 alpha1 a1 f1 z) (sgdRecUpd zs2 ws2 alpha2 a2 f2 z) <= dist d ws1 ws2 + estab zs1 a1} / [sslen a1, 1] @-}
lemma :: Dist Double -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSize ->  StepSizes -> LossFunction -> DataPoint -> ()
lemma d zs1 ws1 alpha1 a1 f1 zs2 ws2 alpha2 a2 f2 z = 
  dist (kant d) (sgdRecUpd zs1 ws1 alpha1 a1 f1 z) (sgdRecUpd zs2 ws2 alpha2 a2 f2 z)
        ?   pureUpdateEq z alpha1 f1
        ?   pureUpdateEq z alpha2 f2
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (pureUpdate z alpha1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (pureUpdate z alpha2 f2))
        ?   pureBindDist d d 0 (update z alpha1 f1) (sgd zs1 ws1 a1 f1)
                             (update z alpha2 f2) (sgd zs2 ws2 a2 f2) 
                             (contractive d z alpha1 f1 z alpha2 f2)
    =<= dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
        ? sgdDist d zs1 ws1 a1 f1 zs2 ws2 a2 f2
    =<= dist d ws1 ws2 + estab zs1 a1
    *** QED

{-@ assume pureUpdateEq :: zs:DataPoint -> a:StepSize -> f:LossFunction
               -> {pureUpdate zs a f == ppure . (update zs a f)} @-}
pureUpdateEq :: DataPoint -> StepSize -> LossFunction -> ()
pureUpdateEq zs a f = ()
