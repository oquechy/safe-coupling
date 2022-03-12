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

import           Monad.PrM 
import           Monad.PrM.Laws
import           Monad.PrM.Relational.TCB.EDist
import           Monad.PrM.Relational.Theorems (bindDistEq)
import           Data.Dist 
import           SGD.SGD 


{-@ measure SGD.Theorem.lip :: Double @-}
{-@ assume lip :: {v:Double|SGD.Theorem.lip = v && v >= 0 } @-}
lip :: Double
lip = 10


{-@ assume relationalupdatep :: d:Dist Double -> z1:DataPoint -> α1:StepSize -> f1:LossFunction 
                             -> z2:DataPoint -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 α1 f1 ws1) (update z2  α2 f2 ws2) = dist d ws1 ws2 + 2.0 * lip * α1 } @-}
relationalupdatep :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
relationalupdatep _ _ _ _ _ _ _ _ _ = ()


{-@ assume relationalupdateq :: d:Dist Double -> z1:DataPoint -> α1:StepSize -> f1:LossFunction 
                             -> {z2:DataPoint|z1 = z2} -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 α1 f1 ws1) (update z2  α2 f2 ws2) = dist d ws1 ws2} @-}
relationalupdateq :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
relationalupdateq = undefined


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
                    -> { estab zs (SS x xs) == 2.0 * lip * x * (one / lend zs) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  === 2.0 * lip / (lend zs) * sum (SS x xs)
  === 2.0 * lip * x * (one / lend zs) + estab zs xs 
  *** QED 

{-@ ple thm @-}
{-@ thm :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> α1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {α2:StepSizes| α2 = α1} -> {f2:LossFunction|f1 = f2} -> 
            { dist (kant d) (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= dist d ws1 ws2 + estab zs1 α1} / [sslen α1, 0]@-}
thm :: Dist Double -> DataSet -> Weight -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
thm d zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2 =
  dist (kant d) (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    === dist (kant d) (ppure ws1) (ppure ws2)
        ? pureDist d ws1 ws2
    === dist d ws1 ws2
        ? estabEmp zs1 
    === dist d ws1 ws2 + estab zs1 α1
    *** QED 

thm d zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 =
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
        ? pureUpdateEq (head zs1) α1 f1
        ? pureUpdateEq (head zs2) α2 f2

    =<= (one / lend zs1) * (dist (kant d) (bind (sgd zs1 ws1 a1 f1) (ppure . update (head zs1) α1 f1 )) 
                                    (bind (sgd zs2 ws2 a2 f2) (ppure . update (head zs2) α2 f2 ))) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

        ?   pureBindDist d d (2 * lip * α1) (update (head zs1) α1 f1) (sgd zs1 ws1 a1 f1) 
                                    (update (head zs2) α2 f2) (sgd zs2 ws2 a2 f2) 
                                    (relationalupdatep d (head zs1) α1 f1 (head zs2) α2 f2) 
        
    =<= (one / lend zs1) * (dist (kant d) (sgd zs1 ws1 a1 f1)  
                                    (sgd zs2 ws2 a2 f2) + (2.0 * lip * α1)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

         ? thm d zs1 ws1 a1 f1 zs2 ws2 a2 f2
         ? assert (dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2) <= dist d ws1 ws2 + estab zs1 a1)
    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
        + (1 - (one / lend zs1)) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ? bindDistEq d (dist d ws1 ws2 + estab zs1 a1) sgdRec1 utail1 sgdRec2 utail2
                     (lemma d zs1 ws1 α1 a1 f1 zs2 ws2 α2 a2 f2)
        ? assert (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2) <= dist d ws1 ws2 + estab zs1 a1)
        ? assert (0 <= (1 - (one / lend zs1)))
        ? multHelper ((one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1))) (1 - (one / lend zs1)) 
                 (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
                 (dist d ws1 ws2 + estab zs1 a1)
    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
        + (1 - (one / lend zs1)) * (dist d ws1 ws2 + estab zs1 a1)

    =<= (one / lend zs1) * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
            + (1 - (one / lend zs1)) * (dist d ws1 ws2 + estab zs1 a1)

    =<= dist d ws1 ws2 + 2.0 * lip * α1 * (one / lend zs1) + estab zs1 a1
        ?   estabconsR zs1 α1 a1
                            
    =<= dist d ws1 ws2 + estab zs1 (SS α1 a1)
    =<= dist d ws1 ws2 + estab zs1 as1
    *** QED
 where
  pureUpd1 = pureUpdate (head zs1) α1 f1
  pureUpd2 = pureUpdate (head zs2) α2 f2
  sgdRec1 = sgdRecUpd zs1 ws1 α1 a1 f1
  sgdRec2 = sgdRecUpd zs2 ws2 α2 a2 f2
  uhead1 = ppure (head zs1)
  utail1 = unif (tail zs1)
  uhead2 = ppure (head zs2)
  utail2 = unif (tail zs2)
thm d zs1 ws1 _ f1 zs2 ws2 _ f2 = ()

{-@ multHelper :: a:Double -> b:{Double | 0 <= b} -> c:Double -> d:{Double | c <= d } 
               -> { a + b * c <= a + b * d }  @-}
multHelper :: Double -> Double -> Double -> Double -> () 
multHelper _ _ _ _ = ()



{-@ lemma :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> α1:StepSize -> a1:StepSizes -> f1:LossFunction -> 
             zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
             ws2:Weight -> α2:{StepSize | α1 = α2} -> {a2:StepSizes| a2 = a1} -> f2:{LossFunction|f1 = f2} ->  
             z:DataPoint -> 
             {dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z) <= dist d ws1 ws2 + estab zs1 a1} / [sslen a1, 1] @-}
lemma :: Dist Double -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSize ->  StepSizes -> LossFunction -> DataPoint -> ()
lemma d zs1 ws1 α1 a1 f1 zs2 ws2 α2 a2 f2 z = 
  dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z)
        ?   pureUpdateEq z α1 f1
        ?   pureUpdateEq z α2 f2
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (pureUpdate z α1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (pureUpdate z α2 f2))
        ?   pureBindDist d d 0 (update z α1 f1) (sgd zs1 ws1 a1 f1)
                             (update z α2 f2) (sgd zs2 ws2 a2 f2) 
                             (relationalupdateq d z α1 f1 z α2 f2)
    =<= dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
        ? thm d zs1 ws1 a1 f1 zs2 ws2 a2 f2
    =<= dist d ws1 ws2 + estab zs1 a1
    *** QED


{-@ assume pureUpdateEq :: zs:DataPoint -> a:StepSize -> f:LossFunction
               -> {pureUpdate zs a f == ppure . update zs a f} @-}
pureUpdateEq :: DataPoint -> StepSize -> LossFunction -> ()
pureUpdateEq zs a f = () 
