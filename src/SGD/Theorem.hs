{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple-local"      @-}

module SGD.Theorem where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                , fmap
                                                )
import           Language.Haskell.Liquid.ProofCombinators hiding ((===), (=<=), (?), (***))

import           Misc.ProofCombinators

import           Monad.PrM               hiding ( sum )
import           Monad.PrM.Lift
import           Monad.PrM.Laws
import           Monad.PrM.Relational.TCB.EDist
import           Monad.PrM.Relational.Theorems
import           Data.Dist 
import           Data.List 
import           SGD.SGD 
import           SGD.DataPointDist

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
                    -> { estab zs (SS x xs) == 2.0 * lip * x * (mydiv 1.0 (lend zs)) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  === 2.0 * lip / (lend zs) * sum (SS x xs)
  === 2.0 * lip * x * (1 / lend zs) + estab zs xs 
  === 2.0 * lip * x * (mydiv 1.0 (lend zs)) + estab zs xs 
  *** QED 
        
{-@ ple thm @-}
{-@ thm :: d:Dist Double 
        -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]|1 <= len zs}
        -> {zs1:DataSet|isPermutation (cons x zs) zs1} -> ws1:Weight -> as1:StepSizes -> f1:LossFunction 
        -> {zs2:DataSet|isPermutation (cons y zs) zs2} -> ws2:Weight -> {as2:StepSizes|as2 = as1} 
        -> {f2:LossFunction|f1 = f2}
        -> {dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2) <= dist d ws1 ws2 + estab zs1 as1} / [sslen as1, 0]@-}
thm :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] 
    -> DataSet -> Weight -> StepSizes -> LossFunction 
    -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
thm d x y zs zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2 =
  dist (kant d) (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    === dist (kant d) (ppure ws1) (ppure ws2)
        ? pureDist d ws1 ws2
    =<= dist d ws1 ws2
        ? estabEmp zs1 
    =<= dist d ws1 ws2 + estab zs1 α1
    *** QED 

thm d x y zs zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 
    = assertWith (dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2) <= dist d ws1 ws2 + estab zs1 as1) (
        dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    === dist (kant d) (bind (unif zs1) sgdRec1) 
                      (bind (unif zs2) sgdRec2)
        ?   unifPermut distDataPoint xs zs1 
    === dist (kant d) (bind (unif xs) sgdRec1) 
                      (bind (unif zs2) sgdRec2)
        ?   unifPermut distDataPoint ys zs2
    === dist (kant d) (bind (unif (cons x zs)) sgdRec1) 
                      (bind (unif (cons y zs)) sgdRec2)
        ?   unifChoice x zs 
        ?   assert (unif (cons x zs) == choice (mydiv 1.0 (lend (cons x zs))) (ppure x) (unif zs))
        ?   unifChoice y zs
        ?   assert (unif (cons y zs) == choice (mydiv 1.0 (lend (cons y zs))) (ppure y) (unif zs))
    === dist (kant d) (bind (choice (1.0 `mydiv` lend (cons x zs)) uhead1 utail1) sgdRec1)
                      (bind (choice (1.0 `mydiv` lend (cons y zs)) uhead2 utail2) sgdRec2)
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
        ?   thmNeq d x y zs zs1 ws1 zs2 ws2 α1 a1 f1
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * α1) 
            + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   thmEq d x y zs zs1 ws1 zs2 ws2 α1 a1 f1
        ? assert (α1 == α2)
       ? assert (dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 α1 a1 f1)) 
                               (bind (unif zs) (sgdRecUpd zs2 ws2 α1 a1 f1))  
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 α1 a1 f1)) 
                               (bind (unif zs) (sgdRecUpd zs2 ws2 α2 a2 f2))  
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2)
                 <= dist d ws1 ws2 + estab zs1 a1)
       ? assert (0.0 <= 1.0 - p )
       ? assert (
           p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * α1) 
            + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
          <= 
           p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * α1) 
            + (1.0 - p) * (dist d ws1 ws2 + estab zs1 a1)   
       )
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + 2.0 * lip * α1) 
            + (1.0 - p) * (dist d ws1 ws2 + estab zs1 a1)
    =<= dist d ws1 ws2 + 2.0 * lip * α1 * p + estab zs1 a1
        ?   permutLen xs zs1
        ?   assert (lend zs1 == lend (cons x zs))
        ?   estabconsR zs1 α1 a1
    =<= dist d ws1 ws2 + estab zs1 (SS α1 a1)
    =<= dist d ws1 ws2 + estab zs1 as1
    *** QED
    )
 
 where
  p = 1.0 `mydiv` lend (cons x zs)
  pureUpd1 = pureUpdate x α1 f1
  pureUpd2 = pureUpdate y α2 f2
  sgdRec1 = sgdRecUpd zs1 ws1 α1 a1 f1
  sgdRec2 = sgdRecUpd zs2 ws2 α2 a2 f2
  uhead1 = ppure x
  utail1 = unif zs
  uhead2 = ppure y
  utail2 = unif zs
  xs = cons x zs
  ys = cons y zs
thm _ _ _ d zs1 ws1 _ f1 zs2 ws2 _ f2 = ()

{-@ ple thmNeq @-}
{-@ thmNeq :: d:Dist Double -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
           -> {zs1:DataSet|isPermutation (cons x zs) zs1}
           -> ws1:Weight
           -> {zs2:DataSet|isPermutation (cons y zs) zs2}
           -> ws2:Weight 
           -> α:StepSize -> αs:StepSizes -> f:LossFunction 
           -> { dist (kant d) (bind (ppure x) (sgdRecUpd zs1 ws1 α αs f)) 
                              (bind (ppure y) (sgdRecUpd zs2 ws2 α αs f)) 
                <= dist d ws1 ws2 + estab zs1 αs + 2.0 * lip * α} / [sslen αs, 1] @-}
thmNeq :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> ()
thmNeq d x y zs zs1 ws1 zs2 ws2 α αs f
    =   dist (kant d) (bind (ppure x) (sgdRecUpd zs1 ws1 α αs f)) 
                      (bind (ppure y) (sgdRecUpd zs2 ws2 α αs f))
    === dist (kant d) (bind (ppure x) sgdRec1) 
                      (bind (ppure y) sgdRec2)
        ?   leftId x sgdRec1 
        ?   leftId y sgdRec2 
    === dist (kant d) (sgdRec1 x) (sgdRec2 y)
    === dist (kant d) (bind (sgd zs1 ws1 αs f) pureUpd1) 
                      (bind (sgd zs2 ws2 αs f) pureUpd2)
        ?   pureUpdateEq x α f
        ?   pureUpdateEq y α f
    === dist (kant d) (bind (sgd zs1 ws1 αs f) (ppure . update x α f)) 
                      (bind (sgd zs2 ws2 αs f) (ppure . update y α f))
    === dist (kant d) (fmap (update x α f) (sgd zs1 ws1 αs f)) 
                      (fmap (update y α f) (sgd zs2 ws2 αs f))
        ?   fmapDist d d (2.0 * lip * α) (update x α f) (sgd zs1 ws1 αs f) 
                                       (update y α f) (sgd zs2 ws2 αs f) 
                                       (relationalupdatep d x α f y α f)
    =<= dist (kant d) (sgd zs1 ws1 αs f) (sgd zs2 ws2 αs f) + 2.0 * lip * α
        ?   thm d x y zs zs1 ws1 αs f zs2 ws2 αs f
    =<= dist d ws1 ws2 + estab zs1 αs + 2.0 * lip * α
    *** QED
    where   
        pureUpd1 = pureUpdate x α f
        pureUpd2 = pureUpdate y α f
        sgdRec1 = sgdRecUpd zs1 ws1 α αs f
        sgdRec2 = sgdRecUpd zs2 ws2 α αs f
        uhead1 = ppure x
        uhead2 = ppure y

{-@ ple thmEq @-}
{-@ thmEq :: d:Dist Double -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
          -> {zs1:DataSet|isPermutation (cons x zs) zs1}
          -> ws1:Weight
          -> {zs2:DataSet|isPermutation (cons y zs) zs2}
          -> ws2:Weight
          -> α:StepSize -> αs:StepSizes -> f:LossFunction 
          -> { dist (kant d) (bind (unif zs) (sgdRecUpd zs1 ws1 α αs f)) 
                              (bind (unif zs) (sgdRecUpd zs2 ws2 α αs f)) 
                <= dist d ws1 ws2 + estab zs1 αs } / [sslen αs, 2] @-}
thmEq :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> ()
thmEq d x y zs zs1 ws1 zs2 ws2 α αs f 
    =   dist (kant d) (bind (unif zs) sgdRec1) 
                      (bind (unif zs) sgdRec2)
        ?   bindDistEq d (dist d ws1 ws2 + estab zs1 αs) 
                       sgdRec1 utail sgdRec2 utail
                       (lemma d x y zs zs1 ws1 α αs f zs2 ws2 α αs f)
    =<= dist d ws1 ws2 + estab zs1 αs
    *** QED
    where
        sgdRec1 = sgdRecUpd zs1 ws1 α αs f
        sgdRec2 = sgdRecUpd zs2 ws2 α αs f
        utail = unif zs

{-@ lemma :: d:Dist Double
          -> x:DataPoint -> y:DataPoint -> {zs:[DataPoint]| 1 <= len zs}
          -> {zs1:DataSet|isPermutation (cons x zs) zs1}
          -> ws1:Weight
          -> α1:StepSize -> a1:StepSizes -> f1:LossFunction
          -> {zs2:DataSet|isPermutation (cons y zs) zs2}
          -> ws2:Weight -> α2:{StepSize|α1 = α2} -> {a2:StepSizes|a2 = a1} -> f2:{LossFunction|f1 = f2} 
          -> z:DataPoint 
          -> {dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z) <= dist d ws1 ws2 + estab zs1 a1} / [sslen a1, 1] @-}
lemma :: Dist Double -> DataPoint -> DataPoint -> [DataPoint] -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSize ->  StepSizes -> LossFunction -> DataPoint -> ()
lemma d x y zs zs1 ws1 α1 a1 f1 zs2 ws2 α2 a2 f2 z = 
  dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z)
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (pureUpdate z α1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (pureUpdate z α2 f2))
        ? pureUpdateEq z α1 f1
        ? pureUpdateEq z α2 f2
    === dist (kant d) (bind (sgd zs1 ws1 a1 f1) (ppure . update z α1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (ppure . update z α2 f2))
    === dist (kant d) (fmap (update z α1 f1) (sgd zs1 ws1 a1 f1)) 
                      (fmap (update z α2 f2) (sgd zs2 ws2 a2 f2))
        ?   fmapDist d d 0 (update z α1 f1) (sgd zs1 ws1 a1 f1)
                             (update z α2 f2) (sgd zs2 ws2 a2 f2) 
                             (relationalupdateq d z α1 f1 z α2 f2)
    =<= dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
        ?   thm d x y zs zs1 ws1 a1 f1 zs2 ws2 a2 f2
    =<= dist d ws1 ws2 + estab zs1 a1
    *** QED

{-@ assume pureUpdateEq :: zs:DataPoint -> a:StepSize -> f:LossFunction
               -> {pureUpdate zs a f == ppure . update zs a f} @-}
pureUpdateEq :: DataPoint -> StepSize -> LossFunction -> ()
pureUpdateEq zs a f = () 


-- Monomorphic Proof Combinators 

infixl 3 ===
{-@ (===) :: x:Double -> y:{Double | y == x} -> {v:Double | v == x && v == y} @-}
(===) :: Double -> Double -> Double
_ === y  = y


infixl 3 =<=
{-@ (=<=) :: x:Double -> y:{Double | x <= y} -> {v:Double | v == y && x <= y} @-}
(=<=) :: Double -> Double -> Double
_ =<= x  = x

{-@ assertWith :: b:Bool -> {v:a | b} -> {b} @-}
assertWith :: Bool -> a -> ()
assertWith _ _ = () 


infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool, pb :: b -> Bool>. a<pa> -> b -> a<pa> @-}
(?) :: a -> b -> a 
x ? _ = x 

infixl 3 ***
(***) :: Double -> QED -> Proof
_ *** _ = ()