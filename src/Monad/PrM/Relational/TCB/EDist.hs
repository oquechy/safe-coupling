-----------------------------------------------------------------
-- | Expected Distance Specifications for PrM Primitives ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Monad.PrM.Relational.TCB.EDist where 

import Data.Dist 
import Data.List 
import Monad.PrM
import Monad.PrM.Lift
import Monad.PrM.Relational.TCB.Spec

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators

{-@ reflect kdist @-}
{-@ kdist :: Dist a -> PrM a -> PrM a -> {v:Double | 0 <= v } @-} 
kdist :: Dist a -> PrM a -> PrM a -> Double 
kdist d = dist (kant d)



{-@ pureDist :: d:Dist a -> x1:a -> x2:a 
                    -> { dist (kant d) (ppure x1) (ppure x2) <= dist d x1 x2} @-}
pureDist :: Dist a -> a -> a -> ()
pureDist d x1 x2 
      =   kdist d (ppure x1) (ppure x2)
      ?   muDist d k (ppure x1) (ppure x2) mu ()
      =<= k
      *** QED
      where 
            k = dist d x1 x2
            mu = [((x1, x2), 1)]

{-@ assume bindDist :: d:Dist b -> m:Double -> p:(a -> a -> Bool)
                    -> f1:(a -> PrM b) -> e1:PrM a 
                    -> f2:(a -> PrM b) -> e2:{PrM a | lift p e1 e2} 
                    -> lemma:(x1:a -> {x2:a| p x1 x2 } 
                             -> { dist (kant d) (f1 x1) (f2 x2) <= m}) 
                    -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDist :: Dist b ->  Double -> (a -> a -> Bool) -> (a -> PrM b) -> PrM a -> (a -> PrM b) -> PrM a -> (a -> a -> ()) -> ()
bindDist _ _ _ _ _ _ _ _ = ()

{-@ assume fmapDist :: da:Dist a -> db:Dist b
                        -> m:Double 
                        -> f1:(a -> b) -> e1:PrM a 
                        -> f2:(a -> b) -> e2:PrM a 
                        -> (x1:a -> x2:a -> { dist db (f1 x1) (f2 x2) <= dist da x1 x2 + m}) 
                        -> { dist (kant db) (fmap f1 e1) (fmap f2 e2) <= dist (kant da) e1 e2 + m } @-}
fmapDist :: Dist a -> Dist b -> Double -> (a -> b) -> PrM a -> (a -> b) ->  PrM a ->  (a -> a -> ()) -> ()
fmapDist _ _ _ _ _ _ _ _ = () 

{-@ assume liftA2Dist :: da:Dist a -> db:Dist b -> dc:Dist c 
                      -> ma:Double -> ka:Double -> mb:Double -> kb:Double -> m:Double 
                      -> f1:(a -> b -> c) -> e1:PrM a -> u1:PrM b
                      -> f2:(a -> b -> c) -> e2:PrM a -> u2:PrM b
                      -> {_:()|dist (kant da) e1 e2 <= ka}
                      -> {_:()|dist (kant db) u1 u2 <= kb}
                      -> (x1:a -> y1:b -> x2:a -> y2:b 
                            -> {dist dc (f1 x1 y1) (f2 x2 y2) <= ma * dist da x1 x2 + mb * dist db y1 y2 + m})
                      -> {dist (kant dc) (liftA2 f1 e1 u1) (liftA2 f2 e2 u2) <= ma * ka + mb * kb + m} @-}
liftA2Dist :: Dist a -> Dist b -> Dist c -> Double -> Double -> Double -> Double -> Double 
           -> (a -> b -> c) -> PrM a -> PrM b -> (a -> b -> c) -> PrM a -> PrM b 
           -> () -> () -> (a -> b -> a -> b -> ())
           -> ()  
liftA2Dist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = ()

{-@ assume unifDist :: d:Dist a -> xsl:[a] -> xsr:{[a] | xsl == xsr}
                          -> { dist (kant d) (unif xsl) (unif xsr) == 0 } @-}
unifDist :: Dist a -> [a] -> [a] -> ()
unifDist _ _ _ = ()

{-@ assume choiceDist :: d:Dist a -> p:Prob -> e1:PrM a -> e1':PrM a 
                      -> q:{Prob | p = q } -> e2:PrM a -> e2':PrM a 
                      -> { dist (kant d) (choice p e1 e1') (choice q e2 e2') <= p * (dist (kant d) e1 e2) + (1.0 - p) * (dist (kant d) e1' e2')} @-}
choiceDist :: Dist a -> Prob -> PrM a -> PrM a -> Prob -> PrM a -> PrM a -> ()
choiceDist _ _ _ _ _ _ _ = ()

{-@ assume bernoulliDist :: d:Dist Double -> p:Prob -> {q:Prob | p <= q}
                         -> {dist (kant d) (bernoulli p) (bernoulli q) <= dist d 1 0 * (q - p)} @-}
bernoulliDist :: Dist Double -> Prob -> Prob -> ()
bernoulliDist d p q = ()
    where _ = dist (kant d) (bernoulli p) (bernoulli q) <= dist d 1 0 * (q - p)