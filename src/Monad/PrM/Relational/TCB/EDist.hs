-----------------------------------------------------------------
-- | Expected Distance Specifications for PrM Primitives ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.PrM.Relational.TCB.EDist where 

import Data.Dist 
import Data.List 
import Monad.PrM
import Monad.PrM.Relational.TCB.Spec

{-@ measure Monad.PrM.Relational.TCB.EDist.kant :: Dist a -> Dist (PrM a) @-}
{-@ assume kant :: d:Dist a -> {dd:Dist (PrM a) | dd = Monad.PrM.Relational.TCB.EDist.kant d } @-}
kant :: Dist a -> Dist (PrM a)
kant = undefined 

{-@ reflect edist @-}
{-@ edist :: Dist a -> PrM a -> PrM a -> {v:Double | 0 <= v } @-} 
edist :: Dist a -> PrM a -> PrM a -> Double 
edist d = dist (kant d)

{-@ assume pureDist :: d:Dist a -> x1:a -> x2:a 
                    -> { dist (kant d) (ppure x1) (ppure x2) = dist d x1 x2} @-}
pureDist :: Dist a -> a -> a -> ()
pureDist _ _ _ = ()

{-@ assume bindDist :: d:Dist b -> m:Double -> p:(a -> a -> Bool)
                    -> f1:(a -> PrM b) -> e1:PrM a 
                    -> f2:(a -> PrM b) -> e2:{PrM a | lift p e1 e2} 
                    -> lemma:(x1:a -> {x2:a| p x1 x2 } 
                             -> { dist (kant d) (f1 x1) (f2 x2) <= m}) 
                    -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDist :: Dist b ->  Double -> (a -> a -> Bool) -> (a -> PrM b) -> PrM a -> (a -> PrM b) -> PrM a -> (a -> a -> ()) -> ()
bindDist _ _ _ _ _ _ _ _ = ()

{-@ assume pureBindDist :: da:Dist a -> db:Dist b
                        -> m:Double 
                        -> f1:(a -> b) -> e1:PrM a 
                        -> f2:(a -> b) -> e2:PrM a 
                        -> (x1:a -> x2:a -> { dist db (f1 x1) (f2 x2) <= dist da x1 x2 + m}) 
                        -> { dist (kant db) (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= dist (kant da) e1 e2 + m } @-}
pureBindDist :: Dist a -> Dist b -> Double -> (a -> b) -> PrM a -> (a -> b) ->  PrM a ->  (a -> a -> ()) -> ()
pureBindDist _ _ m f1 e1 f2 e2 t = () 

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