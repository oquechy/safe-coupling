-----------------------------------------------------------------
-- | Expected Distance Specifications for Distr Primitives ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.Distr.Relational.TCB.EDist where 

import Data.Dist 
import Data.List 
import Monad.Distr
import Monad.Distr.Relational.TCB.Spec

{-@ measure Monad.Distr.Relational.TCB.EDist.kant :: Dist a -> Dist (Distr a) @-}
{-@ assume kant :: d:Dist a -> {dd:Dist (Distr a) | dd = Monad.Distr.Relational.TCB.EDist.kant d } @-}
kant :: Dist a -> Dist (Distr a)
kant = undefined 

{-@ reflect edist @-}
{-@ edist :: Dist a -> Distr a -> Distr a -> {v:Double | 0 <= v } @-} 
edist :: Dist a -> Distr a -> Distr a -> Double 
edist d = dist (kant d)

{-@ assume pureDist :: d:Dist a -> x1:a -> x2:a 
                    -> { dist (kant d) (ppure x1) (ppure x2) = dist d x1 x2} @-}
pureDist :: Dist a -> a -> a -> ()
pureDist _ _ _ = ()

{-@ assume bindDist :: d:Dist b -> m:Double -> p:(a -> a -> Bool)
                    -> f1:(a -> Distr b) -> e1:Distr a 
                    -> f2:(a -> Distr b) -> e2:{Distr a | lift p e1 e2} 
                    -> lemma:(x1:a -> {x2:a| p x1 x2 } 
                             -> { dist (kant d) (f1 x1) (f2 x2) <= m}) 
                    -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDist :: Dist b ->  Double -> (a -> a -> Bool) -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> Distr a -> (a -> a -> ()) -> ()
bindDist _ _ _ _ _ _ _ _ = ()

{-@ assume pureBindDist :: da:Dist a -> db:Dist b
                        -> m:Double 
                        -> f1:(a -> b) -> e1:Distr a 
                        -> f2:(a -> b) -> e2:Distr a 
                        -> (x1:a -> x2:a -> { dist db (f1 x1) (f2 x2) <= dist da x1 x2 + m}) 
                        -> { dist (kant db) (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= dist (kant da) e1 e2 + m } @-}
pureBindDist :: Dist a -> Dist b -> Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
pureBindDist _ _ m f1 e1 f2 e2 t = () 

{-@ assume unifDist :: d:Dist a -> xsl:[a] -> xsr:{[a] | xsl == xsr}
                          -> { dist (kant d) (unif xsl) (unif xsr) == 0 } @-}
unifDist :: Dist a -> [a] -> [a] -> ()
unifDist _ _ _ = ()

{-@ assume choiceDist :: d:Dist a -> p:Prob -> e1:Distr a -> e1':Distr a 
                      -> q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
                      -> { dist (kant d) (choice p e1 e1') (choice q e2 e2') <= p * (dist (kant d) e1 e2) + (1.0 - p) * (dist (kant d) e1' e2')} @-}
choiceDist :: Dist a -> Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
choiceDist _ _ _ _ _ _ _ = ()

{-@ assume bernoulliDist :: d:Dist Double -> p:Prob -> {q:Prob | p <= q}
                         -> {dist (kant d) (bernoulli p) (bernoulli q) <= dist d 1 0 * (q - p)} @-}
bernoulliDist :: Dist Double -> Prob -> Prob -> ()
bernoulliDist d p q = ()
    where _ = dist (kant d) (bernoulli p) (bernoulli q) <= dist d 1 0 * (q - p)