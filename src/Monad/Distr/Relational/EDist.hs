-----------------------------------------------------------------
-- | Expected Distance Specifications for Distr Primitives ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection" @-}

module Monad.Distr.Relational.EDist where 

import Data.Dist 
import Monad.Distr
import Monad.Distr.EDist

{-@ assume pureDist :: d:Dist a -> x1:a -> x2:a 
                    -> {expDist (ppure x1) (ppure x2) = dist d x1 x2} @-}
pureDist :: Dist a -> a -> a -> ()
pureDist _ _ _ = ()

{-@ assume bindDist :: m:Double -> p:(a -> a -> Bool)
                    -> f1:(a -> Distr b) -> e1:Distr a 
                    -> f2:(a -> Distr b) -> e2:{Distr a | lift p e1 e2 } 
                    -> lemma:(x1:a -> {x2:a|p x1 x2} -> { expDist (f1 x1) (f2 x2) <= m}) 
                    -> { expDist (bind e1 f1) (bind e2 f2) <= m } @-}
bindDist :: Double -> (a -> a -> Bool) -> (a -> Distr b) -> Distr a -> (a -> Distr b) -> Distr a -> (a -> a -> ()) -> ()
bindDist _ _ _ _ _ _ _ = ()

{-@ assume pureBindDist :: da:Dist a -> db:Dist b
                        -> m:Double 
                        -> f1:(a -> b) -> e1:Distr a 
                        -> f2:(a -> b) -> e2:Distr a 
                        -> (x1:a -> x2:a -> { dist db (f1 x1) (f2 x2) <= dist da x1 x2 + m}) 
                        -> { expDist (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= expDist e1 e2 + m } @-}
pureBindDist :: Dist a -> Dist b -> Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
pureBindDist _ _ m f1 e1 f2 e2 t = () 

{-@ assume unifDist :: xsl:[a] -> xsr:{[a] | xsl == xsr}
                          -> {expDist (unif xsl) (unif xsr) == 0 } @-}
unifDist :: [a] -> [a] -> ()
unifDist _ _ = ()

{-@ assume choiceDist :: p:Prob -> e1:Distr a -> e1':Distr a 
                      ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
                      ->  { expDist (choice p e1 e1') (choice q e2 e2') <= p * (expDist e1 e2) + (1.0 - p) * (expDist e1' e2')} @-}
choiceDist :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
choiceDist _ _ _ _ _ _ = ()


{-@ predicate BijCoupling X Y = true @-}
{-@ assume bindDistEq :: m:Double 
                      -> f1:(a -> Distr b) -> e1:Distr a 
                      -> f2:(a -> Distr b) -> e2:{Distr a | BijCoupling e1 e2 } 
                      -> (x:a -> { expDist (f1 x) (f2 x) <= m}) 
                      -> { expDist (bind e1 f1) (bind e2 f2) <= m } @-}
bindDistEq :: Double -> (a -> Distr b) -> Distr a -> (a -> Distr b) ->  Distr a ->  (a -> ()) -> ()
bindDistEq _ _ _ _ _ _ = () -- NV can we derive this from bindDist? 
