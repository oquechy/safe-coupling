{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Examples.ExpDist where

import           Monad.PrM
import           Monad.PrM.Lift
import           Data.Dist

import           Monad.PrM.Relational.TCB.EDist
import           Misc.ProofCombinators

import           Prelude                 hiding ( map
                                                , max
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                , uncurry
                                                , const
                                                )

{-@ relationalu :: d:Dist a -> {xs:[a]|0 < len xs} -> {dist (kant d) (unif xs) (unif xs) == 0} @-}
relationalu :: Dist a -> [a] -> ()
relationalu d xs = unifDist d xs xs 


-- Attention: In the Haskell code you need to write 4.0 instead of just 4 to avoid implicit conversion
{-@ exDistPure :: () -> {dist (kant distDouble) (ppure 4.0) (ppure 2.0) <= 2.0 } @-}
exDistPure :: () -> ()
exDistPure _ = pureDist distDouble 4.0 2.0 

{-@ ex2DistPure :: p:Prob ->  xs:{[Double] | 0 < len xs } 
                -> {dist (kant distDouble) (choice p (ppure 4.0) (unif xs)) (choice p (ppure 2.0) (unif xs)) <= p * 2.0 } @-}
ex2DistPure :: Prob -> [Double] -> ()
ex2DistPure p xs 
  = relationalu distDouble xs `const` 
    exDistPure () `const` 
    choiceDist distDouble p (ppure 4.0) (unif xs) p (ppure 2.0) (unif xs)

