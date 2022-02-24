{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Examples.ExpDist where

import           Monad.Distr
import           Data.Dist
import           Data.List

import           Monad.Distr.EDist
import           Monad.Distr.Relational.EDist
import           Misc.ProofCombinators

import           Prelude                 hiding ( map
                                                , max
                                                , repeat
                                                , foldr
                                                , fmap
                                                , mapM
                                                , iterate
                                                , uncurry
                                                )

{-@ relationalu :: ed:EDist a -> xs:[a] -> {edist ed (unif xs) (unif xs) == 0} @-}
relationalu :: EDist a -> [a] -> ()
relationalu ed xs = unifDist ed xs xs 


-- Attention: In the Haskell code you need to write 4.0 instead of just 4 to avoid implicit conversion
{-@ exDistPure :: ed:EDist Double -> () -> {edist ed (ppure 4.0) (ppure 2.0) <= 2.0 } @-}
exDistPure :: EDist Double -> () -> ()
exDistPure ed _ = pureDist ed distDouble 4.0 2.0  

{-@ ex2DistPure :: ed:EDist Double -> p:Prob ->  xs:{[Double] | 0 < len xs } 
                -> {edist ed (choice p (ppure 4.0) (unif xs)) (choice p (ppure 2.0) (unif xs)) <= p * 2.0 } @-}
ex2DistPure :: EDist Double -> Prob -> [Double] -> ()
ex2DistPure ed p xs 
  = relationalu ed xs `const` 
    exDistPure ed () `const` 
    choiceDist ed p (ppure 4.0) (unif xs) p (ppure 2.0) (unif xs)

