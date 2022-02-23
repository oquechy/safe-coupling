{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Examples.ExpDist where

import           Monad.Distr
import           Data.Dist
import           Data.List
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

{-@ relationalu :: xs:[a] -> {expDist (unif xs) (unif xs) == 0} @-}
relationalu :: [a] -> ()
relationalu xs = relationalunif xs xs 


-- Attention: In the Haskell code you need to write 4.0 instead of just 4 to avoid implicit conversion
{-@ exDistPure :: () -> {expDist (ppure 4.0) (ppure 2.0) <= 2.0 } @-}
exDistPure :: () -> ()
exDistPure _ = relationalppure distDouble 4.0 2.0  

{-@ ex2DistPure :: p:Prob ->  xs:{[Double] | 0 < len xs } 
                -> {expDist (choice p (ppure 4.0) (unif xs)) (choice p (ppure 2.0) (unif xs)) <= p * 2.0 } @-}
ex2DistPure :: Prob -> [Double] -> ()
ex2DistPure p xs 
  = relationalu xs `const` 
    exDistPure () `const` 
    relationalchoice p (ppure 4.0) (unif xs) p (ppure 2.0) (unif xs)

