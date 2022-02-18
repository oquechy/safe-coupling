{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module ExpDist where

import           Monad.Distr
import           Data.Dist
import           Data.List

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
relationalu _ = () 


{-@ exDistPure :: () -> {expDist (ppure 4) (ppure 2) <= dist 4 2 } @-}
exDistPure :: () -> ()
exDistPure _ = relationalppure 4 2  



{-@ ex2DistPure :: p:Prob ->  xs:[Int] -> {expDist (choice p (ppure 4) (unif xs))  (choice p (ppure 2) (unif xs)) <= p * dist 4 2 } @-}
ex2DistPure :: Prob -> [Int] -> ()
ex2DistPure p xs = exDistPure () `const` relationalchoice p (ppure 4) (unif xs) p (ppure 2) (unif xs)

