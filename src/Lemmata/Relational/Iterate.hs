{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Lemmata.Relational.Iterate where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (iterate)

import           TD0 
import           Language.Haskell.Liquid.ProofCombinators


{-@ relationaliterate :: m:{_|0 <= m} -> {k:_|k >= 0} -> n:Nat 
                      -> x1:_ -> {x2:_|llen x1 == llen x2 && bounded m x1 x2} 
                      -> f:({v:List Double| llen v == llen x1} -> Distr ({o:List Double | llen o == llen x1})) 
                      -> (m:{_|0 <= m} -> y1:{List Double | llen x1 = llen y1 } -> y2:{List Double | llen y2 == llen x1 } -> {bounded m y1 y2 => lift (bounded (k * m)) (f y1) (f y2)})
                      -> {lift (bounded (pow k n * m)) (iterate n (llen x1) f x1) (iterate n (llen x2) f x2)} @-}
relationaliterate :: Double -> Double -> Int 
                  -> List Double -> List Double 
                  -> (List Double -> Distr (List Double)) 
                  -> (Double -> List Double -> List Double -> ()) 
                  -> ()
relationaliterate m k n x1 x2 _ _ | n <= 0
    =   liftPure (bounded (pow k n * m)) x1 x2 ()
relationaliterate m k n x1 x2 f lemma 
    =   liftBind (bounded (pow k n * m)) (bounded (k * m)) 
                 (f x1) (iterate (n - 1) (llen x1) f)
                 (f x2) (iterate (n - 1) (llen x2) f)
                 (lemma m x1 x2)
                 undefined
                --  (relationaliterate (k * m) k (n - 1) f lemma)
            
