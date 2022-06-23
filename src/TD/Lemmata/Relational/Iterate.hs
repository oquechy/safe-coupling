{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Lemmata.Relational.Iterate where 

import           Monad.Distr
import           Data.Dist
import           Data.List
import           Prelude hiding (iterate)

import           Monad.Distr.Relational.TCB.Axiom 
import           Monad.Distr.Predicates

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


{-@ iterateSpec :: m:{_|0 <= m} -> {k:_|k >= 0} -> n:Nat -> l:Nat
                      -> f:(v:ListN l -> Distr (ListN l))
                      -> (m:{_|0 <= m} -> y1:{List Double|llen y1 = l} -> y2:{List Double|llen y2 = l} -> {bounded m y1 y2 => lift (bounded (k * m)) (f y1) (f y2)})
                      -> x1:ListN l -> x2:ListN l
                      -> {bounded m x1 x2 => lift (bounded (pow k n * m)) ((iterate n (llen x1) f) (x1)) 
                                                                          ((iterate n (llen x2) f) (x2))} / [n] @-}
iterateSpec :: Double -> Double -> Int -> Int
                  -> (List Double -> Distr (List Double)) 
                  -> (Double -> List Double -> List Double -> ()) 
                  -> List Double -> List Double
                  -> ()
iterateSpec m k 0 _ _ _ x1 x2 | bounded m x1 x2
    =   pureAxiom (bounded (pow k 0 * m)) x1 x2 ()
iterateSpec m k n l f lemma x1 x2 | bounded m x1 x2
    =   assert (pow k (n-1) * (k * m) == pow k n * m) ? 
        bindAxiom (bounded (pow k n * m)) (bounded (k * m)) 
                 (f x1) (iterate (n - 1) (llen x1) f)
                 (f x2) (iterate (n - 1) (llen x2) f)
                 (lemma m x1 x2)
                 (iterateSpec (k * m) k (n - 1) l f lemma)
iterateSpec m k n l f lemma x1 x2 = ()
