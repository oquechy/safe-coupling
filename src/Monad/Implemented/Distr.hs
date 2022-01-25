-- | Implements Monad.Distr

{-@ LIQUID "--reflection" @-}

module Monad.Implemented.Distr where 

import           Data.List
import           Prelude                 hiding ( zipWith
                                                , all
                                                )


import           Numeric.Probability.Distribution

type Distr = T Prob
type Prob  = Double

bind :: Distr a -> (a -> Distr b) -> Distr b
bind = (>>=) 

ppure :: a -> Distr a
ppure = pure 

bernoulli :: Prob -> Distr Bool
bernoulli p = fromFreqs [(True, p), (False, 1 - p)]

choice :: Prob -> Distr a -> Distr a -> Distr a
choice p x y = cond (bernoulli p) x y 

unif :: [a] -> Distr a
unif = uniform

eq :: Ord a => Distr a -> Distr a -> Bool
eq = equal

eqVf :: Ord a => List (Distr a) -> List (Distr a) -> Bool
eqVf v v' = llen v == llen v' && all (zipWith eq v v')