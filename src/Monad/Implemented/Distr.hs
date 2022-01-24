-- | Implements Monad.Distr

module Monad.Implemented.Distr where 

import Numeric.Probability.Distribution

type Distr = T Prob
type Prob  = Double

bind :: Distr a -> (a -> Distr b) -> Distr b
bind = (>>=) 

ppure :: a -> Distr a
ppure = pure 

choice :: Prob -> Distr a -> Distr a -> Distr a
choice p x y = cond (pure (p <= 0.5)) x y 

unif :: [a] -> Distr a
unif = uniform