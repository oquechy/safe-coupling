[![Haskell CI](https://github.com/nikivazou/safe-coupling/actions/workflows/haskell.yml/badge.svg)](https://github.com/nikivazou/safe-coupling/actions/workflows/haskell.yml)

# safe-coupling
Library for relational verification of probabilistic algorithms.

See branch [icfp-22-artifact](https://github.com/oquechy/safe-coupling/tree/icfp-22-artifact) for the older version that corresponds to our ICFP'22 [submission](https://disk.yandex.ru/i/UxXDQ-tQS-kqrA).

Supports two proving modes:
 - Upper bound _Kantorovich distance_ between two distributions
 - Establish a _boolean relation_ on a coupling of two distributions

Includes two larger examples of verification:
 - Stability of stochastic gradient descent (src/SGD) using Kantorovich distance
 - Convergence of temporal difference learning (src/TD0) using lifted boolean relations

## A smaller example (src/Bins/Bins.hs)

This function recursively counts how many times the ball hit the bin after n attempted throws:

    bins :: Double -> Nat -> PrM Nat
    bins _ 0 = ppure 0
    bins p n = liftA2 (+) (bernoulli p) (bins p (n - 1)) 

Throws succeed with probability _p_ which is simulated by `bernoulli p`. The function returns a distribution over natural numbers. When comparing the results of two throwers with respective chances of success _p_ and _q > p_, we expect the second thrower to score notably better with the increase of _n_. Formally, we can show that Kantorovich distance between `bins p n` and `bins q n` is upper bounded by _(q - p)·n_.

## Proof (src/Bins/Theorem.hs)

The proof uses four definitions from the library:
 * In the first case, no throws were made. Axiom `pureDist` allows deriving Kantorovich distance between pure expressions. In our case, _0_ and _0_.
 * In the second case, axiom `liftA2Dist` derives Kantorovich distance between the inductive cases. Numeric arguments specify the expected bound in the format _a·x + b·y + c_ where _x_ and _y_ are bounds for the second and third arguments of `liftA2` respectively. As the last argument, the axiom requires proof of linearity of plus. It is empty since it can be automatically constructed by an SMT-solver.
 * Axiom `bernoulliDist` upper bounds the distance between calls to `bernoulli` with _q - p_ — this is our _x_. The second upper bound _y_ is provided by a recursive call to our theorem. 
 * A function `distInt` is used to measure the distance between arguments of `liftA2`. In this case, all of them provide integer values. A pre-defined distance between _n_ and _m_ is _|n - m|_ but this allows customization.

```
{-@ binsDist :: p:Prob -> {q:Prob|p <= q} -> n:Nat 
             -> {dist (kant distInt) (bins p n) (bins q n) <= n * (q - p)} / [n] @-}
binsDist :: Prob -> Prob -> Nat -> ()
binsDist p q 0 = pureDist distInt 0 0 
binsDist p q n
= liftA2Dist d d d 1 (q - p) 1 ((n - 1) * (q - p)) 0
    (+) (bernoulli p) (bins p (n - 1)) 
    (+) (bernoulli q) (bins q (n - 1))
    (bernoulliDist d p q)
    (binsDist p q (n - 1))
    (\_ _ _ _ -> ())
where 
    d = distInt
```

This concludes the mechanized proof of the boundary _(q-p)·n_.

## Installation
1. Install stack https://docs.haskellstack.org/en/stable/install_and_upgrade/

2. Compile the library and case studies

        $ cd safe-coupling
        $ stack install --fast
        ...
        Registering library for safe-coupling-0.1.0.0..


3. Run unit tests on executable case studies

        $ stack test
        ...                          
        test/Spec.hs
        Spec
            Bins
            mockbins 1 it:     OK
            mockbins 2 it:     OK
            bins 1 it:         OK
            bins 2 it:         OK (0.02s)
            exp dist mockbins: OK (0.12s)
            SGD
            sgd:               OK
            TD0
            td0 base:          OK
            td0 simple:        OK

        All 8 tests passed (0.12s)

        safe-coupling> Test suite safe-coupling-test passed
        Completed 2 action(s).


In case of errors try

    $ stack clean

