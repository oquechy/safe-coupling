# Safe Couplings: Coupled Refinement Types


This artifact includes

 - Appendix with the soundness proof

 - Source code of `safe-coupling` library and case studies

## Instructions to build the library
 
 1. Install dependencies:
    - Z3 Theorem Prover https://github.com/Z3Prover/z3/releases. Tested with versions 4.8.8 and 4.8.15.
        
    - Ncurses. On Debian, you need both libncurses and libncurses-dev.

    - Haskell Tool Stack https://docs.haskellstack.org/en/stable/install_and_upgrade. Tested with 2.3.3 and 2.7.5.

 2. Build the library and compile mechanized proofs of case studies. At this stage, the compilation of theorems `src/SGD/Theorem.hs` and `src/TD/Theorem.hs` guarantees that SGD and TD0 satisfy stability and convergence respectively. Note that Bins.Theorem and SGD.Theorem may take longer to compile than other modules (~1 minute).  

        $ cd safe-coupling
        $ stack install
        ...
        Registering library for safe-coupling-0.1.0.0..


3. Run unit tests on executable case studies. This ensures that SGD and TD0 are runnable and reasonably implemented.

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
        Completed 9 action(s).

4. Generate a statistics table for case studies. Here, `loc` - lines of code of the bare algorithm implementation without Liquid Haskell specs, `p. loc` - lines of proof, `t (sec)` - proof compilation time in seconds. 
        
        $ ./loc
        ...                          
                        Table 2
                          loc     p. loc    t (sec)
        bins spec         12         30     119.49
        bins dist         12        149     11.17
               td         35        132     52.01
              sgd         37        144     29.15

In case of errors try
```
$ stack clean
```

## Library structure

Type `Distr a` at `src/Monad/Distr.hs:18` represents `PrM a` described in Sections 2.1 and 3.3 of the paper. The type supports operations of a probabilistic monad. See the rest of `src/Monad/Distr.hs`. 

The module also includes function `lift` at `src/Monad/Distr.hs:51` that corresponds to predicate lifting for predicate `p`. In the paper, we use the diamond operator for this purpose.

The `bins` example from Section 2 can be found in `src/Bins` inside the library: 
- `src/Bins/Bins.hs` - source code of `bins`
- `src/Bins/TheoremSpec.hs:43` - stochastic dominance theorem (Section 2.3, l.234)
- `src/Bins/TheoremDist.hs:137` - distance bound (Section 2.5, l.340)

Distance data type (Section 3.2) is defined in `src/Data/Dist.hs`.

The proof system relies on two sets of axioms:
- `src/Monad/Distr/Relational/TCB/Axiom.hs` is discussed in Sections 2.2, 3.4
- `src/Monad/Distr/Relational/TCB/EDist.hs` is discussed in Sections 2.4, 3.5

Lastly, there are two larger case studies of verification in the library.

Convergence of temporal difference learning (Section 4.1) using lifted boolean relations:
 - `src/TD/TD0.hs` - source code of `TD0`
 - `src/TD/Theorem.hs:26` - convergence theorem (Section 4.1.2, l.630)
 - `src/TD/Lemmata` - helper lemmas

Stability of stochastic gradient descent (Section 4.2) using Kantorovich distance:

 - `src/SGD/SGD.hs` - source code of `SGD`
 - `src/SGD/Theorem.hs:86` - stability theorem (Section 4.2.2)

Script `loc` generates measurements from Table 2. It measures an average compilation time for each of the proofs `src/Bins/TheoremSpec.hs`, `src/Bins/TheoremDist.hs`, `src/SGD/Theorem.hs`, and `src/TD/Theorem.hs` including lemmas.

The soundness proof of these assumptions in their more general form can be found in the `~/appendix.pdf`.

## Case studies

This section elaborates on the implementation details that were omitted in the paper.

### Bins Implementation

For better readability, `bins` presented in the paper in the form:

    {-@ bins :: n:Nat → Prob → PrM {r:Nat | r ≤ n} @-}
    bins 0 _ = pure 0
    bins n p = do x ← bins (n - 1) p
                  y ← bernoulli p
                  pure (x + y)

The actual implementation is different in several aspects:

* We don't use do notation. Instead, code is written with explicit calls to `bind`. 

        {-@ bins :: n:Nat → Prob → PrM {r:Nat | r ≤ n} @-}
        bins 0 _ = pure 0
        bins n p = bind (bins (n - 1) p) (\x →
                   bind (bernoulli p) (\y →
                   pure (x + y))

    Haskell's extension `RebindableSyntax` would allow us to use do notation with our custom function `bind` instead of default operator `>>=`. However, it doesn't with the second problem.

* We extract lambdas to top-level definitions. 

        {-@ reflect bins @-}
        {-@ bins :: n:Nat → Prob → PrM {r:Nat | r ≤ n} / [n] @-}
        bins 0 _ = pure 0
        bins n p = bind (bins (n - 1) p) (addBernoulli p (n - 1))

        {-@ reflect addBernoulli @-}
        {-@ addBernoulli :: Prob → n:Nat → {x:Nat | x ≤ n } → Distr {r:Nat | d ≤ n + 1 } @-}
        addBernoulli p n x = bind (bernoulli p) (pure . plus x)

        {-@ reflect plus @-}
        {-@ plus :: x:Nat → y:Nat → {r:Nat | r = x + y } @-} 
        plus x y = x + y 
        
    Right now, Liquid Haskell doesn't support lambda abstractions in _reflected_ definitions (see footnote on p. 6). Function `bins` is reflected to enable equational rewriting in the theorem that reasons about its structure.

    An additional component of type specification `[n]` helps the typechecker to find a termination metric.

* Finally, `Nat` in the definition of `bins` was replaced with `Double` to reduce type conversions in the proof.

### Bins Spec Proof

Following the changes in the structure of `bins`, the proof also diverges from the one presented in the paper. Again, the program is split into three separate functions and uses type `Double` instead of `Nat`.
