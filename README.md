# Safe Couplings: Coupled Refinement Types


This artifact includes

 - Appendix with the soundness proof

 - Source code of `safe-coupling` library and case studies

Instructions to build the library:
 
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


In case of errors try
```
$ stack clean
```

### Library structure

Type `Distr a` at `src/Monad/Distr.hs:18` represents `PrM a` described in Sections 2.1 and 3.3 of the paper. The type supports operations of a probabilistic monad. See the rest of `src/Monad/Distr.hs`

The `bins` example from Section 2 can be found in `src/Bins` inside the library: 
- `src/Bins/Bins.hs` - source code of `bins`
- `src/Bins/TheoremSpec.hs` - stochastic dominance theorem (Section 2.3, l.234)
- `src/Bins/TheoremDist.hs` - distance bound (Section 2.5, l.340)

Distance data type (Section 3.2) is defined in `src/Data/Dist.hs`.

The proof system relies on two sets of axioms:
- `src/Monad/Distr/Relational/TCB/Axiom.hs` is discussed in Sections 2.2, 3.4
- `src/Monad/Distr/Relational/TCB/EDist.hs` is discussed in Sections 2.4, 3.5

Lastly, there are two larger case studies of verification in the library.

Convergence of temporal difference learning (Section 4.1) using lifted boolean relations:
 - `src/TD/TD0.hs` - source code of `TD0`
 - `src/TD/Theorem.hs:21` - convergence theorem (Section 4.1.2, l.630)
 - `src/TD/Lemmata` - helper lemmas

Stability of stochastic gradient descent (Section 4.2) using Kantorovich distance:

 - `src/SGD/SGD.hs` - source code of `SGD`
 - `src/SGD/Theorem.hs:76` - stability theorem (Section 4.2.2)

Script `loc` generates measurements from Table 2. It measures an average compilation time for each of the proofs `src/Bins/TheoremSpec.hs`, `src/Bins/TheoremDist.hs`, `src/SGD/Theorem.hs:76`, and `src/TD/Theorem.hs:21` including lemmas.

The soundess proof of these assumptions in their more general form can be found in the `~/appendix.pdf`.

