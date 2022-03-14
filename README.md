# safe-coupling
Library for relational verification of probabilistic algorithms.

## Instructions to build the library:
 1. Install stack https://docs.haskellstack.org/en/stable/install_and_upgrade/

 2. Compile the library and case studies
```
$ cd safe-coupling
$ stack install --fast
...
Registering library for safe-coupling-0.1.0.0..
```

3. Run unit tests on executable case studies
```
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
```

In case of errors try
```
$ stack clean
```

