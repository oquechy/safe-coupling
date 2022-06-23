# ICFP 2022 Artifact

Name:    **Safe Couplings: Coupled Refinement Types**

## Artifact Instructions

The artifact contains a library `~/safe-coupling` and a paper appendix `~/appendix.pdf`. 

The library can be used to verify two sorts of relational properties of probabilistic programs:
 - Upper bound _Kantorovich distance_ between two distributions
 - Establish a _boolean relation_ on a coupling of two distributions

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

### Building

1. Go to the library root inside the QEMU image.
      
         $ cd safe-coupling

2. Compile the library and case studies. At this stage, the compilation of theorems `src/SGD/Theorem.hs` and `src/TD/Theorem.hs` guarantees that SGD and TD0 satisfy stability and convergence respectively. Note that Bins.Theorem and SGD.Theorem may take longer to compile than other modules (~1 minute).  

        $ stack install
        ...
        Registering library for safe-coupling-0.1.0.0..

3. Run unit tests on case studies. This ensures that SGD and TD0 are runnable and reasonably implemented.

        $ stack test
        ...                          
        test/Spec.hs
         Spec
            Bins
               mockbins 1 it:     OK
               mockbins 2 it:     OK
               bins 1 it:         OK
               bins 2 it:         OK
               exp dist mockbins: OK (0.09s)
            SGD
               sgd:               OK
            TD0
               td0 base:          OK
               td0 simple:        OK

         All 8 tests passed (0.10s)

         safe-coupling   > Test suite safe-coupling-test passed
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

    $ stack clean

## QEMU Instructions

The ICFP 2022 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``apt-get install qemu-kvm``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```

### Artifact Preparation

Authors should install software dependencies into the VM image as needed,
preferably via the standard Debian package manager. For example, to install
GHC and cabal-install, login to the host and type:

```
$ sudo apt update
$ sudo apt install ghc
$ sudo apt install cabal-install
```

If you really need a GUI then you can install X as follows, but we prefer
console-only artifacts whenever possible.

```
$ sudo apt install xorg
$ sudo apt install xfce4   # or some other window manager
$ startx
```

See Debugging.md for advice on resolving other potential problems.

If your artifact needs lots of memory you may need to increase the value
of the `QEMU_MEM_MB` variable in the `start.sh` script.

When preparing your artifact, please also follow the [Submission
Guidelines](https://icfp22.sigplan.org/track/icfp-2022-artifact-evaluation#Submission-Guidelines).
