# RISC-V ISA Semantics for Lean

This translation of the official [SAIL RISC-V
SPEC](https://github.com/riscv/sail-riscv/) into the [Lean Theorem
Prover](https://lean-lang.org) covers the full RISC-V SPEC and passes the Lean
type-checkers without errors.

⚠️ However, our Lean backend for sail is still work-in-progress.  This means,
this resulting Lean code is neither executable nor polished in any way. ⚠️

## How to build this model

This repository generates automatically the RISC-V Lean model from the official Sail model. To generate it locally, follow the following steps.

### Build Sail

The released version of Sail does not support Lean output, so we need to build
Sail from its git repository. All the details are given in the [official
instructions](https://github.com/rems-project/sail/blob/sail2/INSTALL.md#installing-development-versions-of-sail).
What follows here is a summary:

#### 1. Install `OCaml`'s opam using your package manager
#### 2. Install the depdencies

On Debian/Ubuntu
```
sudo apt-get install build-essential libgmp-dev z3 pkg-config
```
or on MacOS
```
brew install gmp z3 pkgconf
```

#### 3. Install sail
```
git clone https://github.com/rems-project/sail.git
```

Using opam:
```
opam pin add sail
```

With dune, inside the Sail root directory:
```
opam install . --deps-only
dune build --release
dune install
```

### Build the RISC-V model

To build the RISC-V model, first clone the repository
```
git clone https://github.com/riscv/sail-riscv.git
```

and then build it using the cmake:
```
cmake -S . -B build -DCMAKE_BUILD_TYPE=RelWithDebInfo
cmake --build build/ --target generated_lean_rv64d
```

The resulting Lean model will be in `build/model/Lean_RV64D` and can be built using `lake build`

# Development & Support

This project is developed by
[Tobias Grosser](https://grosser.science) and
[Leo Stefanesco](https://stefanesco.com/) at the
[University of Cambridge](http://cam.ac.uk/),
[James Parker](https://www.galois.com/team/james-parker),
[Lee Newcomb](https://www.galois.com/team/julie-newcomb),
[Ben Selfridge](https://www.galois.com/team/ben-selfridge),
and [Ben Hamlin](https://www.galois.com/team/ben-hamlin)
at
[Galois Inc.](https://www.galois.com/), and
[Jakob von Raumer](https://von-raumer.de/)
and [Ryan Lahfa](https://github.com/RaitoBezarius) at
[LindyLabs](https://lindylabs.net/).
[Peter Sewell](https://www.cl.cam.ac.uk/~pes20/),
[Alasdair Armstrong](https://www.cst.cam.ac.uk/people/aa2019) (both
[Cambridge](https://cam.ac.uk)) and
[Brian Campbell](https://people.inf.ed.ac.uk/Brian_Campbell.html) ([University of
Edinburgh](https://ed.ac.uk)) supported through consulting and code.

[Luisa Cicolini](https://github.com/luisacicolini),
[Leo Stefanesco](https://stefanesco.com/),
[Siddharth Bhat](https://pixel-druid.com/),
[Sarah Kuhn](https://ch.linkedin.com/in/sarah-kuhn-9b64b1226) and
[Tobias Grosser](https://grosser.science) (all Cambridge) also polish Lean's BitVector library (maintained by the [Lean FRO](https://lean-fro.org)),
develop further proof
automation, and work on manually improving the bitvector level statements of these
SAIL semantics in support of this project.

We also thank [Arthur Adjedj](https://github.com/arthur-adjedj) for support and code.

This work was funded by a grant provided by the [Ethereum Foundation](https://ethereum.foundation/) and its [Verified zkEVM Project](https://verified-zkevm.org) led by
[Alexander Hicks](http://verified-zkevm.org/).

# Statistics

Lines: 175,768  
Definitions: 4,779  
Inductive definitions: 206  
Abbreviations: 185  

## Warnings and Errors

Errors found: 0  
Warnings found: 0  
