# Tyro

An improved implementation of the algorithm described in Finding Minimum Type Error Sources, Pavlinovic, King, Wies (2014). Includes _delayed instantiation_, the measurement of which is the subject of my MSc work.

The working name of Tyro was `z3ml`, and this name may still appear throughout the codebase and in the names of components.

# Installation

### Preparation

Install [Haskell Stack](https://docs.haskellstack.org/en/stable/install_and_upgrade/) and [OCaml opam](https://opam.ocaml.org/doc/Install.html). These are package managers.
Compilers for Haskell and OCaml are **not** required -- Stack and opam will install appropriate compilers themselves.
This helps to prevent version rot over time. Please report an issue if a build problem appears to be version-related.

First: navigate to the directory you'd like to work in, and clone Tyro.

```bash
$ git clone ...
$ cd tyro
```

### Frontend Installation

The next step is to install the frontend, written in OCaml. This will produce an executable named `zgen`.

From the root of your clone (`tyro/`), execute the following:

```bash
$ cd tyro_frontend
$ opam switch create .
```

Say Y when it asks if you want to create zgen as a new package. `opam` will install all the dependencies, then install `zgen`.
You'll be reminded to run `eval $(opam env)`, once you do `zgen` will become available on your PATH. Run `zgen -help` to confirm
(there is no `--version` option at the moment).

### Solver Installation

Tyro uses `z3` (but see [developing Tyro](#development)).

Even old versions of `z3` will do -- I haven't been able to find an exact minimum, but any version since the last half of 2015 should work.
Tyro was evaluated with version 4.8.12. The most recent version at the time of writing is 4.13.0.

A suitable version (probably around 4.8.7) should be available through your system package manager.
Otherwise, z3 can be obtained from [releases on GitHub](https://github.com/Z3Prover/z3/releases/).

### Backend Installation

The backend library is written in Haskell. For convenience, the subproject includes an executable component which calls out to
the frontend, backend library, and MaxSMT solver as appropriate.

If you're following along, your current working directory is `tyro/tyro_frontend`. Execute the following:

```bash
$ cd ../tyro
$ stack install
```

Stack will install all the dependencies, and then build and install `tyro`. Some warnings from the Haskell compiler are expected.
Confirm that `tyro` is available on your path with `tyro --help`.

# Development

Though the `tyro` executable drives the whole toolchain, the underlying architecture is actually composed of three phases:

 1. The 'frontend' -- the ocaml project that generates constraints from an input program.
 2. The 'backend' -- a Haskell library for manipulating generated constraints and SMT-LIB code, and interfacing with a MaxSMT solver.
 3. The 'solver' -- a MaxSMT solver, which `tyro` expects to be `z3`.

Each of these phases exists independently, but the 'backend' is not actually an executable. It is a library for manipulating the pieces.
The `tyro` executable is a driver program, installed _alongside_ the library, which coordinates the 3 phases and calls out to the library
as appropriate.

To change the frontend or solver in use, you can write a new driver script or modify `tyro/app/Main.hs` to call the appropriate one.
The solver should be configurable on the command line in a future version, but probably not the frontend.

A suitable frontend should accept a filename for a file containing a program as the only argument, and then emit constraints
in the appropriate format to stdout. The format does use OCaml syntax for types, however other than this it is not tied to OCaml in any way.
A suitable frontend could conceivably be implemented for other programming languages and the backend would still consume them.

The backend's job is to consume the intermediate format to produce an SMT-LIB script. The library function which handles this is `Conversion.convert`.
It will use the AST+constraint encoding defined by `Conversion.makeTypingAssertions`. Two encoding functions are implemented and a third is planned.
See the comments in `tyro/src/Conversion.hs`.

Suitable frontends and backends could, of course, be implemented in any language -- as long as they agree on the intermediate and SMT-LIB protocols.

For more information about the intermediate representation, see tyro/README.md.

# Organization

tyro_frontend/ contains an OCaml project, consisting of a heavily hacked port of EzyOCaml. This port has been updated to use compiler-libs and to work with version 4.13.1 of OCaml. Then, it has been hacked to implement Wies et. al.'s constraint generation algorithm with delayed instantiation. When this tool runs, it produces an intermediate `.z3ml` file. See tyro/README.md for more information.

tyro/ contains a Haskell project which consumes the `.z3ml` files produced by the frontend (or written by hand) to create a `.smt` file containing an SMT-LIB2 script. The project also contains a driver program which can invoke the frontend on an OCaml program, consume the generated `.z3ml` file to create an SMT script, invoke `z3` on that script, and finally interpret the output to display the (set of) sources range(s) identified as the most likely error source.

z3ml/README.md is a good place to look next.

# Project Goals

The problem we aim to contribute to is _type error provenance_. This concerns the region of source code which is the underlying cause of a type error.
We do not aim to give good information about _why_ there is a type error, just _where_. In fact, the tool is not capable to producing "why" information at all.
To use in practice, the output must be combined with that of `ocamlc` or some other typechecker,
and our output can then be used as a hint towards where a fix might need to occur.
Most often, the locations reported by `ocamlc` and `tyro` are different, but near to each other.
However, in the case of trickier type errors, the reported locations are often far apart.

We aim to demonstrate an improvement to Wies et. al.'s algorithm, called _delayed instantiation_.
Every use of a polymorphic let-bound value in a typical inference algorithm requires instantiating the type of the value.
In constraint generation algorithms, this problem is much worse - the let-bound values have associated constraints.
If we are not able to solve and discharge these constraints during constraint generation, then we must also instantiate _all_ of the constraints associated with a let-bound value whenever it is used.
Delayed instantiation instead records that an instantiation is needed, but leaves it up to the SMT solver to decide when, or if, to actually do it.
Program locations which the SMT solver can determine to be irrelevant while therefore not lead to instantiations, and the SMT scripts are significantly smaller (though certainly no easier to read).

Since we aim to demonstrate and evaluate an algorithm, the implementation does not cover all of OCaml. The most egregious missing features are mutually recursive bindings (which have significantly over-generalized types in each other's bodies) and modules. Builtin ("pervasive") modules should work, though some issues have arisen ocassionally in testing. Custom modules do not seem to work at all. Fixing both of these issues is in the project scope, but probably not in the scope of my MSc as we are able to evaluate the algorithm without these features.

Other missing features include complete support for record types, especially with ambiguous field names; GADTs; certain forms of type declaration, and environment-restricted let-generalization. We fully generalize every let-bound value, even if some unification variables in its type are free in the environment. This is a well-known complication of HM let-generalization which we ignore for simplicity; doing this is common in the community for demonstrating localization algorithms.

# Aside: "Let should not be generalized"

Work on type systems other than OCaml's (see, for example, OutsideIn(X): Modular type inference with local assumptions, Simon P. Jones et. al.) has strongly suggested that most let-bound values are used monomorphically.
A system which only generalizes let-bound values _with type annotations_ would be freed completely from the instantiation problem.
Such a language would not be OCaml, but would be an interesting underlying system for a new language which uses the techniques of Wies et. al. and/or Haack and Wells to generate nice type errors.

To experiment with a tyro-like tool for such a language, one would need to implement a new frontend, or modify the existing one.
The main file of interest for modifying Tyro's frontend would be `tyro_frontend/lib/easyocaml/ezyGenerate.ml`.
