# Preparation

Install Haskell Stack and [OCaml opam](https://opam.ocaml.org/doc/Install.html). These are package managers.
Compilers for Haskell and OCaml are **not** required -- Stack and opam will install appropriate compilers themselves.

# Installation

First: navigate to the directory you'd like to work in, and clone Tyro.

```bash
$ cd tyro
```

### Frontend Installation

The next step is to install the frontend, written in OCaml. This will produce an executable named `zgen`.

From the root of your clone (`tyro/`), execute the following:

```bash
$ cd tyro/tyro_frontend
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

