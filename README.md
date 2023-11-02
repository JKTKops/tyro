# z3ml

An implementation of the algorithm described in Finding Minimum Type Error Sources, Pavlinovic, King, Wies (2014).

Includes _delayed instantiation_, the measurement of which is the subject of my MSc work.

# Organization

z3ml_frontend/ contains an OCaml project using compiler-libs which consists of a heavily hacked port of EzyOCaml. This port has been updated to use compiler-libs and to work with version 4.13.1 of OCaml. Then, it has been hacked to implement Wies et. al.'s constraint generation algorithm with delayed instantiation. When this tool runs, it produces an intermediate `.z3ml` file. See z3ml/README.md for more information.

z3ml/ contains a Haskell project which consumes the `.z3ml` files produced by the frontend (or written by hand) to create a `.smt` file containing an SMT-LIB2 script. The project also contains a driver program which can invoke the frontend on an OCaml program, consume the generated `.z3ml` file to create an SMT script, invoke `z3` on that script, and finally interpret the output to display the (set of) sources range(s) identified as the most likely error source.

z3ml/README.md is a good place to look next.

# Project Goals

The problem we aim to contribute to is _type error provenance_. This concerns the region of source code which is the underlying cause of a type error.
We do not aim to give good information about _why_ there is a type error, just _where_. In fact, the tool is not capable to producing "why" information at all.
To use in practice, the output must be combined with that of `ocamlc` or some other typechecker,
and our output can then be used as a hint towards where a fix might need to occur.
`ocamlc`'s reported location and our reported location often differ significantly.

We aim to demonstrate an improvement to Wies et. al.'s algorithm, called _delayed instantiation_.
Every use of a let-bound value in a typical inference algorithm requires instantiating the type of the value.
In constraint generation algorithms, this problem is much worse - the let-bound values have associated constraints.
If we are not able to solve and discharge these constraints during constraint generation, then we must also instantiate _all_ of the constraints associated with a let-bound value whenever it is used.
Delayed instantiation instead records that an instantiation is needed, but leaves it up to the SMT solver to decide when, or if, to actually do it.
Program locations which the SMT solver can determine to be irrelevant while therefore not lead to instantiations, and the SMT scripts are significantly smaller (though certainly no easier to read).

Since we aim to demonstrate and evaluate an algorithm, the implementation does not cover all of OCaml. The most egregious missing features are mutually recursive bindings (which have significantly over-generalized types in each other's bodies) and modules. Builtin ("pervasive") modules should work, though some issues have arisen ocassionally in testing. Custom modules do not seem to work at all. Fixing both of these issues is in the project scope, but probably not in the scope of my MSc as we are able to evaluate the algorithm without these features.

Other missing features include complete support for record types, especially with ambiguous field names; GADTs; certain forms of type declaration, and environment-restricted let-generalization. We fully generalize every let-bound value, even if some unification variables in its type are free in the environment. This is a well-known complication of HM let-generalization which we ignore for simplicity; doing this is common in the community for demonstrating features such as this.

# Aside: "Let should not be generalized"

Work on type systems other than OCaml's (see, for example, OutsideIn(X): Modular type inference with local assumptions, Simon P. Jones et. al.) has strongly suggested that most let-bound values are used monomorphically.
A system which only generalizes let-bound values _with type annotations_ would be freed completely from the instantiation problem.
Such a language would not be OCaml, but would be an interesting underlying system for a new language which uses the techniques of Wies et. al. and/or Haack and Wells to generate nice type errors.

