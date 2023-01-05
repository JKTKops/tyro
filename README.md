# z3ml

An implementation of the algorithm described in Finding Minimum Type Error Sources, Pavlinovic, King, Wies (2014).

This part of the system handles reading the constraint / location path file (see below) and outputs an SMT solver script compatible with SMT-LIB 2.6.

## Minimum Type Error Sources

The algorithm finds a minimum-cost set of program locations which describe all of the type errors in the program. The weight of each location can be selected in the constraint file if desired, but will
otherwise default to the number of (transitive, reflexive) children of that location.

This heuristic is described in the paper and is fairly effective. However, the constraint generator is responsible for appropriately setting relevant constraints to be hard.

Some useful cases where this should be done include
* the type signatures of library functions
* the constraint associated with the location of a local variable which is only used once.

The last one can also be generalized, with a hard constraint that asserts local variables are used at least once after replacing all error sources.

## Constraint/Location files

The syntax of these files is still tentative. Only textual input is accepted at the moment, but a `-s` command line flag is planned which accepts serialized input instead.

Example:
```
let f = fun x y -> y x in f 1 0
```
```
0 1;1-1;32
1 1;9-1;23
2 1;15-1;23
3 1;20-1;23
4 1;20-1;21
5 1;22-1;23
6 1;27-1;32
7 1;27-1;30
8 1;31-1;32
9 1;27-1;28
10 1;29-1;30
---
1 A1('a1, 'a2, 'b1, 'b2) {
  1 'a1 = ('b1 -> 'a2)
  ... }
---
0 'a0 = 'a6
...
9 A1('a1.1, 'a2.1, 'b1.1, 'b2.1)
...
```
The full file for this example contains some 16 assertions.

Each constraint file consists of three parts; an enumeration of locations, definitions of schemes, and raw constraints.
Tokens are separated by arbitrary whitespace.

### Part 1: Enumeration

```
Enumeration(0) := "0" Location
Enumeration(n) := Enumeration(n-1) n Location

Location := int ';' int '-' int ';' int
```

The tree structure (really, forest) is inferred from the ranges in the enumeration. There's a logarithmic cost to this. A future version may include the structure in the constraint file, perhaps with a syntax similar to graphviz-dot.

### Part 2: Constraint Schemes

Handling polymorphic variables (more) efficiently is described in the paper via _constraint schemes_. Each scheme is quanitified
over some number of type variables. In the natural use-case for let-bound variables, the scheme is quantified over all variables introduced
while typechecking the definition of the binding (including the variable representing the type of the binding itself). Whenever the scheme's
constraints are needed, instead a fresh instantiation of the quantified variables is produced and a reference to the scheme is inserted
into the constraints.

To define such a scheme to this system, we need to know its name, the quantified variables, and the entailed constraints.
The location of the scheme itself is the location of the definition.

```
Tyvar := "'" name
Tyvars := List{Tyvar, ","}
Schemes := List{Scheme}

Scheme := int SchemeName '(' Tyvars ')' '{' Constraints '}'
```

### Part 3: Constraints

```
Constraints := List{Constraint}

Constraint := int Type '=' Type
            | int SchemeName '(' Tyvars ')'

Type
  := PType name
   | PType

# parenthesized type, type constant, or type variable
PType := '(' Type '->' Type ')' 
       | '(' Type ( '*' Type )* ')'
       | name | "'" name
```

The `int` in each constraint is the number associated with the corresponding program range. 

Note that this gives the constraint generator quite some freedom to produce constraints however it wants, as long as it can attribute locations to them. For example, type variables in annotations can be treated as locally abstract while typechecking the definition, but as type variables when typechecking the use sites.

However, type constructors will not be kind-checked by this system since kind polymorphism is not supported. Whatever produces the constraints should check kinds.
