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
a0 =0= a6
a1.1 =1= b1.1 -> a2.1
...
```
The full file for this example contains some 16 assertions.

The paper describes an optimization which replaces duplicated sets of assertions from `let`-bound variables with a single quantified assertion. This is not currently supported. The syntax will introduce the quantified assertions before the regular ones, and they will be exported to SMT-LIB 2 as a defined function symbol.

### Part 1: Enumeration

The input consists of three parts. The first part is an enumeration of locations being type-checked. Tokens are separated by arbitrary whitespace.

```
Enumeration(0) := "0" Location
Enumeration(n) := Enumeration(n-1) n Location

Location := int ';' int '-' int ';' int
```

The tree structure (really, forest) is inferred from the ranges in the enumeration. There's a logarithmic cost to this. A future version may include the structure in the constraint file, perhaps with a syntax similar to graphviz-dot.

### Part 2: Constraints

```
Constraints := List{Constraint}

Constraint := Type '=' int '=' Type

Type
  := PType '->' PType
   | PType name
   | PType

# parenthesized type, type constant, or type variable
PType := '(' Type ( '*' Type )* ')' | name | "'" name
```

The `int` in each constraint is the number associated with the corresponding program range. 

Note that this gives the constraint generator quite some freedom to produce constraints however it wants, as long as it can attribute locations to them. For example, type variables in annotations can be treated as locally abstract while typechecking the definition, but to type variables when typechecking the use sites.
