# Lean @ SSFT 2024

This repository contains materials used during Leo de Moura and David
Thrane Christiansen's presentation at SSFT 2024.

## Getting Ready

To prepare for the Lean lectures, please install Lean using the
[official instructions](https://lean-lang.org/lean4/doc/quickstart.html).
This will set up everything you need for the summer school.

If for some reason you can't follow these instructions, please make
sure that the way you install Lean ends up with an installation of
`elan`, the Lean toolchain version manager, rather than a specific
version of Lean itself (e.g. from `nixpkgs`). The installation of elan
worked if you can type `lean +4.7.0 --version` in your home directory,
and it prints out `Lean (version 4.7.0, ...)`, and typing
`lean +nightly-2024-05-19 --version` prints something like
`Lean (version 4.9.0-nightly-2024-04-19, ...)`.

## First Lecture: Introduction to Lean

This lecture is an introduction to writing programs, and proving them
correct, in Lean. After an introduction to Lean's syntax and the very
basics of using its type theory as a logic, we interactively write a
program that filters JSON objects, and prove it correct with respect
to a number of specifications.

The following files are part of the first lecture:

 * `Intro.lean`
 * The contents of the `tests/` directory
 * `Main.lean` - the entry point for the JSON filter
 * `Filter.lean` and the contents of `Filter/`:
   - `Filter/List.lean` - a verified implementation of filtering lists
   - `Filter/Array.lean` - a verified implementation of filtering arrays
   - `Filter/Input.lean` - utilities for reading JSON (not part of
     lectures)
   - `Filter/Query.lean` - a query language (not part of lectures)



## Second Lecture: 

This lecture demonstrates how to use Lean for implementing languages
and proving things about programs written in them. The programs are
written in Imp, a minimal imperative language that features while
loops, mutable variables, and conditionals.

The following files are part of the second lecture:
 * `Imp.lean` - the top-level module that exists to import the others
 * `Imp/Expr.lean` - definition of an expression datatype and
   convenient syntax for writing it
 * `Imp/Expr/` - expressions and evaluation:
   - `Imp/Expr/Eval.lean` - Evaluating expressions
   - `Imp/Expr/Optimize.lean` - Constant-folding optimization of
     expressions
   - `Imp/Expr/Delab.lean` - Interactive display of expressions (not
     part of lectures)
 * `Imp/Stmt.lean` - definition of a statement datatype and convenient
   syntax for writing it
   - `Imp/Stmt/Optimize.lean` - Optimization of expressions
   - `Imp/Stmt/BigStep.lean` - Operational semantics and proof that
     optimization is correct
   - `Imp/Stmt/Delab.lean` - Interactive display of statements (not
     part of lectures)

