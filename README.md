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

### Lab Session

Please experiment with the Lean features and the ideas that were
presented in the first lecture. Here are some exercises to get you
started:

 * Implement `map` for list. What are some properties that it should
   satisfy? Prove that it does.
 * State and prove some further properties of array filter (see the
   list filter file if you need inspiration)
 * Implement `map` for arrays. State and prove some properties about it.
 * Define a function that appends two lists. Prove that the length of
   the output is the sum of the lengths of the input.

## Second Lecture: 

This lecture demonstrates how to use Lean for implementing languages
and proving things about programs written in them. The programs are
written in Imp, a minimal imperative language that features while
loops, mutable variables, and conditionals.

The following files are part of the second lecture:
 * `Imp.lean` - the top-level module that exists to import the others;
   also contains a final demo.
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
   - `Imp/Stmt/Basic.lean` - The core datastructure and syntax for statements
   - `Imp/Stmt/Optimize.lean` - Optimization of statements
   - `Imp/Stmt/BigStep.lean` - Operational semantics and proof that
     optimization is correct
   - `Imp/Stmt/Delab.lean` - Interactive display of statements (not
     part of lectures)

### Lab Session

These exercises are intended to be done in the context of the
development from the second lecture.

 * Add a new case to the optimizer for `Expr` and update the
   correctness proof accordingly
 * These exercises don't require modifications to the `Stmt` datatype:
   * Add a unary `if` statement (that is, one without an `else`clause)
     to the user-facing syntax for `Stmt`
   * Add a `do...while...` statement to the surface syntax that
     executes the body at least once
 * Add a `switch` statement like that of C, which takes an expression
   and a sequence of clauses, each of which is a value and a
   statement. The expression is evaluated, and then the first clause
   whose value matches its result is executed. If no clause matches,
   nothing happens.
    * First, add it to the `Stmt` datatype and design a surface syntax
      for it.
    * Next, add it to the optimizer. It's fine if it does nothing.
    * Add `switch` to the big-step semantics, and update the various
      proofs.
