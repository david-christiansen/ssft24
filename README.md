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

In order to follow along in the final demo, you'll also need CaDiCaL -
the code has been tested with version 1.9.5. It is available in many
standard software repositories. For the final demo, you may also need
to increase your stack space - `ulimit -s 65520` seems to reliably
work.

## Branches

In case you want to follow along, the sample code in this repository
is organized into branches that represent checkpoints in the
interactive development:

 * `lec1/start` - the initial state of the repository
 * `lec1/step1` - the repository after the introductory code
   (`Intro.lean`) has been added and the implementation for `filter`
   on lists is no longer a stub
 * `lec1/step2` - the repository after the implementation from
   `lec1/step1` was verified
 * `lec1/step3` - the implementation using packed arrays has been
   added, but not verified
 * `lec1/step4` - the final state
 * `lec2/start` - the code from the first lecture is complete, and the
   second lecture is in its starting state (missing some proofs and
   definitions)
 * `lec2/step1` - the expression language has been implemented, with a
   verified optimization pass
 * `lec2/step2` - the statements of Imp have been implemented, with a
   big-step semantics and a verified optimization pass
 * `main` and `lec2/step3` - the final state of the imperative language

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
presented in the first lecture. We don't expect you to have time to
complete all these exercises, so please do the first one and then pick
what you're interested in to work on:

 * Define a function that appends two lists. Prove that the length of
   the output is the sum of the lengths of the input.
 * Implement `map` for `List`. What are some properties that it should
   satisfy? Prove that it does.
 * Define a binary tree datatype with two constructors: one represents
   the empty tree, and the other represents a labelled branch with a
   data item and two subtrees.
   * Define a predicate `All : (α → Prop) → Tree α → Prop` such that
     `All p t` is true whenever all data items in `t` satisfy `p`
   * Define a predicate `Sorted : Tree Nat → Prop` such that empty
     trees are sorted and branches are sorted if their left and right
     subtrees are sorted, all elements of the left subtree are less
     than or equal to the data item, and all elements of the right
     subtree are strictly greater than the data item.
   * Define a function `Tree.insert : Nat → Tree Nat → Tree Nat` that
     inserts a natural number into the given tree. If the input tree
     is sorted, then the output should be.
   * Prove that if a predicate holds for all natural numbers in a
     tree, and it holds for some new number, then it also holds for
     the all numbers in the tree with the new number inserted
   * Prove that inserting a number into a sorted tree yields a sorted
     tree.
   * Write an inductive predicate that holds when a tree contains a
     given element. It should have signature
     `Tree.Mem (x : α) : Tree α → Prop`.
   * Prove that if all data items in a tree satisfy a predicate and
     some particular item is in the tree (according to `Tree.Mem`),
     then that particular item satisfies the predicate.
   * Write a function that determines whether a given `Nat` is
     contained within a sorted tree, with type `Nat → Tree Nat → Bool`.
   * Prove that if all numbers in a tree `t` satisfy a predicate, and
     `contains n t = true`, then `n` satisfies the predicate.
   * Prove the correctness of `contains`: if a tree is sorted, then
     `Tree.Mem n t` is logically equivalent to `contains n t = true`.
 * State and prove some further properties of array filter (see the
   list filter file if you need inspiration)
 * Implement `map` for arrays. State and prove some properties about it.

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

 * Add a bitwise xor operator to Expr. Lean's bitwise xor operator is
   `^^^`.
 * Add a new arithmetic identity to the optimizer for `Expr` and
   update the correctness proof accordingly. For example, it could
   replace `E - E` with `0`, or `E + 0` with `E`.
 * These exercises don't require modifications to the `Stmt` datatype:
   * Add a unary `if` statement (that is, one without an `else`clause)
     to the user-facing syntax for `Stmt`
   * Add a `do...while...` statement to the surface syntax that
     executes the body at least once
 * Add a failure handler expression to `Expr`. The expression
   `try E1 then E2` should have `E1`'s value, unless the value is
   undefined, in which case it has `E2`'s value. Update the concrete
   syntax and the evaluator accordingly.
 * Add a random number generator to Imp:
   * Add a new statement that assigns a pseudorandom value to a given
     variable, and give it a concrete syntax
   * Define a pseudorandom number generator as a two-field structure
     with a state and a function from a state to a pair of a fresh
     state and a value. Implement a generator - there's no need for it
     to be secure, and a generator that just counts upwards is fine
     for the purposes of this exercise.
   * Update the big-step semantics to thread a random number generator
     through program execution. Provide a big-step rule for the `rand`
     statement and update the rest of Imp as needed so all the proofs
     go through.


## Tactic Cheatsheet

These are a few of the proof tactics that may be useful for the lab
sessions, along with summaries of the arguments and configuration
options that we think are most relevant:

 * `assumption` - if a local hypothesis solves the goal, use it
 * `contradiction` - search the local context for an "obvious"
   contradiction, and close the goal if it's found
 * `omega` - a Presburger arithmetic solver that can take care of many
   goals involving arithmetic
 * `intro x ...` - Transforms a goal like `A -> ... -> C` into `C`,
   with `A ...` made into assumptions named `x ...`
   * `x` can be replaced with a pattern when `A` has exactly one
     constructor
 * `unfold f` - replaces `f` with its definition in the goal
   * `unfold f at h` - replaces `f` with its definition in hypothesis
     `h`
 * `simp` - simplify the goal using a collection of rewrite rules. If
   `simp` makes the goal simple enough, it will go ahead and solve it.
   * `simp [r, ...]` - simplify the goal using additional rules `r,
     ...`. Rule possibilities include definition names, which causes
     them to be unfolded; proofs of equalities, which causes the left
     side to be replaced with the right side; and `*`, which causes
     local assumptions to be taken into account
   * `simp at h` - simplify hypothesis `h` instead of the goal (can be
     combined with rules list)
   * `simp_all` - perform as much simplification as possible
 * `rw [r1, ...]` - apply rewrites to the goal, one after the
   other. Each rewrite is the name of a theorem or assumption that
   proves an equality, and the left side is replaced with the right
   side. Preceding the rule with `←` causes the right side to be
   replaced with the left. Additional assumptions of the equality
   theorems are added as new goals. Can also be used with `at` to
   rewrite in an assumption.
 * `apply l` - apply the lemma `l` to the goal, matching up the
   lemma's conclusion with the goal and creating new goals for each
   assumption of the lemma that must be satisfied
   * `apply?` - search the Lean libraries for lemmas that might be
     relevant
 * `exact l` - just like `apply`, except fails if it introduces new
   goals
   * `exact?` - search the Lean libraries for lemmas that close the
     goal
 * `constructor` - apply the first type-correct constructor of the
   goal type
 * `T1 <;> T2` - runs `T1`, then runs `T2` in each subgoal that it
   creates
 * `repeat T` - runs `T` repeatedly until it fails
 * `repeat' T` - runs `T` repeatedly in each subgoal until it fails
 * `try T` - runs `T`, resetting the proof state if `T` fails
 * `. TACS` - in a context with multiple goals, focuses on the
   first. Fails if tactics `TACS` doesn't result in zero open goals.
 * `next =>` - in a context with multiple goals, focuses on the
   first. Fails if included tactics don't result in zero open goals.
 * `next h ...=>` - in a context with multiple goals, focuses on the
   first, assigning the names `h ...` to its unnamed
   assumptions. Fails if included tactics don't result in zero open
   goals.
 * `case c h ... =>` - in a context with multiple goals, focuses on
   the one named `c`. Otherwise like `next h ... =>`.
 * `split` - in a goal that contains an `if` or `match`, creates one
   new goal for each possible path of execution.
 * `cases e` - create a new goal for each constructor of a datatype or
   inductively defined proposition that is `e`'s type
   * `cases e with | c h ... => TACS ...` - like `cases`, but requires
     an explicit case for each goal `c` with hypotheses `h ...`
 * `induction x` - create a new goal for each constructor of a datatype
   or inductively defined proposition, assuming the current goal for
   each recursive occurrence (that is, with indution hypotheses).
   * `induction e with | c h ... => TACS ...` - like `induction`, but
     requires an explicit case for each goal `c` with hypotheses `h
     ...`
   * `induction e using i` - like `induction`, but uses the induction
     principle `i` instead of the default one
 * `have x : t := e` - introduce a new local assumption `x : t`, where
   `e` proves `t` (`e` often begins with `by`)
   * `x` can be omitted; in this case, the assumption is named `this`
   * `: t` can be omitted when `e`'s type can be inferred
   * `x` can be replaced with a pattern when `e`'s type has at most
     one constructor

