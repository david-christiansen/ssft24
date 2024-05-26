import Imp.Expr

namespace Imp

/-- Statements in Imp -/
inductive Stmt where
  /-- A statement that does nothing -/
  | skip
  /-- Executes `stmt1` then `stmt2` -/
  | seq (stmt1 stmt2 : Stmt)
  /-- Modifies a variable in the state -/
  | assign (name : String) (val : Expr)
  /--
  Conditional: executes `ifTrue` when `cond`'s value is nonzero, `ifFalse` otherwise
  -/
  | if (cond : Expr) (ifTrue ifFalse : Stmt)
  /--
  Repeats `body` as long as `cond` evaluates to a nonzero value
  -/
  | while (cond : Expr) (body : Stmt)
deriving Repr, DecidableEq

/-- Imp statements -/
declare_syntax_cat stmt
/-- A statement that does nothing -/
syntax "skip" ";" : stmt
/-- Sequencing: one statement after another -/
syntax stmt ppDedent(ppLine stmt) : stmt
/-- Assignment -/
syntax varname " := " exp ";" : stmt
/-- Conditional statement -/
syntax "if " "(" exp ")" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine stmt ppDedent(ppLine "}") : stmt
/-- Loop -/
syntax "while " "(" exp ")" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : stmt
/-- Escape to Lean -/
syntax:max "~" term:max : stmt

/-- Include an Imp statement in Lean code -/
syntax:min "imp" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : term

/-
The above rules are equivalent to the following, but with nicer-looking compiler output:

syntax "skip" ";" : stmt
syntax stmt stmt : stmt
syntax varname " := " exp ";" : stmt
syntax "if " "(" exp ") " "{" stmt "}" "else" "{" stmt "}" : stmt
syntax "while " "(" exp ") "  "{" stmt "}" : stmt
syntax:max "~" term:max : stmt

syntax:min "imp" "{" stmt "}" : term
-/


open Lean in
macro_rules
  | `(imp { skip; }) =>
    `(Stmt.skip)
  | `(imp { $s1 $s2 }) =>
    `(Stmt.seq (imp {$s1}) (imp {$s2}))
  | `(imp { $x:varname := $e;}) =>
    `(Stmt.assign (var {$x}) (expr {$e}))
  | `(imp { if ($c) {$s1} else {$s2} }) =>
    `(Stmt.if (expr{$c}) (imp{$s1}) (imp{$s2}))
  | `(imp { while ($c) {$s} }) =>
    `(Stmt.while (expr{$c}) (imp{$s}))
  | `(imp { ~$stx }) =>
    pure stx


def swap : Stmt := imp {
  temp := x;
  x := y;
  y := temp;
}

def min : Stmt := imp {
  if (x < y) {
    min := x;
  } else {
    min := y;
  }
}

def fact : Stmt := imp {
  out := 1;
  while (n > 0) {
    out := out * n;
    n := n - 1;
  }
}
