import Imp.Expr

namespace Imp

inductive Stmt where
  | skip
  | seq (stmt1 stmt2 : Stmt)
  | assign (name : String) (val : Expr)
  | if (cond : Expr) (ifTrue ifFalse : Stmt)
  | while (cond : Expr) (body : Stmt)
deriving Repr, DecidableEq

namespace Stmt

declare_syntax_cat stmt
scoped syntax "skip" ";" : stmt
scoped syntax stmt ppDedent(ppLine stmt) : stmt
scoped syntax varname " := " exp ";" : stmt
scoped syntax "if " "(" exp ")" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}" ppHardSpace "else" ppHardSpace "{") ppLine stmt ppDedent(ppLine "}") : stmt
scoped syntax "while " "(" exp ")" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : stmt
scoped syntax:max "~" term:max : stmt

syntax "imp" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : term


open Lean in
macro_rules
  | `(imp { skip; }) => `(Stmt.skip)
  | `(imp { $s1 $s2 }) => `(Stmt.seq (imp {$s1}) (imp {$s2}))
  | `(imp { $x:varname := $e;}) =>
      `(Stmt.assign (var {$x}) (expr {$e}))
  | `(imp { if ($c) {$s1} else {$s2} }) => `(Stmt.if (expr{$c}) (imp{$s1}) (imp{$s2}))
  | `(imp { while ($c) {$s} }) => `(Stmt.while (expr{$c}) (imp{$s}))
  | `(imp { ~$stx }) => pure stx

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
