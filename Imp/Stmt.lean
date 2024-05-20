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

syntax "program" ppHardSpace "{" ppLine stmt ppDedent(ppLine "}") : term


open Lean in
macro_rules
  | `(program { skip; }) => `(Stmt.skip)
  | `(program { $s1 $s2 }) => `(Stmt.seq (program {$s1}) (program {$s2}))
  | `(program { $x:varname := $e;}) =>
      `(Stmt.assign var {$x} expr {$e})
  | `(program { if ($c) {$s1} else {$s2} }) => `(Stmt.if expr{$c} (program{$s1}) (program{$s2}))
  | `(program { while ($c) {$s} }) => `(Stmt.while expr{$c} (program{$s}))
  | `(program { ~$stx }) => pure stx
