/-
This file makes the convenient syntax from `Imp.Stmt.Basic` show up in Lean's output. It's not part
of what's being taught in the lectures.
-/
import Lean.PrettyPrinter.Delaborator
import Imp.Stmt.Basic
import Imp.Expr

open Lean PrettyPrinter.Delaborator SubExpr

namespace Imp.Stmt.Delab

open Imp.Stmt
open Imp.Expr.Delab

partial def delabStmtInner : DelabM (TSyntax `stmt) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Stmt.skip => `(stmt| skip;)
    | Stmt.seq _ _ =>
      let s1 ← withAppFn <| withAppArg delabStmtInner
      let s2 ← withAppArg delabStmtInner
      `(stmt| $s1 $s2)
    | Stmt.assign _ _ =>
      let x ← withAppFn <| withAppArg delabNameInner
      let e ← withAppArg delabExprInner
      `(stmt| $x:varname := $e;)
    | Stmt.while _ _ =>
      let c ← withAppFn <| withAppArg delabExprInner
      let body ← withAppArg delabStmtInner
      `(stmt| while ($c) { $body })
    | Stmt.if _ _ _ =>
      let c ← withAppFn <| withAppFn <| withAppArg delabExprInner
      let t ← withAppFn <| withAppArg delabStmtInner
      let f ← withAppArg delabStmtInner
      `(stmt| if ($c) { $t } else { $f })
    | _ =>
      `(stmt| ~$(← delab))
  annAsTerm stx

@[delab app.Imp.Stmt.skip, delab app.Imp.Stmt.seq, delab app.Imp.Stmt.while, delab app.Imp.Stmt.assign, delab app.Imp.Stmt.if]
partial def delabStmt : Delab := do
  -- This delaborator only understands a certain arity - bail if it's incorrect
  guard <| match_expr ← getExpr with
    | Stmt.skip => true
    | Stmt.seq _ _ => true
    | Stmt.while _ _ => true
    | Stmt.assign _ _ => true
    | Stmt.if _ _ _ => true
    | _ => false
  match ← delabStmtInner with
  | `(stmt|~$e) => pure e
  | s => `(term|imp{$s})

/-- info: Imp.Stmt.skip : Stmt -/
#guard_msgs in
#check Stmt.skip

/--
info: imp {
  skip;
} : Stmt
-/
#guard_msgs in
#check imp {skip;}

/--
info: imp {
  skip;
  skip;
} : Stmt
-/
#guard_msgs in
#check imp {skip; skip;}

/--
info: imp {
  skip;
  skip;
  x := 5;
} : Stmt
-/
#guard_msgs in
#check imp {skip; skip; x := 5;}

/--
info: imp {
  skip;
  if (0 < x) {
    x := x - 1;
  } else {
    skip;
  }
} : Stmt
-/
#guard_msgs in
#check imp {skip; if (x > 0) { x := x - 1;} else {skip;}}

/--
info: imp {
  skip;
  while (0 < x) {
      x := x - 1;
    }
  if (x) {
    skip;
  } else {
    while (5 < x) {
      skip;
      skip;
    }
  }
} : Stmt
-/
#guard_msgs in
#check imp {skip; while (x > 0) { x := x - 1;} if (x) {skip;} else {while (x > 5) {skip; skip;}}}

/--
info: let s :=
  imp {
    skip;
  };
imp {
  skip;
  while (0 < x) {
      x := x - 1;
    }
  if (x) {
    skip;
  } else {
    while (5 < x) {
      skip;
      ~s
    }
  }
} : Stmt
-/
#guard_msgs in
#check let s := imp {skip;}; imp {skip; while (x > 0) { x := x - 1;} if (x) {skip;} else {while (x > 5) {skip; ~s}}}
