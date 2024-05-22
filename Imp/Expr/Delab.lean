import Lean.PrettyPrinter.Delaborator
import Imp.Expr.Basic
import Imp.Expr.Syntax

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

namespace Imp.Expr.Delab

def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

def delabNameInner : DelabM (TSyntax `varname) := do
  let e ← getExpr
  match e with
  | .lit (.strVal s) =>
    let x := mkIdent <| .mkSimple s
    pure <| ⟨x.raw⟩
  | _ => `(varname|~($(← delab))) >>= annAsTerm

partial def delabExprInner : DelabM (TSyntax `exp) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Expr.const x =>
      match_expr x with
      | OfNat.ofNat _ n _ =>
        if let some n' := n.nat? then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else if let .lit (.natVal n') := n then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else withAppArg `(exp| ~$(← delab))
      | Int.ofNat n =>
        if let some n' := n.nat? then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else if let .lit (.natVal n') := n then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else withAppArg `(exp| ~$(← delab))
      | BitVec.ofNat _ _ => (⟨·.raw⟩) <$> (withAppArg <| withAppArg <| delab)
      | _ =>
        `(exp| ~(Expr.const $(← withAppArg delab)))
    | Expr.var _ => do
      let x ← withAppArg delabNameInner
      `(exp|$x:varname)
    | Expr.bin op _ _ =>
      let s1 ← withAppFn <| withAppArg delabExprInner
      let s2 ← withAppArg delabExprInner
      match_expr op with
      | BinOp.plus => `(exp| $s1 + $s2)
      | BinOp.minus => `(exp| $s1 - $s2)
      | BinOp.times => `(exp| $s1 * $s2)
      | BinOp.div => `(exp| $s1 / $s2)
      | BinOp.and => `(exp| $s1 && $s2)
      | BinOp.or => `(exp| $s1 || $s2)
      | BinOp.lt => `(exp| $s1 < $s2)
      | BinOp.le => `(exp| $s1 ≤ $s2)
      | BinOp.eq => `(exp| $s1 == $s2)
      | BinOp.lsh => `(exp| $s1 <<< $s2)
      | BinOp.rsh => `(exp| $s1 >>> $s2)
      | BinOp.band => `(exp| $s1 &&& $s2)
      | BinOp.bor => `(exp| $s1 ||| $s2)
      | _ => `(exp|~(Expr.bin $(← withAppFn <| withAppFn <| withAppArg delab) $(← withAppFn <| withAppArg delab) $(← withAppArg delab)))
    | Expr.un op _ =>
      let s ← withAppArg delabExprInner
      match_expr op with
      | UnOp.neg => `(exp|-$s)
      | UnOp.not => `(exp|!$s)
      | _ => `(exp| ~(Expr.un $(← withAppFn <| withAppArg delab) $(← withAppArg delab)))
    | _ =>
      `(exp| ~$(← delab))
  annAsTerm stx

@[delab app.Imp.Expr.const, delab app.Imp.Expr.var, delab app.Imp.Expr.un, delab app.Imp.Expr.bin]
partial def delabExpr : Delab := do
  -- This delaborator only understands a certain arity - bail if it's incorrect
  guard <| match_expr ← getExpr with
    | Expr.const _ => true
    | Expr.var _ => true
    | Expr.un _ _ => true
    | Expr.bin _ _ _ => true
    | _ => false
  match ← delabExprInner with
  | `(exp|~$e) => pure e
  | e => `(term|expr {$(⟨e⟩)})

/-- info: expr { 5 } : Expr -/
#guard_msgs in
#check Expr.const 5

/-- info: expr { 5 } : Expr -/
#guard_msgs in
#check expr { 5 }

/-- info: expr { x } : Expr -/
#guard_msgs in
#check expr { x }

/-- info: expr { 5 + 23 - 10 } : Expr -/
#guard_msgs in
#check expr { 5 + 23 - 10 }

/-- info: expr { 5 + (23 - 10) } : Expr -/
#guard_msgs in
#check expr { 5 + (23 - 10) }

/-- info: expr { -8 <<< 4 } : Expr -/
#guard_msgs in
#check expr {-8 <<< 4}

/--
info: let x := expr { 23 };
expr { ~x * ~x } : Expr
-/
#guard_msgs in
#check let x := expr {23}; expr {~x * ~x}
