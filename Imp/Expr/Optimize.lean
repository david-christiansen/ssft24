import Imp.Expr
import Imp.Expr.Eval

namespace Imp.Expr

def optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .un op e =>
    match optimize e with
    | .const i =>
      if let some v := op.apply i then .const v
      else .un op (.const i)
    | e' => .un op e'
  | .bin op e1 e2 =>
    match optimize e1, optimize e2 with
    | .const i, .const i' =>
      if let some v := op.apply i i' then .const v
      else .bin op (.const i) (.const i')
    | e1', e2' => .bin op e1' e2'

theorem optimize_ok (e : Expr) : e.eval ρ = e.optimize.eval ρ := by
  induction e <;> simp [optimize]
  case un op e ih =>
    split <;> simp [eval, *]
    cases op <;> simp [UnOp.apply, eval]
  case bin op e1 e2 ih1 ih2 =>
    split <;> simp [eval, *]
    cases op <;> simp [BinOp.apply, eval]
    split
    . simp [eval, BinOp.apply]; split <;> trivial
    . simp [eval]
