import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | .const i => sorry
  | .var x => sorry
  | .un op e => sorry
  | .bin op e1 e2 => sorry

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e with
  | const i => sorry
  | var x => sorry
  | un op e ih => sorry
  | bin op e1 e2 ih1 ih2 => sorry

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  sorry
