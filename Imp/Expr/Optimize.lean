import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | expr => expr

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by sorry

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by sorry
