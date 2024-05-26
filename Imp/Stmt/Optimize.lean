import Imp.Expr
import Imp.Stmt.Basic
import Imp.Stmt.Delab

namespace Imp.Stmt

/-- Optimize a statement -/
def optimize : Stmt → Stmt
  | stmt => stmt
