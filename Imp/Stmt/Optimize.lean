import Imp.Expr
import Imp.Stmt.Basic
import Imp.Stmt.Delab

namespace Imp.Stmt

/-- Optimize a statement -/
def optimize : Stmt → Stmt
  | imp {skip;} => sorry
  | imp {~s1 ~s2} => sorry
  | imp {~x := ~e;} => sorry
  | imp {if (~c) {~s1} else {~s2}} => sorry
  | imp {while (~c) {~s}} => sorry
