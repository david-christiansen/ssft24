import Imp.Expr.Basic

open Lean

namespace Imp

/-- Values stored in memory - 32-bit integers -/
abbrev Value := BitVec 32

/-- An environment maps variables names to their values (no pointers) -/
def Env := String → Value

namespace Env

/-- Set a value in an environment -/
def set (x : String) (v : Value) (ρ : Env) : Env :=
  fun y => if x == y then v else ρ y

/-- Look up a value in an environment -/
def get (x : String) (ρ : Env) : Value :=
  ρ x

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env := fun _ => i

@[simp]
theorem get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem get_set_same {ρ : Env} : (ρ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem get_set_different {ρ : Env} : x ≠ y → (ρ.set x v).get y = ρ.get y := by
  intros
  simp [get, set, *]

end Env

namespace Expr

/-- Helper that implements unary operators -/
def UnOp.apply : UnOp → Value → Option Value
  | .neg, x => some (- x)
  | .not, x => some (if x == 0 then 1 else 0)

/-- Helper that implements binary operators -/
def BinOp.apply : BinOp → Value → Value → Option Value
  | .plus, x, y => some (x + y)
  | .minus, x, y => some (x - y)
  | .times, x, y => some (x * y)
  | .lsh, x, y => some (x <<< y)
  | .rsh, x, y => some (x >>> y)
  | .band, x, y => some (x &&& y)
  | .bor, x, y => some (x ||| y)
  | .div, x, y => if y == 0 then none else some (x / y)
  | .and, x, y => some (if x == 0 then 0 else y)
  | .or, x, y => some (if x == 0 then y else x)
  | .eq, x, y => some (if x == y then 1 else 0)
  | .le, x, y => some (if x ≤ y then 1 else 0)
  | .lt, x, y => some (if x < y then 1 else 0)

/--
Evaluates an expression, finding the value if it has one.

Expressions that divide by zero don't have values - the result is undefined.
-/
def eval (ρ : Env) : Expr → Option Value
  | .const i => some i
  | .var x => ρ.get x
  | .un op e => do
    let v ← e.eval ρ
    op.apply v
  | .bin op e1 e2 => do
    let v1 ← e1.eval ρ
    let v2 ← e2.eval ρ
    op.apply v1 v2
