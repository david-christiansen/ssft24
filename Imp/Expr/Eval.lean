import Imp.Expr

namespace Imp

abbrev Value := BitVec 32

def Env := String → Value

namespace Env

def set (x : String) (v : Value) (ρ : Env) : Env :=
  fun y => if x == y then v else ρ y

def get (x : String) (ρ : Env) : Value :=
  ρ x

def init (i : Value) : Env := fun _ => i

end Env

namespace Expr

def freeVars : Expr → List String
  | .const _ => []
  | .var x => [x]
  | .un _ e => e.freeVars
  | .bin _ e1 e2 => e1.freeVars ++ e2.freeVars

def UnOp.apply : UnOp → Value → Option Value
  | .neg, x => some (- x)
  | .not, x => some (if x == 0 then 1 else 0)

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
