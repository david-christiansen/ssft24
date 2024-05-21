import Lean.PrettyPrinter.Delaborator
import LeanSAT.Reflect.Tactics.BVDecide

import Imp.Expr
import Imp.Expr.Eval
import Imp.Expr.Optimize
import Imp.Expr.Delab

import Imp.Stmt
import Imp.Stmt.Delab
import Imp.Stmt.BigStep
import Imp.Stmt.Optimize

namespace Imp

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

open Stmt

open BitVec


def popcount : Stmt := imp {
  x := x - ((x >>> 1) &&& 0x55555555);
  x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  x := x + (x >>> 8);
  x := x + (x >>> 16);
  x := x &&& 0x0000003F;
}

def popcountLoop : Stmt := imp {
  i := 32;
  count := 0;
  while (i > 0) {
    count := count + (x &&& 1);
    i := i - 1;
    x := x >>> 1;
  }
  x := count;
}

def pop_spec' (x : BitVec 32) : BitVec 32 :=
  go x 0#32 32
where
  go (x : BitVec 32) (pop : BitVec 32) (i : Nat) : BitVec 32 :=
    match i with
    | 0 => pop
    | i + 1 =>
      let pop := pop + (x &&& 1#32)
      go (x >>> 1#32) pop i


@[simp]
theorem Env.get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem Env.get_set_same {ρ : Env} : (ρ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem Env.get_set_different {ρ : Env} : x ≠ y → (ρ.set x v).get y = ρ.get y := by
  intros
  simp [get, set, *]

theorem popCount_correctBig : ∃ ρ, (run' (Env.init x) popcount 8) = some ρ ∧ ρ "x" = pop_spec' x := by
  simp [run', popcount, Expr.eval, Expr.BinOp.apply, Env.set, Value, pop_spec', pop_spec'.go]
  bv_decide
