import Lean.PrettyPrinter.Delaborator
import LeanSAT.Reflect.Tactics.BVDecide

import Imp.Expr
import Imp.Stmt

namespace Imp.Stmt

open BitVec -- Enables bitvector literal syntax and lemmas

/-
The final demo - read this file last!
-/

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

/--
Alternative implementation of popcount from Hacker's Delight, Second Edition, by Henry S. Warren,
Jr. Figure 5-2 on p. 82.
-/
def popcount : Stmt := imp {
  x := x - ((x >>> 1) &&& 0x55555555);
  x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  x := x + (x >>> 8);
  x := x + (x >>> 16);
  x := x &&& 0x0000003F;
}


def pop_spec (x : BitVec 32) : BitVec 32 :=
  go x 0 32
where
  go (x : BitVec 32) (pop : BitVec 32) (i : Nat) : BitVec 32 :=
    match i with
    | 0 => pop
    | i + 1 =>
      let pop := pop + (x &&& 1#32)
      go (x >>> 1#32) pop i


theorem popCount_correctBig :
    ∃ ρ, (run (Env.init x) popcount 8) = some ρ ∧ ρ "x" = pop_spec x := by
  simp [run, popcount, Expr.eval, Expr.BinOp.apply, Env.set, Value, pop_spec, pop_spec.go]
  bv_decide
