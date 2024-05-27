import Imp.Expr

import Imp.Stmt.Delab
import Imp.Stmt.Optimize

namespace Imp

def Truthy (v : Option Value) : Prop :=
  match v with
  | some v => v ≠ 0
  | none => False

instance : Decidable (Truthy v) :=
  match v with
  | some v =>
    if h : v ≠ 0 then .isTrue h else .isFalse h
  | none => .isFalse id

@[simp]
theorem Truthy.some_nonzero : Truthy (some v) = (v ≠ 0) := by
  simp [Truthy]

@[simp]
theorem Truthy.not_none : Truthy none = False := by
  simp [Truthy]

@[simp]
theorem Truthy.eval_const : Truthy (Expr.eval σ (.const v)) = (v ≠ 0) := by
  simp [Truthy, Expr.eval]

def Falsy (v : Option Value) : Prop := v = some 0

@[simp]
theorem Falsy.eval_const : Falsy (Expr.eval σ (.const v)) = (v = 0) := by
  simp [Falsy, Expr.eval]

@[simp]
theorem Falsy.some_zero : Falsy (some v) = (v = 0) := by
  simp [Falsy]

@[simp]
theorem Falsy.not_none : Falsy none = False := by
  simp [Falsy]


instance : Decidable (Falsy v) := inferInstanceAs (Decidable (v = some 0))

theorem Truthy.not_falsy : Truthy v → ¬Falsy v := by
  intro h1 h2
  simp [Truthy, Falsy] at *
  cases v <;> simp at * <;> contradiction


namespace Stmt

inductive BigStep : Env → Stmt → Env → Prop where

/--
`swap` terminates, and the resulting environment contains swapped inputs.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by sorry

/--
`swap` terminates, and the resulting environment contains swapped inputs. This proof is shorter.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by sorry

example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) swap σ' ∧ σ'.get "x" = y ∧ σ'.get "y" = x  := by sorry

example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) min σ' ∧ if x < y then σ'.get "min" = x else σ'.get "min" = y := by sorry

def loop := imp {while (1) {skip;}}

theorem infinite_loop : ¬ BigStep σ loop σ' := by sorry

theorem optimize_ok : BigStep σ s σ' → BigStep σ s.optimize σ' := by sorry

/--
Run a program, with the depth of the recursive calls limited by the `Nat` parameter. Returns `none`
if the program doesn't terminate fast enough or if some other problem means the result is undefined
(e.g. division by zero).
 -/
def run (σ : Env) (s : Stmt) : Nat → Option Env
  | 0 => none
  | n + 1 =>
    match s with
    | imp {skip;} =>
      some σ
    | imp {~s1 ~s2} => do
      let σ' ← run σ s1 n
      run σ' s2 n
    | imp {~x := ~e;} => do
      let v ← e.eval σ
      pure (σ.set x v)
    | imp {if (~c) {~s1} else {~s2}} => do
      let v ← c.eval σ
      if v = 0 then
        run σ s2 n
      else
        run σ s1 n
    | imp {while (~c) {~s1}} => do
      let v ← c.eval σ
      if v = 0 then
        pure σ
      else
        let σ' ← run σ s1 n
        run σ' (imp {while (~c) {~s1}}) n

/--
`run` is correct: if it returns an answer, then that final state can be reached by the big-step
semantics. This is not total correctness - `run` could always return `none` - but it does increase
confidence.
-/
theorem run_some_implies_big_step : run σ s n = some σ' → BigStep σ s σ' := by sorry
/-
  intro term
  induction σ, s, n using run.induct generalizing σ' <;> unfold run at term <;> simp_all
  case case3 σ n s1 s2 ih1 ih2 =>
    let ⟨σ'', ⟨st1, st2⟩⟩ := term
    constructor
    . apply ih1
      apply st1
    . apply ih2
      apply st2
  case case4 =>
    let ⟨σ'', ⟨evEq, setEq⟩⟩ := term
    subst_eqs
    constructor; assumption
  case case5 ih1 ih2 =>
    let ⟨v, ⟨evEq, step⟩⟩ := term
    by_cases h : v = 0
    . subst_eqs; simp at *
      apply BigStep.ifFalse
      . simp [Falsy, *]
      . exact ih1 step
    . subst_eqs; simp at *
      apply BigStep.ifTrue
      . simp [Truthy, *]
      . simp [*] at step
        apply ih2; assumption
  case case6 ih1 ih2 =>
    let ⟨v, ⟨evEq, step⟩⟩ := term
    by_cases h : v = 0
    . subst_eqs; simp at *
      apply BigStep.whileFalse
      simp [Falsy, *]
    . subst_eqs; simp [*] at *
      simp [h] at step
      let ⟨σ', ⟨oneStep, loopStep⟩⟩ := step
      apply BigStep.whileTrue
      . rw [evEq]
        simp [*]
      . apply ih1
        exact oneStep
      . apply ih2
        exact loopStep
-/
