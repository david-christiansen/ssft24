import Imp.Expr

import Imp.Stmt.Delab
import Imp.Stmt.Optimize

namespace Imp

/--
Truthiness: the result of evaluating an expression is "truthy" if it's defined and non-zero.
-/
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
theorem Truthy.eval_const : Truthy (Expr.eval ρ (.const v)) = (v ≠ 0) := by
  simp [Truthy, Expr.eval]

/--
Falsiness: the result of evaluating an expression is "falsy" if it's 0
-/
def Falsy (v : Option Value) : Prop := v = some 0

@[simp]
theorem Falsy.eval_const : Falsy (Expr.eval ρ (.const v)) = (v = 0) := by
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
  | skip :
    BigStep ρ (imp {skip;}) ρ
  | seq :
    BigStep ρ s1 ρ' → BigStep ρ' s2 ρ'' →
    BigStep ρ (imp{ ~s1 ~s2}) ρ''
  | assign :
    e.eval ρ = some v →
    BigStep ρ (imp {~x := ~e;}) (ρ.set x v)
  | ifTrue :
    Truthy (c.eval ρ) → BigStep ρ s1 ρ' →
    BigStep ρ (imp {if (~c) {~s1} else {~s2}}) ρ'
  | ifFalse :
    Falsy (c.eval ρ) → BigStep ρ s2 ρ' →
    BigStep ρ (imp {if (~c) {~s1} else {~s2}}) ρ'
  | whileTrue :
    Truthy (c.eval ρ) →
    BigStep ρ body ρ' →
    BigStep ρ' (imp {while (~c) {~body}}) ρ'' →
    BigStep ρ (imp {while (~c) {~body}}) ρ''
  | whileFalse :
    Falsy (c.eval ρ) →
    BigStep ρ (imp {while (~c) {~body}}) ρ

attribute [simp] BigStep.skip

/--
`swap` terminates, and the resulting environment contains swapped inputs.
-/
example : ∃ρ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap ρ' ∧ ρ'.get "x" = 22 ∧ ρ'.get "y" = 5 := by
  unfold swap
  apply Exists.intro
  constructor
  . apply BigStep.seq
    . apply BigStep.assign
      simp [Expr.eval, Env.get, Env.set]
      rfl
    . apply BigStep.seq
      . apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
      . simp
        apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
  . simp [Env.get, Env.set]

/--
`swap` terminates, and the resulting environment contains swapped inputs. This proof is shorter.
-/
example : ∃ρ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap ρ' ∧ ρ'.get "x" = 22 ∧ ρ'.get "y" = 5 := by
  repeat' constructor

/--
`swap` terminates, and the resulting environment contains swapped inputs. This version works no
matter what the input values are.
-/
example : ∃ρ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) swap ρ' ∧ ρ'.get "x" = y ∧ ρ'.get "y" = x  := by
  repeat' constructor

/--
`min` computes the minimum of its inputs.
-/
example : ∃ρ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) min ρ' ∧ if x < y then ρ'.get "min" = x else ρ'.get "min" = y := by
  unfold min
  by_cases h : x < y
  . apply Exists.intro; constructor
    . apply BigStep.ifTrue
      . simp [Expr.eval, Expr.BinOp.apply, Env.get, Env.set, *]; decide
      . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
    . simp [Env.get, Env.set]
      intro; contradiction
  . apply Exists.intro; constructor
    . apply BigStep.ifFalse
      . simp [Expr.eval, Expr.BinOp.apply, Env.get, Env.set, *]
      . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
    . simp [Env.get, Env.set]
      intro; contradiction

def loop := imp {while (1) {skip;}}

/--
`loop` is really an infinite loop - there is no final state that it can result in.
-/
theorem infinite_loop : ¬ BigStep ρ loop ρ' := by
  generalize h' : loop = l
  intro h
  induction h <;> try (simp [loop, *] at *; done)
  case whileTrue =>
    simp [*]
  case whileFalse cFalse =>
    unfold loop at h'
    cases h'
    simp at cFalse
    contradiction

theorem optimize_ok : BigStep ρ s ρ' → BigStep ρ s.optimize ρ' := by
  intro h
  induction h with simp only [optimize]
  | «skip» => constructor
  | seq s1 s2 ih1 ih2 =>
    split
    next eq2 =>
      rw [eq2] at ih1
      cases ih1; apply ih2
    next eq1 eq2 =>
      rw [eq1] at ih2
      cases ih2; apply ih1
    next =>
      apply BigStep.seq ih1 ih2
  | assign m =>
    constructor
    rw [← Expr.optimize_ok]
    assumption
  | ifTrue isTrue l ih =>
    split
    next isFalse =>
      rw [Expr.optimize_ok] at isTrue
      rw [isFalse] at isTrue
      simp [Truthy, Expr.eval] at isTrue
    next notFalse _isConst =>
      apply ih
    next =>
      split
      . assumption
      . apply BigStep.ifTrue
        . rw [← Expr.optimize_ok]
          assumption
        . assumption
  | ifFalse isFalse l ih =>
    split
    next =>
      apply ih
    next nonZero isConst =>
      rw [Expr.optimize_ok, isConst] at isFalse
      simp at isFalse
      contradiction
    next =>
      split
      . simp [*]
      . apply BigStep.ifFalse
        . rw [← Expr.optimize_ok]
          assumption
        . assumption
  | whileFalse =>
    split <;> try simp
    apply BigStep.whileFalse
    rw [← Expr.optimize_ok]
    assumption
  | whileTrue isTrue bodyStep nextStep ih1 ih2 =>
    split
    next c isZero =>
      rw [Expr.optimize_ok, isZero] at isTrue
      simp at isTrue
    next c isNotZero =>
      apply BigStep.whileTrue
      . rw [← Expr.optimize_ok]
        assumption
      . apply ih1
      . simp [optimize] at ih2
        assumption


def run (ρ : Env) (s : Stmt) : Nat → Option Env
  | 0 => none
  | n + 1 =>
    match s with
    | imp {skip;} =>
      some ρ
    | imp {~s1 ~s2} => do
      let ρ' ← run ρ s1 n
      run ρ' s2 n
    | imp {~x := ~e;} => do
      let v ← e.eval ρ
      pure (ρ.set x v)
    | imp {if (~c) {~s1} else {~s2}} => do
      let v ← c.eval ρ
      if v = 0 then
        run ρ s2 n
      else
        run ρ s1 n
    | imp {while (~c) {~s1}} => do
      let v ← c.eval ρ
      if v = 0 then
        pure ρ
      else
        let ρ' ← run ρ s1 n
        run ρ' (imp {while (~c) {~s1}}) n

theorem run'_correct : run ρ s n = some ρ' → BigStep ρ s ρ' := by
  intro term
  induction ρ, s, n using run.induct generalizing ρ' <;> unfold run at term <;> simp_all
  case case3 ρ n s1 s2 ih1 ih2 =>
    let ⟨ρ'', ⟨st1, st2⟩⟩ := term
    constructor
    . apply ih1
      apply st1
    . apply ih2
      apply st2
  case case4 =>
    let ⟨ρ'', ⟨evEq, setEq⟩⟩ := term
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
      let ⟨ρ', ⟨oneStep, loopStep⟩⟩ := step
      apply BigStep.whileTrue
      . rw [evEq]
        simp [*]
      . apply ih1
        exact oneStep
      . apply ih2
        exact loopStep
