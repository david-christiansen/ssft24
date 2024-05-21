import Imp.Expr
import Imp.Expr.Eval
import Imp.Stmt
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

@[simp]
theorem Falsy.some_const : Falsy (some (BitVec.ofNat _ n)) → (n % 2 ^ 32 = 0) := by
  simp [Falsy, BitVec.ofNat, ← Fin.val_inj]

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

theorem BigStep.unique : BigStep ρ s ρ' → BigStep ρ s ρ'' → ρ' = ρ'' := by
  intro h1 h2
  induction h1 generalizing ρ'' with
  | «skip» => cases h2; rfl
  | seq _s1 _s2 ih1 ih2 =>
    cases h2 with
    | seq s1' s2' =>
      have := ih1 s1'
      subst this
      apply ih2 s2'
  | assign isVal =>
    cases h2 with
    | assign isVal' =>
      rw [isVal] at *
      subst_eqs
      rfl
  | ifTrue isTrue _stepTrue ih =>
    cases h2 with
    | ifTrue isTrue' stepTrue' =>
      exact ih stepTrue'
    | ifFalse isFalse =>
      have := isTrue.not_falsy
      contradiction
  | ifFalse isFalse _stepFalse ih =>
    cases h2 with
    | ifTrue isTrue' stepTrue' =>
      have := isTrue'.not_falsy
      contradiction
    | ifFalse isFalse' stepFalse' =>
      exact ih stepFalse'
  | whileTrue isTrue _stepBody _stepLoop ihBody ihLoop =>
    cases h2 with
    | whileTrue isTrue' stepBody' stepLoop' =>
      have := ihBody stepBody'
      subst this
      exact ihLoop stepLoop'
    | whileFalse isFalse' =>
      have := isTrue.not_falsy
      contradiction
  | whileFalse isFalse =>
    cases h2 with
    | whileTrue isTrue' stepBody' stepLoop' =>
      have := isTrue'.not_falsy
      contradiction
    | whileFalse isFalse' =>
      rfl





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
  induction h with try (simp [loop, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loop at h'
    cases h'
    cases cFalse

def loopOf (s) := imp {while (1) {~s}}

theorem infinite_loopOf : ¬ BigStep ρ (loopOf s) ρ' := by
  generalize h' : loopOf s = l
  intro h
  induction h with try (simp [loopOf, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loopOf at h'
    cases h'
    cases cFalse


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


inductive BigRes : Nat → Env → Stmt → Type where
  | done (ρ' : Env) : BigStep ρ s ρ' → BigRes n ρ s
  | noGas : BigRes n ρ s
  | crash : ¬(∃ρ', BigStep ρ s ρ') →  BigRes n ρ s

theorem BigStep.no_seq : ¬(∃ ρ', BigStep ρ (imp {~s1 ~s2}) ρ') ↔ ¬(∃ ρ' ρ'', BigStep ρ s1 ρ' ∧ BigStep ρ' s2 ρ'') := by
  constructor
  . intro no
    intro ⟨ρ', ρ'', st1, st2⟩
    apply no
    constructor; constructor
    exact st1
    exact st2
  . intro no
    rintro ⟨ρ', ⟨st1, st2⟩⟩
    apply no
    constructor; constructor
    constructor
    . assumption
    . assumption

theorem BigStep.no_assign : ¬(∃ ρ', BigStep ρ (imp {~x := ~e;}) ρ') ↔ e.eval ρ = none := by
  constructor
  . intro noSteps
    cases h : e.eval ρ <;> simp
    apply noSteps
    constructor
    constructor
    exact h
  . intro isNone
    intro h
    rcases h with ⟨_, ⟨isSome⟩⟩
    rw [isNone] at *; contradiction


def run (ρ : Env) (s : Stmt) : (n : Nat) → BigRes n ρ s
  | 0 => .noGas
  | n + 1 =>
    match s with
    | imp {skip;} =>
      .done ρ .skip
    | imp {~s1 ~s2} =>
      match run ρ s1 n with
      | .done ρ' st1 =>
        match run ρ' s2 n with
        | .done ρ'' st2 => .done ρ'' (.seq st1 st2)
        | .noGas => .noGas
        | .crash no => .crash <| by
          rw [BigStep.no_seq]
          rintro ⟨ρ', ρ'', st1', st2'⟩
          apply no
          have := BigStep.unique st1 st1'
          subst this
          constructor; assumption
      | .noGas => .noGas
      | .crash no => .crash <| by
        rw [BigStep.no_seq]
        intro h
        simp at h
        apply no
        rcases h with ⟨_, _, ⟨_, _⟩⟩
        constructor; assumption
    | imp {~x := ~e;} =>
      match h : e.eval ρ with
      | none => .crash <| by
        rw [BigStep.no_assign]
        simp [*]
      | some v => .done _ (.assign h)
    | imp {if (~c) {~s1} else {~s2}} =>
      match h : c.eval ρ with
      | none => .crash <| by
        intro ⟨ρ', st⟩
        cases st with
        | ifTrue =>
          simp [*] at *
        | ifFalse =>
          simp [*] at *
      | some v =>
        if h' : v = 0 then
          match run ρ s2 n with
          | .done ρ' step => .done ρ' (.ifFalse (by simp [h, h']) step)
          | .noGas => .noGas
          | .crash no => .crash <| by
            intro ⟨ρ', st⟩
            apply no
            cases st with
            | ifTrue isTrue step1 =>
              have := isTrue.not_falsy
              simp [*] at *
            | ifFalse isFalse step2 =>
              constructor; assumption
        else
          match run ρ s1 n with
          | .done ρ' step => .done ρ' (.ifTrue (by simp [h, h']; assumption) step)
          | .noGas => .noGas
          | .crash no => .crash <| by
            intro ⟨ρ', st⟩
            apply no
            cases st with
            | ifTrue isTrue step1 =>
              constructor; assumption
            | ifFalse isFalse step2 =>
              simp [Falsy, h, h'] at isFalse
              contradiction
    | imp {while (~c) {~s1}} =>
      match h : c.eval ρ with
      | none => .crash <| by
        intro ⟨ρ', st⟩
        cases st <;> simp [*] at *
      | some v =>
        if h' : v = 0 then
          .done _ <| .whileFalse (by simp [*])
        else
          have truthy : Truthy (c.eval ρ) := by simp [*]; assumption
          match run ρ s1 n with
          | .done ρ' step =>
            match run ρ' (imp {while (~c) {~s1}}) n with
            | .done ρ'' step' =>
              .done ρ'' (.whileTrue truthy step step')
            | .noGas => .noGas
            | .crash no =>
              .crash <| by
                intro ⟨ρ'', st⟩
                cases st
                . have := BigStep.unique step (by assumption)
                  subst this
                  apply no
                  constructor; assumption
                . simp [*] at *; contradiction
          | .noGas => .noGas
          | .crash no => .crash <| by
            intro ⟨ρ', st⟩
            cases st with
            | whileFalse =>
              simp [*] at *; contradiction
            | whileTrue =>
              apply no
              constructor; assumption

def run' (ρ : Env) (s : Stmt) : (n : Nat) → Option Env
  | 0 => none
  | n + 1 =>
    match s with
    | imp {skip;} =>
      some ρ
    | imp {~s1 ~s2} => do
      let ρ' ← run' ρ s1 n
      run' ρ' s2 n
    | imp {~x := ~e;} => do
      let v ← e.eval ρ
      pure (ρ.set x v)
    | imp {if (~c) {~s1} else {~s2}} => do
      let v ← c.eval ρ
      if v = 0 then
        run' ρ s2 n
      else
        run' ρ s1 n
    | imp {while (~c) {~s1}} => do
      let v ← c.eval ρ
      if v = 0 then
        pure ρ
      else
        let ρ' ← run' ρ s1 n
        run' ρ' (imp {while (~c) {~s1}}) n


def terminatesWith (n : Nat) (ρ : Env) (s : Stmt) : Option Env :=
  match run ρ s n with
  | .done ρ' _ => some ρ'
  | _ => none
