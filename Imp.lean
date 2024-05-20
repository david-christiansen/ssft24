import Lean.PrettyPrinter.Delaborator
import LeanSAT.Reflect.Tactics.BVDecide

import Imp.Expr
import Imp.Expr.Eval
import Imp.Expr.Optimize
import Imp.Expr.Delab

import Imp.Stmt
import Imp.Stmt.Delab

namespace Imp

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

open Stmt

open BitVec

def Stmt.optimize : Stmt → Stmt
  | program {skip;} => program {skip;}
  | program {~s1 ~s2} =>
    match s1.optimize, s2.optimize with
    | program {skip;}, s2' => s2'
    | s1', program {skip;} => s1'
    | s1', s2' => program {~s1' ~s2'}
  | program {if (~c) {~s1} else {~s2}} =>
    let c' := c.optimize
    match c' with
    | .const 0 => s2.optimize
    | .const _ => s1.optimize
    | _ =>
      let s1' := s1.optimize
      let s2' := s2.optimize
      if s1' = s2' then
        s1'
      else program {if (~c') {~s1.optimize} else {~s2.optimize}}
  | program {while (~c) {~s}} =>
    let c' := c.optimize
    match c' with
    | .const 0 => program {skip;}
    | _ => program {while (~c') {~s.optimize}}
  | program {~x := ~e;} =>
    program {~x := ~e.optimize;}

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
theorem Truthy.eval_const : Truthy (Expr.eval ρ (.const v)) = (v ≠ 0) := by
  simp [Truthy, Expr.eval]

def Falsy (v : Option Value) : Prop := v = some 0

@[simp]
theorem Falsy.eval_const : Falsy (Expr.eval ρ (.const v)) = (v = 0) := by
  simp [Falsy, Expr.eval]

@[simp]
theorem Falsy.some_zero : Falsy (some v) = (v = 0) := by
  simp [Falsy]

@[simp]
theorem Falsy.some_const : Falsy (some (BitVec.ofNat _ n)) → (n % 2 ^ 32 = 0) := by
  simp [Falsy, BitVec.ofNat, ← Fin.val_inj]


instance : Decidable (Falsy v) := inferInstanceAs (Decidable (v = some 0))


inductive BigStep : Env → Stmt → Env → Prop where
  | skip :
    BigStep ρ (program {skip;}) ρ
  | seq :
    BigStep ρ s1 ρ' → BigStep ρ' s2 ρ'' →
    BigStep ρ (program{ ~s1 ~s2}) ρ''
  | assign :
    e.eval ρ = some v →
    BigStep ρ (program {~x := ~e;}) (ρ.set x v)
  | ifTrue :
    Truthy (c.eval ρ) → BigStep ρ s1 ρ' →
    BigStep ρ (program {if (~c) {~s1} else {~s2}}) ρ'
  | ifFalse :
    Falsy (c.eval ρ) → BigStep ρ s2 ρ' →
    BigStep ρ (program {if (~c) {~s1} else {~s2}}) ρ'
  | whileTrue :
    Truthy (c.eval ρ) →
    BigStep ρ body ρ' →
    BigStep ρ' (program {while (~c) {~body}}) ρ'' →
    BigStep ρ (program {while (~c) {~body}}) ρ''
  | whileFalse :
    Falsy (c.eval ρ) →
    BigStep ρ (program {while (~c) {~body}}) ρ

attribute [simp] BigStep.skip



def loop := program {while (1) {skip;}}

def loopOf (s) := program {while (1) {~s}}

theorem Stmt.infinite_loop : ¬ BigStep ρ loop ρ' := by
  generalize h' : loop = l
  intro h
  induction h with try (simp [loop, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loop at h'
    cases h'
    cases cFalse

theorem Stmt.infinite_loopOf : ¬ BigStep ρ (loopOf s) ρ' := by
  generalize h' : loopOf s = l
  intro h
  induction h with try (simp [loopOf, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loopOf at h'
    cases h'
    cases cFalse

theorem Stmt.optimize_ok : BigStep ρ s ρ' → BigStep ρ s.optimize ρ' := by
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

inductive SmallStep : Env → Stmt → Env → Stmt → Prop where
  | seq1 : SmallStep ρ s1 ρ' s1' → SmallStep ρ (.seq s1 s2) ρ' (.seq s1' s2)
  | seq2 : SmallStep ρ (.seq .skip s2) ρ s2
  | assign : e.eval ρ = some v → SmallStep ρ (.assign x e) (ρ.set x v) .skip
  | ifTrue : Truthy (c.eval ρ) → SmallStep ρ (.if c s1 s2) ρ s1
  | ifFalse : Falsy (c.eval ρ) → SmallStep ρ (.if c s1 s2) ρ s2
  | whileTrue : Truthy (c.eval ρ) → SmallStep ρ (.while c s) ρ (.seq s (.while c s))
  | whileFalse : Falsy (c.eval ρ) → SmallStep ρ (.while c s) ρ .skip

inductive SmallStep' : Env → Stmt → Env → Stmt → Prop where
  | seq1 :
    SmallStep' ρ s1 ρ' s1' →
    SmallStep'
      ρ  (program {~s1 ~s2})
      ρ' (program {~s1 ~s2})
  | seq2 :
    SmallStep'
      ρ (program {skip; ~s2})
      ρ s2
  | assign : {e : Expr} →
    e.eval ρ = some v →
    SmallStep'
      ρ           (program {~x := ~e;})
      (ρ.set x v) (program {skip;})
  | ifTrue :
    Truthy (c.eval ρ) →
    SmallStep'
      ρ (program {if (~c) {~s1} else {~s2}})
      ρ s1
  | ifFalse :
    Falsy (c.eval ρ) →
    SmallStep'
      ρ (program {if (~c) {~s1} else {~s2}})
      ρ s2
  | whileTrue :
    Truthy (c.eval ρ) →
    SmallStep'
      ρ (program {while (~c) {~s}})
      ρ (program {~s while(~c) {~s}})
  | whileFalse :
    Falsy (c.eval ρ) →
    SmallStep'
      ρ (program {while (~c) {~s}})
      ρ (program {skip;})

structure ValidStep (ρ : Env) (s : Stmt) where
  env : Env
  stmt : Stmt
  ok : SmallStep ρ s env stmt

instance : Repr (ValidStep ρ s) where
  reprPrec x p := "⟨ ⋯, " ++ repr x.stmt ++ ", ...⟩"

inductive SmallSeq : Nat → Env → Stmt → Env → Stmt → Type where
  | done : SmallSeq n ρ .skip ρ .skip
  | noGas : SmallSeq 0 ρ s ρ s
  | crash : s ≠ .skip → (¬ ∃ ρ' s', SmallStep ρ s ρ' s') → SmallSeq n ρ s ρ s
  | step : SmallStep ρ s ρ' s' → SmallSeq n ρ' s' ρ'' s'' → SmallSeq (n + 1) ρ s ρ'' s''

def SmallSeq.render (vars : List String) : SmallSeq n ρ s ρ' s' → Std.Format
  | .done => "DONE!"
  | .noGas => "No more gas..."
  | .crash _ _ => "CRASH!"
  | .step _ ss =>
    repr s ++ .line ++ "{" ++ .joinSep (vars.map (fun x => x ++ " ↦ " ++ toString (ρ x))) "," ++ "}" ++ .line ++ s!"====[{n}]=====>" ++ .line ++ ss.render vars

def SmallSeq.final (vars : List String) (_ : SmallSeq n ρ s ρ' s') : Std.Format :=
  repr s' ++ .line ++ "{" ++ .joinSep (vars.map (fun x => x ++ " ↦ " ++ toString (ρ' x))) "," ++ "}"

def smallStep (ρ : Env) (s : Stmt) : ValidStep ρ s ⊕ (Inhabited <| ValidStep ρ s → False) :=
  match s with
  | program{skip;} => .inr ⟨nofun⟩
  | program{ ~s1 ~s2} =>
    if h : s1 = .skip then
      .inl ⟨_, _, h ▸ SmallStep.seq2⟩
    else
      match smallStep ρ s1 with
      | .inl ⟨_, _, step⟩ => .inl ⟨_, _, .seq1 step⟩
      | .inr ⟨c⟩ => .inr <| by
        constructor
        intro ⟨_, _, step⟩
        cases step
        . apply c
          constructor; assumption
        . contradiction
  | .assign x e =>
    match h : e.eval ρ with
    | some v => .inl ⟨_, _, .assign h⟩
    | none => .inr <| by
      constructor
      intro ⟨_, _ , step⟩
      cases step
      next prf => rw [h] at prf; contradiction
  | .while c s =>
    if h : Truthy (c.eval ρ) then
      .inl <| ⟨_, _, .whileTrue h⟩
    else if h' : Falsy (c.eval ρ) then
      .inl <| ⟨_, _, .whileFalse h'⟩
    else
      .inr <| by
        constructor
        intro ⟨_, _, step⟩
        cases step <;> contradiction
  | .if c s1 s2 =>
    if h : Truthy (c.eval ρ) then
      .inl ⟨_, _, .ifTrue h⟩
    else if h' : Falsy (c.eval ρ) then
      .inl ⟨_, _, .ifFalse h'⟩
    else
      .inr <| by
        constructor
        intro ⟨_, _, step⟩
        cases step <;> contradiction


def runFor (n : Nat) (ρ : Env) (s : Stmt) : (ρ' : Env) × (s' : Stmt) × SmallSeq n ρ s ρ' s' :=
  if h : s = .skip then
    ⟨ρ, s, by cases h; apply SmallSeq.done⟩
  else
    match n with
    | 0 => ⟨_, _, .noGas⟩
    | n' + 1 =>
      match smallStep ρ s with
      | .inl ⟨ρ', s', prf⟩ =>
        ⟨_, ⟨_, .step prf (runFor n' ρ' s').2.2⟩⟩
      | .inr ⟨contra⟩ => .mk _ <| .mk _ <| .crash h <| by
        intro ⟨ρ', ⟨s', step⟩⟩
        apply contra
        constructor; assumption

def fib : Stmt := program {
  x := 0; y := 0;
  while (n > 0) {
    x := y;
    y := y + n;
    n := n + - 1;
  }
}

#eval let ρ' := runFor 20 (Env.init 42 |>.set "n" 6 |>.set "x" 0) fib |>.fst; (ρ' "x", ρ' "y", ρ' "n")

#eval smallStep (Env.init 99 |>.set "n" 0) (program{ while (n > 0) {n := n - 1;} }) |> (match · with | .inl x => some x | .inr _ => none)

#eval
  let ρ' := runFor 200 (Env.init 42 |>.set "n" 6 |>.set "x" 0) fib
  ρ'.snd.snd.final ["x", "y", "n"]

def runFor' (n : Nat) (ρ : Env) (s : Stmt) : Option Env :=
  if let program {skip;} := s then
    some ρ
  else
    match n with
    | 0 => none
    | n' + 1 =>
      match smallStep ρ s with
      | .inl ⟨ρ', s', _⟩ =>
        runFor' n' ρ' s'
      | .inr _ => none

def popcount : Stmt := program {
  x := x - ((x >>> 1) &&& 0x55555555);
  x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  x := x + (x >>> 8);
  x := x + (x >>> 16);
  x := x &&& 0x0000003F;
}

def popcountLoop : Stmt := program {
  i := 32;
  count := 0;
  while (i > 0) {
    count := count + (x &&& 1);
    i := i - 1;
    x := x >>> 1;
  }
  x := count;
}

def popcountLoop2 : Stmt := program {
  i := 32;
  count := 0;
  while (i > 0) {
    count := count + (x &&& 80000000);
    i := i - 1;
    x := x <<< 1;
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

#guard (runFor' 11 (Env.init 9) popcount).isSome

#guard (runFor' 240 (Env.init 9) popcountLoop).isSome

#eval (runFor' 11 (Env.init 3) popcount).map (· "x")
#eval (runFor' 240 (Env.init 3) popcountLoop) |>.map (· "x")

#eval (runFor' 11 (Env.init 1230123) popcount).map (· "x")
#eval (runFor' 11 (Env.init 1230123) popcountLoop) |>.map (· "x")


theorem Env.set_order {ρ : Env} : x ≠ y → (ρ.set x v1 |>.set y v2) = (ρ.set y v2 |>.set x v1) := by
  intro h
  funext z
  simp [Env.set]
  split <;> split
  . subst_eqs; contradiction
  . rfl
  . rfl
  . rfl

theorem Char.lt_irrefl (c : Char) : ¬ (c < c) := by
  simp [LT.lt]
  intro lt
  unfold Char.lt at lt
  unfold instLTUInt32 at lt
  simp_all
  unfold instLTFin at lt
  simp_all


theorem Env.set_reorder {ρ : Env} : x < y → (ρ.set y v2 |>.set x v1) = (ρ.set x v1 |>.set y v2) := by
  intro h
  have : x ≠ y := by
    simp [LT.lt, List.lt] at h
    intro eq
    rw [eq] at h
    apply List.lt_irrefl' Char.lt_irrefl y.data h
  funext z
  simp [Env.set]
  split <;> split
  . subst_eqs; contradiction
  . rfl
  . rfl
  . rfl

@[simp]
theorem Env.get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem Env.get_set_same {ρ : Env} : (ρ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem Env.get_set_different {ρ : Env} : x ≠ y → (ρ.set x v).get y = ρ.get y := by
  intros
  simp [get, set, *]


-- These seem like they should be simprocs :-)

@[simp]
theorem Env.set_dedup {ρ : Env} :  (ρ.set x v1 |>.set x v2) = (ρ.set x v2) := by
  funext z
  simp [Env.set]
  split <;> simp

@[simp]
theorem Env.set_dedup2 {ρ : Env} : (ρ.set x v1 |>.set y v |>.set x v2) = (ρ.set y v |>.set x v2) := by
  funext z
  simp [Env.set]
  split <;> simp

@[simp]
theorem Env.set_dedup3 {ρ : Env} : (ρ.set x v1 |>.set y v |>.set z v' |>.set x v2) = (ρ.set y v |>.set z v' |>.set x v2) := by
  funext z
  simp [Env.set]
  repeat split <;> try rfl

@[simp]
theorem Expr.eval_const : Expr.eval ρ (.const v) = some v := by simp [Expr.eval]

theorem popCount_correct : ∃ ρ, (runFor' 11 (Env.init x) popcount) = some ρ ∧ ρ "x" = pop_spec' x := by
  simp [runFor', popcount, smallStep, Env.init, Expr.eval, Expr.BinOp.apply, Env.set, pop_spec', pop_spec'.go, Value]
  bv_decide

#eval 5

@[simp]
theorem BitVec.and_self {x : BitVec 32} : x &&& x = x := by
  bv_decide

@[simp]
theorem BitVec.and_self_ofNat {x : Nat} : BitVec.ofNat 32 x &&& BitVec.ofNat 32 x = BitVec.ofNat 32 x := by
  simp

macro "cleanup_env" : tactic =>
  `(tactic| (
    (repeat conv in Env.get "x" (Env.set "i" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat conv in Env.get "x" (Env.set "count" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat conv in Env.get "i" (Env.set "x" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat conv in Env.get "i" (Env.set "count" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat conv in Env.get "count" (Env.set "x" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat conv in Env.get "count" (Env.set "i" _ _) => rw [Env.get_set_different (by decide)]);
    (repeat rw [Env.get_set_same]))
  )


-- This is an horrible hack that gets it to compute. Why aren't the simp lemmas firing?
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1024 in
set_option trace.bv true in
theorem popCountLoop_correct : ∃ ρ, (runFor' 240 (Env.init x) popcountLoop) = some ρ ∧ ρ.get "x" = pop_spec' x := by
  have : "count" ≠ "i" := by decide
  have : "count" ≠ "x" := by decide
  have : "x" ≠ "i" := by decide
  have : 1#32 ≠ 0#32 := by decide
  unfold popcountLoop
  -- Not sure why I need to call repeat multiple times...
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  simp [pop_spec', pop_spec'.go, Value]
  -- Holds by reflexivity; both implement the same algorithm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1024 in
set_option trace.bv true in
theorem popCountLoop2_correct : ∃ ρ, (runFor' 240 (Env.init x) popcountLoop2) = some ρ ∧ ρ.get "x" = pop_spec' x := by
  have : "count" ≠ "i" := by decide
  have : "count" ≠ "x" := by decide
  have : "x" ≠ "i" := by decide
  have : 1#32 ≠ 0#32 := by decide
  unfold popcountLoop2
  -- Not sure why I need to call repeat multiple times...
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  repeat (unfold runFor'; simp [smallStep, Expr.eval, Expr.BinOp.apply, *]; cleanup_env)
  simp [pop_spec', pop_spec'.go, Value]
  -- Why doesn't this work? Is there a bug?
  bv_decide
