import Lean.PrettyPrinter.Delaborator
import LeanSAT.Reflect.Tactics.BVDecide

abbrev Value := BitVec 32

def Env := String → Value

def Env.set (x : String) (v : Value) (ρ : Env) : Env :=
  fun y => if x == y then v else ρ y

def Env.get (x : String) (ρ : Env) : Value :=
  ρ x

def Env.init (i : Value) : Env := fun _ => i

inductive UnOp where
  | neg
  | not
deriving Repr, DecidableEq

inductive BinOp where
  | plus | minus | times | div
  | lsh | rsh
  | band | bor
  | and | or
  | lt | le | eq
deriving Repr, DecidableEq

inductive Expr where
  | const (i : Value)
  | var (name : String)
  | un (op : UnOp) (e : Expr)
  | bin (op : BinOp) (e1 e2 : Expr)
deriving Repr, DecidableEq

declare_syntax_cat varname
syntax ident : varname
syntax "~" term : varname

syntax "var " "{" varname "}" : term

open Lean in
macro_rules
  | `(var { $x:ident }) => `(term|$(quote x.getId.toString))
  | `(var { ~$stx }) => pure stx

namespace Expr.Syntax
declare_syntax_cat exp
syntax varname : exp
/-- Numeric constant -/
syntax num : exp
/-- Arithmetic complement -/
syntax:75 "-" exp:75 : exp
/-- Addition -/
syntax:65 exp:65 " + " exp:66 : exp
/-- Multiplication -/
syntax:70 exp:70 " * " exp:71 : exp
/-- Subtraction -/
syntax:65 exp:65 " - " exp:66 : exp
/-- Division -/
syntax:65 exp:65 " / " exp:66 : exp

-- todo precs
syntax:55 exp:55 " <<< " exp:56 :exp
syntax:55 exp:55 " >>> " exp:56 :exp
syntax:55 exp:55 " &&& " exp:56 :exp
syntax:55 exp:55 " ||| " exp:56 :exp

--todo precs for these
/-- Boolean conjunction -/
syntax:65 exp:65 " && " exp:66 : exp
/-- Boolean disjunction -/
syntax:65 exp:65 " || " exp:66 : exp

/-- Boolean negation -/
syntax:75 "!" exp:75 : exp
/-- Less than -/
syntax:50 exp:50 " < " exp:50 : exp
/-- Less than or equal to -/
syntax:50 exp:50 " ≤ " exp:50 : exp
/-- Equal -/
syntax:50 exp:50 " = " exp:50 : exp
/-- Equal -/
syntax:50 exp:50 " == " exp:50 : exp
/-- Greater than or equal to -/
syntax:50 exp:50 " ≥ " exp:50 : exp
/-- Greater than -/
syntax:50 exp:50 " > " exp:50 : exp

/-- Parens -/
syntax "(" exp ")" : exp

syntax "~" term : exp

syntax "lean " "{" term "}" : exp

syntax "expr" "{" exp "}" : term

open Lean in
macro_rules
  | `(expr{$x:ident}) => `(Expr.var $(quote x.getId.toString))
  | `(expr{$n:num}) => `(Expr.const $(quote n.getNat))

  | `(expr{-$e}) => `(Expr.un .neg expr{$e})
  | `(expr{!$e}) => `(Expr.un .not expr{$e})

  | `(expr{$e1 + $e2}) => `(Expr.bin .plus expr{$e1} expr{$e2})
  | `(expr{$e1 * $e2}) => `(Expr.bin .times expr{$e1} expr{$e2})
  | `(expr{$e1 - $e2}) => `(Expr.bin .minus expr{$e1} expr{$e2})
  | `(expr{$e1 / $e2}) => `(Expr.bin .div expr{$e1} expr{$e2})

  | `(expr{$e1 >>> $e2}) => `(Expr.bin .rsh expr{$e1} expr{$e2})
  | `(expr{$e1 <<< $e2}) => `(Expr.bin .lsh expr{$e1} expr{$e2})
  | `(expr{$e1 ||| $e2}) => `(Expr.bin .bor expr{$e1} expr{$e2})
  | `(expr{$e1 &&& $e2}) => `(Expr.bin .band expr{$e1} expr{$e2})


  | `(expr{$e1 && $e2}) => `(Expr.bin .and expr{$e1} expr{$e2})
  | `(expr{$e1 || $e2}) => `(Expr.bin .or expr{$e1} expr{$e2})

  | `(expr{$e1 < $e2}) => `(Expr.bin .lt expr{$e1} expr{$e2})
  | `(expr{$e1 ≤ $e2}) => `(Expr.bin .le expr{$e1} expr{$e2})
  | `(expr{$e1 == $e2}) => `(Expr.bin .eq expr{$e1} expr{$e2})
  | `(expr{$e1 ≥ $e2}) => `(Expr.bin .le expr{$e2} expr{$e1})
  | `(expr{$e1 > $e2}) => `(Expr.bin .lt expr{$e2} expr{$e1})
  | `(expr{($e)}) => `(expr{$e})
  | `(expr{~$stx}) => pure stx

end Expr.Syntax

def Expr.freeVars : Expr → List String
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

def Expr.eval (ρ : Env) : Expr → Option Value
  | .const i => some i
  | .var x => ρ x
  | .un op e => do
    let v ← e.eval ρ
    op.apply v
  | .bin op e1 e2 => do
    let v1 ← e1.eval ρ
    let v2 ← e2.eval ρ
    op.apply v1 v2

def Expr.optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .un op e =>
    match optimize e with
    | .const i =>
      if let some v := op.apply i then .const v
      else .un op (.const i)
    | e' => .un op e'
  | .bin op e1 e2 =>
    match optimize e1, optimize e2 with
    | .const i, .const i' =>
      if let some v := op.apply i i' then .const v
      else .bin op (.const i) (.const i')
    | e1', e2' => .bin op e1' e2'

theorem Expr.optimize_ok (e : Expr) : e.eval ρ = e.optimize.eval ρ := by
  induction e <;> simp [optimize]
  next op e ih =>
    split <;> simp [eval, *]
    cases op <;> simp [UnOp.apply, eval]
  next op e1 e2 ih1 ih2 =>
    split <;> simp [eval, *]
    cases op <;> simp [BinOp.apply, eval]
    split
    . simp [eval, BinOp.apply]; split <;> trivial
    . simp [eval]

inductive Stmt where
  | skip
  | seq (stmt1 stmt2 : Stmt)
  | assign (name : String) (val : Expr)
  | if (cond : Expr) (ifTrue ifFalse : Stmt)
  | while (cond : Expr) (body : Stmt)
deriving Repr, DecidableEq

namespace Stmt.Syntax
declare_syntax_cat stmt
scoped syntax "skip" : stmt
scoped syntax stmt ";" ppDedent(ppLine stmt) : stmt
scoped syntax varname " := " exp : stmt
scoped syntax "if " "(" exp ")" "{" ppIndent(ppLine stmt) ppLine "}" " else " "{" ppIndent(ppLine stmt) ppLine "}" : stmt
scoped syntax ppAllowUngrouped "while " "(" exp ")" ppHardSpace "{" ppIndent(ppLine stmt) ppLine "}" : stmt
scoped syntax ppAllowUngrouped ppDedentIfGrouped("lean" ppHardSpace ppGroup("{ " ppLine term ppDedent(ppLine) " }")) : stmt
scoped syntax "~" term : stmt

syntax "program" ppHardSpace "{" ppLine stmt ppDedent(ppLine) "}" : term


open Lean in
macro_rules
  | `(program { skip }) => `(Stmt.skip)
  | `(program { $s1; $s2 }) => `(Stmt.seq program {$s1} program {$s2})
  | `(program { $x:varname := $e}) =>
      `(Stmt.assign var {$x} expr {$e})
  | `(program { if ($c) {$s1} else {$s2} }) => `(Stmt.if expr{$c} program{$s1} program{$s2})
  | `(program { while ($c) {$s} }) => `(Stmt.while expr{$c} program{$s})
  | `(program { ~$stx }) => pure stx

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

-- Shamelessly stolen from Lean's term parenthesizer
@[category_parenthesizer exp]
def exp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `exp true wrapParens prec $
    parenthesizeCategoryCore `exp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)

@[delab app.Stmt.skip, delab app.Stmt.seq, delab app.Stmt.while, delab app.Stmt.assign, delab App.Stmt.if]
partial def delabStmt : Delab := do
  -- This delaborator only understands a certain arity - bail if it's incorrect
  guard <| match_expr ← getExpr with
    | Stmt.skip => true
    | Stmt.seq _ _ => true
    | Stmt.while _ _ => true
    | Stmt.assign _ _ => true
    | Stmt.if _ _ _ => true
    | _ => false
  let stx' ← delabStmt
  if stx'.raw.isAntiquot then
    let stx := stx'.raw.getAntiquotTerm
    pure ⟨stx⟩
  else
    `(term|program{$stx'})
where
  annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
    (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩
  delabName : DelabM (TSyntax `varname) := do
    let e ← getExpr
    match e with
    | .lit (.strVal s) =>
      let x := mkIdent <| .mkSimple s
      pure <| ⟨x.raw⟩
    | _ => `(varname|~$(← delab)) >>= annAsTerm
  delabExpr : DelabM (TSyntax `exp) := do
    let e ← getExpr
    let stx ←
      match_expr e with
      | Expr.const x =>
        match_expr x with
        | Int.ofNat n =>
          if let some n' := n.nat? then
            pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
          else if let .lit (.natVal n') := n then
            pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
          else withAppArg `(exp| ~$(← delab))
        | BitVec.ofFin _w f => `(exp|99)
        | _ => withAppArg `(exp| ~$(← delab))
      | Expr.var _ => do
        let x ← withAppArg delabName
        `(exp|$x:varname)
      | Expr.bin op _ _ =>
        let s1 ← withAppFn <| withAppArg delabExpr
        let s2 ← withAppArg delabExpr
        match_expr op with
        | BinOp.plus => `(exp| $s1 + $s2)
        | BinOp.minus => `(exp| $s1 - $s2)
        | BinOp.times => `(exp| $s1 * $s2)
        | BinOp.div => `(exp| $s1 / $s2)
        | BinOp.and => `(exp| $s1 && $s2)
        | BinOp.or => `(exp| $s1 || $s2)
        | BinOp.lt => `(exp| $s1 < $s2)
        | BinOp.lt => `(exp| $s1 ≤ $s2)
        | BinOp.lt => `(exp| $s1 == $s2)
        | _ => `(exp| ~$(← delab))
      | Expr.un op _ =>
        let s ← withAppArg delabExpr
        match_expr op with
        | UnOp.neg => `(exp|-$s)
        | UnOp.not => `(exp|!$s)
        | _ => `(exp| ~$(← delab))
      | _ => `(exp| ~$(← delab))
    annAsTerm stx
  delabStmt : DelabM (TSyntax `stmt) := do
    let e ← getExpr
    let stx ←
      match_expr e with
      | Stmt.skip => `(stmt| skip)
      | Stmt.seq _ _ =>
        let s1 ← withAppFn <| withAppArg delabStmt
        let s2 ← withAppArg delabStmt
        `(stmt| $s1 ; $s2)
      | Stmt.assign _ _ =>
        let x ← withAppFn <| withAppArg delabName
        let e ← withAppArg delabExpr
        `(stmt| $x:varname := $e)
      | Stmt.while _ _ =>
        let c ← withAppFn <| withAppArg delabExpr
        let body ← withAppArg delabStmt
        `(stmt| while ($c) { $body })
      | Stmt.if _ _ _ =>
        let c ← withAppFn <| withAppFn <| withAppArg delabExpr
        let t ← withAppFn <| withAppArg delabStmt
        let f ← withAppArg delabStmt
        `(stmt| if ($c) { $t } else { $f })
      | _ =>
        `(stmt| ~$(← delab))
    annAsTerm stx



end Stmt.Syntax

set_option pp.rawOnError true

open Stmt.Syntax in
#reduce fun s => program {skip; ~s}

open Stmt.Syntax in
def Stmt.optimize : Stmt → Stmt
  | program {skip} => program {skip}
  | program {~s1; ~s2} =>
    match s1.optimize, s2.optimize with
    | program {skip}, s2' => s2'
    | s1', program {skip} => s1'
    | s1', s2' => program {~s1'; ~s2'}
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
    | .const 0 => program {skip}
    | _ => program {while (~c') {~s.optimize}}
  | program {~x := ~e} =>
    program {~x := ~e.optimize}




inductive IsSkip : (s : Stmt) → Prop where
  | isSkip : IsSkip .skip

instance : DecidablePred IsSkip := by
  intro s
  cases s
  case skip => apply isTrue; constructor
  all_goals
    apply isFalse; intro h; cases h

def AsBool (ρ : Env) (e : Expr) (b : Bool) : Prop :=
  ∃ v, e.eval ρ = some v ∧ (b = true ↔ v ≠ 0)

open BitVec

instance : Decidable (AsBool ρ e b) :=
  match h : e.eval ρ with
  | none => .isFalse <| by intro ⟨v, ⟨p1, p2⟩⟩; rw [h] at p1; cases p1
  | some v =>
    if h' : v ≠ 0#32 then
      match b with
      | true => .isTrue ⟨v, ⟨h, by simp [*]⟩⟩
      | false => .isFalse <| by
        intro ⟨v', ⟨x, y⟩⟩
        rw [h] at x; cases x
        have := y.mpr h'
        cases this
    else
      match b with
      | true => .isFalse <| by
        intro ⟨v', ⟨x, y⟩⟩
        rw [h] at *; cases h; cases x
        have := y.mp rfl
        contradiction
      | false => .isTrue ⟨v, ⟨h, by simp [*]⟩⟩

open Stmt.Syntax in
inductive BigStep : Env → Stmt → Env → Prop where
  | skip :
    BigStep ρ (program {skip}) ρ
  | seq :
    BigStep ρ s1 ρ' → BigStep ρ' s2 ρ'' →
    BigStep ρ (program{ ~s1; ~s2}) ρ''
  | assign :
    e.eval ρ = some v →
    BigStep ρ (program {~x := ~e}) (ρ.set x v)
  | ifTrue :
    AsBool ρ c true → BigStep ρ s1 ρ' →
    BigStep ρ (program {if (~c) {~s1} else {~s2}}) ρ'
  | ifFalse :
    AsBool ρ c false → BigStep ρ s2 ρ' →
    BigStep ρ (program {if (~c) {~s1} else {~s2}}) ρ'
  | whileTrue :
    AsBool ρ c true →
    BigStep ρ body ρ' →
    BigStep ρ' (program {while (~c) {~body}}) ρ'' →
    BigStep ρ (program {while (~c) {~body}}) ρ''
  | whileFalse :
    AsBool ρ c false →
    BigStep ρ (program {while (~c) {~body}}) ρ

theorem AsBool.optimize_ok : AsBool ρ e b ↔ AsBool ρ e.optimize b := by
  constructor
  . intro ⟨v, hasVal, truthy⟩
    exists v
    constructor
    . rw [← Expr.optimize_ok]
      assumption
    . assumption
  . intro ⟨v, hasVal, truthy⟩
    exists v
    constructor
    . rw [Expr.optimize_ok]
      assumption
    . assumption


open Stmt.Syntax in
def loop := program {while (1) {skip}}

open Stmt.Syntax in
def loopOf (s) := program {while (1) {~s}}



@[simp]
theorem AsBool.const_false : AsBool ρ (.const i) false → i = 0 := by
  intro ⟨v, val, b⟩
  simp [Expr.eval] at val
  simp at b
  simp [*]

@[simp]
theorem AsBool.not_const_1_false : ¬AsBool ρ (.const 1) false := by
  intro h
  have := h.const_false
  cases this

@[simp]
theorem AsBool.not_const_0_true : ¬AsBool ρ (.const 0) true := by
  intro ⟨v, val, b⟩
  simp [Expr.eval] at *
  rw [val] at b
  contradiction

open Stmt.Syntax in
theorem Stmt.infinite_loop : ¬ BigStep ρ loop ρ' := by
  generalize h' : loop = l
  intro h
  induction h with try (simp [loop, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loop at h'
    cases h'
    apply cFalse.not_const_1_false

open Stmt.Syntax in
open BitVec in
theorem Stmt.infinite_loopOf : ¬ BigStep ρ (loopOf s) ρ' := by
  generalize h' : loopOf s = l
  intro h
  induction h with try (simp [loopOf, *] at *; done)
  | whileTrue =>
    simp [*]
  | whileFalse cFalse =>
    unfold loopOf at h'
    cases h'
    cases cFalse.not_const_1_false


theorem Stmt.optimize_ok : BigStep ρ s ρ' → BigStep ρ s.optimize ρ' := by
  intro h
  induction h with simp only [optimize]
  | skip => constructor
  | seq s1 s2 ih1 ih2 =>
    split
    next eq2 =>
      rw [eq2] at ih1
      cases ih1
      apply ih2
    next eq1 eq2 =>
      rw [eq1] at ih2
      cases ih2
      apply ih1
    next =>
      apply BigStep.seq ih1 ih2
  | assign m =>
    constructor
    rw [← Expr.optimize_ok]
    assumption
  | ifTrue isTrue l ih =>
    split
    next isFalse =>
      rw [AsBool.optimize_ok] at isTrue
      rw [isFalse] at isTrue
      cases isTrue.not_const_0_true
    next notFalse isConst =>
      apply ih
    next =>
      split
      . assumption
      . apply BigStep.ifTrue
        . rw [← AsBool.optimize_ok]
          assumption
        . assumption
  | ifFalse isFalse l ih =>
    split
    next =>
      apply ih
    next nonZero isConst =>
      rw [AsBool.optimize_ok, isConst] at isFalse
      have := isFalse.const_false
      cases nonZero this
    next =>
      split
      . simp [*]
      . apply BigStep.ifFalse
        . rw [← AsBool.optimize_ok]
          assumption
        . assumption
  | whileFalse =>
    split
    next =>
      constructor
    next =>
      apply BigStep.whileFalse
      rw [← AsBool.optimize_ok]
      assumption
  | whileTrue isTrue bodyStep nextStep ih1 ih2 =>
    split
    next c isZero =>
      rw [AsBool.optimize_ok, isZero] at isTrue
      cases isTrue.not_const_0_true
    next c isNotZero =>
      apply BigStep.whileTrue
      . rw [← AsBool.optimize_ok]
        assumption
      . apply ih1
      . simp [optimize] at ih2
        assumption




inductive SmallStep : Env → Stmt → Env → Stmt → Prop where
  | seq1 : SmallStep ρ s1 ρ' s1' → SmallStep ρ (.seq s1 s2) ρ' (.seq s1' s2)
  | seq2 : SmallStep ρ (.seq .skip s2) ρ s2
  | assign : e.eval ρ = some v → SmallStep ρ (.assign x e) (ρ.set x v) .skip
  | ifTrue : AsBool ρ c true → SmallStep ρ (.if c s1 s2) ρ s1
  | ifFalse : AsBool ρ c false → SmallStep ρ (.if c s1 s2) ρ s2
  | whileTrue : AsBool ρ c true → SmallStep ρ (.while c s) ρ (.seq s (.while c s))
  | whileFalse : AsBool ρ c false → SmallStep ρ (.while c s) ρ .skip

open Stmt.Syntax in
inductive SmallStep' : Env → Stmt → Env → Stmt → Prop where
  | seq1 :
    SmallStep' ρ s1 ρ' s1' →
    SmallStep'
      ρ  (program {~s1 ; ~s2})
      ρ' (program {~s1'; ~s2})
  | seq2 :
    SmallStep'
      ρ (program {skip; ~s2})
      ρ s2
  | assign :
    e.eval ρ = some v →
    SmallStep'
      ρ           program {~x := ~e}
      (ρ.set x v) program {skip}
  | ifTrue :
    AsBool ρ c true →
    SmallStep'
      ρ program {if (~c) {~s1} else {~s2}}
      ρ s1
  | ifFalse :
    AsBool ρ c false →
    SmallStep'
      ρ program {if (~c) {~s1} else {~s2}}
      ρ s2
  | whileTrue :
    AsBool ρ c true →
    SmallStep'
      ρ program {while (~c) {~s}}
      ρ program {~s; while(~c) {~s}}
  | whileFalse :
    AsBool ρ c false →
    SmallStep'
      ρ program {while (~c) {~s}}
      ρ .skip

structure ValidStep (ρ : Env) (s : Stmt) where
  env : Env
  stmt : Stmt
  ok : SmallStep ρ s env stmt

instance : Repr (ValidStep ρ s) where
  reprPrec x p := "⟨ ⋯, " ++ repr x.stmt ++ ", ...⟩"

inductive SmallSeq : Nat → Env → Stmt → Env → Stmt → Type where
  | done : SmallSeq n ρ .skip ρ .skip
  | noGas : SmallSeq 0 ρ s ρ s
  | crash : ¬IsSkip s → (¬ ∃ ρ' s', SmallStep ρ s ρ' s') → SmallSeq n ρ s ρ s
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
  | .skip => .inr ⟨nofun⟩
  | .seq s1 s2 =>
    if h : IsSkip s1 then
      let .isSkip := h
      .inl ⟨_, _, .seq2⟩
    else
      match smallStep ρ s1 with
      | .inl ⟨_, _, step⟩ => .inl ⟨_, _, .seq1 step⟩
      | .inr ⟨c⟩ => .inr <| by
        constructor
        intro h
        let ⟨_, _, step⟩ := h
        cases step
        . apply c
          constructor; assumption
        . contradiction
  | .assign x e =>
    match h : e.eval ρ with
    | some v => .inl ⟨_, _, .assign h⟩
    | none => .inr <| by
      constructor
      intro h'
      let ⟨_, _ , step⟩ := h'
      cases step
      next prf => rw [h] at prf; contradiction
  | .while c s =>
    if h : AsBool ρ c true then
      .inl <| ⟨_, _, .whileTrue h⟩
    else if h' : AsBool ρ c false then
      .inl <| ⟨_, _, .whileFalse h'⟩
    else
      .inr <| by
        constructor
        intro ⟨_, _, step⟩
        cases step <;> contradiction
  | .if c s1 s2 =>
    if h : AsBool ρ c true then
      .inl ⟨_, _, .ifTrue h⟩
    else if h' : AsBool ρ c false then
      .inl ⟨_, _, .ifFalse h'⟩
    else
      .inr <| by
        constructor
        intro ⟨_, _, step⟩
        cases step <;> contradiction


def runFor (n : Nat) (ρ : Env) (s : Stmt) : (ρ' : Env) × (s' : Stmt) × SmallSeq n ρ s ρ' s' :=
  if h : IsSkip s then
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

open Stmt.Syntax in
def fib : Stmt := program {
  x := 0; y := 0;
  while (n > 0) {
    x := y;
    y := y + n;
    n := n + - 1
  }
}

#eval let ρ' := runFor 20 (Env.init 42 |>.set "n" 6 |>.set "x" 0) fib |>.fst; (ρ' "x", ρ' "y", ρ' "n")

open Stmt.Syntax in
#eval smallStep (Env.init 99 |>.set "n" 0) program{ while (n > 0) {n := n - 1} } |> (match · with | .inl x => some x | .inr _ => none)

#eval
  let ρ' := runFor 200 (Env.init 42 |>.set "n" 6 |>.set "x" 0) fib
  ρ'.snd.snd.final ["x", "y", "n"]

def runFor' (n : Nat) (ρ : Env) (s : Stmt) : Option Env :=
  if IsSkip s then
    some ρ
  else
    match n with
    | 0 => none
    | n' + 1 =>
      match smallStep ρ s with
      | .inl ⟨ρ', s', _⟩ =>
        runFor' n' ρ' s'
      | .inr _ => none

open Stmt.Syntax in
def popcount : Stmt := program {
  x := x - ((x >>> 1) &&& 0x55555555);
  x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  x := x + (x >>> 8);
  x := x + (x >>> 16);
  x := x &&& 0x0000003F
}

open Stmt.Syntax in
def popcountLoop : Stmt := program {
  i := 32;
  count := 0;
  while (i > 0) {
    count := count + (x &&& 1);
    i := i - 1;
    x := x >>> 1
  };
  x := count
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


set_option maxRecDepth 2000 in
theorem popCount_correct : ∃ ρ, (runFor' 11 (Env.init x) popcount) = some ρ ∧ ρ "x" = pop_spec' x := by
  simp (config:={decide := true}) [runFor', popcount, smallStep, Env.init, Expr.eval, BinOp.apply, Env.set, OfNat.ofNat]
  dsimp [pop_spec', pop_spec'.go]
  unfold Value at x
  unfold Value
  bv_decide

/- This doesn't work (so much defeq!)
set_option trace.bv true
set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
theorem popCountLoop_correct : ∃ ρ, (runFor' 240 (Env.init x) popcountLoop) = some ρ ∧ ρ "x" = pop_spec' x := by
  simp (config:={decide := true}) [runFor', popcount, smallStep, Env.init, Expr.eval, BinOp.apply, Env.set, OfNat.ofNat, AsBool]
  dsimp [pop_spec', pop_spec'.go]
  unfold Value at x
  unfold Value
  bv_decide
-/
