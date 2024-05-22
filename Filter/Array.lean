namespace Filter.Array

/-
This implementation of `filter` shows a few interesting aspects of Lean:

 * Lean's `do`-notation contains syntax for mutable variables and iteration. These are translated
   behind the scenes to appropriate monad transformers.

 * `Array.push` will mutate the array in place if the array value's reference count is exactly 1, so
   this code's seeming use of mutation becomes real mutation, with accidental aliasing leading to
   extra copying instead of scary bugs
-/
def filter1 (p : α → Prop) [DecidablePred p] (arr : Array α) : Array α := Id.run do
  let mut out := #[]
  for x in arr do
    if p x then out := out.push x
  return out

/-
This version of `filter` is easier to prove things about. `do` notation is nice, but the desugared
programs are more difficult to use in verification than hand-written loops/tail-recursive functions.
-/
def filter (p : α → Prop) [DecidablePred p] (arr : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (out : Array α) : Array α :=
    if h : i < arr.size then
      if p arr[i] then
        go (i + 1) (out.push arr[i])
      else
        go (i + 1) out
    else out
  termination_by arr.size - i

def All (p : α → Prop) (arr : Array α) : Prop :=
  (i : Nat) → (lt : i < arr.size) →  p arr[i]

@[simp]
theorem all_empty (p : α → Prop) : All p #[] := fun i lt =>
  by contradiction

@[simp]
theorem push_all (hAll : All p xs) (hx : p x) : All p (xs.push x) := by
  intros
  intro i lt
  by_cases i = xs.size
  · simp [*]
  · simp at lt
    have : i < xs.size := by omega
    simp [Array.get_push_lt, *]
    apply hAll


/-
Prove that the inner loop in `filter` ensures that the predicate holds for its result, on the
assumption that it holds for all elements in the initial accumulator.

The following tactics may be useful:
 * `unfold f` replaces `f` with its definition in the goal
 * `split` replaces a goal that contains an `if` or `match` expression with a new goal for each
   branch
 * `apply` applies an existing lemma
 * `assumption` proves the goal using a hypothesis if possible

Because the proof should follow the recursive structure of the program, you may additionally need to
copy the termination argument from the program to the proof.
-/
theorem filter_go_all [DecidablePred p] (hAcc : All p acc)
    : All p (filter.go p xs i acc) := by
  unfold filter.go
  split
  · split
    . apply filter_go_all
      apply push_all
      . assumption
      . assumption
    . apply filter_go_all
      . assumption
  · assumption
termination_by xs.size - i


theorem filter_all (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by
  simp [filter, filter_go_all]


/-
This version of the proof uses Lean's functional induction feature, which allows the `induction`
tactic to automatically follow the recursive structure of a function. Using the induction tactic
also makes it easier to write a highly automated proof that will be more robust in the face of minor
changes to `filter`.
-/
theorem filter_go_all' [DecidablePred p] (hAcc : All p acc)
    : All p (filter.go p xs i acc) := by
  induction i, acc using filter.go.induct p xs <;> unfold filter.go <;> simp [*]

theorem filter_all' (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by
  simp [filter, filter_go_all']
