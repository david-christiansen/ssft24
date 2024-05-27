namespace Filter.Array

def filter1 (p : α → Prop) [DecidablePred p] (arr : Array α) : Array α := Id.run do
  let mut out := #[]
  for x in arr do
    if p x then out := out.push x
  return out

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


theorem filter_go_all' [DecidablePred p] (hAcc : All p acc)
    : All p (filter.go p xs i acc) := by
  induction i, acc using filter.go.induct p xs <;> unfold filter.go <;> simp [*]

theorem filter_all' (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by
  simp [filter, filter_go_all']
