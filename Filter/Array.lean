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
  sorry

@[simp]
theorem all_empty (p : α → Prop) : All p #[] := sorry

@[simp]
theorem push_all (hAll : All p xs) (hx : p x) : All p (xs.push x) := by sorry


theorem filter_go_all [DecidablePred p] (hAcc : All p acc)
    : All p (filter.go p xs i acc) := sorry


theorem filter_all (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by sorry


theorem filter_go_all' [DecidablePred p] (hAcc : All p acc)
    : All p (filter.go p xs i acc) := by sorry

theorem filter_all' (p : α → Prop) [DecidablePred p] : All p (filter p xs) := by sorry
