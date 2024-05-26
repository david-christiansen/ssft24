
namespace Filter.List

-- `DecidablePred p` means that we can use `if` to check whether a value satisfies `p`
-- Example : if p x then ... else ...
def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => if p x then x :: filter p xs' else filter p xs'



def filter_length (p : α → Prop) [DecidablePred p] : (filter p xs).length ≤ xs.length := sorry

/- Reminder:
inductive Repeats (x : α) : List α → Prop where
  | nil : Repeats x []
  | cons : Repeats x xs → Repeats x (x :: xs)
-/
/-- `All p xs` states that `p` holds for all entries in the list `xs` -/
inductive All (p : α → Prop) : List α → Prop where

theorem filter_all (p : α → Prop) [DecidablePred p]
    : All p (filter p xs) := by sorry

theorem filter_elem (p : α → Prop) [DecidablePred p] : x ∈ xs → p x → x ∈ filter p xs := by sorry

/-- `Sublist xs ys` means that all entries of `xs` occur, in that
order, in `ys`, possibly with extra entries -/
inductive Sublist : List α → List α → Prop where

theorem filter_sublist [DecidablePred p] : Sublist (filter p xs) xs := by sorry
