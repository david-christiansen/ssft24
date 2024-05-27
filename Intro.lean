-------------------------
-- Programming in Lean --
-------------------------

def double (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => double n' + 2

#eval double 5

#check double

def double' : Nat → Nat
  | 0 => 0
  | n' + 1 => double' n' + 2

def multiply (k : Nat) : Nat → Nat
  | 0 => 0
  | n' + 1 => multiply k n' + k

def append : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

inductive Tree (α : Type) where
  | leaf : Tree α
  | branch : Tree α → α → Tree α → Tree α

def Tree.toList : Tree α → List α
  | leaf => []
  | branch l x r => l.toList ++ [x] ++ r.toList

#eval (Tree.branch (Tree.branch Tree.leaf 1 Tree.leaf) 2 Tree.leaf).toList


inductive Even : Nat → Prop where
  | isEven : (half : Nat) → Even (half + half)

example : Even 6 := .isEven 3

inductive Repeats (x : α) : List α → Prop where
  | nil : Repeats x []
  | cons : Repeats x xs → Repeats x (x :: xs) -- here xs is implicitly an argument

example : Repeats 3 [3,3,3] := .cons (.cons (.cons .nil))

def Both (p q : α → Prop) : α → Prop := fun x => p x ∧ q x
