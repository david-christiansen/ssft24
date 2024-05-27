-------------------------
-- Programming in Lean --
-------------------------


def double (n : Nat) : Nat := sorry


-- #eval double 5


-- #check double


def double' : Nat → Nat := sorry


def multiply (k : Nat) : Nat → Nat := sorry


def append : List α → List α → List α := sorry


inductive Tree (α : Type) where


def Tree.toList : Tree α → List α := sorry


-- #eval (Tree.branch (Tree.branch Tree.leaf 1 Tree.leaf) 2 Tree.leaf).toList


inductive Even : Nat → Prop where


-- example : Even 6 := .isEven 3


inductive Repeats (x : α) : List α → Prop where


-- example : Repeats 3 [3,3,3] := .cons (.cons (.cons .nil))


def Both (p q : α → Prop) : α → Prop := sorry
