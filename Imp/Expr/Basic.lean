namespace Imp.Expr

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

end Expr

inductive Expr where
  | const (i : BitVec 32)
  | var (name : String)
  | un (op : Expr.UnOp) (e : Expr)
  | bin (op : Expr.BinOp) (e1 e2 : Expr)
deriving Repr, DecidableEq
