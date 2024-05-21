import Lean.PrettyPrinter.Delaborator

open Lean
open Lean.PrettyPrinter Parenthesizer


namespace Imp.Expr

declare_syntax_cat varname
syntax ident : varname
syntax:max "~" term:max : varname

syntax "var " "{" varname "}" : term

macro_rules
  | `(var { $x:ident }) => `(term|$(quote x.getId.toString))
  | `(var { ~$stx }) => pure stx

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

syntax:max "~" term:max : exp

syntax "lean " "{ " term " }" : exp

syntax:min "expr " "{ " exp " }" : term

open Lean in
macro_rules
  | `(expr{$x:ident}) => `(Expr.var $(quote x.getId.toString))
  | `(expr{$n:num}) => `(Expr.const $(quote n.getNat))

  | `(expr{-$e}) => `(Expr.un .neg (expr{$e}))
  | `(expr{!$e}) => `(Expr.un .not (expr{$e}))

  | `(expr{$e1 + $e2}) => `(Expr.bin .plus (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 * $e2}) => `(Expr.bin .times (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 - $e2}) => `(Expr.bin .minus (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 / $e2}) => `(Expr.bin .div (expr{$e1}) (expr{$e2}))

  | `(expr{$e1 >>> $e2}) => `(Expr.bin .rsh (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 <<< $e2}) => `(Expr.bin .lsh (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ||| $e2}) => `(Expr.bin .bor (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 &&& $e2}) => `(Expr.bin .band (expr{$e1}) (expr{$e2}))


  | `(expr{$e1 && $e2}) => `(Expr.bin .and (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 || $e2}) => `(Expr.bin .or (expr{$e1}) (expr{$e2}))

  | `(expr{$e1 < $e2}) => `(Expr.bin .lt (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ≤ $e2}) => `(Expr.bin .le (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 == $e2}) => `(Expr.bin .eq (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ≥ $e2}) => `(Expr.bin .le (expr{$e2}) (expr{$e1}))
  | `(expr{$e1 > $e2}) => `(Expr.bin .lt (expr{$e2}) (expr{$e1}))
  | `(expr{($e)}) => `(expr{$e})
  | `(expr{~$stx}) => pure stx

-- Shamelessly stolen from Lean's term parenthesizer
@[category_parenthesizer exp]
def exp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `exp true wrapParens prec $
    parenthesizeCategoryCore `exp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
