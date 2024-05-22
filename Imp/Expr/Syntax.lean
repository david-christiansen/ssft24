import Lean.PrettyPrinter.Parenthesizer
import Imp.Expr.Basic

namespace Imp.Expr

open Lean PrettyPrinter Parenthesizer

declare_syntax_cat varname
syntax ident : varname
syntax:max "~" term:max : varname

syntax "var " "{" varname "}" : term

macro_rules
  | `(var { $x:ident }) => `(term|$(quote x.getId.toString))
  | `(var { ~$stx }) => pure stx

declare_syntax_cat exp
syntax varname : exp
/-- Numeric constant -/
syntax num : exp

/-- Arithmetic complement -/
syntax:75 "-" exp:75 : exp

/-- Multiplication -/
syntax:70 exp:70 " * " exp:71 : exp
/-- Division -/
syntax:70 exp:70 " / " exp:71 : exp

/-- Addition -/
syntax:65 exp:65 " + " exp:66 : exp
/-- Subtraction -/
syntax:65 exp:65 " - " exp:66 : exp

syntax:55 exp:55 " <<< " exp:56 :exp
syntax:55 exp:55 " >>> " exp:56 :exp

/-- Boolean negation -/
syntax:75 "!" exp:75 : exp
/-- Less than -/
syntax:50 exp:50 " < " exp:51 : exp
/-- Less than or equal to -/
syntax:50 exp:50 " ≤ " exp:51 : exp
/-- Greater than or equal to -/
syntax:50 exp:50 " ≥ " exp:51 : exp
/-- Greater than -/
syntax:50 exp:50 " > " exp:51 : exp
/-- Equal -/
syntax:45 exp:45 " == " exp:46 : exp

syntax:40 exp:40 " &&& " exp:41 :exp
syntax:40 exp:40 " ||| " exp:41 :exp

/-- Boolean conjunction -/
syntax:35 exp:35 " && " exp:36 : exp
/-- Boolean disjunction -/
syntax:35 exp:35 " || " exp:36 : exp

/-- Parens -/
syntax "(" exp ")" : exp

/-- Escape to Lean -/
syntax:max "~" term:max : exp

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


-- Shamelessly stolen from Lean's term parenthesizer - applies the precedence rules in the grammar
-- to add parentheses as needed.
@[category_parenthesizer exp]
def exp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `exp true wrapParens prec $
    parenthesizeCategoryCore `exp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
