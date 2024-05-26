
namespace Filter.List

-- `DecidablePred p` means that we can use `if` to check whether a value satisfies `p`
-- Example : if p x then ... else ...
def filter (p : α → Prop) [DecidablePred p] (xs : List α) : List α := xs
