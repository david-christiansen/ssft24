import Lean.Data.Json

namespace Filter

open Lean (Json Parsec)
open Lean.Parsec

def readJsonArray (input : String) : Except String (Array Json) := do
  match jsons input.mkIterator with
  | .success _ v => pure v
  | .error _ e => throw e
where
  jsons : Lean.Parsec (Array Json) := do
    ws
    let val ← many Json.Parser.anyCore
    eof
    pure val

partial def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut str := ""
  let mut l ← stdin.getLine
  while !l.isEmpty do
    str := str ++ l
    l ← stdin.getLine
  pure str
