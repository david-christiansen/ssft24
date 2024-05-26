import Lean.Data.Json
import Filter

open Lean (Json)
open Filter

def main : List String → IO UInt32
  | [q] => do
    let query ←
      match Json.parse q >>= Query.parse (ctxt := .val) with
      | .error e => IO.eprintln e; return 1
      | .ok q' => pure q'
    let input ← readStdin
    match readJsonArray input with
    | .error e => IO.eprintln e; return 3
    | .ok vals =>
      for v in Filter.List.filter (query.matches · = true) vals.toList do
        IO.println v
      return 0
  | _ => do
    IO.println "Usage: jsonfilterfilter QUERY"
    return 2
