-- This program uses the compiler's JSON library
import Lean.Data.Json
import Filter.List
import Filter.Array

namespace Filter

open Lean (Json FromJson ToJson)

/-- Where can a query be applied in a JSON value? -/
inductive Context where
  | /-- Querying the fields of an object -/
    object
  | /-- Querying the elements of an array -/
    array
  | /-- Querying an ordinary JSON value -/
    val

/-- Queries that apply to a given context -/
inductive Query : Context → Type where
  | /-- Always succeeds -/
    any : Query ctxt
  | /-- Always fails -/
    none : Query ctxt
  | /-- Succeeds when the value being queried is `v` -/
    is (v : Json) : Query .val
  | /-- Succeeds when the value is a string -/
    string : Query .val
  | /-- Succeeds when the value is an object that satisfies an object query -/
    obj : Query .object → Query .val
  | /-- Succeeds when the object has the given key and the associated value satisfies the query -/
    key : String → Query .val → Query .object
  | /-- Succeeds when the object is an array whose elements satisfy a query -/
    array : Query .array → Query .val
  | /-- Succeeds when the array being queried has a value at the given index that satisfies the query -/
    at : Nat → Query .val → Query .array
  | /-- Succeeds when the array being queried has the given length -/
    length : Nat → Query .array
  | /-- Succeeds when both arguments succeed -/
    and : Query ctxt → Query ctxt → Query ctxt
  | /-- Succeeds when one of the provided arguments succeeds -/
    or : Query ctxt → Query ctxt → Query ctxt

-- Which types can the given query context apply to?  This is a
-- dependent type where a function is used to compute the type of a
-- later argument from the value of an earlier one.
abbrev Context.Subject : Context → Type
  | .val => Json
  | .array => Array Json
  | .object => Lean.RBNode String (fun _ => Json)

def Query.matches (q : Query ctxt) (v : ctxt.Subject) : Bool :=
  match q, v with
  | .any, _ => true
  | .none, _ => false
  | .is v', v => v == v'
  | .string, .str _ => true
  | .string, _ => false
  | .obj q', .obj fields => q'.matches fields
  | .obj _, _ => false
  | .key k q', fields =>
    if let some v := fields.find compare k then q'.matches v else false
  | .array q', .arr elts => q'.matches elts
  | .array _, _ => false
  | .at n q', elts =>
    if let some v := elts[n]? then q'.matches v else false
  | .length n, elts => elts.size == n
  | .and q1 q2, v => q1.matches v && q2.matches v
  | .or q1 q2, v =>  q1.matches v || q2.matches v

partial def Query.parse {ctxt: Context} (input : Json) : Except String (Query ctxt) := do
  match ctxt, input with
  | _, "any" => pure .any
  | _, "none" => pure .none
  | .val, .arr #["is", o] => pure (.is o)
  | .val, "string" => pure .string
  | .val, .arr #["object", o] => obj <$> parse o
  | .object, .obj fields =>
    let mut q : Query .object := .any
    for ⟨k, v⟩ in fields.toArray do
      q := .and q (.key k (← parse v))
    pure q
  | .object, other => throw s!"expected object, got {other}"
  | .val, .arr #["array", a] => array <$> parse a
  | .array, v@(.obj fields) =>
    match fields.toArray with
    | #[⟨"length", n⟩] =>
      let n' : Nat ← FromJson.fromJson? n
      pure (.length n')
    | #[⟨"at", n⟩, ⟨"satisfies", q'⟩] =>
      pure (.at (← FromJson.fromJson? n) (← parse q'))
    | _ => throw s!"expected object with single key 'length' or keys 'at' and 'satisfies', got {v}"
  | ctxt, .arr more =>
    if h : more.size > 2 then
      match more[0]'(by omega) with
      | "and" =>
        let q1 ← parse (more[1]'(by omega))
        let q2 ← parse (more[2]'(by omega))
        let mut q := .and q1 q2
        for h : i in [3:more.size] do
          q := .and q (← parse more[i])
        pure q
      | "or" =>
        let q1 ← parse (more[1]'(by omega))
        let q2 ← parse (more[2]'(by omega))
        let mut q := .or q1 q2
        for h : i in [3:more.size] do
          q := .or q (← parse more[i])
        pure q
      | other => throw s!"Expected 'and' or 'or', got {other}"
    else
      throw s!"Expected at least two elements in {more}"
  | ctxt, other => throw s!"didn't understand {other}"
