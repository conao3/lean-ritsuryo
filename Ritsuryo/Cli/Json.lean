module

public section

namespace Ritsuryo.Cli

inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (fields : Array (String × Json))
  deriving Inhabited

namespace Json

def get? (j : Json) (key : String) : Option Json :=
  match j with
  | .obj fields => (fields.find? (·.1 == key)).map (·.2)
  | _ => none

def isScalar : Json → Bool
  | .arr _ => false
  | .obj _ => false
  | _ => true

def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '0'

def escape (s : String) : String :=
  s.foldl (init := "\"") (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        acc ++ "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++
          String.singleton (hexDigit (c.toNat % 16))
      else acc.push c) ++ "\""

def scalarText : Json → String
  | .null => "None"
  | .bool true => "True"
  | .bool false => "False"
  | .num n => toString n
  | .str s => s
  | .arr _ => ""
  | .obj _ => ""

partial def pretty (j : Json) (indent : Nat := 0) : String :=
  let pad (n : Nat) := "".pushn ' ' n
  match j with
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => escape s
  | .arr xs =>
    if xs.isEmpty then "[]"
    else
      let items := xs.toList.map fun x => pad (indent + 4) ++ pretty x (indent + 4)
      "[\n" ++ ",\n".intercalate items ++ "\n" ++ pad indent ++ "]"
  | .obj fields =>
    if fields.isEmpty then "{}"
    else
      let items := fields.toList.map fun (k, v) =>
        pad (indent + 4) ++ escape k ++ ": " ++ pretty v (indent + 4)
      "{\n" ++ ",\n".intercalate items ++ "\n" ++ pad indent ++ "}"

structure Parser where
  chars : Array Char
  pos : Nat

abbrev ParseM := StateT Parser (Except String)

def peek? : ParseM (Option Char) := do
  let s ← get
  return s.chars[s.pos]?

def advance : ParseM Unit :=
  modify fun s => { s with pos := s.pos + 1 }

partial def skipWs : ParseM Unit := do
  match ← peek? with
  | some c =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      advance
      skipWs
  | none => pure ()

def expect (c : Char) : ParseM Unit := do
  match ← peek? with
  | some d =>
    if c == d then advance else throw s!"expected '{c}' but found '{d}'"
  | none => throw s!"expected '{c}' but reached the end"

def expectWord (w : String) : ParseM Unit :=
  w.toList.forM expect

def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : ParseM Nat := do
  let mut v := 0
  for _ in [0:4] do
    match ← peek? with
    | some c =>
      match hexValue c with
      | some d =>
        v := v * 16 + d
        advance
      | none => throw s!"invalid hex digit '{c}'"
    | none => throw "unterminated \\u escape"
  return v

partial def parseString : ParseM String := do
  expect '"'
  let rec loop (acc : String) : ParseM String := do
    match ← peek? with
    | none => throw "unterminated string"
    | some '"' =>
      advance
      return acc
    | some '\\' =>
      advance
      match ← peek? with
      | some '"' => advance; loop (acc.push '"')
      | some '\\' => advance; loop (acc.push '\\')
      | some '/' => advance; loop (acc.push '/')
      | some 'b' => advance; loop (acc.push (Char.ofNat 8))
      | some 'f' => advance; loop (acc.push (Char.ofNat 12))
      | some 'n' => advance; loop (acc.push '\n')
      | some 'r' => advance; loop (acc.push '\r')
      | some 't' => advance; loop (acc.push '\t')
      | some 'u' =>
        advance
        let hi ← hex4
        if 0xD800 ≤ hi && hi < 0xDC00 then
          expect '\\'
          expect 'u'
          let lo ← hex4
          loop (acc.push (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))))
        else loop (acc.push (Char.ofNat hi))
      | _ => throw "invalid escape"
    | some c =>
      advance
      loop (acc.push c)
  loop ""

partial def parseNumber : ParseM Int := do
  let neg ← do
    if (← peek?) == some '-' then
      advance
      pure true
    else pure false
  let rec digits (acc : Nat) (count : Nat) : ParseM (Nat × Nat) := do
    match ← peek? with
    | some c =>
      if c.isDigit then
        advance
        digits (acc * 10 + (c.toNat - '0'.toNat)) (count + 1)
      else return (acc, count)
    | none => return (acc, count)
  let (v, count) ← digits 0 0
  if count == 0 then throw "invalid number"
  match ← peek? with
  | some '.' => throw "only integers are accepted"
  | some 'e' => throw "only integers are accepted"
  | some 'E' => throw "only integers are accepted"
  | _ => pure ()
  return if neg then -(v : Int) else v

partial def parseValue : ParseM Json := do
  skipWs
  match ← peek? with
  | some '{' =>
    advance
    skipWs
    if (← peek?) == some '}' then
      advance
      return .obj #[]
    let rec fields (acc : Array (String × Json)) : ParseM (Array (String × Json)) := do
      skipWs
      let k ← parseString
      skipWs
      expect ':'
      let v ← parseValue
      skipWs
      match ← peek? with
      | some ',' =>
        advance
        fields (acc.push (k, v))
      | some '}' =>
        advance
        return acc.push (k, v)
      | _ => throw "expected ',' or '}'"
    return .obj (← fields #[])
  | some '[' =>
    advance
    skipWs
    if (← peek?) == some ']' then
      advance
      return .arr #[]
    let rec items (acc : Array Json) : ParseM (Array Json) := do
      let v ← parseValue
      skipWs
      match ← peek? with
      | some ',' =>
        advance
        items (acc.push v)
      | some ']' =>
        advance
        return acc.push v
      | _ => throw "expected ',' or ']'"
    return .arr (← items #[])
  | some '"' => return .str (← parseString)
  | some 't' => expectWord "true"; return .bool true
  | some 'f' => expectWord "false"; return .bool false
  | some 'n' => expectWord "null"; return .null
  | some _ => return .num (← parseNumber)
  | none => throw "unexpected end of input"

def parse (s : String) : Except String Json := do
  let (v, st) ← (do
    let v ← parseValue
    skipWs
    pure v).run { chars := s.toList.toArray, pos := 0 }
  if st.pos < st.chars.size then throw "trailing characters after JSON value"
  return v

end Json

end Ritsuryo.Cli
