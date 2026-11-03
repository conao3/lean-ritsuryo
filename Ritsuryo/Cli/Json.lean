module

/-!
# CLI の JSON

CLI の入力（`--cli-input-json`、`file://` の値）と出力に使う JSON の型と、その整形・構文解析。
Lean の `Lean.Data.Json` を import すると、CLI のバイナリが `Lean` 全体を取り込んで 134 MiB になり、起動も遅くなる
（README の計測）。そのため、CLI に要る分だけをこのファイルに書き、ライブラリと CLI は `Lean` に依存しない。

- 数は整数（`Int`）だけを扱う。金額は円、日数は日の整数で、小数の割合は文字列で出す。入力に小数や指数があれば
  構文解析の誤りにする。
- オブジェクトはキーと値の組の配列で持ち、出力ではキーを入れた順に並べる。
- `pretty` は 4 字下げで整形する。
-/

public section

namespace Ritsuryo.Cli

/-- JSON の値。数は整数だけで、オブジェクトはキーの順を保つ。 -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (fields : Array (String × Json))
  deriving Inhabited

namespace Json

/-- オブジェクトのキーの値。オブジェクトでないか、キーがなければ `none`。 -/
def get? (j : Json) (key : String) : Option Json :=
  match j with
  | .obj fields => (fields.find? (·.1 == key)).map (·.2)
  | _ => none

/-- 配列でもオブジェクトでもない値か。 -/
def isScalar : Json → Bool
  | .arr _ => false
  | .obj _ => false
  | _ => true

/-- 0 から 15 の数を小文字の 16 進数字にする。 -/
def hexDigit (n : Nat) : Char :=
  "0123456789abcdef".toList.getD n '0'

/-- 文字列を JSON の文字列リテラルにする。引用符と逆斜線と制御文字をエスケープする。 -/
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

/-- `--output text` と `table` に出すスカラーの文字列。AWS CLI と同じく null は `None`、真偽値は `True`・`False`。 -/
def scalarText : Json → String
  | .null => "None"
  | .bool true => "True"
  | .bool false => "False"
  | .num n => toString n
  | .str s => s
  | .arr _ => ""
  | .obj _ => ""

/-- 4 字下げで整形した JSON。`indent` は今の字下げの幅。 -/
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

/-- 構文解析の状態。入力の文字の配列と、読んでいる位置。 -/
structure Parser where
  chars : Array Char
  pos : Nat

/-- 構文解析のモナド。誤りはメッセージの文字列で返す。 -/
abbrev ParseM := StateT Parser (Except String)

/-- 今の位置の文字。入力の終わりでは `none`。 -/
def peek? : ParseM (Option Char) := do
  let s ← get
  return s.chars[s.pos]?

/-- 1 文字進める。 -/
def advance : ParseM Unit :=
  modify fun s => { s with pos := s.pos + 1 }

/-- 空白・改行・タブを読み飛ばす。 -/
partial def skipWs : ParseM Unit := do
  match ← peek? with
  | some c =>
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then
      advance
      skipWs
  | none => pure ()

/-- 今の文字が `c` なら進め、違えば誤りにする。 -/
def expect (c : Char) : ParseM Unit := do
  match ← peek? with
  | some d =>
    if c == d then advance else throw s!"expected '{c}' but found '{d}'"
  | none => throw s!"expected '{c}' but reached the end"

/-- `true`・`false`・`null` のような語をそのまま読む。 -/
def expectWord (w : String) : ParseM Unit :=
  w.toList.forM expect

/-- 16 進数字の値。 -/
def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `\u` の後の 4 桁の 16 進数を読む。 -/
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

/-- 引用符で囲んだ文字列を読む。`\uD83D\uDE00` のようなサロゲートペアは 1 文字にする。 -/
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
          if !(0xDC00 ≤ lo && lo < 0xE000) then throw "invalid surrogate pair"
          loop (acc.push (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00))))
        else loop (acc.push (Char.ofNat hi))
      | _ => throw "invalid escape"
    | some c =>
      advance
      loop (acc.push c)
  loop ""

/-- 整数を読む。小数点や指数があれば誤りにする。 -/
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

/-- JSON の値を 1 つ読む。先頭の文字でオブジェクト・配列・文字列・語・数を見分ける。 -/
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

/-- 文字列全体を 1 つの JSON の値として読む。値の後に空白以外が残れば誤りにする。 -/
def parse (s : String) : Except String Json := do
  let (v, st) ← (do
    let v ← parseValue
    skipWs
    pure v).run { chars := s.toList.toArray, pos := 0 }
  if st.pos < st.chars.size then throw "trailing characters after JSON value"
  return v

end Json

end Ritsuryo.Cli
