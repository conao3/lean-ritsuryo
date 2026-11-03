module

public import Ritsuryo.Cli.Json

/-!
# `--output text` と `--output table`

AWS CLI の `--output text`・`--output table` と同じ形で、出力の JSON を文字列にする（`json` は `Json.pretty`）。

- `text`: タブ区切りの行。入れ子のオブジェクトと配列は、キーを大文字にしたものを行頭に置く。
- `table`: 罫線で囲んだ表。オブジェクトはキーと値の 2 列、同じキーのオブジェクトの配列は列見出しつきの表にし、
  入れ子は内側の枠にする。日本語の文字は幅 2 として数え、列をそろえる。
-/

public section

namespace Ritsuryo.Cli

/-- 端末での文字の幅。東アジアの全角の文字（ハングル、CJK、全角形など）は 2、それ以外は 1。 -/
def charWidth (c : Char) : Nat :=
  let n := c.toNat
  if (0x1100 ≤ n && n ≤ 0x115F) || (0x2E80 ≤ n && n ≤ 0xA4CF) || (0xAC00 ≤ n && n ≤ 0xD7A3) ||
      (0xF900 ≤ n && n ≤ 0xFAFF) || (0xFE30 ≤ n && n ≤ 0xFE4F) || (0xFF00 ≤ n && n ≤ 0xFF60) ||
      (0xFFE0 ≤ n && n ≤ 0xFFE6) || 0x20000 ≤ n then 2
  else 1

/-- 端末での文字列の幅。 -/
def displayWidth (s : String) : Nat :=
  s.foldl (fun acc c => acc + charWidth c) 0

/-- 幅 `w` になるまで右に空白を足す。 -/
def padRight (s : String) (w : Nat) : String :=
  s.pushn ' ' (w - displayWidth s)

/-- 幅 `w` の中央に置く。余りの空白は右に寄せる。 -/
def center (s : String) (w : Nat) : String :=
  let gap := w - displayWidth s
  ("".pushn ' ' (gap / 2)) ++ s ++ ("".pushn ' ' (gap - gap / 2))

/-- `--output text` の行。オブジェクトはスカラーのフィールドを 1 行にまとめ、入れ子は大文字のキーを行頭に
置いて続ける。スカラーだけの配列は 1 行にする。`prefix?` は行頭に置くキー。 -/
partial def textLines (prefix? : Option String) (j : Json) : List String :=
  let withPrefix (cells : List String) : String :=
    "\t".intercalate (match prefix? with | some p => p :: cells | none => cells)
  match j with
  | .obj fields =>
    let scalars := fields.toList.filter (·.2.isScalar)
    let head := if scalars.isEmpty then [] else [withPrefix (scalars.map (·.2.scalarText))]
    let nested := fields.toList.filter (!·.2.isScalar)
    head ++ nested.flatMap fun (k, v) => textLines (some k.toUpper) v
  | .arr xs =>
    if xs.all (·.isScalar) then
      if xs.isEmpty then [] else [withPrefix (xs.toList.map (·.scalarText))]
    else xs.toList.flatMap (textLines prefix?)
  | v => [withPrefix [v.scalarText]]

/-- `--output text`。AWS CLI と同じくタブ区切りで、入れ子のオブジェクトは大文字のキーを行頭に置く。
最上位のオブジェクトのスカラー（`SchemaVersion` など）は、意味が分かるように `キー<TAB>値` の行にして最後に出す。 -/
def renderText (j : Json) : String :=
  let lines := match j with
    | .obj fields =>
      let nested := fields.toList.filter (!·.2.isScalar)
      let scalars := fields.toList.filter (·.2.isScalar)
      nested.flatMap (fun (k, v) => textLines (some k.toUpper) v) ++
        scalars.map fun (k, v) => k.toUpper ++ "\t" ++ v.scalarText
    | v => textLines none v
  "\n".intercalate lines ++ "\n"

/-- 表の枠。上の罫線、中央にそろえた題、罫線、本体の行、下の罫線の順に並べる。 -/
def frame (title : String) (body : List String) (width : Nat) : List String :=
  let inner := width - 2
  let rule := "+" ++ "".pushn '-' inner ++ "+"
  [rule, "|" ++ center title inner ++ "|", rule] ++ body.map (fun l => "|" ++ l ++ "|") ++ [rule]

/-- 配列の要素がどれも同じキーの並びを持ち、値がスカラーだけのオブジェクトなら、そのキーの並び（表の列）。 -/
def columnsOf (xs : Array Json) : Option (List String) :=
  match (xs[0]? : Option Json) with
  | some (.obj fields) =>
    let keys := fields.toList.map (·.1)
    if xs.all fun
        | .obj fs => fs.toList.map (·.1) == keys && fs.all (·.2.isScalar)
        | _ => false
    then some keys else none
  | _ => none

/-- `--output table` の行。`minWidth` は外側の枠の幅に合わせるための最小の幅。
オブジェクトはスカラーをキーと値の 2 列にし、入れ子のものを同じ幅の内側の枠にする。 -/
partial def tableLines (title : String) (j : Json) (minWidth : Nat := 0) : List String :=
  match j with
  | .obj fields =>
    let scalars := fields.toList.filter (·.2.isScalar)
    let nested := fields.toList.filter (!·.2.isScalar)
    let keyW := scalars.foldl (fun w (k, _) => max w (displayWidth k)) 0
    let valW := scalars.foldl (fun w (_, v) => max w (displayWidth v.scalarText)) 0
    let rowW := if scalars.isEmpty then 0 else keyW + valW + 7
    -- 内側の枠を一度幅の指定なしで作って幅を測り、外側の幅を決めてから作り直す。
    let subs := nested.map fun (k, v) => tableLines k v
    let subW := subs.foldl (fun w ls => max w (ls.headD "").length) 0
    let width := [minWidth, rowW + 2, subW + 2, displayWidth title + 6].foldl max 0
    let inner := width - 2
    let valW' := inner - keyW - 7
    let rows := scalars.map fun (k, v) =>
      "  " ++ padRight k keyW ++ " | " ++ padRight v.scalarText valW' ++ "  "
    let subs := nested.map fun (k, v) => tableLines k v inner
    frame title (rows ++ subs.flatten) width
  | .arr xs =>
    if xs.all (·.isScalar) then
      let w := xs.foldl (fun w v => max w (displayWidth v.scalarText)) 0
      let width := [minWidth, w + 6, displayWidth title + 6].foldl max 0
      frame title (xs.toList.map fun v => "  " ++ padRight v.scalarText (width - 6) ++ "  ") width
    else
      match columnsOf xs with
      | some keys =>
        let cell (x : Json) (k : String) : String := ((x.get? k).map (·.scalarText)).getD ""
        let widths := keys.map fun k =>
          xs.foldl (fun w x => max w (displayWidth (cell x k))) (displayWidth k)
        let natural := widths.foldl (fun acc w => acc + w + 3) 1
        let width := [minWidth, natural + 2, displayWidth title + 6].foldl max 0
        -- 題が列の合計より長いときは、余った幅を最後の列に足す。
        let extra := width - 2 - natural
        let widths := match widths.reverse with
          | last :: rest => ((last + extra) :: rest).reverse
          | [] => []
        let row (cells : List String) : String :=
          "  " ++ " | ".intercalate ((cells.zip widths).map fun (c, w) => padRight c w) ++ "  "
        let sep := "+" ++ "".pushn '-' (width - 4) ++ "+"
        frame title ([row keys, sep] ++ xs.toList.map fun x => row (keys.map (cell x))) width
      | none =>
        let subs := xs.toList.map fun x => tableLines title x minWidth
        let width := subs.foldl (fun w ls => max w (ls.headD "").length) minWidth
        (xs.toList.map fun x => tableLines title x width).flatten
  | v => tableLines title (.obj #[("Value", v)]) minWidth

/-- `--output table` の文字列。`title` はサブコマンド名の PascalCase。 -/
def renderTable (title : String) (j : Json) : String :=
  "\n".intercalate (tableLines title j) ++ "\n"

end Ritsuryo.Cli
