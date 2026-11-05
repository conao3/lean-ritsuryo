module

public import Ritsuryo.Cli.Core
public import Ritsuryo.Law
public import Ritsuryo.Calendar.Date
public import Ritsuryo.Holiday.Data.Generated

/-!
# 出力の共通部分

どのサブコマンドの出力も、同じ形のオブジェクト（エンベロープ）に入れる。

- `Result`: 計算結果（日付、金額）
- `Steps`: 途中の値（起算日、応当日、繰り下げ前の末日、区分ごとの税額、切捨て前の額）
- `Basis`: 計算に使った条文（法令名、条・項・号、e-Gov の法令 ID）
- `Assumptions`: 計算の前提にした解釈と、利用者が選んだ前提
- `Data`: 使ったデータの版（祝日 CSV の取得日と範囲、割合の表の出典）。データを使わない計算では空のオブジェクト
- `SchemaVersion`: 出力の形の版

このファイルは、エンベロープを組む `envelope` と、日付の文字列への変換・読み取り、条文の一覧の JSON、
祝日 CSV の版の JSON を置く。
-/

public section

namespace Ritsuryo.Cli

/-- 出力の `SchemaVersion` に入れる、出力の形の版。 -/
def schemaVersion : String := "1"

/-- 2 桁に 0 で詰める。 -/
def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

/-- 年を 4 桁以上に 0 で詰める。負の年は `-` を前に置く。 -/
def yearText (y : Int) : String :=
  if y < 0 then "-" ++ "".pushn '0' (4 - (toString (-y)).length) ++ toString (-y)
  else "".pushn '0' (4 - (toString y).length) ++ toString y

/-- 日付を `YYYY-MM-DD` の文字列にする。 -/
def dateText (d : Date) : String :=
  s!"{yearText d.year}-{pad2 d.month}-{pad2 d.day}"

/-- 日付を `YYYY-MM-DD` の JSON の文字列にする。 -/
def dateJson (d : Date) : Json :=
  .str (dateText d)

/-- 日付があればその文字列、なければ null（応当日がない場合など）。 -/
def optDateJson : Option Date → Json
  | some d => dateJson d
  | none => .null

/-- `YYYY-MM-DD` の文字列を日付にする。実在しない日付（2 月 30 日など）は `none`。 -/
def parseDate (s : String) : Option Date :=
  match s.splitOn "-" with
  | [y, m, d] => do
    let d' : Date := ⟨(← y.toNat?), ← m.toNat?, ← d.toNat?⟩
    if d'.Valid then some d' else none
  | _ => none

/-- `Args` のキーの日付。形は `checkValue` で確かめてあるので、実在しない日付は終了コード 254 にする。 -/
def dateArg (a : Args) (key : String) : Except CliError Date := do
  let some s := a.str? key | throw (usageError s!"{key} がない")
  match parseDate s with
  | some d => pure d
  | none => throw (domainError s!"{s} は存在しない日付")

/-- `Basis` の配列。法令名と条ごとに、`Ritsuryo/Law.lean` から e-Gov の法令 ID を引いて入れる。 -/
def basisJson (items : List (String × String)) : Json :=
  .arr (items.toArray.map fun (law, article) =>
    .obj #[("Law", .str law), ("Article", .str article),
      ("LawId", .str ((Law.find? law).map (·.lawId) |>.getD ""))])

/-- `Data.HolidayCsv`。使った祝日 CSV の取得元、Last-Modified、SHA-256、年の範囲。 -/
def holidayDataJson : Json :=
  .obj #[("HolidayCsv", .obj #[
    ("Source", .str Holiday.Data.source),
    ("LastModified", .str Holiday.Data.lastModified),
    ("Sha256", .str Holiday.Data.sha256),
    ("FirstYear", .num Holiday.Data.firstYear),
    ("LastYear", .num Holiday.Data.lastYear)])]

/-- 出力のエンベロープ。`data` が `null` のときは空のオブジェクトにする。 -/
def envelope (result steps : Json) (basis : List (String × String)) (assumptions : List String)
    (data : Json) : Json :=
  let data := match data with
    | .null => .obj #[]
    | d => d
  .obj #[("Result", result), ("Steps", steps), ("Basis", basisJson basis),
    ("Assumptions", .arr (assumptions.toArray.map .str)), ("Data", data),
    ("SchemaVersion", .str schemaVersion)]

/-- `help` の OUTPUT に出す出力の雛形。`Result` と `Steps` をサブコマンドごとに受け取り、残りは空の値にする。 -/
def envelopeSkeleton (result steps : Json) : Json :=
  envelope result steps [("", "")] [""] (.obj #[("HolidayCsv", .obj #[("Source", .str ""),
    ("LastModified", .str ""), ("Sha256", .str ""), ("FirstYear", .num 0),
    ("LastYear", .num 0)])])

end Ritsuryo.Cli
