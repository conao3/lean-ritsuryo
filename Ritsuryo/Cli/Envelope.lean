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
-/

public section

namespace Ritsuryo.Cli

def schemaVersion : String := "1"

def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else toString n

def yearText (y : Int) : String :=
  if y < 0 then "-" ++ "".pushn '0' (4 - (toString (-y)).length) ++ toString (-y)
  else "".pushn '0' (4 - (toString y).length) ++ toString y

def dateText (d : Date) : String :=
  s!"{yearText d.year}-{pad2 d.month}-{pad2 d.day}"

def dateJson (d : Date) : Json :=
  .str (dateText d)

def optDateJson : Option Date → Json
  | some d => dateJson d
  | none => .null

def parseDate (s : String) : Option Date :=
  match s.splitOn "-" with
  | [y, m, d] => do
    let d' : Date := ⟨(← y.toNat?), ← m.toNat?, ← d.toNat?⟩
    if d'.Valid then some d' else none
  | _ => none

def dateArg (a : Args) (key : String) : Except CliError Date := do
  let some s := a.str? key | throw (usageError s!"{key} がない")
  match parseDate s with
  | some d => pure d
  | none => throw (domainError s!"{s} は存在しない日付")

def basisJson (items : List (String × String)) : Json :=
  .arr (items.toArray.map fun (law, article) =>
    .obj #[("Law", .str law), ("Article", .str article),
      ("LawId", .str ((Law.find? law).map (·.lawId) |>.getD ""))])

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

def envelopeSkeleton (result steps : Json) : Json :=
  envelope result steps [("", "")] [""] (.obj #[("HolidayCsv", .obj #[("Source", .str ""),
    ("LastModified", .str ""), ("Sha256", .str ""), ("FirstYear", .num 0),
    ("LastYear", .num 0)])])

end Ritsuryo.Cli
