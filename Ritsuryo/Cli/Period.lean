module

public import Ritsuryo.Cli.Envelope
public import Ritsuryo.Period.Impl
public import Ritsuryo.Period.Age
public import Ritsuryo.Period.Rollover
public import Ritsuryo.Period.Presets
public import Ritsuryo.Holiday.Lookup

/-!
# 期間・年齢・祝日のサブコマンド

`period`、`age`、`holiday`、`deadline` の各サブコマンドの実行関数と、そのコマンド表。

- `period compute-expiry`: 民法第140条〜第143条（`--rule civil`）または国税通則法第10条第1項
  （`--rule national-tax-general`）で期間の末日を求め、`--rollover-rule` があれば休日の繰り下げをする。
- `period compute-rollover`: 民法第142条、民事訴訟法第95条第3項、国税通則法第10条第2項による繰り下げ。
- `age get-attainment-date`・`age compute-age`: 年齢計算ニ関スル法律による年齢。
- `holiday list-holidays`・`holiday check-holiday`: 祝日法第2条・第3条の休日と、その区分。
- `deadline`: 個別の法律が定める期間（控訴・上告・即時抗告の期間、所得税の確定申告の期限）。

計算そのものは `Ritsuryo.Period` と `Ritsuryo.Holiday` の関数（証明のついたもの）を呼び、このファイルでは
引数の読み取りと、`Steps`・`Basis`・`Assumptions`・`Data` の組み立てだけをする。
祝日データ（内閣府の CSV）の範囲の外で国民の祝日が要るときは、終了コード 254 にする。
-/

public section

namespace Ritsuryo.Cli

open Ritsuryo.Period

/-- `--holiday-classes` に渡せる休日の区分の名前。 -/
def holidayClassValues : List String :=
  HolidayClass.all.map HolidayClass.name

/-- `--rollover-rule` に渡せる繰り下げの規則の名前。 -/
def rolloverRuleValues : List String :=
  ["none", "civil-142", "civil-procedure-95", "national-tax-10"]

/-- 繰り下げに関するパラメータ。`required` のときは `--rollover-rule` を必須にし、`none` を選べなくする。 -/
def rolloverParams (required : Bool) : List Param := [
  { name := "rollover-rule"
    type := .enum (if required then rolloverRuleValues.drop 1 else rolloverRuleValues)
    required
    help := "末日が休日のときの繰り下げ。civil-142（民法第142条）、civil-procedure-95" ++
      "（民事訴訟法第95条第3項）、national-tax-10（国税通則法第10条第2項）" ++
      (if required then "" else "、none（繰り下げない。既定）") },
  { name := "holiday-classes"
    type := .enumList holidayClassValues
    help := "civil-142 で休日とする日の区分。既定は sunday national-holiday" },
  { name := "assume-no-trade-custom"
    type := .flag
    help := "civil-142 で、その休日に取引をしない慣習があるものとする。ないときは繰り下げない" },
  { name := "new-year-general-holiday"
    type := .flag
    help := "national-tax-10 で 1月2日・3日を「一般の休日」とする（既定は true。国税通則法基本通達第10条関係4）" }]

/-- `--rollover-rule` の名前と関連するパラメータから、繰り下げの規則を作る。`none` なら繰り下げない。 -/
def rolloverRuleOf (a : Args) (name : String) : Except CliError (Option RolloverRule) := do
  let classes ← match a.strs? "HolidayClasses" with
    | some xs => pure (xs.filterMap HolidayClass.ofName?)
    | none => pure [.sunday, .nationalHoliday]
  match name with
  | "none" => pure none
  | "civil-142" => pure (some (.civil142 classes (a.flag "AssumeNoTradeCustom" false)))
  | "civil-procedure-95" => pure (some .civilProcedure95)
  | "national-tax-10" => pure (some (.nationalTax10 (a.flag "NewYearGeneralHoliday" true)))
  | other => throw (usageError s!"--rollover-rule {other} はない")

/-- 繰り下げの規則の根拠条文。 -/
def ruleBasis : RolloverRule → List (String × String)
  | .civil142 .. => [("民法", "第142条")]
  | .civilProcedure95 => [("民事訴訟法", "第95条第1項"), ("民事訴訟法", "第95条第3項")]
  | .nationalTax10 _ => [("国税通則法", "第10条第2項"), ("国税通則法施行令", "第2条第2項")]

/-- 繰り下げの規則が前提にする解釈と、利用者が選んだ前提。`Assumptions` に入れる。 -/
def ruleAssumptions : RolloverRule → List String
  | .civil142 classes custom =>
    if custom then
      ["末日が " ++ ", ".intercalate (classes.map HolidayClass.name) ++
        " に当たる日に取引をしない慣習があるものとする（民法第142条）"]
    else ["取引をしない慣習を前提にしないため、民法第142条による繰り下げをしない"]
  | .civilProcedure95 => []
  | .nationalTax10 general =>
    if general then ["1月2日・3日を国税通則法第10条第2項の「一般の休日」とする（国税通則法基本通達第10条関係4）"]
    else ["1月2日・3日を国税通則法第10条第2項の「一般の休日」としない"]

/-- 祝日データを使ったときに `Assumptions` に入れる前提（`docs/interpretation.md` の祝日法の読み方）。 -/
def nationalHolidayAssumption : String :=
  "内閣府の祝日 CSV の日（特例法による休日を含む）を国民の祝日に関する法律に規定する休日として扱う"

/-- 繰り下げで飛ばした 1 日の `RolledOverDays` の要素。規則が休日とする区分のうち当たるものと、祝日の名称。 -/
def skippedDay (rule : RolloverRule) (d : Date) : Json :=
  let classes := (rule.classesOf.filter (HolidayClass.holds Holiday.isHoliday d ·)).map
    HolidayClass.name
  .obj #[("Date", dateJson d), ("HolidayClasses", .arr (classes.toArray.map .str)),
    ("HolidayName", match Holiday.entry? d with
      | some e => .str e.name
      | none => .null)]

/-- `d` を規則で繰り下げ、繰り下げた日と、飛ばした日の一覧を返す。
規則が国民の祝日を使うときは、`d` と繰り下げた日が祝日データの範囲にあることを確かめる（範囲外は終了コード 254）。 -/
def applyRollover (rule : RolloverRule) (d : Date) : Except CliError (Date × Json) := do
  let uses := rule.classesOf.contains .nationalHoliday
  let some r := rollover (rule.isHoliday Holiday.isHoliday) 366 d
    | throw (otherError s!"{dateText d} から 366 日以内に休日でない日がない")
  if uses && !(Holiday.inRange d && Holiday.inRange r) then
    throw (domainError (s!"{dateText d} から {dateText r} は祝日データの範囲" ++
      s!"（{Holiday.Data.firstYear}〜{Holiday.Data.lastYear} 年）の外にある"))
  let n := (r.toDays - d.toDays).toNat
  let skipped := (List.range n).map fun (i : Nat) =>
    skippedDay rule (Date.ofDays (d.toDays + (i : Int)))
  return (r, .arr skipped.toArray)

/-- `--days`・`--weeks`・`--months`・`--years` のちょうど 1 つから期間の長さを読む。 -/
def lengthOf (a : Args) : Except CliError (String × Length) := do
  let opts := [("Days", Length.days), ("Weeks", Length.weeks), ("Months", Length.months),
    ("Years", Length.years)]
  match opts.filterMap fun (k, f) => (a.nat? k).map fun n => (k, f n) with
  | [x] => pure x
  | _ => throw (usageError "--days、--weeks、--months、--years のどれか 1 つを渡す")

/-- 国税通則法第10条第1項の期間の長さにする。同項は週による期間を定めていないので、週は `none`。 -/
def taxLengthOf : Length → Option TaxLength
  | .days n => some (.days n)
  | .months n => some (.months n)
  | .years n => some (.years n)
  | .weeks _ => none

/-- `period compute-expiry`。期間の末日を求め、`--rollover-rule` があれば繰り下げる。 -/
def computeExpiry (a : Args) : Except CliError Json := do
  let event ← dateArg a "EventDate"
  let (_, len) ← lengthOf a
  let mid := a.flag "StartAtMidnight" false
  let ruleName := (a.str? "Rule").getD "civil"
  let (res, basis, assumptions) ← match ruleName with
    | "national-tax-general" =>
      match taxLengthOf len with
      | some t => pure (computeTax event mid t,
          [("国税通則法", "第10条第1項第1号"), ("国税通則法", "第10条第1項第2号"),
            ("国税通則法", "第10条第1項第3号")],
          [if mid then "期間が午前零時から始まるものとして初日を算入する（国税通則法第10条第1項第1号ただし書）"
            else "初日を算入しない（国税通則法第10条第1項第1号）"])
      | none => throw (usageError "国税通則法第10条第1項は週による期間を定めていない。--weeks は使えない")
    | _ => pure (compute event mid len,
        [("民法", "第140条"), ("民法", "第141条"), ("民法", "第143条第1項"), ("民法", "第143条第2項")],
        [if mid then "期間が午前零時から始まるものとして初日を算入する（民法第140条ただし書）"
          else "期間は午前零時から始まらないものとして初日を算入しない（民法第140条本文）"])
  let rule? ← rolloverRuleOf a ((a.str? "RolloverRule").getD "none")
  let (final, skipped, basis, assumptions, data) ← match rule? with
    | none => pure (res.expiry, Json.arr #[], basis, assumptions, Json.null)
    | some rule =>
      let (r, skipped) ← applyRollover rule res.expiry
      let uses := rule.classesOf.contains .nationalHoliday
      pure (r, skipped, basis ++ ruleBasis rule,
        assumptions ++ ruleAssumptions rule ++
          ["繰り下げた日がまた休日に当たるときは、休日でない日まで繰り下げる"] ++
          (if uses then [nationalHolidayAssumption] else []),
        if uses then holidayDataJson else Json.null)
  return envelope (.obj #[("ExpiryDate", dateJson final)])
    (.obj #[("EventDate", dateJson event), ("StartAtMidnight", .bool mid),
      ("StartDate", dateJson res.start), ("CorrespondingDate", optDateJson res.corresponding),
      ("ExpiryBeforeRollover", dateJson res.expiry), ("RolledOverDays", skipped)])
    basis assumptions data

/-- `period compute-rollover`。日付を規則で繰り下げる。 -/
def computeRollover (a : Args) : Except CliError Json := do
  let d ← dateArg a "Date"
  let some rule ← rolloverRuleOf a ((a.str? "RolloverRule").getD "none")
    | throw (usageError "--rollover-rule に none は使えない")
  let (r, skipped) ← applyRollover rule d
  let uses := rule.classesOf.contains .nationalHoliday
  return envelope (.obj #[("Date", dateJson r)])
    (.obj #[("InputDate", dateJson d), ("RolledOverDays", skipped)])
    (ruleBasis rule)
    (ruleAssumptions rule ++ ["繰り下げた日がまた休日に当たるときは、休日でない日まで繰り下げる"] ++
      (if uses then [nationalHolidayAssumption] else []))
    (if uses then holidayDataJson else .null)

/-- 年齢の計算の根拠条文。年齢計算ニ関スル法律と、応当日のない月の末日を決める民法第143条第2項。 -/
def ageBasis : List (String × String) :=
  [("年齢計算ニ関スル法律", "第1項"), ("年齢計算ニ関スル法律", "第2項"), ("民法", "第143条第2項")]

/-- `age get-attainment-date`。`n` 歳に達する日と、`n` 年後の応当日（なければ null）を出す。 -/
def getAttainmentDate (a : Args) : Except CliError Json := do
  let birth ← dateArg a "BirthDate"
  let some n := a.nat? "Age" | throw (usageError "--age は必須")
  let ym : YearMonth := ⟨birth.year + n, birth.month⟩
  let corr : Option Date :=
    if birth.day ≤ ym.daysInMonth then some ⟨ym.year, ym.month, birth.day⟩ else none
  return envelope (.obj #[("AttainmentDate", dateJson (Age.attainmentDate birth n))])
    (.obj #[("BirthDate", dateJson birth), ("Age", .num n),
      ("CorrespondingDate", optDateJson corr)])
    ageBasis
    ["出生日を初日として算入し（年齢計算ニ関スル法律第1項）、n 年後の応当日の前日（応当日がない月はその月の末日）に n 歳に達する（同第2項、民法第143条）"]
    .null

/-- `age compute-age`。`--as-of` の日の終わりの満年齢と、その前後の年齢に達する日を出す。 -/
def computeAge (a : Args) : Except CliError Json := do
  let birth ← dateArg a "BirthDate"
  let asOf ← dateArg a "AsOf"
  if asOf.toDays < birth.toDays then
    throw (domainError s!"--as-of {dateText asOf} は --birth-date {dateText birth} より前")
  let n := Age.ageOn birth asOf
  return envelope (.obj #[("Age", .num n)])
    (.obj #[("BirthDate", dateJson birth), ("AsOf", dateJson asOf),
      ("AttainmentDate", dateJson (Age.attainmentDate birth n)),
      ("NextAttainmentDate", dateJson (Age.attainmentDate birth (n + 1)))])
    ageBasis
    ["AsOf の日の終わりの満年齢を出す。n 歳に達する日（AttainmentDate）の当日は n 歳とする"]
    .null

/-- CSV の行の区分（`Class`）と根拠（`Article`）。「休日」の行は、その日に施行されていた第3条第2項の
振替休日に当たるかで、振替休日と国民の休日に分ける。 -/
def holidayClassOf (y : Int) (e : Holiday.Entry) : String × String :=
  match e.kind with
  | .national => ("national-holiday", "国民の祝日に関する法律 第2条")
  | .treatedAsNational =>
    ("special-law-holiday", "天皇の即位の日及び即位礼正殿の儀の行われる日を休日とする法律")
  | .specialLaw => ("special-law-holiday", e.name)
  | .rest =>
    let H := fun z => (Holiday.nationalDays y).contains z
    if Holiday.isSubstituteAt H (Date.toDays ⟨y, e.month, e.day⟩) then
      ("substitute-holiday", "国民の祝日に関する法律 第3条第2項")
    else ("citizens-holiday", "国民の祝日に関する法律 第3条第3項")

/-- `holiday list-holidays`。`--year` の年の CSV の行を、区分と根拠つきで並べる。 -/
def listHolidays (a : Args) : Except CliError Json := do
  let some y := a.nat? "Year" | throw (usageError "--year は必須")
  let y : Int := y
  if !(Holiday.Data.firstYear ≤ y && y ≤ Holiday.Data.lastYear) then
    throw (domainError s!"{y} 年は祝日データの範囲（{Holiday.Data.firstYear}〜{Holiday.Data.lastYear} 年）の外")
  let items := (Holiday.entriesOf y).map fun e =>
    let (cls, article) := holidayClassOf y e
    Json.obj #[("Date", dateJson ⟨y, e.month, e.day⟩), ("Name", .str e.name), ("Class", .str cls),
      ("Article", .str article)]
  return envelope (.obj #[("Year", .num y), ("Holidays", .arr items.toArray)]) (.obj #[])
    [("国民の祝日に関する法律", "第2条"), ("国民の祝日に関する法律", "第3条第2項"),
      ("国民の祝日に関する法律", "第3条第3項")]
    ["休日の行は、施行日に応じた第3条第2項・第3項の規定で振替休日と国民の休日に分ける"]
    holidayDataJson

/-- `holiday check-holiday`。日付が当たる休日の区分と、繰り下げの規則ごとに休日に当たるかを出す。
民法第142条は、取引をしない慣習があるものとして判定する。 -/
def checkHoliday (a : Args) : Except CliError Json := do
  let d ← dateArg a "Date"
  if !Holiday.inRange d then
    throw (domainError (s!"{dateText d} は祝日データの範囲" ++
      s!"（{Holiday.Data.firstYear}〜{Holiday.Data.lastYear} 年）の外"))
  let classes := (HolidayClass.all.filter (HolidayClass.holds Holiday.isHoliday d ·)).map
    HolidayClass.name
  let civilClasses ← match a.strs? "HolidayClasses" with
    | some xs => pure (xs.filterMap HolidayClass.ofName?)
    | none => pure [.sunday, .nationalHoliday]
  let general := a.flag "NewYearGeneralHoliday" true
  let rules : List (String × RolloverRule) := [("civil-142", .civil142 civilClasses true),
    ("civil-procedure-95", .civilProcedure95), ("national-tax-10", .nationalTax10 general)]
  let national := match Holiday.entry? d with
    | some e =>
      let (cls, article) := holidayClassOf d.year e
      Json.obj #[("Name", .str e.name), ("Class", .str cls), ("Article", .str article)]
    | none => .null
  return envelope
    (.obj #[("Date", dateJson d), ("Weekday", .str d.weekday.toString),
      ("NationalHoliday", national), ("HolidayClasses", .arr (classes.toArray.map .str)),
      ("Rules", .arr (rules.toArray.map fun (n, r) =>
        .obj #[("RolloverRule", .str n), ("IsHoliday", .bool (r.isHoliday Holiday.isHoliday d))]))])
    (.obj #[])
    ([("国民の祝日に関する法律", "第3条")] ++ ruleBasis (.civil142 [] true) ++
      ruleBasis .civilProcedure95 ++ ruleBasis (.nationalTax10 true))
    (ruleAssumptions (.civil142 civilClasses true) ++ ruleAssumptions (.nationalTax10 general) ++
      [nationalHolidayAssumption])
    holidayDataJson

/-- 出力の雛形の `RolledOverDays`。 -/
def rolledOverSkeleton : Json :=
  .arr #[.obj #[("Date", .str ""), ("HolidayClasses", .arr #[.str ""]), ("HolidayName", .str "")]]

/-- 民事訴訟法の期間の末日（`deadline` の控訴・上告・即時抗告）。 -/
def computeCourtDeadline (p : CourtPeriod) (eventKey : String) (a : Args) :
    Except CliError Json := do
  let event ← dateArg a eventKey
  let res := compute event false p.length
  let (final, skipped) ← applyRollover .civilProcedure95 res.expiry
  return envelope
    (.obj #[("Deadline", dateJson final), ("Period", .str p.title),
      ("Invariable", .bool p.invariable)])
    (.obj #[("EventDate", dateJson event), ("StartDate", dateJson res.start),
      ("CorrespondingDate", optDateJson res.corresponding),
      ("ExpiryBeforeRollover", dateJson res.expiry), ("RolledOverDays", skipped)])
    (p.provisions ++ [("民事訴訟法", "第95条第1項"), ("民法", "第140条"), ("民法", "第141条"),
      ("民法", "第143条第2項"), ("民事訴訟法", "第95条第3項")] ++
      (if p.invariable then [("民事訴訟法", "第96条第1項")] else []))
    (["起算点は" ++ p.event ++ "。初日を算入しない（民事訴訟法第95条第1項、民法第140条本文）",
      "繰り下げた日がまた休日に当たるときは、休日でない日まで繰り下げる", nationalHolidayAssumption] ++
      (if p.invariable then [p.title ++ "は不変期間で、裁判所は伸縮できない（民事訴訟法第96条第1項ただし書）。" ++
        "遠隔の地に住所がある者のための付加期間（同条第2項）は含めない"] else []))
    holidayDataJson

/-- 所得税の確定申告の期限（`deadline get-income-tax-return-deadline`）。 -/
def getIncomeTaxReturnDeadline (a : Args) : Except CliError Json := do
  let some y := a.nat? "TaxYear" | throw (usageError "--tax-year は必須")
  let due := incomeTaxReturnDue y
  let general := a.flag "NewYearGeneralHoliday" true
  let (final, skipped) ← applyRollover (.nationalTax10 general) due
  return envelope (.obj #[("Deadline", dateJson final)])
    (.obj #[("TaxYear", .num y), ("StatutoryDueDate", dateJson due), ("RolledOverDays", skipped)])
    ([("所得税法", "第120条第1項")] ++ ruleBasis (.nationalTax10 general))
    (["その年の翌年3月15日（第三期の末日。所得税法第120条第1項）を期限とし、休日などに当たるときは繰り下げる",
      nationalHolidayAssumption] ++ ruleAssumptions (.nationalTax10 general))
    holidayDataJson

/-- `deadline` の民事訴訟法の期間のサブコマンドを作る。起算の日のパラメータ名と説明だけが期間ごとに違う。 -/
def courtDeadlineSubcommand (p : CourtPeriod) (sub help eventParam eventHelp : String) :
    Subcommand :=
  { name := sub
    help
    params := [{ name := eventParam, type := .date, required := true, help := eventHelp }]
    outputSkeleton := envelopeSkeleton
      (.obj #[("Deadline", .str ""), ("Period", .str ""), ("Invariable", .bool false)])
      (.obj #[("EventDate", .str ""), ("StartDate", .str ""), ("CorrespondingDate", .str ""),
        ("ExpiryBeforeRollover", .str ""), ("RolledOverDays", rolledOverSkeleton)])
    run := computeCourtDeadline p (pascalCase eventParam) }

/-- `deadline` コマンドの表。 -/
def deadlineCommand : Command :=
  { name := "deadline"
    help := "個別の法律が定める期間の期限（控訴・上告・即時抗告・所得税の確定申告）"
    subcommands := [
      courtDeadlineSubcommand appealPeriod "compute-appeal-deadline"
        "控訴期間の末日（民事訴訟法第285条。送達を受けた日から2週間の不変期間）"
        "served-date" "判決書の送達を受けた日",
      courtDeadlineSubcommand finalAppealPeriod "compute-final-appeal-deadline"
        "上告期間の末日（民事訴訟法第313条・第285条。送達を受けた日から2週間の不変期間）"
        "served-date" "判決書の送達を受けた日",
      courtDeadlineSubcommand immediateAppealPeriod "compute-immediate-appeal-deadline"
        "即時抗告期間の末日（民事訴訟法第332条。告知を受けた日から1週間の不変期間）"
        "notified-date" "裁判の告知を受けた日",
      { name := "get-income-tax-return-deadline"
        help := "所得税の確定申告の期限（所得税法第120条第1項、国税通則法第10条第2項）"
        params := [
          { name := "tax-year", type := .nat, required := true, help := "所得税の年分（西暦）" },
          { name := "new-year-general-holiday", type := .flag,
            help := "1月2日・3日を「一般の休日」とする（既定は true）" }]
        outputSkeleton := envelopeSkeleton (.obj #[("Deadline", .str "")])
          (.obj #[("TaxYear", .num 0), ("StatutoryDueDate", .str ""),
            ("RolledOverDays", rolledOverSkeleton)])
        run := getIncomeTaxReturnDeadline }] }

/-- `period`・`age`・`holiday`・`deadline` のコマンドの表。 -/
def periodCommands : List Command := [
  { name := "period"
    help := "期間の満了日と、末日が休日のときの繰り下げ"
    subcommands := [
      { name := "compute-expiry"
        help := "日・週・月・年による期間の満了日（民法第140条〜第143条、国税通則法第10条）"
        params := [
          { name := "event-date", type := .date, required := true,
            help := "期間の起算の基準になる日（事実の発生日）" },
          { name := "days", type := .nat, help := "日による期間の日数" },
          { name := "weeks", type := .nat, help := "週による期間の週数（--rule civil だけ）" },
          { name := "months", type := .nat, help := "月による期間の月数" },
          { name := "years", type := .nat, help := "年による期間の年数" },
          { name := "rule", type := .enum ["civil", "national-tax-general"],
            help := "civil（民法第140条〜第143条。既定）または national-tax-general（国税通則法第10条第1項）" },
          { name := "start-at-midnight", type := .flag,
            help := "期間が午前零時から始まるものとして初日を算入する（既定は false）" }] ++
          rolloverParams false
        outputSkeleton := envelopeSkeleton (.obj #[("ExpiryDate", .str "")])
          (.obj #[("EventDate", .str ""), ("StartAtMidnight", .bool false), ("StartDate", .str ""),
            ("CorrespondingDate", .str ""), ("ExpiryBeforeRollover", .str ""),
            ("RolledOverDays", rolledOverSkeleton)])
        run := computeExpiry },
      { name := "compute-rollover"
        help := "日付が休日に当たるときに、休日でない日まで繰り下げる"
        params := [{ name := "date", type := .date, required := true, help := "繰り下げる前の日" }] ++
          rolloverParams true
        outputSkeleton := envelopeSkeleton (.obj #[("Date", .str "")])
          (.obj #[("InputDate", .str ""), ("RolledOverDays", rolledOverSkeleton)])
        run := computeRollover }] },
  { name := "age"
    help := "年齢の計算（年齢計算ニ関スル法律）"
    subcommands := [
      { name := "get-attainment-date"
        help := "n 歳に達する日"
        params := [
          { name := "birth-date", type := .date, required := true, help := "出生日" },
          { name := "age", type := .nat, required := true, help := "年齢" }]
        outputSkeleton := envelopeSkeleton (.obj #[("AttainmentDate", .str "")])
          (.obj #[("BirthDate", .str ""), ("Age", .num 0), ("CorrespondingDate", .str "")])
        run := getAttainmentDate },
      { name := "compute-age"
        help := "ある日の満年齢"
        params := [
          { name := "birth-date", type := .date, required := true, help := "出生日" },
          { name := "as-of", type := .date, required := true, help := "年齢を求める日" }]
        outputSkeleton := envelopeSkeleton (.obj #[("Age", .num 0)])
          (.obj #[("BirthDate", .str ""), ("AsOf", .str ""), ("AttainmentDate", .str ""),
            ("NextAttainmentDate", .str "")])
        run := computeAge }] },
  { name := "holiday"
    help := "国民の祝日と休日（国民の祝日に関する法律第2条・第3条）"
    subcommands := [
      { name := "list-holidays"
        help := "年の祝日と休日の一覧"
        params := [{ name := "year", type := .nat, required := true, help := "西暦年" }]
        outputSkeleton := envelopeSkeleton (.obj #[("Year", .num 0), ("Holidays", .arr #[.obj #[
          ("Date", .str ""), ("Name", .str ""), ("Class", .str ""), ("Article", .str "")]])])
          (.obj #[])
        run := listHolidays },
      { name := "check-holiday"
        help := "日付がどの休日の区分と繰り下げの規則に当たるか"
        params := [
          { name := "date", type := .date, required := true, help := "調べる日" },
          { name := "holiday-classes", type := .enumList holidayClassValues,
            help := "civil-142 で休日とする日の区分。既定は sunday national-holiday" },
          { name := "new-year-general-holiday", type := .flag,
            help := "national-tax-10 で 1月2日・3日を「一般の休日」とする（既定は true）" }]
        outputSkeleton := envelopeSkeleton (.obj #[("Date", .str ""), ("Weekday", .str ""),
          ("NationalHoliday", .obj #[("Name", .str ""), ("Class", .str ""), ("Article", .str "")]),
          ("HolidayClasses", .arr #[.str ""]),
          ("Rules", .arr #[.obj #[("RolloverRule", .str ""), ("IsHoliday", .bool false)]])])
          (.obj #[])
        run := checkHoliday }] },
  deadlineCommand]

end Ritsuryo.Cli
