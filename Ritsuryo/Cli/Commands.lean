module

public import Ritsuryo.Cli.Core
public import Ritsuryo.Law
public import Ritsuryo.Period.Impl
public import Ritsuryo.Period.Age
public import Ritsuryo.Period.Rollover
public import Ritsuryo.Holiday.Lookup

public section

namespace Ritsuryo.Cli

open Ritsuryo.Period

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

def envelope (result steps : Json) (basis : List (String × String)) (assumptions : List String)
    (data : Json) : Json :=
  .obj #[("Result", result), ("Steps", steps), ("Basis", basisJson basis),
    ("Assumptions", .arr (assumptions.toArray.map .str)), ("Data", data),
    ("SchemaVersion", .str schemaVersion)]

def envelopeSkeleton (result steps : Json) : Json :=
  envelope result steps [("", "")] [""] (.obj #[("HolidayCsv", .obj #[("Source", .str ""),
    ("LastModified", .str ""), ("Sha256", .str ""), ("FirstYear", .num 0),
    ("LastYear", .num 0)])])

def holidayClassValues : List String :=
  HolidayClass.all.map HolidayClass.name

def rolloverRuleValues : List String :=
  ["none", "civil-142", "civil-procedure-95", "national-tax-10"]

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

def ruleBasis : RolloverRule → List (String × String)
  | .civil142 .. => [("民法", "第142条")]
  | .civilProcedure95 => [("民事訴訟法", "第95条第1項"), ("民事訴訟法", "第95条第3項")]
  | .nationalTax10 _ => [("国税通則法", "第10条第2項"), ("国税通則法施行令", "第2条第2項")]

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

def nationalHolidayAssumption : String :=
  "内閣府の祝日 CSV の日（特例法による休日を含む）を国民の祝日に関する法律に規定する休日として扱う"

def skippedDay (rule : RolloverRule) (d : Date) : Json :=
  let classes := (rule.classesOf.filter (HolidayClass.holds Holiday.isHoliday d ·)).map
    HolidayClass.name
  .obj #[("Date", dateJson d), ("HolidayClasses", .arr (classes.toArray.map .str)),
    ("HolidayName", match Holiday.entry? d with
      | some e => .str e.name
      | none => .null)]

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

def lengthOf (a : Args) : Except CliError (String × Length) := do
  let opts := [("Days", Length.days), ("Weeks", Length.weeks), ("Months", Length.months),
    ("Years", Length.years)]
  match opts.filterMap fun (k, f) => (a.nat? k).map fun n => (k, f n) with
  | [x] => pure x
  | _ => throw (usageError "--days、--weeks、--months、--years のどれか 1 つを渡す")

def taxLengthOf : Length → Option TaxLength
  | .days n => some (.days n)
  | .months n => some (.months n)
  | .years n => some (.years n)
  | .weeks _ => none

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

def ageBasis : List (String × String) :=
  [("年齢計算ニ関スル法律", "第1項"), ("年齢計算ニ関スル法律", "第2項"), ("民法", "第143条第2項")]

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

def rolledOverSkeleton : Json :=
  .arr #[.obj #[("Date", .str ""), ("HolidayClasses", .arr #[.str ""]), ("HolidayName", .str "")]]

def commands : List Command := [
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
        run := checkHoliday }] }]

end Ritsuryo.Cli
