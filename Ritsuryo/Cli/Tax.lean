module

public import Ritsuryo.Cli.Envelope
public import Ritsuryo.Tax.Income
public import Ritsuryo.Tax.Inheritance
public import Ritsuryo.Tax.Consumption
public import Ritsuryo.Tax.Delinquency
public import Ritsuryo.Tax.Penalty

/-!
# 税のサブコマンド

`income-tax`、`inheritance-tax`、`consumption-tax`、`delinquency-tax`、`interest-tax`、`penalty-tax` の
実行関数と、そのコマンド表。金額は円の整数で受け取り、円の整数で出す。割合は `"2.8%"` のような文字列で出す。
-/

public section

namespace Ritsuryo.Cli

open Ritsuryo.Tax

/-- 千分の一単位の割合を `"2.8%"` の形にする。 -/
def tenthsPercent (n : Nat) : String :=
  s!"{n / 10}.{n % 10}%"

/-- 分数を既約にして `"1/4"` の形にする。 -/
def fractionText (num den : Nat) : String :=
  let g := Nat.gcd num den
  if g == 0 then "0" else s!"{num / g}/{den / g}"

def natArg (a : Args) (key : String) : Nat :=
  (a.nat? key).getD 0

def itemsArg (a : Args) (key : String) : Array Json :=
  match a.get? key with
  | some (.arr xs) => xs
  | _ => #[]

/-- 「国税通則法 第65条第1項」の形の規定名を `(法令名, 条)` に分ける。 -/
def splitProvision (s : String) : String × String :=
  match s.splitOn " " with
  | [law, article] => (law, article)
  | _ => (s, "")

/-! ## income-tax -/

def reconstructionLaw : String :=
  "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法"

def defenseLaw : String :=
  "我が国の防衛力の抜本的な強化等のために必要な財源の確保に関する特別措置法"

def incomeLine (input base tax : Nat) : Json :=
  .obj #[("Input", .num input), ("Base", .num base), ("Tax", .num tax)]

def computeIncomeTax (a : Args) : Except CliError Json := do
  let some year := a.nat? "TaxYear" | throw (usageError "--tax-year は必須")
  if year < 2015 then
    throw (domainError s!"{year} 年分は扱えない。所得税法第89条の現行の税率表は平成27年分（2015 年分）以後に適用される")
  let o := natArg a "TaxableIncome"
  let r := natArg a "TaxableRetirementIncome"
  let t := natArg a "TaxableTimberIncome"
  let res := Income.compute year o r t
  let rp := Income.reconstructionPermille year
  let dp := Income.defensePermille year
  let special : List (String × String) :=
    (if rp > 0 then [(reconstructionLaw, "第9条第1項"), (reconstructionLaw, "第13条")] else []) ++
    (if year ≥ 2027 && rp > 0 then
      [("所得税法等の一部を改正する法律（令和8年法律第12号）", "附則第88条第1項")] else []) ++
    (if dp > 0 then [(defenseLaw, "第5条の5第1項"), (defenseLaw, "第5条の9")] else [])
  return envelope
    (.obj #[("IncomeTax", .num res.incomeTax), ("ReconstructionTax", .num res.reconstructionTax),
      ("DefenseTax", .num res.defenseTax), ("Total", .num res.total),
      ("Payable", .num res.payable)])
    (.obj #[("TaxYear", .num year),
      ("TaxableIncome", incomeLine o res.ordinaryBase res.ordinaryTax),
      ("TaxableRetirementIncome", incomeLine r res.retirementBase res.retirementTax),
      ("TaxableTimberIncome", incomeLine t res.timberBase res.timberTax),
      ("ReconstructionRate", .str (tenthsPercent rp)), ("DefenseRate", .str (tenthsPercent dp))])
    ([("所得税法", "第89条第1項"), ("国税通則法", "第118条第1項")] ++ special ++
      [("国税通則法", "第119条第1項")])
    ["入力は所得控除の後の課税総所得金額・課税退職所得金額・課税山林所得金額で、千円未満を切り捨てて税率表を当てる",
      "課税山林所得金額は、五分の一の金額に税率表を当てて五を掛ける（5 分 5 乗）",
      "基準所得税額は第89条の税額とし、税額控除（配当控除・外国税額控除など）はないものとする",
      "復興特別所得税・防衛特別所得税は一円未満を切り捨てる",
      "Payable は所得税と特別所得税の合計の百円未満を切り捨てた額で、源泉徴収税額・予定納税額を引く前の額"]
    .null

def incomeLineSkeleton : Json :=
  .obj #[("Input", .num 0), ("Base", .num 0), ("Tax", .num 0)]

def incomeTaxCommand : Command :=
  { name := "income-tax"
    help := "所得税（所得税法第89条）と復興特別所得税・防衛特別所得税"
    subcommands := [
      { name := "compute-tax"
        help := "課税所得金額に対する所得税の額（速算表は第89条の積み上げと一致することを証明済み）"
        params := [
          { name := "tax-year", type := .nat, required := true, help := "所得税の年分（西暦、2015 以後）" },
          { name := "taxable-income", type := .nat, help := "課税総所得金額（円）" },
          { name := "taxable-retirement-income", type := .nat, help := "課税退職所得金額（円）" },
          { name := "taxable-timber-income", type := .nat, help := "課税山林所得金額（円）" }]
        outputSkeleton := envelopeSkeleton
          (.obj #[("IncomeTax", .num 0), ("ReconstructionTax", .num 0), ("DefenseTax", .num 0),
            ("Total", .num 0), ("Payable", .num 0)])
          (.obj #[("TaxYear", .num 0), ("TaxableIncome", incomeLineSkeleton),
            ("TaxableRetirementIncome", incomeLineSkeleton),
            ("TaxableTimberIncome", incomeLineSkeleton),
            ("ReconstructionRate", .str ""), ("DefenseRate", .str "")])
        run := computeIncomeTax }] }

/-! ## inheritance-tax -/

def heirKindName : Inheritance.HeirKind → String
  | .spouse => "spouse"
  | .child => "child"
  | .ascendant => "ascendant"
  | .fullSibling => "full-sibling"
  | .halfSibling => "half-sibling"

def heirsOf (a : Args) : Inheritance.Heirs :=
  { spouse := a.flag "Spouse" false
    biologicalChildren := natArg a "BiologicalChildren"
    adoptedChildren := natArg a "AdoptedChildren"
    ascendants := natArg a "Ascendants"
    fullSiblings := natArg a "FullSiblings"
    halfSiblings := natArg a "HalfSiblings" }

def heirParams : List Param := [
  { name := "spouse", type := .flag, help := "配偶者がいる（既定は false）" },
  { name := "biological-children", type := .nat,
    help := "実子の数（特別養子・配偶者の実子である養子など相続税法第15条第3項で実子とみなす者を含む）" },
  { name := "adopted-children", type := .nat, help := "養子の数（実子とみなす者を除く）" },
  { name := "ascendants", type := .nat, help := "直系尊属のうち親等の最も近い者の数（子がいないときに相続人になる）" },
  { name := "full-siblings", type := .nat, help := "父母の双方を同じくする兄弟姉妹の数（子も直系尊属もいないとき）" },
  { name := "half-siblings", type := .nat, help := "父母の一方のみを同じくする兄弟姉妹の数" }]

def heirAssumptions : List String :=
  ["相続の放棄はなかったものとして数える（相続税法第15条第2項）",
    "代襲相続（民法第901条）、相続欠格・廃除は扱わない"]

def computeInheritanceTax (a : Args) : Except CliError Json := do
  let some value := a.nat? "TaxableValueTotal" | throw (usageError "--taxable-value-total は必須")
  let h := heirsOf a
  let res := Inheritance.compute value h
  let heirs := res.heirs.toArray.map fun (x : Inheritance.HeirTax) =>
    Json.obj #[("Heir", .str (heirKindName x.kind)),
      ("Share", .str (fractionText x.numerator res.denominator)),
      ("Acquired", .num x.acquired), ("Tax", .num x.tax)]
  return envelope (.obj #[("TotalTax", .num res.total)])
    (.obj #[("TaxableValueTotal", .num value), ("HeirCount", .num res.heirCount),
      ("BasicDeduction", .num res.basicDeduction), ("TaxableEstate", .num res.taxableEstate),
      ("Heirs", .arr heirs), ("TotalBeforeRounding", .num res.totalBeforeRounding)])
    [("相続税法", "第15条第1項"), ("相続税法", "第15条第2項"), ("相続税法", "第16条"), ("民法", "第887条第1項"),
      ("民法", "第889条第1項"), ("民法", "第890条"), ("民法", "第900条")]
    (["平成27年1月1日以後の相続に適用される税率表と基礎控除による",
      "相続人の数に入れる養子は、実子があれば1人、なければ2人までとし、法定相続分もその人数で按分する（相続税法第15条第2項・第16条）",
      "法定相続分に応ずる取得金額は千円未満を、相続税の総額は百円未満を切り捨てる（相続税法基本通達16-3）"] ++
      heirAssumptions)
    .null

def computeStatutoryShares (a : Args) : Except CliError Json := do
  let h := heirsOf a
  let civil : Inheritance.Heirs :=
    { h with biologicalChildren := h.biologicalChildren + h.adoptedChildren, adoptedChildren := 0 }
  let r := Inheritance.rankOf civil
  if !h.spouse && r == .none then throw (usageError "相続人がいない。--spouse か人数を渡す")
  let sh := Inheritance.statutoryShares civil.spouse r
  let shares := sh.shares.toArray.map fun (k, n) =>
    Json.obj #[("Heir", .str (heirKindName k)), ("Share", .str (fractionText n sh.denominator)),
      ("Numerator", .num n)]
  return envelope (.obj #[("Shares", .arr shares), ("Denominator", .num sh.denominator)])
    (.obj #[("Rank", .str (match r with
      | .children _ => "children"
      | .ascendants _ => "ascendants"
      | .siblings _ _ => "siblings"
      | .none => "none"))])
    [("民法", "第887条第1項"), ("民法", "第889条第1項"), ("民法", "第890条"), ("民法", "第900条")]
    (["養子は実子と同じく子として数える（民法第809条）"] ++ heirAssumptions.drop 1)
    .null

def inheritanceTaxCommand : Command :=
  { name := "inheritance-tax"
    help := "相続税の総額（相続税法第15条・第16条）と法定相続分（民法第900条）"
    subcommands := [
      { name := "compute-total-tax"
        help := "課税価格の合計額と相続人の構成から、相続税の総額を出す"
        params := [({ name := "taxable-value-total", type := .nat, required := true,
                      help := "同一の被相続人から財産を取得した全員の課税価格の合計額（円）" } : Param)] ++ heirParams
        outputSkeleton := envelopeSkeleton (.obj #[("TotalTax", .num 0)])
          (.obj #[("TaxableValueTotal", .num 0), ("HeirCount", .num 0), ("BasicDeduction", .num 0),
            ("TaxableEstate", .num 0),
            ("Heirs", .arr #[.obj #[("Heir", .str ""), ("Share", .str ""),
              ("Acquired", .num 0), ("Tax", .num 0)]]), ("TotalBeforeRounding", .num 0)])
        run := computeInheritanceTax },
      { name := "compute-statutory-shares"
        help := "相続人の構成から法定相続分を出す（民法第900条）"
        params := heirParams
        outputSkeleton := envelopeSkeleton
          (.obj #[("Shares", .arr #[.obj #[("Heir", .str ""), ("Share", .str ""),
              ("Numerator", .num 0)]]),
            ("Denominator", .num 0)])
          (.obj #[("Rank", .str "")])
        run := computeStatutoryShares }] }

/-! ## consumption-tax -/

def rateName : Consumption.Rate → String
  | .standard => "standard"
  | .reduced => "reduced"

def computeInvoiceTax (a : Args) : Except CliError Json := do
  let items ← (itemsArg a "Items").toList.mapM fun j => do
    let some (.num p) := j.get? "Price" | throw (usageError "--items の Price がない")
    let rate : Consumption.Rate :=
      if j.get? "Rate" matches some (.str "reduced") then .reduced else .standard
    pure ({ price := p.toNat, rate } : Consumption.Item)
  if items.isEmpty then throw (usageError "--items に品目がない")
  let basis : Consumption.PriceBasis :=
    if (a.str? "PriceBasis") == some "inclusive" then .inclusive else .exclusive
  let mode : Consumption.Rounding := match a.str? "Rounding" with
    | some "ceil" => .ceil
    | some "half-up" => .halfUp
    | _ => .floor
  let totals := Consumption.invoiceTax mode basis items
  let rows := totals.toArray.map fun (t : Consumption.RateTotal) =>
    Json.obj #[("Rate", .str (rateName t.rate)), ("RatePercent", .num t.rate.percent),
      ("PriceTotal", .num t.priceTotal), ("Tax", .num t.tax)]
  let perItem := totals.toArray.map fun (t : Consumption.RateTotal) =>
    Json.obj #[("Rate", .str (rateName t.rate)), ("PerItemTaxTotal", .num t.perItemTax),
      ("Difference", .num ((t.perItemTax : Int) - t.tax))]
  return envelope
    (.obj #[("Taxes", .arr rows), ("TotalTax", .num (totals.map (·.tax)).sum)])
    (.obj #[("ItemCount", .num items.length),
      ("PriceBasis", .str (if basis == .inclusive then "inclusive" else "exclusive")),
      ("Rounding", .str ((a.str? "Rounding").getD "floor")), ("PerItemRounding", .arr perItem)])
    [("消費税法", "第29条"), ("地方税法", "第72条の83"),
      ("消費税法施行令", if basis == .inclusive then "第70条の10第2号" else "第70条の10第1号")]
    ["税率ごとに価額を合計し、合計に一度だけ割合を掛けて一円未満の端数を処理する（消費税法施行令第70条の10）",
      "PerItemRounding は品目ごとに端数を処理して足した額との比較で、適格請求書には使わない"]
    .null

def consumptionTaxCommand : Command :=
  { name := "consumption-tax"
    help := "消費税（消費税法第29条、地方税法第72条の83）と適格請求書の税額"
    subcommands := [
      { name := "compute-invoice-tax"
        help := "適格請求書の税率ごとの消費税額等（消費税法施行令第70条の10）"
        params := [
          { name := "items"
            type := .structList [("Price", .nat), ("Rate", .enum ["standard", "reduced"])],
            required := true, help := "品目の価額（円）と税率の区分。Price=1000,Rate=standard の形で空白区切りに並べる" },
          { name := "price-basis", type := .enum ["exclusive", "inclusive"],
            help := "exclusive（税抜価額。既定）または inclusive（税込価額）" },
          { name := "rounding", type := .enum ["floor", "ceil", "half-up"],
            help := "一円未満の端数の処理。floor（切捨て。既定）、ceil（切上げ）、half-up（四捨五入）" }]
        outputSkeleton := envelopeSkeleton
          (.obj #[("Taxes", .arr #[.obj #[("Rate", .str ""), ("RatePercent", .num 0),
            ("PriceTotal", .num 0), ("Tax", .num 0)]]), ("TotalTax", .num 0)])
          (.obj #[("ItemCount", .num 0), ("PriceBasis", .str ""), ("Rounding", .str ""),
            ("PerItemRounding", .arr #[.obj #[("Rate", .str ""), ("PerItemTaxTotal", .num 0),
              ("Difference", .num 0)]])])
        run := computeInvoiceTax }] }

/-! ## delinquency-tax / interest-tax -/

def ratesSource : String :=
  "https://www.nta.go.jp/taxes/shiraberu/taxanswer/osirase/9205.htm"

/-- `--special-base-rates` で渡された年の割合を表の前に置いた、年ごとの特例基準割合の表。 -/
def ratesTable (a : Args) : Except CliError (List (Int × Nat)) := do
  let given ← (itemsArg a "SpecialBaseRates").toList.mapM fun j => do
    let some (.num y) := j.get? "Year" | throw (usageError "--special-base-rates の Year がない")
    let some (.str r) := j.get? "Rate" | throw (usageError "--special-base-rates の Rate がない")
    let some t := parseTenths r | throw (usageError s!"--special-base-rates の Rate {r} が正しくない")
    pure (y, t)
  return given ++ Delinquency.specialBaseRates

/-- 期間に含まれる年の割合がすべて表にあることを確かめ、年から割合を引く関数を返す。 -/
def ratesFor (table : List (Int × Nat)) (start : Int) (n : Nat) : Except CliError (Int → Nat) := do
  if n > 0 then
    let y0 := (Date.ofDays start).year
    let y1 := (Date.ofDays (start + n - 1)).year
    for i in List.range ((y1 - y0).toNat + 1) do
      let y := y0 + i
      if (Delinquency.specialBaseRate? table y).isNone then
        throw (domainError (s!"{y} 年の特例基準割合が表にない（収録は 2014〜2026 年）。" ++
          s!"--special-base-rates Year={y},Rate=<延滞税特例基準割合 %> で渡す"))
  return fun y => (Delinquency.specialBaseRate? table y).getD 0

def segmentsJson (r : Delinquency.Result) : Json :=
  .arr ((r.segments.zip r.amounts).toArray.map fun (s, amt) =>
    .obj #[("From", dateJson (Date.ofDays s.first)),
      ("To", dateJson (Date.ofDays (s.first + s.days - 1))),
      ("Days", .num s.days), ("Rate", .str (tenthsPercent s.rate)),
      ("Band", .str (if s.band then "after-two-months" else "within-two-months")),
      ("Amount", .num amt)])

def ratesDataJson (table : List (Int × Nat)) : Json :=
  .obj #[("SpecialBaseRates", .obj #[("Source", .str ratesSource),
    ("Years", .arr (table.toArray.map fun (y, r) =>
      .obj #[("Year", .num y), ("Rate", .str (tenthsPercent r))]))])]

def computeDelinquencyTax (a : Args) : Except CliError Json := do
  let some tax := a.nat? "Tax" | throw (usageError "--tax は必須")
  let legal ← dateArg a "LegalDueDate"
  let due ← match a.str? "DueDate" with
    | some _ => dateArg a "DueDate"
    | none => pure legal
  let paid ← dateArg a "PaymentDate"
  if due.toDays < legal.toDays then throw (usageError "--due-date は --legal-due-date 以後の日を渡す")
  let table ← ratesTable a
  let start := legal.toDays + 1
  let n := (paid.toDays - legal.toDays).toNat
  let rates ← ratesFor table start n
  let r := Delinquency.delinquencyTax rates tax legal due paid
  return envelope (.obj #[("DelinquencyTax", .num r.total)])
    (.obj #[("Tax", .num tax), ("Base", .num r.base), ("LegalDueDate", dateJson legal),
      ("DueDate", dateJson due), ("PaymentDate", dateJson paid), ("Days", .num r.days),
      ("TwoMonthsEnd", optDateJson (r.lowerEnd.map Date.ofDays)), ("Segments", segmentsJson r),
      ("TotalBeforeRounding", .num r.totalBeforeRounding)])
    [("国税通則法", "第60条第2項"), ("国税通則法", "第10条第1項第2号"), ("租税特別措置法", "第94条第1項"),
      ("租税特別措置法", "第96条第2項"), ("利率等の表示の年利建て移行に関する法律", "第25条"),
      ("国税通則法", "第118条第3項"), ("国税通則法", "第119条第4項")]
    ["計算期間は法定納期限の翌日から完納する日まで。納期限の翌日から2月を経過する日までは低い方の割合による",
      "割合が同じ日が続く区間ごとに一円未満を切り捨て、合計の百円未満を切り捨てる。合計が千円未満なら 0",
      "一部納付（国税通則法第62条）、計算期間の特例（第61条）、免除（第63条）は扱わない",
      "特例基準割合は国税庁が公表する各年の延滞税の割合から逆算した値（--special-base-rates で上書きできる）"]
    (ratesDataJson table)

def computeInterestTax (a : Args) : Except CliError Json := do
  let some tax := a.nat? "Tax" | throw (usageError "--tax は必須")
  let fromDate ← dateArg a "FromDate"
  let toDate ← dateArg a "ToDate"
  let table ← ratesTable a
  let start := fromDate.toDays + 1
  let n := (toDate.toDays - fromDate.toDays).toNat
  let rates ← ratesFor table start n
  let r := Delinquency.interestTax rates tax fromDate toDate
  return envelope (.obj #[("InterestTax", .num r.total)])
    (.obj #[("Tax", .num tax), ("Base", .num r.base), ("FromDate", dateJson fromDate),
      ("ToDate", dateJson toDate), ("Days", .num r.days), ("Segments", segmentsJson r),
      ("TotalBeforeRounding", .num r.totalBeforeRounding)])
    [("国税通則法", "第64条第1項"), ("租税特別措置法", "第93条第1項"), ("租税特別措置法", "第93条第2項"),
      ("租税特別措置法", "第96条第1項"), ("租税特別措置法", "第96条第2項"),
      ("利率等の表示の年利建て移行に関する法律", "第25条"), ("国税通則法", "第118条第3項"),
      ("国税通則法", "第119条第4項")]
    ["計算期間は FromDate の翌日から ToDate まで",
      "割合は利子税特例基準割合（2021 年以後は延滞税特例基準割合 − 0.5%、2020 年以前は特例基準割合）と年7.3%の低い方",
      "相続税の延納の利子税（相続税法第52条、租税特別措置法第93条第3項）の割合の調整は扱わない"]
    (ratesDataJson table)

def ratesParam : Param :=
  { name := "special-base-rates", type := .structList [("Year", .nat), ("Rate", .decimal)]
    help := "表にない年や上書きする年の延滞税特例基準割合（%）。Year=2027,Rate=1.8 の形で並べる" }

def segmentSkeleton : Json :=
  .arr #[.obj #[("From", .str ""), ("To", .str ""), ("Days", .num 0), ("Rate", .str ""),
    ("Band", .str ""), ("Amount", .num 0)]]

def ratesDataSkeleton : Json :=
  .obj #[("SpecialBaseRates", .obj #[("Source", .str ""),
    ("Years", .arr #[.obj #[("Year", .num 0), ("Rate", .str "")]])])]

def delinquencyTaxCommand : Command :=
  { name := "delinquency-tax"
    help := "延滞税（国税通則法第60条第2項、租税特別措置法第94条）"
    subcommands := [
      { name := "compute-tax"
        help := "未納の税額と納付の日から延滞税の額を出す"
        params := [
          { name := "tax", type := .nat, required := true, help := "未納の本税の額（円）" },
          { name := "legal-due-date", type := .date, required := true, help := "法定納期限" },
          { name := "due-date", type := .date,
            help := "納期限（期限後申告・修正申告は申告書を提出した日など。既定は法定納期限）" },
          { name := "payment-date", type := .date, required := true, help := "完納する日" },
          ratesParam]
        outputSkeleton := envelope (.obj #[("DelinquencyTax", .num 0)])
          (.obj #[("Tax", .num 0), ("Base", .num 0), ("LegalDueDate", .str ""),
            ("DueDate", .str ""),
            ("PaymentDate", .str ""), ("Days", .num 0), ("TwoMonthsEnd", .str ""),
            ("Segments", segmentSkeleton), ("TotalBeforeRounding", .num 0)])
          [("", "")] [""] ratesDataSkeleton
        run := computeDelinquencyTax }] }

def interestTaxCommand : Command :=
  { name := "interest-tax"
    help := "利子税（国税通則法第64条、租税特別措置法第93条）"
    subcommands := [
      { name := "compute-tax"
        help := "延納・申告期限の延長の期間に対する利子税の額を出す"
        params := [
          { name := "tax", type := .nat, required := true, help := "利子税の計算の基礎となる税額（円）" },
          { name := "from-date", type := .date, required := true, help := "計算期間の初日の前日（法定納期限など）" },
          { name := "to-date", type := .date, required := true, help := "計算期間の末日（納付の日など）" },
          ratesParam]
        outputSkeleton := envelope (.obj #[("InterestTax", .num 0)])
          (.obj #[("Tax", .num 0), ("Base", .num 0), ("FromDate", .str ""), ("ToDate", .str ""),
            ("Days", .num 0), ("Segments", segmentSkeleton), ("TotalBeforeRounding", .num 0)])
          [("", "")] [""] ratesDataSkeleton
        run := computeInterestTax }] }

/-! ## penalty-tax -/

def computePenaltyTax (a : Args) : Except CliError Json := do
  let some tax := a.nat? "Tax" | throw (usageError "--tax は必須")
  let kind : Penalty.Kind := match a.str? "Kind" with
    | some "no-return" => .noReturn
    | some "non-withholding" => .nonWithholding
    | _ => .underpayment
  let timing : Penalty.Timing := match a.str? "Timing" with
    | some "before-notice" => .beforeNotice
    | some "after-notice" => .afterNotice
    | _ => .afterPrediction
  let input : Penalty.Input :=
    { kind, timing, tax, priorTax := natArg a "PriorTax", timelyTax := natArg a "TimelyTax"
      fraud := a.flag "Fraud" false, repeated := a.flag "Repeated" false }
  let r ← match Penalty.compute input with
    | .ok r => pure r
    | .error e => throw (usageError e)
  return envelope (.obj #[("PenaltyTax", .num r.total)])
    (.obj #[("Tax", .num tax), ("Base", .num r.base), ("Excess", .num r.excess),
      ("Provisions", .arr (r.provisions.toArray.map .str)),
      ("TotalBeforeRounding", .num r.totalBeforeRounding)])
    (r.provisions.map splitProvision ++ [("国税通則法", "第118条第3項"), ("国税通則法", "第119条第4項")])
    ["更正・決定・告知を予知していたか、調査通知の前か後かは Timing で受け取った事実による",
      "計算の基礎となる税額と、第65条第2項で百分の五を加える部分は、それぞれ一万円未満を切り捨てる",
      "帳簿の提示がない場合などの加重（第65条第4項、第66条第5項）と、正当な理由がある事実の控除は扱わない"]
    .null

def penaltyTaxCommand : Command :=
  { name := "penalty-tax"
    help := "加算税（国税通則法第65条〜第68条）"
    subcommands := [
      { name := "compute-tax"
        help := "過少申告加算税・無申告加算税・不納付加算税・重加算税の額"
        params := [
          { name := "kind", type := .enum ["underpayment", "no-return", "non-withholding"]
            required := true,
            help := "underpayment（過少申告加算税）、no-return（無申告加算税）、non-withholding（不納付加算税）" },
          { name := "timing", type := .enum ["before-notice", "after-notice", "after-prediction"],
            help := "before-notice（調査通知の前の自主的な申告・納付）、after-notice（調査通知の後、予知の前）、" ++
              "after-prediction（更正・決定・告知を予知した後、または更正・決定・告知。既定）" },
          { name := "tax", type := .nat, required := true, help := "今回の申告・更正・決定・納付で納付すべき税額（円）" },
          { name := "prior-tax", type := .nat, help := "それより前の修正申告・更正などで納付すべきだった税額の合計（円）" },
          { name := "timely-tax", type := .nat, help := "期限内申告税額（円。過少申告加算税で使う）" },
          { name := "fraud", type := .flag, help := "隠蔽・仮装があり、重加算税を課す（第68条）" },
          { name := "repeated", type := .flag,
            help := "過去5年以内に無申告加算税・重加算税を課されたなど、第66条第6項・第68条第4項の加重に当たる" }]
        outputSkeleton := envelopeSkeleton (.obj #[("PenaltyTax", .num 0)])
          (.obj #[("Tax", .num 0), ("Base", .num 0), ("Excess", .num 0),
            ("Provisions", .arr #[.str ""]),
            ("TotalBeforeRounding", .num 0)])
        run := computePenaltyTax }] }

def taxCommands : List Command :=
  [incomeTaxCommand, inheritanceTaxCommand, consumptionTaxCommand, delinquencyTaxCommand,
    interestTaxCommand, penaltyTaxCommand]

end Ritsuryo.Cli
