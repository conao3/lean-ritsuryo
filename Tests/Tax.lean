module

public import Ritsuryo
public import Tests.Harness
public import Tests.Calendar

/-!
# 税計算のテスト

国税庁の公表している計算例（タックスアンサー）と、手で計算した値に照らす。
-/

public section

namespace Ritsuryo.Tests.Tax

open Ritsuryo Ritsuryo.Tax Ritsuryo.Tests.Calendar

/-- 国税庁 タックスアンサー No.2260「所得税の税率」の具体例と、速算表の区分の境目。 -/
def income : TestM Unit := do
  checkEq "No.2260: 課税される所得金額 7,000,000 円の所得税は 974,000 円" (Income.taxOn 7000000) 974000
  checkEq "復興特別所得税は 974,000 × 2.1% = 20,454 円" (Income.compute 2026 7000000 0 0).reconstructionTax
    20454
  checkEq "令和9年分は復興特別所得税 1.1%" (Income.compute 2027 7000000 0 0).reconstructionTax 10714
  checkEq "令和9年分は防衛特別所得税 1%" (Income.compute 2027 7000000 0 0).defenseTax 9740
  checkEq "合計の税率は改正の前後で変わらない" (Income.compute 2027 7000000 0 0).total
    (Income.compute 2026 7000000 0 0).total
  checkEq "1,950,000 円は 5% の区分" (Income.taxOn 1950000) 97500
  checkEq "1,950,999 円は千円未満を切り捨てて 1,950,000 円" (Income.taxOn 1950999) 97500
  checkEq "1,951,000 円は 10% の区分" (Income.taxOn 1951000) 97600
  checkEq "40,000,000 円" (Income.taxOn 40000000) 13204000
  checkEq "50,000,000 円は 45% の区分" (Income.taxOn 50000000) 17704000
  checkEq "999 円は千円未満を切り捨てて 0 円" (Income.taxOn 999) 0
  checkEq "課税山林所得金額 10,000,000 円の 5 分 5 乗は 5 × (2,000,000 円の税額)"
    (Income.timberTaxOn 10000000) (5 * Income.taxOn 2000000)
  checkEq "確定金額は百円未満を切り捨てる" (Income.compute 2026 7000000 0 0).payable 994400

/-- 国税庁 タックスアンサー No.4155「相続税の税率」の例（妻と子 2 人、課税遺産総額 1 億 5,200 万円）。 -/
def inheritance : TestM Unit := do
  let heirs : Inheritance.Heirs :=
    { spouse := true, biologicalChildren := 2, adoptedChildren := 0, ascendants := 0
      fullSiblings := 0, halfSiblings := 0 }
  let r := Inheritance.compute 200000000 heirs
  checkEq "基礎控除額は 3,000 万円 + 600 万円 × 3 人" r.basicDeduction 48000000
  checkEq "課税遺産総額は 1 億 5,200 万円" r.taxableEstate 152000000
  checkEq "No.4155: 相続税の総額は 2,700 万円" r.total 27000000
  checkEq "妻の取得金額 7,600 万円の税額は 1,580 万円" (Inheritance.taxOn 76000000) 15800000
  checkEq "子の取得金額 3,800 万円の税額は 560 万円" (Inheritance.taxOn 38000000) 5600000
  let adopted : Inheritance.Heirs := { heirs with biologicalChildren := 1, adoptedChildren := 3 }
  checkEq "実子があれば養子は 1 人まで数える（相続税法第15条第2項第1号）" (Inheritance.heirCount adopted) 3
  let onlyAdopted : Inheritance.Heirs :=
    { heirs with biologicalChildren := 0, adoptedChildren := 3 }
  checkEq "実子がなければ養子は 2 人まで数える（同項第2号）" (Inheritance.heirCount onlyAdopted) 3
  let none : Inheritance.Heirs := { heirs with spouse := false, biologicalChildren := 0 }
  checkEq "相続人がいないときは課税遺産総額をそのまま表に当てる"
    (Inheritance.compute 100000000 none).total (Inheritance.taxOn 70000000)
  let siblings : Inheritance.Heirs :=
    { spouse := true, biologicalChildren := 0, adoptedChildren := 0, ascendants := 0
      fullSiblings := 1, halfSiblings := 2 }
  let sh := Inheritance.statutoryShares true (Inheritance.rankOf siblings)
  checkEq "配偶者と兄弟姉妹: 分母" sh.denominator 16
  checkEq "配偶者 3/4、全血 1/8、半血 1/16 ずつ" (sh.shares.map (·.2)) [12, 2, 1, 1]

/-- 適格請求書の税額。 -/
def consumption : TestM Unit := do
  let items : List Consumption.Item := [⟨1001, .standard⟩, ⟨1001, .standard⟩, ⟨540, .reduced⟩]
  let t := Consumption.invoiceTax .floor .exclusive items
  checkEq "税抜 2,002 円の 10% は 200 円（切捨て）" ((t.map (·.tax))) [200, 43]
  let three : List Consumption.Item := [⟨105, .standard⟩, ⟨105, .standard⟩, ⟨105, .standard⟩]
  let u := Consumption.invoiceTax .floor .exclusive three
  checkEq "品目ごとに切り捨てると 30 円、合計に掛けると 31 円" (u.map fun r => (r.perItemTax, r.tax))
    [(30, 31)]
  let v := Consumption.invoiceTax .halfUp .inclusive [⟨1100, .standard⟩, ⟨1080, .reduced⟩]
  checkEq "税込 1,100 円の 10/110 は 100 円、税込 1,080 円の 8/108 は 80 円" (v.map (·.tax)) [100, 80]
  checkEq "税込 1,234 円の 10/110 = 112.18… は四捨五入で 112 円"
    (Consumption.taxOf .halfUp .inclusive .standard 1234) 112
  checkEq "切上げなら 113 円" (Consumption.taxOf .ceil .inclusive .standard 1234) 113

/-- 国税庁が公表する延滞税の割合（タックスアンサー No.9205）と、特例基準割合の表から出した割合の照合。 -/
def delinquencyRates : TestM Unit := do
  let published : List (Int × Nat × Nat) := [
    (2014, 29, 92), (2015, 28, 91), (2016, 28, 91), (2017, 27, 90), (2018, 26, 89), (2019, 26, 89),
    (2020, 26, 89), (2021, 25, 88), (2022, 24, 87), (2023, 24, 87), (2024, 24, 87), (2025, 24, 87),
    (2026, 28, 91)]
  for (y, lo, hi) in published do
    let s := (Delinquency.specialBaseRate? Delinquency.specialBaseRates y).getD 0
    checkEq s!"{y} 年の 2 月以内の割合" (Delinquency.lowerRate s) lo
    checkEq s!"{y} 年の 2 月経過後の割合" (Delinquency.higherRate s) hi
  checkEq "2022 年の利子税の割合は 0.9%" (Delinquency.interestRate 2022 14) 9
  checkEq "2026 年の利子税の割合は 1.3%" (Delinquency.interestRate 2026 18) 13
  checkEq "2020 年の利子税の割合は特例基準割合の 1.6%" (Delinquency.interestRate 2020 16) 16

def rates (y : Int) : Nat :=
  (Delinquency.specialBaseRate? Delinquency.specialBaseRates y).getD 0

/-- 延滞税の例。100 万円、法定納期限 2026-03-16 に納めず 2026-07-31 に完納。 -/
def delinquency : TestM Unit := do
  checkEq "納期限 3/16 の翌日から 2 月を経過する日は 5/16" (Date.ofDays (Delinquency.twoMonthsAfter (d 2026 3 16)))
    (d 2026 5 16)
  checkEq "納期限 2025-03-17 の翌日から 2 月を経過する日は 2025-05-17"
    (Date.ofDays (Delinquency.twoMonthsAfter (d 2025 3 17))) (d 2025 5 17)
  let r := Delinquency.delinquencyTax rates 1000000 (d 2026 3 16) (d 2026 3 16) (d 2026 7 31)
  checkEq "区間の額: 61 日 × 2.8% と 76 日 × 9.1%（一円未満切捨て）" r.amounts [4679, 18947]
  checkEq "合計 23,626 円の百円未満を切り捨てて 23,600 円" r.total 23600
  let small := Delinquency.delinquencyTax rates 19999 (d 2026 3 16) (d 2026 3 16) (d 2026 4 30)
  checkEq "税額 19,999 円は一万円未満を切り捨てて 10,000 円を基礎にする" small.base 10000
  checkEq "合計が千円未満なら延滞税は 0" small.total 0
  let span := Delinquency.delinquencyTax rates 1000000 (d 2025 3 17) (d 2025 3 17) (d 2026 2 10)
  checkEq "年をまたぐと割合の変わる日で区間を分ける" (span.segments.map (·.days)) [61, 228, 41]
  let it := Delinquency.interestTax rates 3000000 (d 2026 3 16) (d 2026 5 31)
  checkEq "利子税: 300 万円 × 1.3% × 76 日 ÷ 365 = 8,120 円 → 8,100 円" it.total 8100

def penalty : TestM Unit := do
  let total (i : Penalty.Input) : Nat := match Penalty.compute i with
    | .ok r => r.total
    | .error _ => 999999999
  checkEq "過少申告加算税: 120 万円 × 10% + (120 万円 − 100 万円) × 5%"
    (total { kind := .underpayment, timing := .afterPrediction, tax := 1200000
             timelyTax := 1000000 })
    130000
  checkEq "過少申告加算税: 調査通知の後、予知の前は 5%"
    (total { kind := .underpayment, timing := .afterNotice, tax := 400000 }) 20000
  checkEq "過少申告加算税: 調査通知の前の自主的な修正申告は 0"
    (total { kind := .underpayment, timing := .beforeNotice, tax := 400000 }) 0
  checkEq "無申告加算税: 400 万円は 15%・20%・30% の区分"
    (total { kind := .noReturn, timing := .afterPrediction, tax := 4000000 }) 875000
  checkEq "無申告加算税: 調査通知の前の期限後申告は 5%"
    (total { kind := .noReturn, timing := .beforeNotice, tax := 4000000 }) 200000
  checkEq "無申告加算税: 累積納付税額 250 万円に 100 万円を加えると 725,000 − 475,000 円"
    (total { kind := .noReturn, timing := .afterPrediction, tax := 1000000, priorTax := 2500000 })
    250000
  checkEq "不納付加算税: 10%"
    (total { kind := .nonWithholding, timing := .afterPrediction, tax := 100000 }) 10000
  checkEq "重加算税（過少申告）: 35%"
    (total { kind := .underpayment, timing := .afterPrediction, tax := 1000000, fraud := true })
    350000
  checkEq "重加算税（無申告）に加重: 40% + 10%"
    (total { kind := .noReturn, timing := .afterPrediction, tax := 1000000, fraud := true
             repeated := true })
    500000
  checkEq "加算税が 5,000 円未満なら 0"
    (total { kind := .underpayment, timing := .afterPrediction, tax := 49999 }) 0

def presets : TestM Unit := do
  let (e, r) := Period.courtDeadline Holiday.isHoliday Period.appealPeriod (d 2026 12 15)
  checkEq "控訴期間: 2026-12-15 送達で末日 2026-12-29" e.expiry (d 2026 12 29)
  checkEq "控訴期間: 年末年始を越えて 2027-01-04 に繰り下げ" r (some (d 2027 1 4))
  let (_, r) := Period.courtDeadline Holiday.isHoliday Period.immediateAppealPeriod (d 2026 4 25)
  checkEq "即時抗告期間: 2026-04-25 告知で 2026-05-02（土）から 2026-05-07 に繰り下げ" r
    (some (d 2026 5 7))
  checkEq "所得税の確定申告期限: 令和7年分は 2026-03-15（日）から 2026-03-16"
    (Period.incomeTaxReturnDeadline Holiday.isHoliday true 2025) (some (d 2026 3 16))
  checkEq "所得税の確定申告期限: 令和8年分は 2027-03-15（月）"
    (Period.incomeTaxReturnDeadline Holiday.isHoliday true 2026) (some (d 2027 3 15))

def suites : List (String × TestM Unit) :=
  [("所得税 examples", income), ("相続税 examples", inheritance), ("消費税 examples", consumption),
    ("延滞税の割合", delinquencyRates), ("延滞税 examples", delinquency), ("加算税 examples", penalty),
    ("期間のプリセット", presets)]

end Ritsuryo.Tests.Tax
