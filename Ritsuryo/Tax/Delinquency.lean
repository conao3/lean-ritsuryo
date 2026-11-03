module

public import Ritsuryo.Tax.Rounding
public import Ritsuryo.Period.Impl
meta import Ritsuryo.Basis

/-!
# 延滞税と利子税（国税通則法 第60条第2項、租税特別措置法 第93条・第94条・第96条）

延滞税は、法定納期限の翌日から完納する日までの日数に応じて、未納の税額に年当たりの割合を掛けた額になる
（国税通則法第60条第2項）。割合は、納期限の翌日から2月を経過する日までが年7.3%、その後が年14.6%で、
各年の延滞税特例基準割合が7.3%に満たない年は、その年中の割合を租税特別措置法第94条第1項で置き換える。

このファイルの計算は次のとおり。

1. 計算の基礎となる税額の一万円未満を切り捨てる（国税通則法第118条第3項）。
2. 「納期限の翌日から二月を経過する日」を民法・国税通則法の期間計算で出す（`Period.compute`。初日不算入）。
3. 日ごとに割合を決める（その日の年の特例基準割合と、2月を経過する日の前後）。
4. 割合が同じ日が続く区間に分け、区間ごとに `税額 × 割合 × 日数 ÷ 365` を出して一円未満を切り捨てる
   （租税特別措置法第96条第2項。年当たりの割合は閏年も365日当たり: 利率等の表示の年利建て移行に関する法律第25条）。
5. 区間の額を合計し、百円未満を切り捨て、全額が千円未満なら 0 にする（国税通則法第119条第4項）。

割合は千分の一（0.1%）単位の自然数で持つ。年7.3%は 73、年14.6%は 146。

仕様は「日ごとの `税額 × 割合` の合計」（`rawSpec`）で、区間に分けた計算の端数処理前の額がこれと一致することを
DEL-2 で示す。

e-Gov 法令履歴 `337AC0000000066_20261101_507AC0000000013`（国税通則法）、
`332AC0000000026_20261101_507AC0000000013`（租税特別措置法）、`345AC0000000013_19700401_000000000000000`
（利率等の表示の年利建て移行に関する法律）。

> 国税通則法 第六十条第二項　延滞税の額は、前項各号に規定する国税の法定納期限…の翌日からその国税を完納する日までの期間の日数に応じ、その未納の税額に年十四・六パーセントの割合を乗じて計算した額とする。ただし、納期限…までの期間又は納期限の翌日から二月を経過する日までの期間については、その未納の税額に年七・三パーセントの割合を乗じて計算した額とする。
>
> 租税特別措置法 第九十四条　国税通則法第六十条第二項…に規定する延滞税の年十四・六パーセントの割合及び年七・三パーセントの割合は、これらの規定にかかわらず、各年の延滞税特例基準割合（平均貸付割合に年一パーセントの割合を加算した割合をいう。…）が年七・三パーセントの割合に満たない場合には、その年中においては、年十四・六パーセントの割合にあつては当該延滞税特例基準割合に年七・三パーセントの割合を加算した割合とし、年七・三パーセントの割合にあつては当該延滞税特例基準割合に年一パーセントの割合を加算した割合（当該加算した割合が年七・三パーセントの割合を超える場合には、年七・三パーセントの割合）とする。
>
> 租税特別措置法 第九十三条　次の各号に掲げる規定に規定する利子税の年七・三パーセントの割合は、当該各号に掲げる規定にかかわらず、各年の利子税特例基準割合が年七・三パーセントの割合に満たない場合には、その年中においては、当該利子税特例基準割合とする。
> ２　前項に規定する利子税特例基準割合とは、平均貸付割合…に年〇・五パーセントの割合を加算した割合をいう。
>
> 租税特別措置法 第九十六条第二項　前三条のいずれかの規定の適用がある場合における利子税等の額の計算において、その計算の過程における金額に一円未満の端数が生じたときは、これを切り捨てる。
>
> 利率等の表示の年利建て移行に関する法律 第二十五条　…延滞税、利子税…の額の計算につきこれらの法律の規定その他法令の規定に定める年当たりの割合は、閏年の日を含む期間についても、三百六十五日当たりの割合とする。
-/

@[expose] public section

namespace Ritsuryo.Tax.Delinquency

open Ritsuryo.Date

/-- 各年の延滞税特例基準割合（2021 年以後）と特例基準割合（2014〜2020 年）を千分の一単位で。
国税庁「延滞税について」（タックスアンサー No.9205、令和8年4月1日現在）の各年の割合から、
2月以内の割合 − 1% として逆算した値。2014〜2020 年の特例基準割合は、令和2年改正前の租税特別措置法第94条で
同じく平均貸付割合 + 1% だった。 -/
@[ritsuryo_basis "租税特別措置法" "第94条第1項"]
def specialBaseRates : List (Int × Nat) := [
  (2014, 19), (2015, 18), (2016, 18), (2017, 17), (2018, 16), (2019, 16), (2020, 16),
  (2021, 15), (2022, 14), (2023, 14), (2024, 14), (2025, 14), (2026, 18)]

/-- 表から年の特例基準割合を引く。 -/
@[ritsuryo_basis "租税特別措置法" "第94条第1項"]
def specialBaseRate? (table : List (Int × Nat)) (year : Int) : Option Nat :=
  (table.find? (·.1 == year)).map (·.2)

/-- 2月を経過する日までの割合。本則は年7.3%で、特例基準割合が7.3%未満の年は `特例基準割合 + 1%`
（7.3%を超えるときは7.3%）。 -/
@[ritsuryo_basis "国税通則法" "第60条第2項", ritsuryo_basis "租税特別措置法" "第94条第1項"]
def lowerRate (s : Nat) : Nat :=
  if s < 73 then min (s + 10) 73 else 73

/-- 2月を経過した日以後の割合。本則は年14.6%で、特例基準割合が7.3%未満の年は `特例基準割合 + 7.3%`。 -/
@[ritsuryo_basis "国税通則法" "第60条第2項", ritsuryo_basis "租税特別措置法" "第94条第1項"]
def higherRate (s : Nat) : Nat :=
  if s < 73 then s + 73 else 146

/-- 利子税の割合。本則は年7.3%で、利子税特例基準割合（平均貸付割合 + 0.5%）が7.3%未満の年はその割合
（租税特別措置法第93条第1項・第2項）。平均貸付割合は延滞税特例基準割合 − 1% なので、2021 年以後は
`特例基準割合 − 0.5%`。2020 年以前は令和2年改正前の第93条により特例基準割合そのもの。
割合が0.1%未満になるときは0.1%（第96条第1項）。 -/
@[ritsuryo_basis "租税特別措置法" "第93条第1項", ritsuryo_basis "租税特別措置法" "第93条第2項",
  ritsuryo_basis "租税特別措置法" "第96条第1項"]
def interestRate (year : Int) (s : Nat) : Nat :=
  let t := if 2021 ≤ year then s - 5 else s
  if t < 73 then max t 1 else 73

/-- 仕様: 期間の初日の通算日 `start` から `n` 日間、日ごとの `税額 × その日の割合` を足した額。
単位は 365,000 分の一円（割合が千分の一単位で、年当たりの割合を365日で割るため）。 -/
@[ritsuryo_basis "国税通則法" "第60条第2項", ritsuryo_basis "利率等の表示の年利建て移行に関する法律" "第25条"]
def rawSpec (base : Nat) (rateAt : Int → Nat) (start : Int) (n : Nat) : Nat :=
  ((List.range n).map fun (i : Nat) => base * rateAt (start + i)).sum

/-- 割合が同じ日が続く区間。`band` は 2月を経過する日以前（`false`）か後（`true`）か。 -/
structure Segment where
  first : Int
  days : Nat
  band : Bool
  rate : Nat
  deriving Repr, DecidableEq

/-- 区間の並び（新しい区間が先頭）に 1 日を足す。前の区間と割合も区分も同じなら延ばし、違えば新しい区間を始める。 -/
@[ritsuryo_basis "租税特別措置法" "第96条第2項"]
def addDay (segs : List Segment) (z : Int) (band : Bool) (rate : Nat) : List Segment :=
  match segs with
  | s :: rest =>
    if s.band == band && s.rate == rate then { s with days := s.days + 1 } :: rest
    else ⟨z, 1, band, rate⟩ :: s :: rest
  | [] => [⟨z, 1, band, rate⟩]

/-- `start` から `n` 日間を区間に分ける（古い区間が先頭）。 -/
@[ritsuryo_basis "租税特別措置法" "第96条第2項"]
def segments (bandAt : Int → Bool) (rateAt : Int → Nat) (start : Int) (n : Nat) : List Segment :=
  ((List.range n).foldl (fun acc (i : Nat) => addDay acc (start + i) (bandAt (start + i))
    (rateAt (start + i))) []).reverse

/-- 区間ごとの額（一円未満切捨て）。 -/
@[ritsuryo_basis "租税特別措置法" "第96条第2項",
  ritsuryo_basis "利率等の表示の年利建て移行に関する法律" "第25条"]
def segmentAmount (base : Nat) (s : Segment) : Nat :=
  base * s.rate * s.days / 365000

/-- 計算の途中の値と結果。 -/
structure Result where
  base : Nat
  start : Int
  days : Nat
  lowerEnd : Option Int
  segments : List Segment
  amounts : List Nat
  totalBeforeRounding : Nat
  total : Nat
  deriving Repr

/-- 区間に分けて額を出し、合計を附帯税の端数処理（千円未満は 0、百円未満切捨て）にかける。 -/
@[ritsuryo_basis "国税通則法" "第118条第3項", ritsuryo_basis "国税通則法" "第119条第4項",
  ritsuryo_basis "租税特別措置法" "第96条第2項"]
def computeWith (tax : Nat) (bandAt : Int → Bool) (rateAt : Int → Nat) (start : Int) (n : Nat)
    (lowerEnd : Option Int) : Result :=
  let base := incidentalBase tax
  let segs := segments bandAt rateAt start n
  let amounts := segs.map (segmentAmount base)
  { base, start, days := n, lowerEnd, segments := segs, amounts
    totalBeforeRounding := amounts.sum
    total := interestFinal amounts.sum }

/-- 納期限の翌日から2月を経過する日（の通算日）。納期限の翌日を初日とする2月の期間の末日。 -/
@[ritsuryo_basis "国税通則法" "第60条第2項", ritsuryo_basis "国税通則法" "第10条第1項第2号"]
def twoMonthsAfter (dueDate : Date) : Int :=
  (Period.compute dueDate false (.months 2)).expiry.toDays

/-- 延滞税。`rates` は年ごとの特例基準割合。法定納期限の翌日から完納する日までを計算期間にする。 -/
@[ritsuryo_basis "国税通則法" "第60条第2項", ritsuryo_basis "租税特別措置法" "第94条第1項"]
def delinquencyTax (rates : Int → Nat) (tax : Nat) (legalDueDate dueDate paymentDate : Date) :
    Result :=
  let lowerEnd := twoMonthsAfter dueDate
  let start := legalDueDate.toDays + 1
  let n := (paymentDate.toDays - legalDueDate.toDays).toNat
  computeWith tax (fun z => decide (lowerEnd < z))
    (fun z => let s := rates (ofDays z).year
      if z ≤ lowerEnd then lowerRate s else higherRate s)
    start n (some lowerEnd)

/-- 利子税。`fromDate` の翌日から `toDate` までを計算期間にする（延納・申告期限の延長の期間は、
国税に関する個別の法律が定める起算日を `fromDate` に渡す）。 -/
@[ritsuryo_basis "租税特別措置法" "第93条第1項"]
def interestTax (rates : Int → Nat) (tax : Nat) (fromDate toDate : Date) : Result :=
  let start := fromDate.toDays + 1
  let n := (toDate.toDays - fromDate.toDays).toNat
  computeWith tax (fun _ => false) (fun z => let y := (ofDays z).year
    interestRate y (rates y)) start n none

end Ritsuryo.Tax.Delinquency
