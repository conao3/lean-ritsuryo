module

public import Ritsuryo.Period.Spec.Civil142
public import Ritsuryo.Period.Spec.CivilProcedure95
public import Ritsuryo.Period.Spec.TaxGeneral10
meta import Ritsuryo.Basis

/-!
# 末日が休日に当たるときの繰り下げ（民法 第142条、民事訴訟法 第95条第3項、国税通則法 第10条第2項）

三つの規定はどれも、期間の末日（期限）が休日に当たるときは「その翌日」に満了する（期限とみなす）と定める。
翌日も休日のときについて条文は書いていないので、休日でない最初の日まで繰り下げる
（民事訴訟法第95条第3項では、末日が12月29日なら1月4日になる）。CLI はこの読み方を `Assumptions` に出す。

- `rolloverDays`・`rollover`: CLI が実行する繰り下げ。日付を通算日に移し、休日である間 1 を足す。
- `RolloverRule`: どの規定で繰り下げるかの選択。`isHoliday` が各規定の仕様（`isHolidaySpec`）を返す。

ROL-1（`rol1_least_non_holiday`）が、結果がもとの日以後で休日でない最初の日であることを示す。
-/

@[expose] public section

namespace Ritsuryo.Period

open Date

/-- 通算日 `z` から始めて、`isHoliday` が `true` である間 1 日ずつ進め、休日でない最初の通算日を返す。
`fuel` 日調べても休日でない日がなければ `none` を返す（CLI は 366 日で打ち切る）。 -/
@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def rolloverDays (isHoliday : Int → Bool) : Nat → Int → Option Int
  | 0, _ => none
  | fuel + 1, z => if isHoliday z then rolloverDays isHoliday fuel (z + 1) else some z

/-- 日 `d` が休日なら、休日でない最初の日まで繰り下げた日を返す。`d` が休日でなければ `d` を返す。
`fuel` 日調べても休日でない日がなければ `none` になる。計算は `rolloverDays` で通算日の上で行い、結果を日付に戻す。 -/
@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def rollover (isHoliday : Date → Bool) (fuel : Nat) (d : Date) : Option Date :=
  (rolloverDays (fun z => isHoliday (ofDays z)) fuel d.toDays).map ofDays

/-- 繰り下げの規定。
`civil142` は民法第142条で、休日とする種類と取引をしない慣習の有無を持つ。`civilProcedure95` は民事訴訟法第95条第3項。
`nationalTax10` は国税通則法第10条第2項で、1月2日・1月3日を一般の休日に含めるかを持つ。 -/
inductive RolloverRule where
  | civil142 (classes : List HolidayClass) (noTradeCustom : Bool)
  | civilProcedure95
  | nationalTax10 (newYearIsGeneralHoliday : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace RolloverRule

/-- 規定ごとの休日の判定。各規定の仕様の `isHolidaySpec` をそのまま返す。`national` は祝日法の休日の判定。 -/
@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def isHoliday (national : Date → Bool) : RolloverRule → Date → Bool
  | .civil142 classes custom => Civil.isHolidaySpec national classes custom
  | .civilProcedure95 => CivilProcedure.isHolidaySpec national
  | .nationalTax10 general => TaxGeneral.isHolidaySpec national general

/-- 規定が休日とする種類の一覧。CLI が、繰り下げで飛ばした日がどの種類に当たるかの表示と、
祝日データ（内閣府の CSV）が要るかの判定に使う。民法第142条で慣習がないときは空になる。 -/
@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def classesOf : RolloverRule → List HolidayClass
  | .civil142 classes custom => if custom then classes else []
  | .civilProcedure95 => HolidayClass.all
  | .nationalTax10 general =>
    if general then HolidayClass.all else [.sunday, .saturday, .nationalHoliday, .yearEnd]

end RolloverRule

end Ritsuryo.Period
