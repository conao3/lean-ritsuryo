module

public import Ritsuryo.Holiday.Spec
public import Ritsuryo.Holiday.Data.Generated
meta import Ritsuryo.Basis

/-!
# 祝日法 第3条の改正の経過

第3条第2項（振替休日）は昭和四十八年法律第十号により昭和四十八年四月十二日から、第3条第3項（国民の休日）は
昭和六十年法律第百三号により昭和六十年十二月二十七日から施行された。いずれも平成十七年法律第四十三号により
平成十九年一月一日から現行の文言になった。改正前の規定は次の内容による。

- 昭和四十八年四月十二日から平成十八年十二月三十一日まで: 「国民の祝日」が日曜日にあたるときは、その翌日を休日とする。
- 昭和六十年十二月二十七日から平成十八年十二月三十一日まで: その前日及び翌日が「国民の祝日」である日（日曜日にあたる日及び前項に規定する休日にあたる日を除く。）は、休日とする。

## このファイルの構成

- 表の参照: `entriesOf` が `y` 年の CSV の行を返し、`entry?`・`isHoliday` が日付の行を引く。CSV の範囲外の年は
  行がない扱いになるので、範囲は `inRange` で別に確かめる。
- 国民の祝日と休日の分け方: `nationalDays` は名称が「休日」でない行（第3条の「国民の祝日」）、`restDays` は
  名称が「休日」の行（第3条第2項・第3項の休日）を日番号で返す。
- 日ごとの判定: `isSubstituteAt`・`isCitizensAt` は、判定する日に施行されていた版の第3条第2項・第3項を
  当てはめる。平成十九年一月一日以後は `Spec.lean` の現行の関数（HOL-1 で条文と一致を証明済み）を使う。
- HOL-C1 の検査: `checkYear` が、`nationalDays` から導いた休日と CSV の「休日」の行が一致するかを年ごとに
  確かめる。全年についての評価と証明は `Ritsuryo/Holiday/Check.lean` に置く。
-/

@[expose] public section

namespace Ritsuryo.Holiday

open Date

/-- `y` 年の CSV の行。CSV の範囲（`Data.firstYear` から `Data.lastYear` まで）の外では空になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def entriesOf (y : Int) : List Entry :=
  if Data.firstYear ≤ y ∧ y ≤ Data.lastYear then
    Data.byYear.getD (y - Data.firstYear).toNat []
  else []

/-- 日付の年が CSV の範囲にあるかどうか。範囲外の日に祝日の集合が要るとき、CLI は終了コード 254 で止まる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def inRange (d : Date) : Bool :=
  Data.firstYear ≤ d.year && d.year ≤ Data.lastYear

/-- 日付に当たる CSV の行。なければ `none`。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条", ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def entry? (d : Date) : Option Entry :=
  (entriesOf d.year).find? fun e => e.month == d.month && e.day == d.day

/-- 祝日法に規定する休日かどうか。CSV に行があれば、種類を問わず休日になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def isHoliday (d : Date) : Bool :=
  (entry? d).isSome

/-- `y` 年の、第3条を当てはめるときの「国民の祝日」の日番号。名称が「休日」の行を除いたすべての行になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def nationalDays (y : Int) : List Int :=
  ((entriesOf y).filter (·.kind != .rest)).map fun e => toDays ⟨y, e.month, e.day⟩

/-- `y` 年の CSV の「休日」の行（第3条第2項・第3項による休日）の日番号。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def restDays (y : Int) : List Int :=
  ((entriesOf y).filter (·.kind == .rest)).map fun e => toDays ⟨y, e.month, e.day⟩

/-- 第3条第2項（振替休日）の施行日、昭和四十八年四月十二日の日番号。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def substituteEffective : Int := toDays ⟨1973, 4, 12⟩

/-- 第3条第3項（国民の休日）の施行日、昭和六十年十二月二十七日の日番号。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def citizensEffective : Int := toDays ⟨1985, 12, 27⟩

/-- 現行の第3条第2項・第3項の施行日、平成十九年一月一日の日番号。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def currentEffective : Int := toDays ⟨2007, 1, 1⟩

/-- `z` の日に施行されていた第3条第2項による振替休日かどうか。現行の版は `isSubstitute`。
改正前の版は、日曜日の国民の祝日の翌日を休日にする（翌日がもともと国民の祝日なら何も足さない）。
施行日より前は `false` になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def isSubstituteAt (H : Int → Bool) (z : Int) : Bool :=
  if currentEffective ≤ z then isSubstitute H z
  else substituteEffective ≤ z && !H z && H (z - 1) && Weekday.ofDays (z - 1) == .sunday

/-- `z` の日に施行されていた第3条第3項による国民の休日かどうか。現行の版は `isCitizens`。
改正前の版は、前日と翌日が国民の祝日である日のうち、日曜日と振替休日を除く。施行日より前は `false` になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isCitizensAt (H : Int → Bool) (z : Int) : Bool :=
  if currentEffective ≤ z then isCitizens H z
  else citizensEffective ≤ z && isCitizens H z && Weekday.ofDays z != .sunday &&
    !isSubstituteAt H z

/-- `z` が、その日に施行されていた第3条第2項・第3項のどちらかによる休日かどうか。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項",
  ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isRestDayAt (H : Int → Bool) (z : Int) : Bool :=
  isSubstituteAt H z || isCitizensAt H z

/-- HOL-C1 の 1 年分の検査。`y` 年の国民の祝日から `isRestDayAt` で導いた休日が、CSV の「休日」の行と
一致するかどうか。導かれる休日は必ず国民の祝日の翌日になる（`isRestDayAt_pred`）ので、
すべての日を調べる代わりに、「休日」の行と各国民の祝日の翌日だけを調べる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def checkYear (y : Int) : Bool :=
  let national := nationalDays y
  let rest := restDays y
  let H := fun z => national.contains z
  -- CSV の「休日」の行は、どれも導いた休日になる。
  rest.all (isRestDayAt H) &&
    -- 国民の祝日の翌日は、導いた休日であるときに限り「休日」の行になる。
    national.all fun s => isRestDayAt H (s + 1) == rest.contains (s + 1)

end Ritsuryo.Holiday
