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
-/

@[expose] public section

namespace Ritsuryo.Holiday

open Date

@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def entriesOf (y : Int) : List Entry :=
  if Data.firstYear ≤ y ∧ y ≤ Data.lastYear then
    Data.byYear.getD (y - Data.firstYear).toNat []
  else []

@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def inRange (d : Date) : Bool :=
  Data.firstYear ≤ d.year && d.year ≤ Data.lastYear

@[ritsuryo_basis "国民の祝日に関する法律" "第2条", ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def entry? (d : Date) : Option Entry :=
  (entriesOf d.year).find? fun e => e.month == d.month && e.day == d.day

@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def isHoliday (d : Date) : Bool :=
  (entry? d).isSome

@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def nationalDays (y : Int) : List Int :=
  ((entriesOf y).filter (·.kind != .rest)).map fun e => toDays ⟨y, e.month, e.day⟩

@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def restDays (y : Int) : List Int :=
  ((entriesOf y).filter (·.kind == .rest)).map fun e => toDays ⟨y, e.month, e.day⟩

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def substituteEffective : Int := toDays ⟨1973, 4, 12⟩

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def citizensEffective : Int := toDays ⟨1985, 12, 27⟩

@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def currentEffective : Int := toDays ⟨2007, 1, 1⟩

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def isSubstituteAt (H : Int → Bool) (z : Int) : Bool :=
  if currentEffective ≤ z then isSubstitute H z
  else substituteEffective ≤ z && !H z && H (z - 1) && Weekday.ofDays (z - 1) == .sunday

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isCitizensAt (H : Int → Bool) (z : Int) : Bool :=
  if currentEffective ≤ z then isCitizens H z
  else citizensEffective ≤ z && isCitizens H z && Weekday.ofDays z != .sunday &&
    !isSubstituteAt H z

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項",
  ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isRestDayAt (H : Int → Bool) (z : Int) : Bool :=
  isSubstituteAt H z || isCitizensAt H z

@[ritsuryo_basis "国民の祝日に関する法律" "第3条"]
def checkYear (y : Int) : Bool :=
  let national := nationalDays y
  let rest := restDays y
  let H := fun z => national.contains z
  rest.all (isRestDayAt H) &&
    national.all fun s => isRestDayAt H (s + 1) == rest.contains (s + 1)

end Ritsuryo.Holiday
