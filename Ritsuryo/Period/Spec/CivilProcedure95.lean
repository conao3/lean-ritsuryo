module

public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 民事訴訟法 第95条（訴訟手続の期間の満了日の仕様）

民事訴訟法の期間は民法の期間の規定に従って計算する（第1項）ので、期間そのものは
`Ritsuryo/Period/Spec/Civil138to143.lean` の仕様で出す。このファイルは第3項の、末日が休日に当たるときに
翌日に満了する日の集合を置く。第3項の集合は条文で決まっており、取引の慣習の有無を問わない。

e-Gov 法令履歴 `408AC0000000109_20260624_508AC0000000046`。

> 第九十五条　期間の計算については、民法の期間に関する規定に従う。
> ３　期間の末日が日曜日、土曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日、一月二日、一月三日又は十二月二十九日から十二月三十一日までの日に当たるときは、期間は、その翌日に満了する。
-/

@[expose] public section

namespace Ritsuryo.Period.CivilProcedure

/-- 期間の末日が日曜日、土曜日、国民の祝日に関する法律に規定する休日、一月二日、一月三日又は十二月二十九日から十二月三十一日までの日に当たるときは、期間は、その翌日に満了する。

日 `d` が第3項の日（日曜日・土曜日・祝日法の休日・1月2日・1月3日・12月29日〜31日）のどれかに当たるとき `true` を返す。
`national` は祝日法の休日の判定。 -/
@[ritsuryo_basis "民事訴訟法" "第95条第3項"]
def isHolidaySpec (national : Date → Bool) (d : Date) : Bool :=
  HolidayClass.holds national d .sunday || HolidayClass.holds national d .saturday ||
    HolidayClass.holds national d .nationalHoliday || HolidayClass.holds national d .newYear ||
    HolidayClass.holds national d .yearEnd

end Ritsuryo.Period.CivilProcedure
