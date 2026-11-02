module

public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 民事訴訟法 第95条

e-Gov 法令履歴 `408AC0000000109_20260624_508AC0000000046`。

> 第九十五条　期間の計算については、民法の期間に関する規定に従う。
> ３　期間の末日が日曜日、土曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日、一月二日、一月三日又は十二月二十九日から十二月三十一日までの日に当たるときは、期間は、その翌日に満了する。
-/

@[expose] public section

namespace Ritsuryo.Period.CivilProcedure

/-- 期間の末日が日曜日、土曜日、国民の祝日に関する法律に規定する休日、一月二日、一月三日又は十二月二十九日から十二月三十一日までの日に当たるときは、期間は、その翌日に満了する。 -/
@[ritsuryo_basis "民事訴訟法" "第95条第3項"]
def isHolidaySpec (national : Date → Bool) (d : Date) : Bool :=
  HolidayClass.holds national d .sunday || HolidayClass.holds national d .saturday ||
    HolidayClass.holds national d .nationalHoliday || HolidayClass.holds national d .newYear ||
    HolidayClass.holds national d .yearEnd

end Ritsuryo.Period.CivilProcedure
