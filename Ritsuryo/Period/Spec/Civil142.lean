module

public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 民法 第142条

e-Gov 法令履歴 `129AC0000000089_20260624_508AC0000000045`。

> 第百四十二条　期間の末日が日曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日その他の休日に当たるときは、その日に取引をしない慣習がある場合に限り、期間は、その翌日に満了する。
-/

@[expose] public section

namespace Ritsuryo.Period.Civil

/-- 期間の末日が日曜日、国民の祝日に関する法律に規定する休日その他の休日に当たるときは、その日に取引をしない慣習がある場合に限り、期間は、その翌日に満了する。 -/
@[ritsuryo_basis "民法" "第142条"]
def isHolidaySpec (national : Date → Bool) (classes : List HolidayClass) (noTradeCustom : Bool)
    (d : Date) : Bool :=
  noTradeCustom && classes.any (HolidayClass.holds national d)

end Ritsuryo.Period.Civil
