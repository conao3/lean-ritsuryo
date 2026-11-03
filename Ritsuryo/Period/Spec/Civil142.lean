module

public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 民法 第142条（末日が休日に当たるときの満了日の仕様）

民法の期間の末日が休日に当たるとき、翌日に満了するかを決める判定を置く。
翌日に満了するのは、その日に取引をしない慣習がある場合に限られる。慣習があるかと、どの日を休日とするかは
事実の問題なので、CLI の入力（`--assume-no-trade-custom`、`--holiday-classes`）で受け取る。

`isHolidaySpec` は「その日が満了を翌日へ送る休日か」だけを判定する。翌日も休日のときに休日でない日まで送る計算は
`Ritsuryo/Period/Rollover.lean` の `rollover` が行う。

e-Gov 法令履歴 `129AC0000000089_20260624_508AC0000000045`。

> 第百四十二条　期間の末日が日曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日その他の休日に当たるときは、その日に取引をしない慣習がある場合に限り、期間は、その翌日に満了する。
-/

@[expose] public section

namespace Ritsuryo.Period.Civil

/-- 期間の末日が日曜日、国民の祝日に関する法律に規定する休日その他の休日に当たるときは、その日に取引をしない慣習がある場合に限り、期間は、その翌日に満了する。

日 `d` が満了を翌日へ送る休日かを返す。取引をしない慣習があり（`noTradeCustom`）、かつ `d` が選んだ休日の種類
（`classes`。日曜日・国民の祝日など）のどれかに当たるとき `true` になる。`national` は祝日法の休日の判定。 -/
@[ritsuryo_basis "民法" "第142条"]
def isHolidaySpec (national : Date → Bool) (classes : List HolidayClass) (noTradeCustom : Bool)
    (d : Date) : Bool :=
  noTradeCustom && classes.any (HolidayClass.holds national d)

end Ritsuryo.Period.Civil
