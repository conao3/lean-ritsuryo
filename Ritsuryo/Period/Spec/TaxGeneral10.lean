module

public import Ritsuryo.Period.Spec.Civil138to143
public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 国税通則法 第10条

e-Gov 法令履歴 `337AC0000000066_20261101_507AC0000000013`、国税通則法施行令 `337CO0000000135_20260401_507CO0000000126`。

> 第十条　国税に関する法律において日、月又は年をもつて定める期間の計算は、次に定めるところによる。
> 一　期間の初日は、算入しない。ただし、その期間が午前零時から始まるとき、又は国税に関する法律に別段の定めがあるときは、この限りでない。
> 二　期間を定めるのに月又は年をもつてしたときは、暦に従う。
> 三　前号の場合において、月又は年の始めから期間を起算しないときは、その期間は、最後の月又は年においてその起算日に応当する日の前日に満了する。ただし、最後の月にその応当する日がないときは、その月の末日に満了する。
> ２　国税に関する法律に定める申告、申請、請求、届出その他書類の提出、通知、納付又は徴収に関する期限（時をもつて定める期限その他の政令で定める期限を除く。）が日曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日その他一般の休日又は政令で定める日に当たるときは、これらの日の翌日をもつてその期限とみなす。
>
> 国税通則法施行令第二条第二項　法第十条第二項に規定する政令で定める日は、土曜日又は十二月二十九日、同月三十日若しくは同月三十一日とする。
-/

@[expose] public section

namespace Ritsuryo.Period

inductive TaxLength where
  | days (n : Nat)
  | months (n : Nat)
  | years (n : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace TaxLength

@[ritsuryo_basis "国税通則法" "第10条第1項"]
def toLength : TaxLength → Length
  | .days n => .days n
  | .months n => .months n
  | .years n => .years n

end TaxLength

namespace TaxGeneral

open Date

/-- 一　期間の初日は、算入しない。ただし、その期間が午前零時から始まるとき…は、この限りでない。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項第1号"]
def startDateSpec (event : Date) (startAtMidnight : Bool) : Date :=
  if startAtMidnight then event else nextDate event

/-- 三　…最後の月又は年においてその起算日に応当する日の前日に満了する。ただし、最後の月にその応当する日がないときは、その月の末日に満了する。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項第2号", ritsuryo_basis "国税通則法" "第10条第1項第3号"]
def expiryFromStartSpec (start : Date) : TaxLength → Date
  | .days n => prevDate (start.addDaysNaive n)
  | .months n =>
    let ym := start.yearMonth.addMonthsNaive n
    if start.day ≤ ym.daysInMonth then prevDate ⟨ym.year, ym.month, start.day⟩ else ym.lastDay
  | .years n =>
    let ym : YearMonth := ⟨start.year + n, start.month⟩
    if start.day ≤ ym.daysInMonth then prevDate ⟨ym.year, ym.month, start.day⟩ else ym.lastDay

@[ritsuryo_basis "国税通則法" "第10条第1項"]
def expirySpec (event : Date) (startAtMidnight : Bool) (len : TaxLength) : Date :=
  expiryFromStartSpec (startDateSpec event startAtMidnight) len

/-- 第十条第二項　…日曜日、国民の祝日に関する法律に規定する休日その他一般の休日又は政令で定める日（土曜日又は十二月二十九日、同月三十日若しくは同月三十一日）… -/
@[ritsuryo_basis "国税通則法" "第10条第2項", ritsuryo_basis "国税通則法施行令" "第2条第2項"]
def isHolidaySpec (national : Date → Bool) (newYearIsGeneralHoliday : Bool) (d : Date) : Bool :=
  HolidayClass.holds national d .sunday || HolidayClass.holds national d .nationalHoliday ||
    (newYearIsGeneralHoliday && HolidayClass.holds national d .newYear) ||
    HolidayClass.holds national d .saturday || HolidayClass.holds national d .yearEnd

end TaxGeneral

end Ritsuryo.Period
