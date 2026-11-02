module

public import Ritsuryo.Calendar.Proofs
meta import Ritsuryo.Basis

/-!
# 民法 第138条〜第143条

e-Gov 法令履歴 `129AC0000000089_20260624_508AC0000000045`。

> 第百三十八条　期間の計算方法は、法令若しくは裁判上の命令に特別の定めがある場合又は法律行為に別段の定めがある場合を除き、この章の規定に従う。
>
> 第百四十条　日、週、月又は年によって期間を定めたときは、期間の初日は、算入しない。ただし、その期間が午前零時から始まるときは、この限りでない。
>
> 第百四十一条　前条の場合には、期間は、その末日の終了をもって満了する。
>
> 第百四十三条　週、月又は年によって期間を定めたときは、その期間は、暦に従って計算する。
> ２　週、月又は年の初めから期間を起算しないときは、その期間は、最後の週、月又は年においてその起算日に応当する日の前日に満了する。ただし、月又は年によって期間を定めた場合において、最後の月に応当する日がないときは、その月の末日に満了する。
-/

@[expose] public section

namespace Ritsuryo.Period

inductive Length where
  | days (n : Nat)
  | weeks (n : Nat)
  | months (n : Nat)
  | years (n : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Civil

open Date

/-- 第百四十条　日、週、月又は年によって期間を定めたときは、期間の初日は、算入しない。ただし、その期間が午前零時から始まるときは、この限りでない。 -/
@[ritsuryo_basis "民法" "第140条"]
def startDateSpec (event : Date) (startAtMidnight : Bool) : Date :=
  if startAtMidnight then event else nextDate event

@[ritsuryo_basis "民法" "第143条第2項"]
def sameWeekdayAfterSpec (origin : Date) : Nat → Date → Date
  | 0, x => x
  | fuel + 1, x =>
    if x.weekday = origin.weekday then x else sameWeekdayAfterSpec origin fuel (nextDate x)

/-- 第百四十三条第二項　週…の初めから期間を起算しないときは、その期間は、最後の週…においてその起算日に応当する日の前日に満了する。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def weekCorrespondingSpec (start : Date) : Nat → Date
  | 0 => start
  | n + 1 =>
    let prev := weekCorrespondingSpec start n
    sameWeekdayAfterSpec prev 7 (nextDate prev)

/-- 第百四十三条第二項　…最後の週、月又は年において… -/
@[ritsuryo_basis "民法" "第143条第2項"]
def lastMonthSpec (start : Date) : Length → YearMonth
  | .days _ => start.yearMonth
  | .weeks _ => start.yearMonth
  | .months n => start.yearMonth.addMonthsNaive n
  | .years n => ⟨start.year + n, start.month⟩

/-- 第百四十三条第二項　…その起算日に応当する日… -/
@[ritsuryo_basis "民法" "第143条第2項"]
def correspondingDaySpec (start : Date) : Length → Option Date
  | .days n => some (start.addDaysNaive n)
  | .weeks n => some (weekCorrespondingSpec start n)
  | len =>
    let ym := lastMonthSpec start len
    if start.day ≤ ym.daysInMonth then some ⟨ym.year, ym.month, start.day⟩ else none

/-- 第百四十三条第二項　…その起算日に応当する日の前日に満了する。ただし、…最後の月に応当する日がないときは、その月の末日に満了する。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def expiryFromStartSpec (start : Date) (len : Length) : Date :=
  match correspondingDaySpec start len with
  | some c => prevDate c
  | none => (lastMonthSpec start len).lastDay

/-- 第百四十一条　前条の場合には、期間は、その末日の終了をもって満了する。 -/
@[ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第141条",
  ritsuryo_basis "民法" "第143条第2項"]
def expirySpec (event : Date) (startAtMidnight : Bool) (len : Length) : Date :=
  expiryFromStartSpec (startDateSpec event startAtMidnight) len

end Civil

end Ritsuryo.Period
