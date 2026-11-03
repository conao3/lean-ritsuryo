module

public import Ritsuryo.Period.Spec.Civil138to143
public import Ritsuryo.Period.HolidayClass
meta import Ritsuryo.Basis

/-!
# 国税通則法 第10条（国税の期間の計算と期限の仕様）

国税に関する法律の期間の計算（第1項）と、期限が休日に当たるときの扱い（第2項、施行令第2条第2項）の仕様を置く。

- 第1項: 日・月・年の三つの単位の期間を `TaxLength` で表し、起算日（`startDateSpec`、初日不算入）と
  末日（`expiryFromStartSpec`、応当日の前日、応当日がないときはその月の末日）を条文どおりに書く。
  民法の仕様とは独立に書き、PER-7（`per7_national_tax_general`）が民法の仕様と同じ末日になることと、
  CLI の `computeTax` がこの仕様と一致することを示す。
- 第2項: 期限が日曜日・祝日法の休日・その他一般の休日・土曜日・12月29日〜31日に当たるときは、翌日が期限になる
  （`isHolidaySpec`）。国税通則法基本通達は1月2日・1月3日を一般の休日に含めるので、その扱いを入力で選べる。
  ROL-3 が、1月2日・1月3日を含めたときの集合が民事訴訟法第95条第3項の集合と同じになることを示す。

第1項第1号の「国税に関する法律に別段の定めがあるとき」と、施行令第2条第1項の第2項を適用しない期限は、ライブラリの外にある。

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

/-- 国税に関する法律の期間の長さ。第10条第1項の「日、月又は年をもつて定める期間」の三つの単位と、その数 `n`。 -/
inductive TaxLength where
  | days (n : Nat)
  | months (n : Nat)
  | years (n : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace TaxLength

/-- 国税の期間の長さを、民法の期間の長さ（`Length`）の同じ単位に移す。CLI はこれで民法の計算を使う。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項"]
def toLength : TaxLength → Length
  | .days n => .days n
  | .months n => .months n
  | .years n => .years n

end TaxLength

namespace TaxGeneral

open Date

/-- 一　期間の初日は、算入しない。ただし、その期間が午前零時から始まるとき…は、この限りでない。

起算日を返す。初日不算入なので出来事の日 `event` の翌日、午前零時から始まるとき（`startAtMidnight`）は当日になる。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項第1号"]
def startDateSpec (event : Date) (startAtMidnight : Bool) : Date :=
  if startAtMidnight then event else nextDate event

/-- 三　…最後の月又は年においてその起算日に応当する日の前日に満了する。ただし、最後の月にその応当する日がないときは、その月の末日に満了する。

起算日 `start` から数えた期間の末日を返す。日の期間は起算日の `n` 日後の前日になる。
月の期間は起算日の月から `n` か月進めた月、年の期間は `n` 年後の同じ月を最後の月とし（第2号の暦に従う計算）、
その月の起算日と同じ日付の日の前日になる。その日付がその月にないときは、その月の末日になる。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項第2号", ritsuryo_basis "国税通則法" "第10条第1項第3号"]
def expiryFromStartSpec (start : Date) : TaxLength → Date
  | .days n => prevDate (start.addDaysNaive n)
  | .months n =>
    let ym := start.yearMonth.addMonthsNaive n
    if start.day ≤ ym.daysInMonth then prevDate ⟨ym.year, ym.month, start.day⟩ else ym.lastDay
  | .years n =>
    let ym : YearMonth := ⟨start.year + n, start.month⟩
    if start.day ≤ ym.daysInMonth then prevDate ⟨ym.year, ym.month, start.day⟩ else ym.lastDay

/-- 出来事の日 `event` から期間 `len` の末日を返す。第1号で起算日を決め、第2号・第3号で末日を出す。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項"]
def expirySpec (event : Date) (startAtMidnight : Bool) (len : TaxLength) : Date :=
  expiryFromStartSpec (startDateSpec event startAtMidnight) len

/-- 第十条第二項　…日曜日、国民の祝日に関する法律に規定する休日その他一般の休日又は政令で定める日（土曜日又は十二月二十九日、同月三十日若しくは同月三十一日）…

日 `d` が期限を翌日へ送る日かを返す。日曜日・祝日法の休日・土曜日・12月29日〜31日に当たるとき `true` になる。
`newYearIsGeneralHoliday` が `true` のときは、1月2日・1月3日も一般の休日として含める
（国税通則法基本通達（徴収部関係）第10条関係4の読み方）。 -/
@[ritsuryo_basis "国税通則法" "第10条第2項", ritsuryo_basis "国税通則法施行令" "第2条第2項"]
def isHolidaySpec (national : Date → Bool) (newYearIsGeneralHoliday : Bool) (d : Date) : Bool :=
  HolidayClass.holds national d .sunday || HolidayClass.holds national d .nationalHoliday ||
    (newYearIsGeneralHoliday && HolidayClass.holds national d .newYear) ||
    HolidayClass.holds national d .saturday || HolidayClass.holds national d .yearEnd

end TaxGeneral

end Ritsuryo.Period
