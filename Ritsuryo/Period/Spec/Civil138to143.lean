module

public import Ritsuryo.Calendar.Proofs
meta import Ritsuryo.Basis

/-!
# 民法 第138条〜第143条（期間の計算の仕様）

民法の期間の計算（初日不算入、末日の終了で満了、暦による計算と応当日）を、条文の言葉どおりに書いた仕様。
CLI が実際に動かす計算（通算日による計算）は `Ritsuryo/Period/Impl.lean` にあり、
PER-1（`per1_compute_eq_spec`）が両者の一致を示す。

このファイルの定義は条文の語に対応する。

- 起算日（第140条）: `startDateSpec`。期間の初日を算入せず、出来事の翌日から数える。午前零時から始まるときは当日から数える。
- 最後の週・月・年（第143条第2項）: `lastMonthSpec` が最後の月を、`weekCorrespondingSpec` が最後の週の応当日を出す。
- 応当日（第143条第2項）: `correspondingDaySpec`。最後の月に起算日と同じ日がなければ `none`。
- 末日（第141条・第143条第2項）: `expiryFromStartSpec` と `expirySpec`。応当日の前日、応当日がないときはその月の末日。

日の期間も「起算日から n 日後の前日」と書き、四つの単位を同じ形で扱う。
仕様は暦をそのままたどる素朴な定義で書く。月は `YearMonth.addMonthsNaive`（1 か月ずつ進める）、
日は `Date.addDaysNaive`（1 日ずつ進める）で数える。第138条（特別の定め）と第139条（時間による期間）はライブラリの外にある。

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

/-- 期間の長さ。第140条・第143条の「日、週、月又は年によって期間を定めたとき」の四つの単位と、その数 `n`。 -/
inductive Length where
  | days (n : Nat)
  | weeks (n : Nat)
  | months (n : Nat)
  | years (n : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Civil

open Date

/-- 第百四十条　日、週、月又は年によって期間を定めたときは、期間の初日は、算入しない。ただし、その期間が午前零時から始まるときは、この限りでない。

起算日を返す。初日不算入なので、出来事の日 `event` の翌日が起算日になる。
期間が午前零時から始まるとき（`startAtMidnight`）は `event` 当日が起算日になる。 -/
@[ritsuryo_basis "民法" "第140条"]
def startDateSpec (event : Date) (startAtMidnight : Bool) : Date :=
  if startAtMidnight then event else nextDate event

/-- `x` から 1 日ずつ進め、`origin` と同じ曜日の日を探す。`fuel` 回調べても見つからなければ、その時点の日を返す。
`weekCorrespondingSpec` は `origin` の翌日から 7 日の範囲で呼ぶので、必ず 7 日後で見つかる。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def sameWeekdayAfterSpec (origin : Date) : Nat → Date → Date
  | 0, x => x
  | fuel + 1, x =>
    if x.weekday = origin.weekday then x else sameWeekdayAfterSpec origin fuel (nextDate x)

/-- 第百四十三条第二項　週…の初めから期間を起算しないときは、その期間は、最後の週…においてその起算日に応当する日の前日に満了する。

最後の週の応当日を返す。週を暦に従って数え、起算日の次の同じ曜日の日へ進むことを `n` 回くり返す。
PER-3 がこれを 7n 日後と等しいと示す。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def weekCorrespondingSpec (start : Date) : Nat → Date
  | 0 => start
  | n + 1 =>
    let prev := weekCorrespondingSpec start n
    sameWeekdayAfterSpec prev 7 (nextDate prev)

/-- 第百四十三条第二項　…最後の週、月又は年において…

最後の月（年月）を返す。月の期間は起算日の月から 1 か月ずつ `n` 回進めた月、年の期間は `n` 年後の同じ月になる。
日・週の期間では起算日の月を返す（応当日が常にあるので、末日はこの値によらない）。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def lastMonthSpec (start : Date) : Length → YearMonth
  | .days _ => start.yearMonth
  | .weeks _ => start.yearMonth
  | .months n => start.yearMonth.addMonthsNaive n
  | .years n => ⟨start.year + n, start.month⟩

/-- 第百四十三条第二項　…その起算日に応当する日…

起算日に応当する日を返す。日の期間は起算日の `n` 日後、週の期間は `weekCorrespondingSpec` の日になる。
月・年の期間は最後の月の起算日と同じ日付の日で、その月にその日がない（1月31日起算で2月に31日がない等）ときは `none` になる。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def correspondingDaySpec (start : Date) : Length → Option Date
  | .days n => some (start.addDaysNaive n)
  | .weeks n => some (weekCorrespondingSpec start n)
  | len =>
    let ym := lastMonthSpec start len
    if start.day ≤ ym.daysInMonth then some ⟨ym.year, ym.month, start.day⟩ else none

/-- 第百四十三条第二項　…その起算日に応当する日の前日に満了する。ただし、…最後の月に応当する日がないときは、その月の末日に満了する。

起算日 `start` から数えた期間の末日を返す。応当日があればその前日、応当日がなければ最後の月の末日になる。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def expiryFromStartSpec (start : Date) (len : Length) : Date :=
  match correspondingDaySpec start len with
  | some c => prevDate c
  | none => (lastMonthSpec start len).lastDay

/-- 第百四十一条　前条の場合には、期間は、その末日の終了をもって満了する。

出来事の日 `event` から期間 `len` の末日を返す。第140条で起算日を決め、第143条第2項で末日を出す。
期間はこの日の終了をもって満了する。 -/
@[ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第141条",
  ritsuryo_basis "民法" "第143条第2項"]
def expirySpec (event : Date) (startAtMidnight : Bool) (len : Length) : Date :=
  expiryFromStartSpec (startDateSpec event startAtMidnight) len

end Civil

end Ritsuryo.Period
