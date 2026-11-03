module

public import Ritsuryo.Period.Spec.Civil138to143
public import Ritsuryo.Period.Spec.TaxGeneral10
meta import Ritsuryo.Basis

/-!
# 期間の計算（CLI が実行する実装。民法 第140条・第141条・第143条、国税通則法 第10条第1項）

CLI の `period compute-expiry` などが実行する期間の計算。日付を通算日（`Date.toDays`。ある基準日からの日数を表す整数）に移し、
日・週の加算と前日を整数の足し算・引き算で求める。月・年の計算は年月の通し番号（`YearMonth.addMonths`）で行う。

条文の言葉どおりに書いた仕様は `Ritsuryo/Period/Spec/Civil138to143.lean` にあり、定義は 1 対 1 で対応する。

| 実装 | 仕様 | 条文 |
|---|---|---|
| `startDays` | `Civil.startDateSpec` | 民法第140条（起算日、初日不算入） |
| `lastMonth` | `Civil.lastMonthSpec` | 民法第143条第2項（最後の月） |
| `correspondingDays` | `Civil.correspondingDaySpec` | 民法第143条第2項（応当日） |
| `expiryFromStartDays` | `Civil.expiryFromStartSpec` | 民法第143条第2項（末日） |
| `compute` | `Civil.expirySpec` | 民法第140条・第141条・第143条第2項 |

PER-1（`per1_compute_eq_spec`）が、有効な日付について `compute` の起算日・応当日・末日が仕様と一致することを示す。
国税通則法第10条第1項の期間は `computeTax` が同じ計算で出し、PER-7 が国税通則法の仕様との一致を示す。
-/

@[expose] public section

namespace Ritsuryo.Period

open Date

/-- 起算日の通算日。初日不算入なので出来事の日の通算日に 1 を足す。午前零時から始まるときは当日の通算日になる。 -/
@[ritsuryo_basis "民法" "第140条"]
def startDays (event : Date) (startAtMidnight : Bool) : Int :=
  if startAtMidnight then event.toDays else event.toDays + 1

/-- 最後の月。月の期間は起算日の月の `n` か月後、年の期間は `12 * n` か月後の月になる。
日・週の期間では起算日の月を返す（末日の計算には現れない）。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def lastMonth (start : Date) : Length → YearMonth
  | .days _ => start.yearMonth
  | .weeks _ => start.yearMonth
  | .months n => start.yearMonth.addMonths n
  | .years n => start.yearMonth.addMonths (12 * n)

/-- 起算日に応当する日の通算日。日の期間は起算日の通算日に `n`、週の期間は `7 * n` を足す。
月・年の期間は最後の月の起算日と同じ日付の日の通算日で、その日付がその月にないときは `none` になる。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def correspondingDays (start : Date) : Length → Option Int
  | .days n => some (start.toDays + n)
  | .weeks n => some (start.toDays + 7 * n)
  | len =>
    let ym := lastMonth start len
    if start.day ≤ ym.daysInMonth then some (toDays ⟨ym.year, ym.month, start.day⟩) else none

/-- 起算日 `start` から数えた期間の末日の通算日。応当日があればその前日（通算日から 1 を引く）、
応当日がなければ最後の月の末日の通算日になる。 -/
@[ritsuryo_basis "民法" "第143条第2項"]
def expiryFromStartDays (start : Date) (len : Length) : Int :=
  match correspondingDays start len with
  | some c => c - 1
  | none => (lastMonth start len).lastDay.toDays

/-- 期間の計算の結果。起算日、応当日（月・年の期間で最後の月に応当日がなければ `none`）、末日を持つ。
CLI はこの三つを出力する。 -/
structure Expiry where
  start : Date
  corresponding : Option Date
  expiry : Date
  deriving DecidableEq, Repr

/-- 出来事の日 `event` から期間 `len` を計算する。CLI の `period compute-expiry` が実行する本体。
起算日の通算日を日付に戻してから、応当日と末日の通算日を出し、それぞれ日付に戻す。 -/
@[ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第141条",
  ritsuryo_basis "民法" "第143条第2項"]
def compute (event : Date) (startAtMidnight : Bool) (len : Length) : Expiry :=
  let start := ofDays (startDays event startAtMidnight)
  { start
    corresponding := (correspondingDays start len).map ofDays
    expiry := ofDays (expiryFromStartDays start len) }

/-- 国税通則法第10条第1項の期間を計算する。日・月・年の期間を民法の期間に移して `compute` で計算する。
PER-7 がこれが国税通則法の仕様（`TaxGeneral.expirySpec`）の末日と一致することを示す。 -/
@[ritsuryo_basis "国税通則法" "第10条第1項"]
def computeTax (event : Date) (startAtMidnight : Bool) (len : TaxLength) : Expiry :=
  compute event startAtMidnight len.toLength

end Ritsuryo.Period
