module

public import Ritsuryo.Period.Spec.Civil138to143
public import Ritsuryo.Period.Spec.TaxGeneral10
meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo.Period

open Date

@[ritsuryo_basis "民法" "第140条"]
def startDays (event : Date) (startAtMidnight : Bool) : Int :=
  if startAtMidnight then event.toDays else event.toDays + 1

@[ritsuryo_basis "民法" "第143条第2項"]
def lastMonth (start : Date) : Length → YearMonth
  | .days _ => start.yearMonth
  | .weeks _ => start.yearMonth
  | .months n => start.yearMonth.addMonths n
  | .years n => start.yearMonth.addMonths (12 * n)

@[ritsuryo_basis "民法" "第143条第2項"]
def correspondingDays (start : Date) : Length → Option Int
  | .days n => some (start.toDays + n)
  | .weeks n => some (start.toDays + 7 * n)
  | len =>
    let ym := lastMonth start len
    if start.day ≤ ym.daysInMonth then some (toDays ⟨ym.year, ym.month, start.day⟩) else none

@[ritsuryo_basis "民法" "第143条第2項"]
def expiryFromStartDays (start : Date) (len : Length) : Int :=
  match correspondingDays start len with
  | some c => c - 1
  | none => (lastMonth start len).lastDay.toDays

structure Expiry where
  start : Date
  corresponding : Option Date
  expiry : Date
  deriving DecidableEq, Repr

@[ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第141条",
  ritsuryo_basis "民法" "第143条第2項"]
def compute (event : Date) (startAtMidnight : Bool) (len : Length) : Expiry :=
  let start := ofDays (startDays event startAtMidnight)
  { start
    corresponding := (correspondingDays start len).map ofDays
    expiry := ofDays (expiryFromStartDays start len) }

@[ritsuryo_basis "国税通則法" "第10条第1項"]
def computeTax (event : Date) (startAtMidnight : Bool) (len : TaxLength) : Expiry :=
  compute event startAtMidnight len.toLength

end Ritsuryo.Period
