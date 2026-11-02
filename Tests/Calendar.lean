module

public import Ritsuryo
public import Std.Time
public import Tests.Harness

public section

namespace Ritsuryo.Tests.Calendar

open Ritsuryo Date

def d (y : Int) (m n : Nat) : Date := ⟨y, m, n⟩

instance : ToString Date where
  toString x := s!"{x.year}-{x.month}-{x.day}"

instance : ToString YearMonth where
  toString x := s!"{x.year}-{x.month}"

instance : ToString Weekday where
  toString := Weekday.toString

def examples : TestM Unit := do
  check "2024 is a leap year" (isLeapYear 2024)
  check "2023 is not a leap year" (!isLeapYear 2023)
  check "1900 is not a leap year" (!isLeapYear 1900)
  check "2000 is a leap year" (isLeapYear 2000)
  check "2024-02-29 is valid" (decide (d 2024 2 29).Valid)
  check "2023-02-29 is not valid" (!decide (d 2023 2 29).Valid)
  check "2026-04-31 is not valid" (!decide (d 2026 4 31).Valid)
  checkEq "1970-01-01 is day 0" (toDays (d 1970 1 1)) 0
  checkEq "2026-11-02 day number" (toDays (d 2026 11 2)) 20759
  checkEq "1600-01-01 day number" (toDays (d 1600 1 1)) (-135140)
  checkEq "next of 2023-12-31" (nextDate (d 2023 12 31)) (d 2024 1 1)
  checkEq "next of 2024-02-28" (nextDate (d 2024 2 28)) (d 2024 2 29)
  checkEq "next of 2023-02-28" (nextDate (d 2023 2 28)) (d 2023 3 1)
  checkEq "previous of 2024-03-01" (prevDate (d 2024 3 1)) (d 2024 2 29)
  checkEq "previous of 2026-01-01" (prevDate (d 2026 1 1)) (d 2025 12 31)
  checkEq "1970-01-01 is a Thursday" (d 1970 1 1).weekday .thursday
  checkEq "2026-11-02 is a Monday" (d 2026 11 2).weekday .monday
  checkEq "addMonths 2026-11 + 3" (YearMonth.addMonths ⟨2026, 11⟩ 3) ⟨2027, 2⟩

def stdWeekdayIndex (w : Std.Time.Weekday) : Nat :=
  w.toOrdinal.val.toNat % 7

def differential : TestM Unit := do
  let lo := toDays (d 1600 1 1)
  let hi := toDays (d 2400 12 31)
  let mut mismatches : Array String := #[]
  let mut count := 0
  for i in [0:(hi - lo + 1).toNat] do
    let z := lo + i
    let ours := ofDays z
    let std := Std.Time.PlainDate.ofEpochDay (Std.Time.Day.Offset.ofInt z)
    let stdDate : Date := ⟨std.year.toInt, std.month.val.toNat, std.day.val.toNat⟩
    let stdBack := std.toEpochDay.val
    let weekdayOk := ours.weekday == Weekday.ofIndex (stdWeekdayIndex std.weekday)
    if ours != stdDate || stdBack != z || toDays ours != z || !weekdayOk then
      if mismatches.size < 5 then
        mismatches := mismatches.push s!"day {z}: ours {ours}, Std.Time {stdDate}"
    count := count + 1
  check s!"ofDays, toDays, weekday agree with Std.Time on {count} days (1600-01-01..2400-12-31)"
    mismatches.isEmpty (", ".intercalate mismatches.toList)

def suites : List (String × TestM Unit) :=
  [("calendar examples", examples), ("calendar vs Std.Time", differential)]

end Ritsuryo.Tests.Calendar
