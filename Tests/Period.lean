module

public import Ritsuryo
public import Tests.Harness
public import Tests.Calendar

public section

namespace Ritsuryo.Tests.Period

open Ritsuryo Ritsuryo.Period Ritsuryo.Tests.Calendar

def expiry (e : Date) (mid : Bool) (len : Length) : Date :=
  (compute e mid len).expiry

def rolled (rule : RolloverRule) (x : Date) : Option Date :=
  rollover (rule.isHoliday Holiday.isHoliday) 366 x

instance : ToString (Option Date) where
  toString
    | some x => toString x
    | none => "none"

def civil : TestM Unit := do
  checkEq "1 month from 2026-01-30: no 2/31, so the end of February"
    (expiry (d 2026 1 30) false (.months 1)) (d 2026 2 28)
  checkEq "1 month from 2024-01-30 in a leap year"
    (expiry (d 2024 1 30) false (.months 1)) (d 2024 2 29)
  checkEq "1 month from 2026-01-31 (month end): end of February"
    (expiry (d 2026 1 31) false (.months 1)) (d 2026 2 28)
  checkEq "1 month from 2026-03-31 (month end): end of April"
    (expiry (d 2026 3 31) false (.months 1)) (d 2026 4 30)
  checkEq "1 month from 2026-11-02 ends on the corresponding day"
    (expiry (d 2026 11 2) false (.months 1)) (d 2026 12 2)
  checkEq "10 days from 2026-11-02" (expiry (d 2026 11 2) false (.days 10)) (d 2026 11 12)
  checkEq "1 year starting at midnight on 2026-04-01"
    (expiry (d 2026 4 1) true (.years 1)) (d 2027 3 31)
  checkEq "2 weeks from Monday 2026-11-02" (expiry (d 2026 11 2) false (.weeks 2)) (d 2026 11 16)
  checkEq "1 year from 2024-02-28: start 2024-02-29 has no 2025 counterpart"
    (expiry (d 2024 2 28) false (.years 1)) (d 2025 2 28)
  checkEq "national tax 1 month equals the civil result"
    (computeTax (d 2026 1 30) false (.months 1)).expiry (d 2026 2 28)

def age : TestM Unit := do
  checkEq "born 2008-02-29 attains 18 on 2026-02-28" (Age.attainmentDate (d 2008 2 29) 18)
    (d 2026 2 28)
  checkEq "born 2008-02-29 attains 20 on 2028-02-28 in a leap year"
    (Age.attainmentDate (d 2008 2 29) 20) (d 2028 2 28)
  checkEq "born 2008-04-01 attains 6 on 2014-03-31" (Age.attainmentDate (d 2008 4 1) 6)
    (d 2014 3 31)
  checkEq "born 2000-01-01 attains 20 on 2019-12-31" (Age.attainmentDate (d 2000 1 1) 20)
    (d 2019 12 31)
  checkEq "born 2008-02-29 is 17 on 2026-02-27" (Age.ageOn (d 2008 2 29) (d 2026 2 27)) 17
  checkEq "born 2008-02-29 is 18 on 2026-02-28" (Age.ageOn (d 2008 2 29) (d 2026 2 28)) 18
  checkEq "born 2000-01-01 is 20 on 2019-12-31" (Age.ageOn (d 2000 1 1) (d 2019 12 31)) 20
  checkEq "born 2000-01-01 is 19 on 2019-12-30" (Age.ageOn (d 2000 1 1) (d 2019 12 30)) 19
  checkEq "on the birth date the age is 0" (Age.ageOn (d 2026 11 2) (d 2026 11 2)) 0

def rolloverExamples : TestM Unit := do
  checkEq "民訴 95 条 3 項: 2026-12-29 rolls over the year end to 2027-01-04"
    (rolled .civilProcedure95 (d 2026 12 29)) (some (d 2027 1 4))
  checkEq "民訴 95 条 3 項: 2 weeks from service on 2026-12-15 end on 2027-01-04"
    (rolled .civilProcedure95 (expiry (d 2026 12 15) false (.weeks 2))) (some (d 2027 1 4))
  checkEq "民訴 95 条 3 項: Saturday 2026-05-02 rolls past Golden Week to 2026-05-07"
    (rolled .civilProcedure95 (d 2026 5 2)) (some (d 2026 5 7))
  checkEq "国税通則法 10 条 2 項: Sunday 2026-03-15 rolls to 2026-03-16"
    (rolled (.nationalTax10 true) (d 2026 3 15)) (some (d 2026 3 16))
  checkEq "国税通則法 10 条 2 項 with 1/2 and 1/3 as general holidays"
    (rolled (.nationalTax10 true) (d 2025 1 2)) (some (d 2025 1 6))
  checkEq "国税通則法 10 条 2 項 without 1/2 and 1/3 as general holidays"
    (rolled (.nationalTax10 false) (d 2025 1 2)) (some (d 2025 1 2))
  checkEq "民法 142 条 with the custom: Sunday 2026-11-22 then 勤労感謝の日"
    (rolled (.civil142 [.sunday, .nationalHoliday] true) (d 2026 11 22)) (some (d 2026 11 24))
  checkEq "民法 142 条 without the custom does not roll over"
    (rolled (.civil142 [.sunday, .nationalHoliday] false) (d 2026 11 22)) (some (d 2026 11 22))
  checkEq "民法 142 条 with Saturday added: 2026-11-21 rolls to 2026-11-24"
    (rolled (.civil142 [.sunday, .saturday, .nationalHoliday] true) (d 2026 11 21))
    (some (d 2026 11 24))

def holiday : TestM Unit := do
  check "2026-05-06 is a holiday (振替休日)" (Holiday.isHoliday (d 2026 5 6))
  check "2026-09-22 is a holiday (国民の休日)" (Holiday.isHoliday (d 2026 9 22))
  check "2026-11-02 is not a holiday" (!Holiday.isHoliday (d 2026 11 2))
  check "2019-05-01 is a holiday (休日（祝日扱い）)" (Holiday.isHoliday (d 2019 5 1))
  checkEq "成人の日 2027 is the second Monday of January" (Holiday.nthMonday 2027 1 2)
    (d 2027 1 11)
  checkEq "海の日 2026 is the third Monday of July" (Holiday.nthMonday 2026 7 3) (d 2026 7 20)
  checkEq "CSV rows" Holiday.Data.rowCount 1067
  checkEq "CSV years" (Holiday.Data.lastYear - Holiday.Data.firstYear + 1) 73
  let rest := (List.range 73).foldl
    (fun n (i : Nat) => n + (Holiday.restDays (1955 + (i : Int))).length) 0
  checkEq "休日 rows" rest 116

def suites : List (String × TestM Unit) :=
  [("民法 examples", civil), ("年齢計算 examples", age), ("繰り下げ examples", rolloverExamples),
    ("祝日 examples", holiday)]

end Ritsuryo.Tests.Period
