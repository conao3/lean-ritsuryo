module

public import Ritsuryo.Calendar.Proofs
meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo.Period

inductive HolidayClass where
  | sunday
  | saturday
  | nationalHoliday
  | newYear
  | yearEnd
  deriving DecidableEq, Repr, Inhabited

namespace HolidayClass

@[ritsuryo_basis "民法" "第142条"]
def all : List HolidayClass :=
  [.sunday, .saturday, .nationalHoliday, .newYear, .yearEnd]

@[ritsuryo_basis "民法" "第142条"]
def name : HolidayClass → String
  | .sunday => "sunday"
  | .saturday => "saturday"
  | .nationalHoliday => "national-holiday"
  | .newYear => "new-year"
  | .yearEnd => "year-end"

@[ritsuryo_basis "民法" "第142条"]
def ofName? (s : String) : Option HolidayClass :=
  all.find? (·.name == s)

@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法施行令" "第2条第2項"]
def holds (national : Date → Bool) (d : Date) : HolidayClass → Bool
  | .sunday => d.weekday == .sunday
  | .saturday => d.weekday == .saturday
  | .nationalHoliday => national d
  | .newYear => d.month == 1 && (d.day == 2 || d.day == 3)
  | .yearEnd => d.month == 12 && 29 ≤ d.day && d.day ≤ 31

end HolidayClass

end Ritsuryo.Period
