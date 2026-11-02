module

public import Ritsuryo.Calendar.Days
meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo

inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving DecidableEq, Repr, Inhabited

namespace Weekday

@[ritsuryo_basis "民法" "第142条"]
def ofIndex : Nat → Weekday
  | 0 => sunday
  | 1 => monday
  | 2 => tuesday
  | 3 => wednesday
  | 4 => thursday
  | 5 => friday
  | _ => saturday

@[ritsuryo_basis "民法" "第142条"]
def next : Weekday → Weekday
  | sunday => monday
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday

@[ritsuryo_basis "民法" "第142条"]
def ofDays (z : Int) : Weekday :=
  ofIndex ((z + 4) % 7).toNat

@[ritsuryo_basis "民法" "第142条"]
def toString : Weekday → String
  | sunday => "sunday"
  | monday => "monday"
  | tuesday => "tuesday"
  | wednesday => "wednesday"
  | thursday => "thursday"
  | friday => "friday"
  | saturday => "saturday"

end Weekday

@[ritsuryo_basis "民法" "第142条"]
def Date.weekday (d : Date) : Weekday :=
  Weekday.ofDays d.toDays

end Ritsuryo
