module

public import Ritsuryo.Period.Spec.Civil142
public import Ritsuryo.Period.Spec.CivilProcedure95
public import Ritsuryo.Period.Spec.TaxGeneral10
meta import Ritsuryo.Basis

@[expose] public section

namespace Ritsuryo.Period

open Date

@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def rolloverDays (isHoliday : Int → Bool) : Nat → Int → Option Int
  | 0, _ => none
  | fuel + 1, z => if isHoliday z then rolloverDays isHoliday fuel (z + 1) else some z

@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def rollover (isHoliday : Date → Bool) (fuel : Nat) (d : Date) : Option Date :=
  (rolloverDays (fun z => isHoliday (ofDays z)) fuel d.toDays).map ofDays

inductive RolloverRule where
  | civil142 (classes : List HolidayClass) (noTradeCustom : Bool)
  | civilProcedure95
  | nationalTax10 (newYearIsGeneralHoliday : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace RolloverRule

@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def isHoliday (national : Date → Bool) : RolloverRule → Date → Bool
  | .civil142 classes custom => Civil.isHolidaySpec national classes custom
  | .civilProcedure95 => CivilProcedure.isHolidaySpec national
  | .nationalTax10 general => TaxGeneral.isHolidaySpec national general

@[ritsuryo_basis "民法" "第142条", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項"]
def classesOf : RolloverRule → List HolidayClass
  | .civil142 classes custom => if custom then classes else []
  | .civilProcedure95 => HolidayClass.all
  | .nationalTax10 general =>
    if general then HolidayClass.all else [.sunday, .saturday, .nationalHoliday, .yearEnd]

end RolloverRule

end Ritsuryo.Period
