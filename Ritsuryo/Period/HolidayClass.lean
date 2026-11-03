module

public import Ritsuryo.Calendar.Proofs
meta import Ritsuryo.Basis

/-!
# 休日の種類

期間の末日が休日に当たるときに翌日へ送る規定（民法第142条、民事訴訟法第95条第3項、国税通則法第10条第2項と
同法施行令第2条第2項）は、どれも同じ数種類の日の組み合わせで書ける。このファイルはその種類を `HolidayClass`
として列挙し、日付がその種類に当たるかの判定（`holds`）と、CLI の `--holiday-classes` で使う名前を置く。

各規定がどの種類を休日にするかは `Ritsuryo/Period/Spec/` の各ファイルの `isHolidaySpec` が決める。
-/

@[expose] public section

namespace Ritsuryo.Period

/-- 休日の種類。日曜日、土曜日、国民の祝日に関する法律に規定する休日、1月2日・1月3日、12月29日〜31日の五つ。 -/
inductive HolidayClass where
  | sunday
  | saturday
  | nationalHoliday
  | newYear
  | yearEnd
  deriving DecidableEq, Repr, Inhabited

namespace HolidayClass

/-- 休日の種類のすべて。 -/
@[ritsuryo_basis "民法" "第142条"]
def all : List HolidayClass :=
  [.sunday, .saturday, .nationalHoliday, .newYear, .yearEnd]

/-- CLI の `--holiday-classes` と出力で使う種類の名前。 -/
@[ritsuryo_basis "民法" "第142条"]
def name : HolidayClass → String
  | .sunday => "sunday"
  | .saturday => "saturday"
  | .nationalHoliday => "national-holiday"
  | .newYear => "new-year"
  | .yearEnd => "year-end"

/-- 名前 `s` から種類を引く。どの種類の名前でもなければ `none` を返す。 -/
@[ritsuryo_basis "民法" "第142条"]
def ofName? (s : String) : Option HolidayClass :=
  all.find? (·.name == s)

/-- 日 `d` がその種類の日に当たるかを返す。曜日は `Date.weekday`、祝日法の休日は引数 `national` で判定し、
1月2日・1月3日と12月29日〜31日は月日で判定する。 -/
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
