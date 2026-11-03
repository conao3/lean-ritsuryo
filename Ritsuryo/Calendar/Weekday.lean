module

public import Ritsuryo.Calendar.Days
meta import Ritsuryo.Basis

/-!
# 曜日

民法第142条（期間の末日が日曜日・祝日法に規定する休日その他の休日に当たるときは翌日に満了する）や
国民の祝日に関する法律第3条第2項（振替休日）は、日が日曜日かどうかで結果が変わる。このファイルは
曜日の型 `Weekday` と、1970-01-01 からの日数（`Ritsuryo.Calendar.Days`）から曜日を出す `Weekday.ofDays` を定める。

1970-01-01 は木曜日なので、日数 `z` の曜日は `(z + 4) % 7` 番目（日曜日を 0 とする）になる。
`Int` の `%` は除数が正なら 0〜6 を返すので、1970 年より前の日にも同じ式が当てはまる。
この式と、翌日の曜日が次の曜日になることは CAL-5 で証明する。
-/

@[expose] public section

namespace Ritsuryo

/-- 曜日。日曜日から土曜日まで。 -/
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

/-- 日曜日を 0 とした番号から曜日にする。6 以上はすべて土曜日にするが、`ofDays` からは 0〜6 しか来ない。 -/
@[ritsuryo_basis "民法" "第142条"]
def ofIndex : Nat → Weekday
  | 0 => sunday
  | 1 => monday
  | 2 => tuesday
  | 3 => wednesday
  | 4 => thursday
  | 5 => friday
  | _ => saturday

/-- 翌日の曜日。土曜日の次は日曜日に戻る。 -/
@[ritsuryo_basis "民法" "第142条"]
def next : Weekday → Weekday
  | sunday => monday
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday

/-- 1970-01-01 からの日数 `z` の日の曜日。1970-01-01（`z` = 0）が木曜日（番号 4）なので、
`z + 4` を 7 で割った余りを番号にする。 -/
@[ritsuryo_basis "民法" "第142条"]
def ofDays (z : Int) : Weekday :=
  ofIndex ((z + 4) % 7).toNat

/-- CLI の出力に使う曜日の英語名（小文字）。 -/
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

/-- 日付 `d` の曜日。日数に直してから `Weekday.ofDays` で出す。 -/
@[ritsuryo_basis "民法" "第142条"]
def Date.weekday (d : Date) : Weekday :=
  Weekday.ofDays d.toDays

end Ritsuryo
