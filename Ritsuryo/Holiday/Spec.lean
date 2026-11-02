module

public import Ritsuryo.Calendar.Proofs
meta import Ritsuryo.Basis

/-!
# 国民の祝日に関する法律 第2条・第3条

e-Gov 法令履歴 `323AC1000000178_20200101_430AC1000000057`。

> 第二条　「国民の祝日」を次のように定める。（表の抜粋）
> 成人の日　一月の第二月曜日
> 海の日　七月の第三月曜日
> 敬老の日　九月の第三月曜日
> スポーツの日　十月の第二月曜日
>
> 第三条　「国民の祝日」は、休日とする。
> ２　「国民の祝日」が日曜日に当たるときは、その日後においてその日に最も近い「国民の祝日」でない日を休日とする。
> ３　その前日及び翌日が「国民の祝日」である日（「国民の祝日」でない日に限る。）は、休日とする。
-/

@[expose] public section

namespace Ritsuryo.Holiday

open Date

/-- ２　「国民の祝日」が日曜日に当たるときは、その日後においてその日に最も近い「国民の祝日」でない日を休日とする。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def SubstituteSpec (H : Int → Bool) (z : Int) : Prop :=
  H z = false ∧ ∃ s, s < z ∧ H s = true ∧ Weekday.ofDays s = .sunday ∧
    ∀ x, s < x → x < z → H x = true

/-- ３　その前日及び翌日が「国民の祝日」である日（「国民の祝日」でない日に限る。）は、休日とする。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def CitizensSpec (H : Int → Bool) (z : Int) : Prop :=
  H z = false ∧ H (z - 1) = true ∧ H (z + 1) = true

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def sundayRun (H : Int → Bool) : Nat → Int → Bool
  | 0, _ => false
  | k + 1, x => H x && (Weekday.ofDays x == .sunday || sundayRun H k (x - 1))

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def isSubstitute (H : Int → Bool) (z : Int) : Bool :=
  !H z && sundayRun H 7 (z - 1)

@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isCitizens (H : Int → Bool) (z : Int) : Bool :=
  !H z && H (z - 1) && H (z + 1)

/-- 第二条　成人の日　一月の第二月曜日、海の日　七月の第三月曜日、敬老の日　九月の第三月曜日、スポーツの日　十月の第二月曜日 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def nthMonday (y : Int) (m n : Nat) : Date :=
  let w := ((toDays ⟨y, m, 1⟩ + 4) % 7).toNat
  ⟨y, m, 1 + (8 - w) % 7 + 7 * (n - 1)⟩

end Ritsuryo.Holiday
