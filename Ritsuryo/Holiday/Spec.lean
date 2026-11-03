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

このファイルは、現行の第3条第2項（振替休日）と第3項（国民の休日）を 2 通りに書く。

- 仕様 `SubstituteSpec`・`CitizensSpec`: 条文の文言をそのまま `Prop` にしたもの。
- 実装 `isSubstitute`・`isCitizens`: 計算に使う `Bool` の関数。

どちらも「国民の祝日」の集合を引数 `H : Int → Bool`（日番号 → 国民の祝日かどうか）で受け取り、日を
日番号（`Date.toDays`）で表す。両者が一致することは `Ritsuryo/Holiday/Proofs.lean` の HOL-1 で証明する。
改正前の第3条を含めた日ごとの判定は `Ritsuryo/Holiday/Lookup.lean` に置く。

第2条の「第 n 月曜日」の規則は `nthMonday` で計算し、その性質を HOL-2 で証明する。
-/

@[expose] public section

namespace Ritsuryo.Holiday

open Date

/-- ２　「国民の祝日」が日曜日に当たるときは、その日後においてその日に最も近い「国民の祝日」でない日を休日とする。

仕様: `z` は国民の祝日でなく、`z` より前に日曜日の国民の祝日 `s` があり、`s` の翌日から `z` の前日までが
すべて国民の祝日である。つまり `z` は、日曜日の祝日のあとで最初に来る祝日でない日になる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def SubstituteSpec (H : Int → Bool) (z : Int) : Prop :=
  H z = false ∧ ∃ s, s < z ∧ H s = true ∧ Weekday.ofDays s = .sunday ∧
    ∀ x, s < x → x < z → H x = true

/-- ３　その前日及び翌日が「国民の祝日」である日（「国民の祝日」でない日に限る。）は、休日とする。

仕様: `z` は国民の祝日でなく、前日 `z - 1` と翌日 `z + 1` が国民の祝日である。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def CitizensSpec (H : Int → Bool) (z : Int) : Prop :=
  H z = false ∧ H (z - 1) = true ∧ H (z + 1) = true

/-- `x` から過去へ最大 `k` 日さかのぼる間、国民の祝日が途切れずに続き、その間（`x` を含む）に
日曜日があるかどうか。`x` が祝日でなければ `false`、`x` が日曜日の祝日なら `true`、どちらでもなければ前日へ進む。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def sundayRun (H : Int → Bool) : Nat → Int → Bool
  | 0, _ => false
  | k + 1, x => H x && (Weekday.ofDays x == .sunday || sundayRun H k (x - 1))

/-- 実装: 現行の第3条第2項による振替休日かどうか。`z` が国民の祝日でなく、前日から続く祝日の並びに
日曜日がある。7 日続く並びには必ず日曜日が含まれるので、さかのぼるのは 7 日で足りる。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第2項"]
def isSubstitute (H : Int → Bool) (z : Int) : Bool :=
  !H z && sundayRun H 7 (z - 1)

/-- 実装: 現行の第3条第3項による国民の休日かどうか。`z` が国民の祝日でなく、前日と翌日が国民の祝日である。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
def isCitizens (H : Int → Bool) (z : Int) : Bool :=
  !H z && H (z - 1) && H (z + 1)

/-- 第二条　成人の日　一月の第二月曜日、海の日　七月の第三月曜日、敬老の日　九月の第三月曜日、スポーツの日　十月の第二月曜日

`y` 年 `m` 月の第 `n` 月曜日。`w` はその月の 1 日の曜日（0 が日曜日、1 が月曜日）で、最初の月曜日は
`1 + (8 - w) % 7` 日になり、そこから 7 日ずつ進める。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def nthMonday (y : Int) (m n : Nat) : Date :=
  let w := ((toDays ⟨y, m, 1⟩ + 4) % 7).toNat
  ⟨y, m, 1 + (8 - w) % 7 + 7 * (n - 1)⟩

end Ritsuryo.Holiday
