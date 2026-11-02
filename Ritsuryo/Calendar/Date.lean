module

meta import Ritsuryo.Basis

/-!
# 暦

明治五年太政官布告第三百三十七号（改暦ノ布告）により太陽暦を用いる。閏年は明治三十一年勅令第九十号
（閏年ニ関スル件、e-Gov 法令履歴 `131IO0000000090_18980511_000000000000000`）による。

> 神武天皇即位紀元年数ノ四ヲ以テ整除シ得ヘキ年ヲ閏年トス但シ紀元年数ヨリ六百六十ヲ減シテ百ヲ以テ整除シ得ヘキモノノ中更ニ四ヲ以テ商ヲ整除シ得サル年ハ平年トス
-/

@[expose] public section

namespace Ritsuryo

structure Date where
  year : Int
  month : Nat
  day : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

structure YearMonth where
  year : Int
  month : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Date

@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def isLeapYear (y : Int) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- 閏年ニ関スル件の文言をそのまま写した閏年の判定。年は神武天皇即位紀元（西暦 + 660）で数える。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def IsLeapYearSpec (y : Int) : Prop :=
  let kigen := y + 660
  kigen % 4 = 0 ∧ ¬((kigen - 660) % 100 = 0 ∧ ((kigen - 660) / 100) % 4 ≠ 0)

@[ritsuryo_basis "改暦ノ布告" "本則", ritsuryo_basis "閏年ニ関スル件" "本則"]
def daysInMonth (y : Int) : Nat → Nat
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

@[ritsuryo_basis "改暦ノ布告" "本則"]
def Valid (d : Date) : Prop :=
  1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧ d.day ≤ daysInMonth d.year d.month

instance (d : Date) : Decidable d.Valid := by
  unfold Valid
  infer_instance

@[ritsuryo_basis "改暦ノ布告" "本則"]
def nextDate (d : Date) : Date :=
  if d.day < daysInMonth d.year d.month then
    { d with day := d.day + 1 }
  else if d.month < 12 then
    ⟨d.year, d.month + 1, 1⟩
  else
    ⟨d.year + 1, 1, 1⟩

@[ritsuryo_basis "改暦ノ布告" "本則"]
def prevDate (d : Date) : Date :=
  if 1 < d.day then
    { d with day := d.day - 1 }
  else if 1 < d.month then
    ⟨d.year, d.month - 1, daysInMonth d.year (d.month - 1)⟩
  else
    ⟨d.year - 1, 12, 31⟩

@[ritsuryo_basis "改暦ノ布告" "本則"]
def addDaysNaive (d : Date) : Nat → Date
  | 0 => d
  | n + 1 => addDaysNaive (nextDate d) n

@[ritsuryo_basis "改暦ノ布告" "本則"]
def Lt (a b : Date) : Prop :=
  a.year < b.year ∨ (a.year = b.year ∧ (a.month < b.month ∨ (a.month = b.month ∧ a.day < b.day)))

instance : LT Date := ⟨Lt⟩

instance (a b : Date) : Decidable (a < b) := by
  change Decidable (Lt a b)
  unfold Lt
  infer_instance

@[ritsuryo_basis "改暦ノ布告" "本則"]
def yearMonth (d : Date) : YearMonth :=
  ⟨d.year, d.month⟩

end Date

namespace YearMonth

@[ritsuryo_basis "改暦ノ布告" "本則"]
def next (ym : YearMonth) : YearMonth :=
  if ym.month < 12 then ⟨ym.year, ym.month + 1⟩ else ⟨ym.year + 1, 1⟩

@[ritsuryo_basis "改暦ノ布告" "本則"]
def addMonthsNaive (ym : YearMonth) : Nat → YearMonth
  | 0 => ym
  | n + 1 => addMonthsNaive ym.next n

@[ritsuryo_basis "改暦ノ布告" "本則"]
def index (ym : YearMonth) : Int :=
  ym.year * 12 + ((ym.month : Int) - 1)

@[ritsuryo_basis "改暦ノ布告" "本則"]
def ofIndex (k : Int) : YearMonth :=
  ⟨k / 12, (k % 12).toNat + 1⟩

@[ritsuryo_basis "改暦ノ布告" "本則"]
def addMonths (ym : YearMonth) (n : Nat) : YearMonth :=
  ofIndex (ym.index + n)

@[ritsuryo_basis "改暦ノ布告" "本則"]
def daysInMonth (ym : YearMonth) : Nat :=
  Date.daysInMonth ym.year ym.month

@[ritsuryo_basis "改暦ノ布告" "本則"]
def lastDay (ym : YearMonth) : Date :=
  ⟨ym.year, ym.month, ym.daysInMonth⟩

@[ritsuryo_basis "改暦ノ布告" "本則"]
def firstDay (ym : YearMonth) : Date :=
  ⟨ym.year, ym.month, 1⟩

end YearMonth

end Ritsuryo
