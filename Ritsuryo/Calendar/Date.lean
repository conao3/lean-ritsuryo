module

meta import Ritsuryo.Basis

/-!
# 暦

明治五年太政官布告第三百三十七号（改暦ノ布告）により太陽暦を用いる。閏年は明治三十一年勅令第九十号
（閏年ニ関スル件、e-Gov 法令履歴 `131IO0000000090_18980511_000000000000000`）による。

> 神武天皇即位紀元年数ノ四ヲ以テ整除シ得ヘキ年ヲ閏年トス但シ紀元年数ヨリ六百六十ヲ減シテ百ヲ以テ整除シ得ヘキモノノ中更ニ四ヲ以テ商ヲ整除シ得サル年ハ平年トス

このファイルは、年月日の組 `Date` と年月の組 `YearMonth` を定め、暦の上で 1 日・1 月ずつ進む操作を
条文と見比べやすい素朴な形で書く。

- 閏年: `IsLeapYearSpec` が勅令の文言（皇紀の年数で判定する）をそのまま写した仕様で、`isLeapYear` が
  西暦で書いた実装になる。皇紀の年数は西暦に 660 を足した数なので、両者は同じ年を閏年とする（CAL-6）。
- 月の日数: `daysInMonth` が大の月・小の月と 2 月（閏年なら 29 日）を定める。
- 1 日ずつの移動: `nextDate`・`prevDate` は月末・年末で繰り上がる素朴な翌日・前日で、
  `addDaysNaive` はそれを `n` 回繰り返す。期間計算の仕様（`Ritsuryo.Period.Spec`）はこれらで日を数える。
- 1 月ずつの移動: `YearMonth.next`・`YearMonth.addMonthsNaive` が素朴な翌月で、`YearMonth.addMonths` は
  年月を通し番号（`index`、年 × 12 + 月 − 1）にして足し算する実装になる。

年は `Int` で持ち、紀元前（0 年や負の年）を含む先発グレゴリオ暦として扱う。
日付から日数への変換（`Ritsuryo.Calendar.Days`）と、素朴な操作がその日数で 1 ずつ動くことの証明
（`Ritsuryo.Calendar.Proofs`）は別のファイルに置く。
-/

@[expose] public section

namespace Ritsuryo

/-- 年月日の組。`year` は西暦の年、`month` は 1〜12、`day` は 1 から月の日数まで。
範囲外の値も型の上では作れるので、実在する日付であることは `Date.Valid` で別に述べる。 -/
structure Date where
  year : Int
  month : Nat
  day : Nat
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- 年と月の組。民法第143条の「月」による期間計算で、月単位に進めるときに使う。 -/
structure YearMonth where
  year : Int
  month : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Date

/-- 実装: 西暦 `y` 年が閏年かどうか。4 で割り切れ、かつ 100 で割り切れないか 400 で割り切れる年を閏年とする。
`%` は `Int` の剰余（除数が正なら 0 以上）なので、負の年にもそのまま当てはまる。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def isLeapYear (y : Int) : Bool :=
  y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- 神武天皇即位紀元年数ノ四ヲ以テ整除シ得ヘキ年ヲ閏年トス但シ紀元年数ヨリ六百六十ヲ減シテ百ヲ以テ整除シ得ヘキモノノ中更ニ四ヲ以テ商ヲ整除シ得サル年ハ平年トス

仕様: 勅令の文言どおり、西暦 `y` 年の紀元年数（皇紀）`y + 660` で判定する。紀元年数が 4 で割り切れる年を
閏年とし、そのうち紀元年数から 660 を引いた数（西暦の年）が 100 で割り切れ、その商が 4 で割り切れない年を
平年とする。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def IsLeapYearSpec (y : Int) : Prop :=
  let kigen := y + 660
  kigen % 4 = 0 ∧ ¬((kigen - 660) % 100 = 0 ∧ ((kigen - 660) / 100) % 4 ≠ 0)

/-- `y` 年 `m` 月の日数。1・3・5・7・8・10・12 月は 31 日、4・6・9・11 月は 30 日、2 月は閏年なら 29 日で
それ以外は 28 日。1〜12 以外の月は 0 日とする。 -/
@[ritsuryo_basis "改暦ノ布告" "本則", ritsuryo_basis "閏年ニ関スル件" "本則"]
def daysInMonth (y : Int) : Nat → Nat
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

/-- `d` が暦の上に実在する日付であること。月が 1〜12 で、日が 1 からその月の日数まで。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def Valid (d : Date) : Prop :=
  1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧ d.day ≤ daysInMonth d.year d.month

instance (d : Date) : Decidable d.Valid := by
  unfold Valid
  infer_instance

/-- 素朴な翌日。月末でなければ日を 1 進め、月末なら翌月 1 日、12 月 31 日なら翌年 1 月 1 日にする。
これが日数で 1 進むことは CAL-4 で証明する。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def nextDate (d : Date) : Date :=
  if d.day < daysInMonth d.year d.month then
    { d with day := d.day + 1 }
  else if d.month < 12 then
    ⟨d.year, d.month + 1, 1⟩
  else
    ⟨d.year + 1, 1, 1⟩

/-- 素朴な前日。1 日でなければ日を 1 戻し、1 日なら前月の末日、1 月 1 日なら前年 12 月 31 日にする。
民法第143条第2項の「その起算日に応当する日の前日」を取るのに使う。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def prevDate (d : Date) : Date :=
  if 1 < d.day then
    { d with day := d.day - 1 }
  else if 1 < d.month then
    ⟨d.year, d.month - 1, daysInMonth d.year (d.month - 1)⟩
  else
    ⟨d.year - 1, 12, 31⟩

/-- `d` から `n` 日後の日付を、`nextDate` を `n` 回繰り返して求める。暦を 1 日ずつめくる数え方そのもので、
期間計算の仕様が日を数えるのに使う。実装は日数の足し算（`ofDays (toDays d + n)`）で同じ日を求める。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def addDaysNaive (d : Date) : Nat → Date
  | 0 => d
  | n + 1 => addDaysNaive (nextDate d) n

/-- 日付の前後。年、月、日の順に比べる（辞書式順序）。日数の大小と一致することは CAL-3 で証明する。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def Lt (a b : Date) : Prop :=
  a.year < b.year ∨ (a.year = b.year ∧ (a.month < b.month ∨ (a.month = b.month ∧ a.day < b.day)))

instance : LT Date := ⟨Lt⟩

instance (a b : Date) : Decidable (a < b) := by
  change Decidable (Lt a b)
  unfold Lt
  infer_instance

/-- 日付の属する年月。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def yearMonth (d : Date) : YearMonth :=
  ⟨d.year, d.month⟩

end Date

namespace YearMonth

/-- 素朴な翌月。12 月でなければ月を 1 進め、12 月なら翌年 1 月にする。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def next (ym : YearMonth) : YearMonth :=
  if ym.month < 12 then ⟨ym.year, ym.month + 1⟩ else ⟨ym.year + 1, 1⟩

/-- `ym` から `n` 月後の年月を、`next` を `n` 回繰り返して求める。期間計算の仕様が月を数えるのに使う。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def addMonthsNaive (ym : YearMonth) : Nat → YearMonth
  | 0 => ym
  | n + 1 => addMonthsNaive ym.next n

/-- 年月の通し番号。西暦 0 年 1 月を 0 とし、1 月進むごとに 1 増える（年 × 12 + 月 − 1）。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def index (ym : YearMonth) : Int :=
  ym.year * 12 + ((ym.month : Int) - 1)

/-- 通し番号から年月に戻す。`Int` の除算と剰余は除数が正なら剰余が 0〜11 になるので、
負の番号（紀元前）でも月は 1〜12 に収まる。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def ofIndex (k : Int) : YearMonth :=
  ⟨k / 12, (k % 12).toNat + 1⟩

/-- 実装: `ym` から `n` 月後の年月を、通し番号に `n` を足して求める。`addMonthsNaive` と一致することは
`Ritsuryo.Calendar.Proofs` の `addMonthsNaive_eq` で証明する。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def addMonths (ym : YearMonth) (n : Nat) : YearMonth :=
  ofIndex (ym.index + n)

/-- その年月の日数。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def daysInMonth (ym : YearMonth) : Nat :=
  Date.daysInMonth ym.year ym.month

/-- その年月の末日。民法第143条第2項ただし書の「その月の末日」に当たる。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def lastDay (ym : YearMonth) : Date :=
  ⟨ym.year, ym.month, ym.daysInMonth⟩

/-- その年月の 1 日。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def firstDay (ym : YearMonth) : Date :=
  ⟨ym.year, ym.month, 1⟩

end YearMonth

end Ritsuryo
