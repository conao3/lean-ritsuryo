module

public import Ritsuryo.Period.Impl

/-!
# 期間の証明で使う暦の補題

期間の仕様は日付を 1 日ずつ・1 か月ずつ進める素朴な定義（`Date.addDaysNaive`、`YearMonth.addMonthsNaive`）で書き、
実装は通算日（`toDays`）と年月の通し番号（`YearMonth.addMonths`）で計算する。このファイルは、両者を行き来するための
暦の補題を置く。

- `addDaysNaive_toDays`・`addDaysNaive_eq_ofDays`: `n` 日進めた日は通算日に `n` を足した日になる。
- `valid_of_le`・`lastDay_valid`: 年月と日から作った日付、月の末日が有効な日付になる。
- `toDays_lastDay`・`toDays_lastDay_next`: 月の末日の通算日と、その翌日が翌月の1日になること。
- `YearMonth.addMonths_*`: 通し番号で月を進める計算の性質（`12 * n` か月は `n` 年、足し算でまとめられる、翌月との入れ替え）。
-/

public section

namespace Ritsuryo.Date

/-- 有効な日付 `d` から `n` 日進めた日の通算日は `toDays d + n` で、その日も有効な日付になる。`n` についての帰納法で、
1 日進めると通算日が 1 増えること（`toDays_nextDate`）を `n` 回使う。 -/
theorem addDaysNaive_toDays (d : Date) (h : d.Valid) (n : Nat) :
    toDays (d.addDaysNaive n) = toDays d + n ∧ (d.addDaysNaive n).Valid := by
  induction n generalizing d with
  | zero => exact ⟨by simp [addDaysNaive], h⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := toDays_nextDate d h
    obtain ⟨h3, h4⟩ := ih (nextDate d) h2
    refine ⟨?_, h4⟩
    simp only [addDaysNaive, h3, h1]
    omega

/-- 有効な日付 `d` から `n` 日進めた日は、通算日 `toDays d + n` を日付に戻した日と等しい。 -/
theorem addDaysNaive_eq_ofDays (d : Date) (h : d.Valid) (n : Nat) :
    d.addDaysNaive n = ofDays (toDays d + n) := by
  obtain ⟨h1, h2⟩ := addDaysNaive_toDays d h n
  rw [← h1, ofDays_toDays _ h2]

/-- 月が 1〜12 で、日が 1 以上その月の日数以下なら、その年月日は有効な日付になる。 -/
theorem valid_of_le (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (day : Nat)
    (h3 : 1 ≤ day) (h4 : day ≤ ym.daysInMonth) : (⟨ym.year, ym.month, day⟩ : Date).Valid :=
  ⟨h1, h2, h3, h4⟩

/-- 月が 1〜12 なら、その月の末日は有効な日付になる。 -/
theorem lastDay_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ym.lastDay.Valid := by
  have := daysInMonth_ge ym.year ym.month h1 h2
  exact ⟨h1, h2, by simp only [YearMonth.lastDay, YearMonth.daysInMonth]; omega, by
    simp [YearMonth.lastDay, YearMonth.daysInMonth]⟩

/-- 月の末日の通算日は、その月の1日の通算日に月の日数を足して 1 を引いたものになる。 -/
theorem toDays_lastDay (ym : YearMonth) :
    toDays ym.lastDay = toDays ym.firstDay + ym.daysInMonth - 1 := by
  rw [toDays_day ym.lastDay]
  rfl

/-- 月の末日の翌日（通算日に 1 を足した日）は、翌月の1日になる。 -/
theorem toDays_lastDay_next (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.lastDay + 1 = toDays ym.next.firstDay := by
  rw [toDays_lastDay, toDays_firstDay_next ym h1 h2]
  omega

end Ritsuryo.Date

namespace Ritsuryo.YearMonth

/-- 通し番号で月を進めた結果の月は、常に 1〜12 になる。 -/
theorem addMonths_valid (ym : YearMonth) (n : Nat) :
    1 ≤ (ym.addMonths n).month ∧ (ym.addMonths n).month ≤ 12 :=
  ofIndex_valid _

/-- `12 * n` か月後は、`n` 年後の同じ月になる。実装の年の期間（`12 * n` か月）と仕様の年の期間（`n` 年後の同じ月）をつなぐ。 -/
theorem addMonths_years (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.addMonths (12 * n) = ⟨ym.year + n, ym.month⟩ := by
  obtain ⟨y, m⟩ := ym
  simp only at h1 h2
  simp only [addMonths, ofIndex, index, mk.injEq]
  omega

/-- `a` か月進めてから `b` か月進めると、`a + b` か月進めたのと同じになる。 -/
theorem addMonths_add (ym : YearMonth) (a b : Nat) :
    (ym.addMonths a).addMonths b = ym.addMonths (a + b) := by
  simp only [addMonths, index_ofIndex]
  congr 1
  omega

/-- `n` か月後の翌月は、`n + 1` か月後になる。 -/
theorem addMonths_next (ym : YearMonth) (n : Nat) :
    (ym.addMonths n).next = ym.addMonths (n + 1) := by
  simp only [addMonths, next_ofIndex]
  congr 1
  omega

/-- 翌月から `n` か月後は、もとの月から `n + 1` か月後になる。 -/
theorem next_addMonths (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.next.addMonths n = ym.addMonths (n + 1) := by
  rw [← ofIndex_index ym h1 h2, next_ofIndex]
  simp only [addMonths, index_ofIndex]
  congr 1
  omega

end Ritsuryo.YearMonth
