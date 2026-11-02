module

public import Ritsuryo.Period.Impl

public section

namespace Ritsuryo.Date

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

theorem addDaysNaive_eq_ofDays (d : Date) (h : d.Valid) (n : Nat) :
    d.addDaysNaive n = ofDays (toDays d + n) := by
  obtain ⟨h1, h2⟩ := addDaysNaive_toDays d h n
  rw [← h1, ofDays_toDays _ h2]

theorem valid_of_le (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (day : Nat)
    (h3 : 1 ≤ day) (h4 : day ≤ ym.daysInMonth) : (⟨ym.year, ym.month, day⟩ : Date).Valid :=
  ⟨h1, h2, h3, h4⟩

theorem lastDay_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ym.lastDay.Valid := by
  have := daysInMonth_ge ym.year ym.month h1 h2
  exact ⟨h1, h2, by simp only [YearMonth.lastDay, YearMonth.daysInMonth]; omega, by
    simp [YearMonth.lastDay, YearMonth.daysInMonth]⟩

theorem toDays_lastDay (ym : YearMonth) :
    toDays ym.lastDay = toDays ym.firstDay + ym.daysInMonth - 1 := by
  rw [toDays_day ym.lastDay]
  rfl

theorem toDays_lastDay_next (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.lastDay + 1 = toDays ym.next.firstDay := by
  rw [toDays_lastDay, toDays_firstDay_next ym h1 h2]
  omega

end Ritsuryo.Date

namespace Ritsuryo.YearMonth

theorem addMonths_valid (ym : YearMonth) (n : Nat) :
    1 ≤ (ym.addMonths n).month ∧ (ym.addMonths n).month ≤ 12 :=
  ofIndex_valid _

theorem addMonths_years (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.addMonths (12 * n) = ⟨ym.year + n, ym.month⟩ := by
  obtain ⟨y, m⟩ := ym
  simp only at h1 h2
  simp only [addMonths, ofIndex, index, mk.injEq]
  omega

theorem addMonths_add (ym : YearMonth) (a b : Nat) :
    (ym.addMonths a).addMonths b = ym.addMonths (a + b) := by
  simp only [addMonths, index_ofIndex]
  congr 1
  omega

theorem addMonths_next (ym : YearMonth) (n : Nat) :
    (ym.addMonths n).next = ym.addMonths (n + 1) := by
  simp only [addMonths, next_ofIndex]
  congr 1
  omega

theorem next_addMonths (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.next.addMonths n = ym.addMonths (n + 1) := by
  rw [← ofIndex_index ym h1 h2, next_ofIndex]
  simp only [addMonths, index_ofIndex]
  congr 1
  omega

end Ritsuryo.YearMonth
