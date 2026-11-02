module

public import Ritsuryo.Calendar.Days
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Date

theorem yearStart_decomp (c q r : Int) (hq : 0 ≤ q ∧ q ≤ 24) (hr : 0 ≤ r ∧ r ≤ 3) :
    yearStart (100 * c + 4 * q + r) = 36524 * c + 1461 * q + 365 * r := by
  have h4 : (100 * c + 4 * q + r) / 4 = 25 * c + q := by omega
  have h100 : (100 * c + 4 * q + r) / 100 = c := by omega
  simp only [yearStart, h4, h100]
  omega

theorem decomp_bounds (doe : Int) (h0 : 0 ≤ doe) (h1 : doe ≤ 146096) :
    (0 ≤ centOf doe ∧ centOf doe ≤ 3) ∧ (0 ≤ quadOf doe ∧ quadOf doe ≤ 24) ∧
    (0 ≤ yrOf doe ∧ yrOf doe ≤ 3) ∧
    0 ≤ doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) ∧
    (doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) ≤ 364 ∨
     (doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) = 365 ∧
      yrOf doe = 3 ∧ (quadOf doe ≠ 24 ∨ centOf doe = 3))) := by
  have hc : 0 ≤ centOf doe ∧ centOf doe ≤ 3 ∧ 0 ≤ doe - 36524 * centOf doe ∧
      (doe - 36524 * centOf doe ≤ 36523 ∨ (centOf doe = 3 ∧ doe = 146096)) := by
    simp only [centOf]
    omega
  simp only [quadOf, yrOf]
  generalize centOf doe = c at *
  omega

theorem yoeOf_spec (doe : Int) (h0 : 0 ≤ doe) (h1 : doe ≤ 146096) :
    0 ≤ yoeOf doe ∧ yoeOf doe ≤ 399 ∧ yearStart (yoeOf doe) ≤ doe ∧
    (doe - yearStart (yoeOf doe) ≤ 364 ∨
      (doe - yearStart (yoeOf doe) = 365 ∧ yoeOf doe % 4 = 3 ∧
        (yoeOf doe % 100 ≠ 99 ∨ yoeOf doe = 399))) := by
  have h := decomp_bounds doe h0 h1
  simp only [yoeOf]
  rw [yearStart_decomp _ _ _ h.2.1 h.2.2.1]
  omega

theorem yoeOf_yearStart (yoe doy : Int) (h0 : 0 ≤ yoe) (h1 : yoe ≤ 399) (h2 : 0 ≤ doy)
    (h3 : doy ≤ 364 ∨ (doy = 365 ∧ yoe % 4 = 3 ∧ (yoe % 100 ≠ 99 ∨ yoe = 399))) :
    yoeOf (yearStart yoe + doy) = yoe := by
  have hy : yoe = 100 * (yoe / 100) + 4 * (yoe % 100 / 4) + yoe % 4 := by omega
  have hs := yearStart_decomp (yoe / 100) (yoe % 100 / 4) (yoe % 4) (by omega) (by omega)
  rw [← hy] at hs
  rw [hs]
  have hb : 0 ≤ yoe / 100 ∧ yoe / 100 ≤ 3 ∧ 0 ≤ yoe % 100 / 4 ∧ yoe % 100 / 4 ≤ 24 ∧
      0 ≤ yoe % 4 ∧ yoe % 4 ≤ 3 := by omega
  have hl : doy = 365 → yoe % 4 = 3 ∧ (yoe % 100 / 4 ≠ 24 ∨ yoe / 100 = 3) := by omega
  have hd : doy ≤ 365 := by omega
  clear h3
  generalize yoe / 100 = c at *
  generalize yoe % 100 / 4 = q at *
  generalize hr : yoe % 4 = r at *
  have hc : centOf (36524 * c + 1461 * q + 365 * r + doy) = c := by
    simp only [centOf]
    omega
  have hq : quadOf (36524 * c + 1461 * q + 365 * r + doy) = q := by
    simp only [quadOf, hc]
    omega
  have hm : (36524 * c + 1461 * q + 365 * r + doy - 36524 * c) % 1461 = 365 * r + doy := by
    omega
  have hr' : yrOf (36524 * c + 1461 * q + 365 * r + doy) = r := by
    simp only [yrOf, hc, hm]
    omega
  simp only [yoeOf, hc, hq, hr']
  omega

theorem monthOf_spec (doy : Int) (h0 : 0 ≤ doy) (h1 : doy ≤ 365) :
    0 ≤ monthOf doy ∧ monthOf doy ≤ 11 ∧ monthStart (monthOf doy) ≤ doy ∧
      doy < monthStart (monthOf doy + 1) := by
  simp only [monthOf, monthStart]
  omega

theorem monthOf_monthStart (mp k : Int) (h2 : 0 ≤ k)
    (h3 : k < monthStart (mp + 1) - monthStart mp) : monthOf (monthStart mp + k) = mp := by
  simp only [monthOf, monthStart] at *
  omega

theorem isLeapYear_iff (y : Int) :
    isLeapYear y = true ↔ y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) := by
  simp [isLeapYear]

theorem marchYearStart_succ (y : Int) :
    marchYearStart (y + 1) =
      marchYearStart y + 365 + (if isLeapYear (y + 1) then 1 else 0) := by
  simp only [marchYearStart, yearStart]
  by_cases h : y % 400 = 399
  · have h1 : (y + 1) / 400 = y / 400 + 1 := by omega
    have h2 : (y + 1) % 400 = 0 := by omega
    have h3 : isLeapYear (y + 1) = true := by
      rw [isLeapYear_iff]
      omega
    rw [h1, h2, h]
    simp only [h3, ↓reduceIte]
    omega
  · have h1 : (y + 1) / 400 = y / 400 := by omega
    have h2 : (y + 1) % 400 = y % 400 + 1 := by omega
    rw [h1, h2]
    split
    · rename_i hl
      rw [isLeapYear_iff] at hl
      omega
    · rename_i hl
      rw [isLeapYear_iff] at hl
      omega

end Ritsuryo.Date
