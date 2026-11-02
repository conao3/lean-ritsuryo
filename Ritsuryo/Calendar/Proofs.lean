module

public import Ritsuryo.Calendar.Arith
public import Ritsuryo.Calendar.Weekday
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Date

theorem valid_month (d : Date) (h : d.Valid) :
    0 ≤ marchMonth d.month ∧ marchMonth d.month ≤ 11 ∧
      (if marchMonth d.month < 10 then marchMonth d.month + 3 else marchMonth d.month - 9) =
        (d.month : Int) ∧
      (marchMonth d.month < 10 ↔ 3 ≤ d.month) ∧
      monthOf (monthStart (marchMonth d.month) + d.day - 1) = marchMonth d.month ∧
      0 ≤ monthStart (marchMonth d.month) + d.day - 1 ∧
      (monthStart (marchMonth d.month) + d.day - 1 ≤ 364 ∨
        (monthStart (marchMonth d.month) + d.day - 1 = 365 ∧ d.month = 2 ∧
          isLeapYear d.year = true)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hm : d.month = 1 ∨ d.month = 2 ∨ d.month = 3 ∨ d.month = 4 ∨ d.month = 5 ∨
      d.month = 6 ∨ d.month = 7 ∨ d.month = 8 ∨ d.month = 9 ∨ d.month = 10 ∨
      d.month = 11 ∨ d.month = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    simp only [hm, daysInMonth] at h4 <;>
    simp only [hm, marchMonth, monthStart, monthOf] <;>
    try omega
  split at h4 <;> simp_all <;> omega

theorem ofDays_eq (z era yoe doy : Int) (hera : (z + 719468) / 146097 = era)
    (hdoe : (z + 719468) % 146097 = yearStart yoe + doy)
    (hyoe : yoeOf (yearStart yoe + doy) = yoe) :
    ofDays z =
      ⟨era * 400 + yoe + (if monthOf doy < 10 then 0 else 1),
        (if monthOf doy < 10 then monthOf doy + 3 else monthOf doy - 9).toNat,
        (doy - monthStart (monthOf doy) + 1).toNat⟩ := by
  simp only [ofDays, hera, hdoe, hyoe]
  have : yearStart yoe + doy - yearStart yoe = doy := by omega
  simp only [this]

theorem ofDays_toDays (d : Date) (h : d.Valid) : ofDays (toDays d) = d := by
  obtain ⟨hm0, hm1, hmonth, hlt, hmo, hdoy0, hdoy1⟩ := valid_month d h
  have hy : marchYear d = if d.month ≤ 2 then d.year - 1 else d.year := rfl
  generalize hmp : marchMonth d.month = mp at *
  generalize hdoy : monthStart mp + d.day - 1 = doy at *
  have hys : 0 ≤ yearStart (marchYear d % 400) ∧
      yearStart (marchYear d % 400) + 365 ≤ 146096 := by
    simp only [yearStart]
    omega
  have hcond : doy ≤ 364 ∨
      (doy = 365 ∧ marchYear d % 400 % 4 = 3 ∧
        (marchYear d % 400 % 100 ≠ 99 ∨ marchYear d % 400 = 399)) := by
    rcases hdoy1 with h' | ⟨h365, hfeb, hl⟩
    · exact Or.inl h'
    · have hl := (isLeapYear_iff d.year).mp hl
      have hmy : marchYear d = d.year - 1 := by
        rw [hy]
        simp [hfeb]
      right
      rw [hmy]
      omega
  have hz : toDays d + 719468 =
      marchYear d / 400 * 146097 + (yearStart (marchYear d % 400) + doy) := by
    simp only [toDays, marchYearStart, hmp]
    omega
  have hera : (toDays d + 719468) / 146097 = marchYear d / 400 := by
    rw [hz]
    omega
  have hdoe : (toDays d + 719468) % 146097 = yearStart (marchYear d % 400) + doy := by
    rw [hz]
    omega
  have hyoe := yoeOf_yearStart (marchYear d % 400) doy (by omega) (by omega) hdoy0 hcond
  rw [ofDays_eq _ _ _ _ hera hdoe hyoe, hmo]
  have hY : marchYear d / 400 * 400 + marchYear d % 400 + (if mp < 10 then 0 else 1) =
      d.year := by
    rw [hy]
    split <;> split <;> omega
  have hM : (if mp < 10 then mp + 3 else mp - 9).toNat = d.month := by
    rw [hmonth]
    omega
  have hD : (doy - monthStart mp + 1).toNat = d.day := by
    omega
  rw [hY, hM, hD]

theorem marchMonth_inv (y : Int) (mp : Int) (h0 : 0 ≤ mp) (h1 : mp ≤ 11) :
    1 ≤ (if mp < 10 then mp + 3 else mp - 9) ∧ (if mp < 10 then mp + 3 else mp - 9) ≤ 12 ∧
      marchMonth (if mp < 10 then mp + 3 else mp - 9).toNat = mp ∧
      ((if mp < 10 then mp + 3 else mp - 9).toNat ≤ 2 ↔ ¬mp < 10) ∧
      (mp ≠ 11 → monthStart (mp + 1) - monthStart mp =
        daysInMonth y (if mp < 10 then mp + 3 else mp - 9).toNat) ∧
      (mp = 11 → monthStart mp = 337 ∧
        daysInMonth y (if mp < 10 then mp + 3 else mp - 9).toNat =
          if isLeapYear y then 29 else 28) ∧
      monthStart mp = (153 * mp + 2) / 5 := by
  have hm : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨ mp = 6 ∨ mp = 7 ∨
      mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;> simp [marchMonth, monthStart, daysInMonth]

theorem toDays_ofDays (z : Int) : toDays (ofDays z) = z ∧ (ofDays z).Valid := by
  generalize hera : (z + 719468) / 146097 = era
  generalize hdoe' : (z + 719468) % 146097 = doe
  have hz : z + 719468 = era * 146097 + doe := by omega
  have hdoeb : 0 ≤ doe ∧ doe ≤ 146096 := by omega
  obtain ⟨hy0, hy1, hys, hcond⟩ := yoeOf_spec doe hdoeb.1 hdoeb.2
  generalize hyoe : yoeOf doe = yoe at *
  generalize hdoy : doe - yearStart yoe = doy at *
  have hdoe : (z + 719468) % 146097 = yearStart yoe + doy := by omega
  have hyoe' : yoeOf (yearStart yoe + doy) = yoe := by
    have : yearStart yoe + doy = doe := by omega
    rw [this, hyoe]
  rw [ofDays_eq z era yoe doy hera hdoe hyoe']
  have hdoy365 : doy ≤ 365 := by omega
  obtain ⟨hmp0, hmp1, hms, hms'⟩ := monthOf_spec doy (by omega) hdoy365
  generalize hmp : monthOf doy = mp at *
  have hY : era * 400 + yoe + (if mp < 10 then 0 else 1) =
      (if mp < 10 then 0 else 1) + (era * 400 + yoe) := by omega
  obtain ⟨hM1, hM2, hmm, hle, hlen, hfeb, _⟩ :=
    marchMonth_inv (era * 400 + yoe + (if mp < 10 then 0 else 1)) mp hmp0 hmp1
  generalize hM : (if mp < 10 then mp + 3 else mp - 9) = M at *
  have hmy : marchYear ⟨era * 400 + yoe + (if mp < 10 then 0 else 1), M.toNat,
      (doy - monthStart mp + 1).toNat⟩ = era * 400 + yoe := by
    simp only [marchYear]
    split <;> split <;> omega
  have hmys : marchYearStart (era * 400 + yoe) = era * 146097 + yearStart yoe := by
    simp only [marchYearStart]
    have h1 : (era * 400 + yoe) / 400 = era := by omega
    have h2 : (era * 400 + yoe) % 400 = yoe := by omega
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · simp only [toDays, hmy, hmys, hmm]
    omega
  · dsimp only [Valid]
    refine ⟨by omega, by omega, by omega, ?_⟩
    by_cases h11 : mp = 11
    · subst h11
      obtain ⟨hl337, hdim⟩ := hfeb rfl
      have h10 : ¬((11 : Int) < 10) := by decide
      simp only [h10, ↓reduceIte] at hdim ⊢
      rw [hdim]
      split
      · omega
      · rename_i hnl
        rcases hcond with hc | ⟨h365, hc4, hc100⟩
        · omega
        · exfalso
          apply hnl
          rw [isLeapYear_iff]
          omega
    · have := hlen h11
      omega

theorem toDays_day (d : Date) : toDays d = toDays ⟨d.year, d.month, 1⟩ + d.day - 1 := by
  simp only [toDays, marchYear]
  omega

theorem daysInMonth_ge (y : Int) (m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    28 ≤ daysInMonth y m ∧ daysInMonth y m ≤ 31 := by
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;> simp only [daysInMonth] <;> (try split) <;> omega

theorem toDays_firstDay_next (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.next.firstDay = toDays ym.firstDay + ym.daysInMonth := by
  obtain ⟨y, m⟩ := ym
  simp only at h1 h2
  have hstep := marchYearStart_succ (y - 1)
  have hy : y - 1 + 1 = y := by omega
  rw [hy] at hstep
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;>
    simp only [YearMonth.next, YearMonth.firstDay, YearMonth.daysInMonth, toDays, marchYear,
      marchMonth, monthStart, daysInMonth] <;>
    simp <;>
    (try split) <;>
    simp_all <;>
    omega

theorem toDays_nextDate (d : Date) (h : d.Valid) :
    toDays (nextDate d) = toDays d + 1 ∧ (nextDate d).Valid := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hday := toDays_day d
  have hfirst := toDays_firstDay_next ⟨d.year, d.month⟩ h1 h2
  simp only [YearMonth.firstDay, YearMonth.daysInMonth, YearMonth.next] at hfirst
  unfold nextDate
  by_cases hlt : d.day < daysInMonth d.year d.month
  · simp only [hlt, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [toDays_day { d with day := d.day + 1 }]
      simp only
      omega
    · simp only [Valid]
      omega
  · simp only [hlt, ↓reduceIte]
    by_cases hm : d.month < 12
    · simp only [hm, ↓reduceIte] at hfirst ⊢
      have := daysInMonth_ge d.year (d.month + 1) (by omega) (by omega)
      refine ⟨by omega, ?_⟩
      simp only [Valid]
      omega
    · simp only [hm, ↓reduceIte] at hfirst ⊢
      refine ⟨by omega, ?_⟩
      simp only [Valid, daysInMonth]
      omega

theorem toDays_prevDate (d : Date) (h : d.Valid) :
    toDays (prevDate d) = toDays d - 1 ∧ (prevDate d).Valid := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hday := toDays_day d
  unfold prevDate
  by_cases hd : 1 < d.day
  · simp only [hd, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [toDays_day { d with day := d.day - 1 }]
      simp only
      omega
    · simp only [Valid]
      omega
  · simp only [hd, ↓reduceIte]
    by_cases hm : 1 < d.month
    · simp only [hm, ↓reduceIte]
      have hf := toDays_firstDay_next ⟨d.year, d.month - 1⟩ (by simp only; omega)
        (by simp only; omega)
      have hn : (⟨d.year, d.month - 1⟩ : YearMonth).next = ⟨d.year, d.month⟩ := by
        have h12 : d.month - 1 < 12 := by omega
        simp only [YearMonth.next, h12, ↓reduceIte]
        congr 1
        omega
      rw [hn] at hf
      simp only [YearMonth.firstDay, YearMonth.daysInMonth] at hf
      have hb := daysInMonth_ge d.year (d.month - 1) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [toDays_day ⟨d.year, d.month - 1, daysInMonth d.year (d.month - 1)⟩]
        simp only
        omega
      · simp only [Valid]
        omega
    · simp only [hm, ↓reduceIte]
      have hf := toDays_firstDay_next ⟨d.year - 1, 12⟩ (by simp) (by simp)
      have hn : (⟨d.year - 1, 12⟩ : YearMonth).next = ⟨d.year, 1⟩ := by
        simp [YearMonth.next]
      rw [hn] at hf
      simp only [YearMonth.firstDay, YearMonth.daysInMonth, daysInMonth] at hf
      have hm1 : d.month = 1 := by omega
      have hd1 : d.day = 1 := by omega
      refine ⟨?_, ?_⟩
      · rw [toDays_day ⟨d.year - 1, 12, 31⟩]
        simp only
        rw [hday, hm1, hd1]
        omega
      · simp only [Valid, daysInMonth]
        omega

theorem nextDate_eq_ofDays (d : Date) (h : d.Valid) : nextDate d = ofDays (toDays d + 1) := by
  obtain ⟨he, hv⟩ := toDays_nextDate d h
  rw [← he, ofDays_toDays _ hv]

theorem prevDate_eq_ofDays (d : Date) (h : d.Valid) : prevDate d = ofDays (toDays d - 1) := by
  obtain ⟨he, hv⟩ := toDays_prevDate d h
  rw [← he, ofDays_toDays _ hv]
end Ritsuryo.Date

namespace Ritsuryo.YearMonth

theorem ofIndex_index (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ofIndex ym.index = ym := by
  obtain ⟨y, m⟩ := ym
  simp only [ofIndex, index, mk.injEq] at *
  omega

theorem ofIndex_valid (k : Int) : 1 ≤ (ofIndex k).month ∧ (ofIndex k).month ≤ 12 := by
  simp only [ofIndex]
  omega

theorem index_ofIndex (k : Int) : (ofIndex k).index = k := by
  simp only [ofIndex, index]
  omega

theorem next_ofIndex (k : Int) : (ofIndex k).next = ofIndex (k + 1) := by
  simp only [ofIndex, next]
  by_cases h : (k % 12).toNat + 1 < 12
  · simp only [h, ↓reduceIte, mk.injEq]
    omega
  · simp only [h, ↓reduceIte, mk.injEq]
    omega

theorem addMonthsNaive_eq (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.addMonthsNaive n = ym.addMonths n := by
  induction n generalizing ym with
  | zero => simp [addMonthsNaive, addMonths, ofIndex_index ym h1 h2]
  | succ n ih =>
    simp only [addMonthsNaive]
    have hv := ofIndex_valid (ym.index + 1)
    rw [← ofIndex_index ym h1 h2, next_ofIndex, ih _ hv.1 hv.2]
    simp only [addMonths, index_ofIndex, ofIndex_index ym h1 h2]
    congr 1
    omega

end Ritsuryo.YearMonth

namespace Ritsuryo.Date

open YearMonth

theorem firstDay_ofIndex_succ (k : Int) :
    toDays (ofIndex (k + 1)).firstDay = toDays (ofIndex k).firstDay + (ofIndex k).daysInMonth := by
  have hv := ofIndex_valid k
  rw [← next_ofIndex, toDays_firstDay_next _ hv.1 hv.2]

theorem firstDay_ofIndex_add (k : Int) (n : Nat) :
    toDays (ofIndex k).firstDay + 28 * n ≤ toDays (ofIndex (k + n)).firstDay := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := firstDay_ofIndex_succ (k + n)
    have hv := ofIndex_valid (k + n)
    have hb := daysInMonth_ge (ofIndex (k + n)).year (ofIndex (k + n)).month hv.1 hv.2
    simp only [YearMonth.daysInMonth] at h
    have : k + ((n + 1 : Nat) : Int) = k + n + 1 := by omega
    rw [this]
    omega

theorem firstDay_ofIndex_lt (i j : Int) (h : i < j) :
    toDays (ofIndex i).firstDay + (ofIndex i).daysInMonth ≤ toDays (ofIndex j).firstDay := by
  have h1 := firstDay_ofIndex_succ i
  have h2 := firstDay_ofIndex_add (i + 1) (j - (i + 1)).toNat
  have : i + 1 + ((j - (i + 1)).toNat : Int) = j := by omega
  rw [this] at h2
  omega

theorem lt_of_toDays_lt (a b : Date) (ha : a.Valid) (hb : b.Valid) (h : a < b) :
    a.toDays < b.toDays := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  rw [toDays_day a, toDays_day b]
  change Lt a b at h
  simp only [Lt] at h
  by_cases hym : a.yearMonth.index < b.yearMonth.index
  · have hl := firstDay_ofIndex_lt _ _ hym
    rw [ofIndex_index _ a1 a2, ofIndex_index _ b1 b2] at hl
    simp only [yearMonth, YearMonth.daysInMonth, YearMonth.firstDay] at hl
    omega
  · have hy : a.year = b.year := by
      simp only [yearMonth, index] at hym
      omega
    have hm : a.month = b.month := by
      simp only [yearMonth, index] at hym
      omega
    rw [hy, hm]
    omega

theorem toDays_lt_iff (a b : Date) (ha : a.Valid) (hb : b.Valid) :
    a < b ↔ a.toDays < b.toDays := by
  refine ⟨lt_of_toDays_lt a b ha hb, fun h => ?_⟩
  by_cases hab : a < b
  · exact hab
  · exfalso
    have : b < a ∨ a = b := by
      change ¬Lt a b at hab
      change Lt b a ∨ a = b
      simp only [Lt] at *
      by_cases he : a = b
      · exact Or.inr he
      · left
        obtain ⟨ay, am, ad⟩ := a
        obtain ⟨by', bm, bd⟩ := b
        simp only [Date.mk.injEq] at *
        omega
    rcases this with hlt | heq
    · have := lt_of_toDays_lt b a hb ha hlt
      omega
    · subst heq
      omega

theorem toDays_inj (a b : Date) (ha : a.Valid) (hb : b.Valid) (h : a.toDays = b.toDays) :
    a = b := by
  rw [← ofDays_toDays a ha, ← ofDays_toDays b hb, h]

end Ritsuryo.Date

namespace Ritsuryo.Weekday

theorem ofDays_succ (z : Int) : ofDays (z + 1) = (ofDays z).next := by
  simp only [ofDays]
  have h : (z + 4) % 7 = 0 ∨ (z + 4) % 7 = 1 ∨ (z + 4) % 7 = 2 ∨ (z + 4) % 7 = 3 ∨
      (z + 4) % 7 = 4 ∨ (z + 4) % 7 = 5 ∨ (z + 4) % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;>
    rw [h, show (z + 1 + 4) % 7 = ((z + 4) % 7 + 1) % 7 by omega, h] <;> rfl

end Ritsuryo.Weekday

namespace Ritsuryo.Date

theorem weekday_eq (d : Date) : d.weekday = Weekday.ofIndex ((d.toDays + 4) % 7).toNat := rfl

theorem weekday_nextDate (d : Date) (h : d.Valid) : (nextDate d).weekday = d.weekday.next := by
  simp only [weekday, (toDays_nextDate d h).1, Weekday.ofDays_succ]

theorem isLeapYear_iff_spec (y : Int) : isLeapYear y = true ↔ IsLeapYearSpec y := by
  rw [isLeapYear_iff]
  simp only [IsLeapYearSpec]
  omega

theorem toDays_newYear_succ (y : Int) :
    toDays ⟨y + 1, 1, 1⟩ - toDays ⟨y, 1, 1⟩ = if isLeapYear y then 366 else 365 := by
  have h := marchYearStart_succ (y - 1)
  have hy : y - 1 + 1 = y := by omega
  rw [hy] at h
  simp only [toDays, marchYear, marchMonth, monthStart]
  simp only [show (1 : Nat) ≤ 2 by decide, ↓reduceIte, show y + 1 - 1 = y by omega]
  by_cases hl : isLeapYear y = true
  · simp only [hl, ↓reduceIte] at h ⊢
    omega
  · simp only [hl] at h ⊢
    simp at h ⊢
    omega

end Ritsuryo.Date

namespace Ritsuryo.Date

@[ritsuryo_proof "CAL-1", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal1_ofDays_toDays (d : Date) (h : d.Valid) : ofDays (toDays d) = d :=
  ofDays_toDays d h

@[ritsuryo_proof "CAL-2", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal2_toDays_ofDays (z : Int) : toDays (ofDays z) = z ∧ (ofDays z).Valid :=
  toDays_ofDays z

@[ritsuryo_proof "CAL-3", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal3_lt_iff (a b : Date) (ha : a.Valid) (hb : b.Valid) :
    a < b ↔ a.toDays < b.toDays :=
  toDays_lt_iff a b ha hb

@[ritsuryo_proof "CAL-4", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal4_nextDate (d : Date) (h : d.Valid) :
    nextDate d = ofDays (toDays d + 1) ∧ (nextDate d).Valid :=
  ⟨nextDate_eq_ofDays d h, (toDays_nextDate d h).2⟩

@[ritsuryo_proof "CAL-5", ritsuryo_basis "民法" "第142条"]
theorem cal5_weekday (d : Date) (h : d.Valid) :
    d.weekday = Weekday.ofIndex ((d.toDays + 4) % 7).toNat ∧
      (nextDate d).weekday = d.weekday.next :=
  ⟨weekday_eq d, weekday_nextDate d h⟩

@[ritsuryo_proof "CAL-6", ritsuryo_basis "閏年ニ関スル件" "本則"]
theorem cal6_daysInMonth (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.next.firstDay - toDays ym.firstDay = ym.daysInMonth ∧
      (ym.month = 2 → (ym.daysInMonth = 29 ↔ IsLeapYearSpec ym.year)) := by
  refine ⟨by rw [toDays_firstDay_next ym h1 h2]; omega, fun hm => ?_⟩
  rw [← isLeapYear_iff_spec]
  simp only [YearMonth.daysInMonth, hm, daysInMonth]
  split <;> simp_all

end Ritsuryo.Date
