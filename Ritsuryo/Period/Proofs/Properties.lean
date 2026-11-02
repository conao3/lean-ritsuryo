module

public import Ritsuryo.Period.Proofs.Civil
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Period

open Date

theorem months_formula (s : Date) (n : Nat) :
    expiryFromStartDays s (.months n) =
      if s.day ≤ (s.yearMonth.addMonths n).daysInMonth then
        toDays (s.yearMonth.addMonths n).firstDay + s.day - 2
      else
        toDays (s.yearMonth.addMonths n).firstDay + (s.yearMonth.addMonths n).daysInMonth - 1 := by
  unfold expiryFromStartDays correspondingDays lastMonth
  by_cases hd : s.day ≤ (s.yearMonth.addMonths n).daysInMonth
  · simp only [hd, ↓reduceIte]
    rw [toDays_day ⟨_, _, s.day⟩]
    simp only [YearMonth.firstDay]
    omega
  · simp only [hd, ↓reduceIte]
    rw [toDays_lastDay]

theorem months_bounds (s : Date) (h : s.Valid) (n : Nat) :
    toDays (s.yearMonth.addMonths n).firstDay - 1 ≤ expiryFromStartDays s (.months n) ∧
      expiryFromStartDays s (.months n) ≤
        toDays (s.yearMonth.addMonths n).firstDay + (s.yearMonth.addMonths n).daysInMonth - 1 := by
  rw [months_formula]
  have := h.2.2.1
  split <;> omega

theorem firstDay_addMonths_lt (ym : YearMonth) (a b : Nat) (hab : a < b) :
    toDays (ym.addMonths a).firstDay + (ym.addMonths a).daysInMonth ≤
      toDays (ym.addMonths b).firstDay := by
  simp only [YearMonth.addMonths]
  exact firstDay_ofIndex_lt _ _ (by omega)

theorem months_mono_length (s : Date) (h : s.Valid) (a b : Nat) (hab : a ≤ b) :
    expiryFromStartDays s (.months a) ≤ expiryFromStartDays s (.months b) := by
  by_cases he : a = b
  · subst he
    omega
  · have hl := firstDay_addMonths_lt s.yearMonth a b (by omega)
    have ha := months_bounds s h a
    have hb := months_bounds s h b
    omega

theorem index_le_of_toDays_le (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) : s1.yearMonth.index ≤ s2.yearMonth.index := by
  by_cases hi : s2.yearMonth.index < s1.yearMonth.index
  · exfalso
    have hl := firstDay_ofIndex_lt _ _ hi
    rw [YearMonth.ofIndex_index s1.yearMonth h1.1 h1.2.1,
      YearMonth.ofIndex_index s2.yearMonth h2.1 h2.2.1] at hl
    have hd1 := toDays_day s1
    have hd2 := toDays_day s2
    simp only [yearMonth, YearMonth.firstDay, YearMonth.daysInMonth] at hl
    have := h1.2.2.1
    have := h2.2.2.2
    omega
  · omega

theorem months_mono_start (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) (n : Nat) :
    expiryFromStartDays s1 (.months n) ≤ expiryFromStartDays s2 (.months n) := by
  have hi := index_le_of_toDays_le s1 s2 h1 h2 h
  by_cases he : s1.yearMonth.index = s2.yearMonth.index
  · have hym : s1.yearMonth = s2.yearMonth := by
      rw [← YearMonth.ofIndex_index s1.yearMonth h1.1 h1.2.1,
        ← YearMonth.ofIndex_index s2.yearMonth h2.1 h2.2.1, he]
    have hd1 := toDays_day s1
    have hd2 := toDays_day s2
    have hy : s1.year = s2.year := congrArg YearMonth.year hym
    have hm : s1.month = s2.month := congrArg YearMonth.month hym
    have hday : s1.day ≤ s2.day := by
      rw [hy, hm] at hd1
      omega
    rw [months_formula, months_formula, hym]
    split <;> split <;> omega
  · have hlt : s1.yearMonth.index + n < s2.yearMonth.index + n := by omega
    have hl := firstDay_ofIndex_lt _ _ hlt
    have ha := months_bounds s1 h1 n
    have hb := months_bounds s2 h2 n
    simp only [YearMonth.addMonths] at ha hb
    omega

theorem expiryFromStart_mono_start (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) (len : Length) :
    expiryFromStartDays s1 len ≤ expiryFromStartDays s2 len := by
  cases len with
  | days n => simp only [expiryFromStartDays, correspondingDays]; omega
  | weeks n => simp only [expiryFromStartDays, correspondingDays]; omega
  | months n => exact months_mono_start s1 s2 h1 h2 h n
  | years n => exact months_mono_start s1 s2 h1 h2 h (12 * n)

@[ritsuryo_proof "PER-2", ritsuryo_basis "民法" "第143条第1項",
  ritsuryo_basis "民法" "第143条第2項"]
theorem per2_from_beginning (start : Date) (h : start.Valid) (n : Nat) (hn : 1 ≤ n) :
    (start.day = 1 →
      Civil.expiryFromStartSpec start (.months n) =
        (start.yearMonth.addMonthsNaive (n - 1)).lastDay) ∧
    (start.month = 1 → start.day = 1 →
      Civil.expiryFromStartSpec start (.years n) = ⟨start.year + n - 1, 12, 31⟩) ∧
    (start.weekday = .sunday →
      (Civil.expiryFromStartSpec start (.weeks n)).weekday = .saturday ∧
        toDays (Civil.expiryFromStartSpec start (.weeks n)) = toDays start + 7 * n - 1) := by
  refine ⟨fun hd => ?_, fun hm hd => ?_, fun hw => ?_⟩
  · rw [← expiryFromStart_spec start h, months_formula]
    have hb := daysInMonth_ge (start.yearMonth.addMonths n).year
      (start.yearMonth.addMonths n).month (YearMonth.addMonths_valid start.yearMonth n).1
      (YearMonth.addMonths_valid start.yearMonth n).2
    have hle : start.day ≤ (start.yearMonth.addMonths n).daysInMonth := by
      simp only [YearMonth.daysInMonth]
      omega
    simp only [hle, ↓reduceIte]
    have hv := YearMonth.addMonths_valid start.yearMonth (n - 1)
    have key : toDays (start.yearMonth.addMonths n).firstDay =
        toDays (start.yearMonth.addMonths (n - 1)).lastDay + 1 := by
      rw [toDays_lastDay_next _ hv.1 hv.2, YearMonth.addMonths_next,
        show n - 1 + 1 = n by omega]
    rw [key, hd, YearMonth.addMonthsNaive_eq _ h.1 h.2.1]
    rw [show toDays (start.yearMonth.addMonths (n - 1)).lastDay + 1 + ((1 : Nat) : Int) - 2 =
      toDays (start.yearMonth.addMonths (n - 1)).lastDay by omega]
    exact ofDays_toDays _ (lastDay_valid _ hv.1 hv.2)
  · simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, Civil.lastMonthSpec, hm, hd,
      YearMonth.daysInMonth, daysInMonth]
    simp only [show (1 : Nat) ≤ 31 by decide, ↓reduceIte, prevDate]
    simp only [Nat.lt_irrefl, ↓reduceIte]
  · rw [← expiryFromStart_spec start h]
    have hs : (toDays start + 4) % 7 = 0 := by
      have := Weekday.ofIndex_inj ((toDays start + 4) % 7).toNat 0 (by omega) (by decide) hw
      omega
    simp only [expiryFromStartDays, correspondingDays]
    refine ⟨?_, (toDays_ofDays _).1⟩
    simp only [weekday, (toDays_ofDays _).1, Weekday.ofDays]
    rw [show ((toDays start + 7 * n - 1 + 4) % 7).toNat = 6 by omega]
    rfl

@[ritsuryo_proof "PER-3", ritsuryo_basis "民法" "第143条第2項"]
theorem per3_weeks_years (start : Date) (h : start.Valid) (n : Nat) :
    Civil.expiryFromStartSpec start (.weeks n) = Civil.expiryFromStartSpec start (.days (7 * n)) ∧
      Civil.expiryFromStartSpec start (.years n) =
        Civil.expiryFromStartSpec start (.months (12 * n)) := by
  refine ⟨?_, ?_⟩
  · simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, weekCorresponding_eq start h]
  · have hy := lastMonth_eq start h (.years n)
    have hm := lastMonth_eq start h (.months (12 * n))
    have : Civil.lastMonthSpec start (.years n) = Civil.lastMonthSpec start (.months (12 * n)) := by
      rw [← hy, ← hm]
      rfl
    simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, this]

@[ritsuryo_basis "民法" "第143条第2項"]
theorem per4_not_additive :
    Civil.expiryFromStartSpec
        (nextDate (Civil.expiryFromStartSpec ⟨2025, 1, 31⟩ (.months 1))) (.months 1) =
      ⟨2025, 3, 31⟩ ∧
    Civil.expiryFromStartSpec ⟨2025, 1, 31⟩ (.months 2) = ⟨2025, 3, 30⟩ := by
  decide

theorem firstDay_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ym.firstDay.Valid := by
  have := daysInMonth_ge ym.year ym.month h1 h2
  exact ⟨h1, h2, by simp [YearMonth.firstDay], by simp only [YearMonth.firstDay]; omega⟩

theorem next_month_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    1 ≤ ym.next.month ∧ ym.next.month ≤ 12 := by
  simp only [YearMonth.next]
  split <;> simp <;> omega

theorem spec_toDays (s : Date) (h : s.Valid) (len : Length) :
    toDays (Civil.expiryFromStartSpec s len) = expiryFromStartDays s len := by
  rw [← expiryFromStart_spec s h, (toDays_ofDays _).1]

theorem spec_valid (s : Date) (h : s.Valid) (len : Length) :
    (Civil.expiryFromStartSpec s len).Valid := by
  rw [← expiryFromStart_spec s h]
  exact (toDays_ofDays _).2

@[ritsuryo_proof "PER-4", ritsuryo_basis "民法" "第143条第2項"]
theorem per4_bound (s : Date) (h : s.Valid) (a b : Nat) :
    0 ≤ toDays (Civil.expiryFromStartSpec
          (nextDate (Civil.expiryFromStartSpec s (.months a))) (.months b)) -
        toDays (Civil.expiryFromStartSpec s (.months (a + b))) ∧
      toDays (Civil.expiryFromStartSpec
          (nextDate (Civil.expiryFromStartSpec s (.months a))) (.months b)) -
        toDays (Civil.expiryFromStartSpec s (.months (a + b))) ≤ 3 := by
  have hv1 := spec_valid s h (.months a)
  have hs2 := (toDays_nextDate _ hv1).2
  rw [spec_toDays _ hs2, spec_toDays s h, nextDate_eq_ofDays _ hv1, spec_toDays s h]
  rw [nextDate_eq_ofDays _ hv1, spec_toDays s h] at hs2
  have hym1 := YearMonth.addMonths_valid s.yearMonth a
  have hym2 := YearMonth.addMonths_valid s.yearMonth (a + b)
  have hb1 := daysInMonth_ge (s.yearMonth.addMonths a).year _ hym1.1 hym1.2
  have hb2 := daysInMonth_ge (s.yearMonth.addMonths (a + b)).year _ hym2.1 hym2.2
  rw [months_formula s a]
  by_cases hd : s.day ≤ (s.yearMonth.addMonths a).daysInMonth
  · simp only [hd, ↓reduceIte] at hs2 ⊢
    have he : toDays (s.yearMonth.addMonths a).firstDay + s.day - 2 + 1 =
        toDays ⟨(s.yearMonth.addMonths a).year, (s.yearMonth.addMonths a).month, s.day⟩ := by
      rw [toDays_day ⟨_, _, s.day⟩]
      simp only [YearMonth.firstDay]
      omega
    rw [he, ofDays_toDays _ (valid_of_le _ hym1.1 hym1.2 _ h.2.2.1 hd)]
    rw [months_formula, months_formula s (a + b)]
    have hym : (⟨(s.yearMonth.addMonths a).year, (s.yearMonth.addMonths a).month, s.day⟩ :
        Date).yearMonth = s.yearMonth.addMonths a := rfl
    simp only [hym, YearMonth.addMonths_add]
    split <;> omega
  · simp only [hd, ↓reduceIte] at hs2 ⊢
    rw [show toDays (s.yearMonth.addMonths a).firstDay +
        ((s.yearMonth.addMonths a).daysInMonth : Int) - 1 + 1 =
        toDays (s.yearMonth.addMonths a).next.firstDay by
      rw [toDays_firstDay_next _ hym1.1 hym1.2]
      omega]
    have hn := next_month_valid _ hym1.1 hym1.2
    rw [ofDays_toDays _ (firstDay_valid _ hn.1 hn.2), months_formula, months_formula s (a + b)]
    have hym : (s.yearMonth.addMonths a).next.firstDay.yearMonth = (s.yearMonth.addMonths a).next :=
      rfl
    have hday : (s.yearMonth.addMonths a).next.firstDay.day = 1 := rfl
    rw [hym, hday, YearMonth.next_addMonths _ hym1.1 hym1.2, YearMonth.addMonths_add,
      show a + (b + 1) = a + b + 1 by omega, ← YearMonth.addMonths_next]
    have hn2 := next_month_valid _ hym2.1 hym2.2
    have hb3 := daysInMonth_ge (s.yearMonth.addMonths (a + b)).next.year _ hn2.1 hn2.2
    have hf := toDays_firstDay_next _ hym2.1 hym2.2
    simp only [YearMonth.daysInMonth] at hd hf ⊢
    have h1le : 1 ≤ daysInMonth (s.yearMonth.addMonths (a + b)).next.year
        (s.yearMonth.addMonths (a + b)).next.month := by omega
    simp only [h1le, ↓reduceIte]
    by_cases hd2 : s.day ≤ daysInMonth (s.yearMonth.addMonths (a + b)).year
        (s.yearMonth.addMonths (a + b)).month
    · simp only [hd2, ↓reduceIte]
      omega
    · simp only [hd2, ↓reduceIte]
      omega

@[ritsuryo_proof "PER-5", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per5_monotone (e1 e2 : Date) (startAtMidnight : Bool) :
    (toDays e1 ≤ toDays e2 → ∀ len,
      toDays (compute e1 startAtMidnight len).expiry ≤
        toDays (compute e2 startAtMidnight len).expiry) ∧
    (∀ a b : Nat, a ≤ b →
      toDays (compute e1 startAtMidnight (.days a)).expiry ≤
          toDays (compute e1 startAtMidnight (.days b)).expiry ∧
        toDays (compute e1 startAtMidnight (.weeks a)).expiry ≤
          toDays (compute e1 startAtMidnight (.weeks b)).expiry ∧
        toDays (compute e1 startAtMidnight (.months a)).expiry ≤
          toDays (compute e1 startAtMidnight (.months b)).expiry ∧
        toDays (compute e1 startAtMidnight (.years a)).expiry ≤
          toDays (compute e1 startAtMidnight (.years b)).expiry) := by
  have hs1 := toDays_ofDays (startDays e1 startAtMidnight)
  have hs2 := toDays_ofDays (startDays e2 startAtMidnight)
  simp only [compute, (toDays_ofDays _).1]
  refine ⟨fun hle len => ?_, fun a b hab => ?_⟩
  · apply expiryFromStart_mono_start _ _ hs1.2 hs2.2
    rw [hs1.1, hs2.1]
    cases startAtMidnight <;> simp only [startDays, Bool.false_eq_true, ↓reduceIte] <;> omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [expiryFromStartDays, correspondingDays]
      omega
    · simp only [expiryFromStartDays, correspondingDays]
      omega
    · exact months_mono_length _ hs1.2 a b hab
    · exact months_mono_length _ hs1.2 (12 * a) (12 * b) (by omega)

@[ritsuryo_proof "PER-6", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per6_months_from_event (event : Date) (h : event.Valid) (n : Nat) :
    (compute event false (.months n)).expiry =
      if event.day = daysInMonth event.year event.month then
        (event.yearMonth.addMonths n).lastDay
      else
        ⟨(event.yearMonth.addMonths n).year, (event.yearMonth.addMonths n).month,
          min event.day (event.yearMonth.addMonths n).daysInMonth⟩ := by
  have hT := YearMonth.addMonths_valid event.yearMonth n
  have hbT := daysInMonth_ge (event.yearMonth.addMonths n).year _ hT.1 hT.2
  obtain ⟨e1, e2, e3, e4⟩ := h
  simp only [compute, startDays, Bool.false_eq_true, ↓reduceIte]
  by_cases hlast : event.day = daysInMonth event.year event.month
  · simp only [hlast, ↓reduceIte]
    have hl : toDays event = toDays event.yearMonth.lastDay := by
      rw [toDays_day event]
      rw [toDays_day event.yearMonth.lastDay]
      simp only [yearMonth, YearMonth.lastDay, YearMonth.daysInMonth]
      omega
    have hn := next_month_valid event.yearMonth e1 e2
    rw [hl, toDays_lastDay_next _ e1 e2, ofDays_toDays _ (firstDay_valid _ hn.1 hn.2),
      months_formula]
    have hym : event.yearMonth.next.firstDay.yearMonth = event.yearMonth.next := rfl
    have hday : event.yearMonth.next.firstDay.day = 1 := rfl
    rw [hym, hday, YearMonth.next_addMonths _ e1 e2, ← YearMonth.addMonths_next]
    have hn2 := next_month_valid _ hT.1 hT.2
    have hb3 := daysInMonth_ge (event.yearMonth.addMonths n).next.year _ hn2.1 hn2.2
    have h1le : 1 ≤ (event.yearMonth.addMonths n).next.daysInMonth := by
      simp only [YearMonth.daysInMonth]
      omega
    simp only [h1le, ↓reduceIte]
    rw [← toDays_lastDay_next _ hT.1 hT.2,
      show toDays (event.yearMonth.addMonths n).lastDay + 1 + ((1 : Nat) : Int) - 2 =
        toDays (event.yearMonth.addMonths n).lastDay by omega]
    exact ofDays_toDays _ (lastDay_valid _ hT.1 hT.2)
  · simp only [hlast, ↓reduceIte]
    have hlt : event.day < daysInMonth event.year event.month := by omega
    have hnext : ofDays (toDays event + 1) = ⟨event.year, event.month, event.day + 1⟩ := by
      rw [← nextDate_eq_ofDays event ⟨e1, e2, e3, e4⟩]
      simp only [nextDate, hlt, ↓reduceIte]
    rw [hnext, months_formula]
    have hym : (⟨event.year, event.month, event.day + 1⟩ : Date).yearMonth = event.yearMonth := rfl
    simp only [hym]
    split
    · rename_i hd
      have he : toDays (event.yearMonth.addMonths n).firstDay + ((event.day + 1 : Nat) : Int) - 2 =
          toDays ⟨(event.yearMonth.addMonths n).year, (event.yearMonth.addMonths n).month,
            event.day⟩ := by
        rw [toDays_day ⟨_, _, event.day⟩]
        simp only [YearMonth.firstDay]
        omega
      have hmin : min event.day (event.yearMonth.addMonths n).daysInMonth = event.day := by
        omega
      rw [he, hmin]
      exact ofDays_toDays _ (valid_of_le _ hT.1 hT.2 _ e3 (by omega))
    · rename_i hd
      have hmin : min event.day (event.yearMonth.addMonths n).daysInMonth =
          (event.yearMonth.addMonths n).daysInMonth := by
        omega
      rw [hmin, ← toDays_lastDay]
      exact ofDays_toDays _ (lastDay_valid _ hT.1 hT.2)

theorem taxGeneral_fromStart (start : Date) (len : TaxLength) :
    TaxGeneral.expiryFromStartSpec start len = Civil.expiryFromStartSpec start len.toLength := by
  cases len with
  | days n => rfl
  | months n =>
    simp only [TaxGeneral.expiryFromStartSpec, Civil.expiryFromStartSpec,
      Civil.correspondingDaySpec, Civil.lastMonthSpec, TaxLength.toLength]
    by_cases hd : start.day ≤ (start.yearMonth.addMonthsNaive n).daysInMonth <;> simp [hd]
  | years n =>
    simp only [TaxGeneral.expiryFromStartSpec, Civil.expiryFromStartSpec,
      Civil.correspondingDaySpec, Civil.lastMonthSpec, TaxLength.toLength]
    by_cases hd : start.day ≤ (⟨start.year + n, start.month⟩ : YearMonth).daysInMonth <;> simp [hd]

@[ritsuryo_proof "PER-7", ritsuryo_basis "国税通則法" "第10条第1項"]
theorem per7_national_tax_general (event : Date) (h : event.Valid) (startAtMidnight : Bool)
    (len : TaxLength) :
    TaxGeneral.expirySpec event startAtMidnight len =
        Civil.expirySpec event startAtMidnight len.toLength ∧
      (computeTax event startAtMidnight len).expiry =
        TaxGeneral.expirySpec event startAtMidnight len := by
  have heq : TaxGeneral.expirySpec event startAtMidnight len =
      Civil.expirySpec event startAtMidnight len.toLength := by
    simp only [TaxGeneral.expirySpec, Civil.expirySpec, taxGeneral_fromStart]
    rfl
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (per1_compute_eq_spec event h startAtMidnight len.toLength).2.2

end Ritsuryo.Period
