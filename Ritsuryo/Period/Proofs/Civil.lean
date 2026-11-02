module

public import Ritsuryo.Period.Proofs.Lemmas
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Weekday

theorem ofIndex_inj (a b : Nat) (ha : a < 7) (hb : b < 7) (h : ofIndex a = ofIndex b) :
    a = b := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by omega
  rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' | hb' | hb' | hb' | hb' <;>
    subst ha' hb' <;> simp_all [ofIndex]

theorem ofDays_eq_iff (a b : Int) : ofDays a = ofDays b ↔ a % 7 = b % 7 := by
  simp only [ofDays]
  constructor
  · intro h
    have := ofIndex_inj _ _ (by omega) (by omega) h
    omega
  · intro h
    have : (a + 4) % 7 = (b + 4) % 7 := by omega
    rw [this]

end Ritsuryo.Weekday

namespace Ritsuryo.Period

open Date

theorem weekday_addDaysNaive (d : Date) (h : d.Valid) (k : Nat) :
    (d.addDaysNaive k).weekday = Weekday.ofDays (toDays d + k) := by
  simp only [weekday, (addDaysNaive_toDays d h k).1]

theorem nextDate_addDaysNaive (d : Date) (h : d.Valid) (k : Nat) :
    nextDate (d.addDaysNaive k) = d.addDaysNaive (k + 1) := by
  obtain ⟨_, hv⟩ := addDaysNaive_toDays d h k
  rw [nextDate_eq_ofDays _ hv, addDaysNaive_eq_ofDays d h, addDaysNaive_eq_ofDays d h,
    (toDays_ofDays _).1]
  congr 1
  omega

theorem sameWeekdayAfter_eq (d : Date) (h : d.Valid) (fuel k : Nat) (hk1 : 1 ≤ k) (hk7 : k ≤ 7)
    (hf : fuel + k = 8) :
    Civil.sameWeekdayAfterSpec d fuel (d.addDaysNaive k) = d.addDaysNaive 7 := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    simp only [Civil.sameWeekdayAfterSpec]
    by_cases h7 : k = 7
    · subst h7
      have : (d.addDaysNaive 7).weekday = d.weekday := by
        rw [weekday_addDaysNaive d h, weekday, Weekday.ofDays_eq_iff]
        omega
      simp [this]
    · have : ¬(d.addDaysNaive k).weekday = d.weekday := by
        rw [weekday_addDaysNaive d h, weekday, Weekday.ofDays_eq_iff]
        omega
      simp only [this, ↓reduceIte]
      rw [nextDate_addDaysNaive d h]
      exact ih (k + 1) (by omega) (by omega) (by omega)

theorem weekCorresponding_eq (start : Date) (h : start.Valid) (n : Nat) :
    Civil.weekCorrespondingSpec start n = start.addDaysNaive (7 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Civil.weekCorrespondingSpec, ih]
    obtain ⟨_, hv⟩ := addDaysNaive_toDays start h (7 * n)
    have hs := sameWeekdayAfter_eq _ hv 7 1 (by omega) (by omega) (by omega)
    have h1 : (start.addDaysNaive (7 * n)).addDaysNaive 1 =
        nextDate (start.addDaysNaive (7 * n)) := rfl
    rw [← h1, hs, addDaysNaive_eq_ofDays _ hv, addDaysNaive_eq_ofDays _ h,
      addDaysNaive_eq_ofDays _ h, (toDays_ofDays _).1]
    congr 1
    omega

theorem lastMonth_eq (start : Date) (h : start.Valid) (len : Length) :
    lastMonth start len = Civil.lastMonthSpec start len := by
  obtain ⟨h1, h2, _, _⟩ := h
  cases len with
  | days n => rfl
  | weeks n => rfl
  | months n =>
    simp only [lastMonth, Civil.lastMonthSpec]
    rw [YearMonth.addMonthsNaive_eq _ h1 h2]
  | years n =>
    simp only [lastMonth, Civil.lastMonthSpec]
    exact YearMonth.addMonths_years _ h1 h2 n

theorem lastMonth_valid (start : Date) (h : start.Valid) (len : Length) :
    1 ≤ (lastMonth start len).month ∧ (lastMonth start len).month ≤ 12 := by
  obtain ⟨h1, h2, _, _⟩ := h
  cases len with
  | days n => exact ⟨h1, h2⟩
  | weeks n => exact ⟨h1, h2⟩
  | months n => exact YearMonth.addMonths_valid _ _
  | years n => exact YearMonth.addMonths_valid _ _

theorem correspondingDays_spec (start : Date) (h : start.Valid) (len : Length) :
    (correspondingDays start len).map ofDays = Civil.correspondingDaySpec start len := by
  have hlm := lastMonth_eq start h len
  have hv := lastMonth_valid start h len
  cases len with
  | days n =>
    simp [correspondingDays, Civil.correspondingDaySpec, addDaysNaive_eq_ofDays start h]
  | weeks n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, weekCorresponding_eq start h,
      addDaysNaive_eq_ofDays start h, Option.map_some]
    congr 2
  | months n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, ← hlm]
    split
    · rename_i hd
      simp only [Option.map_some]
      rw [ofDays_toDays _ (valid_of_le _ hv.1 hv.2 _ h.2.2.1 hd)]
    · rfl
  | years n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, ← hlm]
    split
    · rename_i hd
      simp only [Option.map_some]
      rw [ofDays_toDays _ (valid_of_le _ hv.1 hv.2 _ h.2.2.1 hd)]
    · rfl

theorem expiryFromStart_spec (start : Date) (h : start.Valid) (len : Length) :
    ofDays (expiryFromStartDays start len) = Civil.expiryFromStartSpec start len := by
  have hc := correspondingDays_spec start h len
  unfold expiryFromStartDays Civil.expiryFromStartSpec
  rw [← hc]
  cases hcd : correspondingDays start len with
  | some c =>
    simp only [Option.map_some]
    rw [prevDate_eq_ofDays _ (toDays_ofDays c).2, (toDays_ofDays c).1]
  | none =>
    simp only [Option.map_none]
    have hv := lastMonth_valid start h len
    rw [ofDays_toDays _ (lastDay_valid _ hv.1 hv.2), lastMonth_eq start h len]

theorem start_spec (event : Date) (h : event.Valid) (startAtMidnight : Bool) :
    ofDays (startDays event startAtMidnight) = Civil.startDateSpec event startAtMidnight ∧
      (Civil.startDateSpec event startAtMidnight).Valid := by
  cases startAtMidnight with
  | true => exact ⟨ofDays_toDays event h, h⟩
  | false =>
    simp only [startDays, Civil.startDateSpec, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(nextDate_eq_ofDays event h).symm, (toDays_nextDate event h).2⟩

@[ritsuryo_proof "PER-1", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per1_compute_eq_spec (event : Date) (h : event.Valid) (startAtMidnight : Bool)
    (len : Length) :
    (compute event startAtMidnight len).start = Civil.startDateSpec event startAtMidnight ∧
      (compute event startAtMidnight len).corresponding =
        Civil.correspondingDaySpec (Civil.startDateSpec event startAtMidnight) len ∧
      (compute event startAtMidnight len).expiry = Civil.expirySpec event startAtMidnight len := by
  obtain ⟨hs, hv⟩ := start_spec event h startAtMidnight
  simp only [compute, Civil.expirySpec]
  rw [hs]
  exact ⟨rfl, correspondingDays_spec _ hv len, expiryFromStart_spec _ hv len⟩

end Ritsuryo.Period
