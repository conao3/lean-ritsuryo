module

public import Ritsuryo.Holiday.Lookup
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Holiday

theorem isRestDayAt_pred (H : Int → Bool) (z : Int) (h : isRestDayAt H z = true) :
    H (z - 1) = true := by
  simp only [isRestDayAt, isSubstituteAt, isCitizensAt, isSubstitute, isCitizens,
    Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨_, h⟩ := h
      cases k : H (z - 1) with
      | true => rfl
      | false => simp [sundayRun, k] at h
    · simp only [Bool.and_eq_true] at h
      exact h.1.2
  · split at h
    · simp only [Bool.and_eq_true] at h
      exact h.1.2
    · simp only [Bool.and_eq_true] at h
      exact h.1.1.2.1.2

theorem checkAll :
    (List.range (Data.lastYear - Data.firstYear + 1).toNat).all
      (fun i => checkYear (Data.firstYear + i)) = true := by
  decide +kernel

@[ritsuryo_proof "HOL-C1", ritsuryo_basis "国民の祝日に関する法律" "第3条第2項",
  ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
theorem holc1_csv_rest_days (y : Int) (h1 : Data.firstYear ≤ y) (h2 : y ≤ Data.lastYear)
    (z : Int) :
    isRestDayAt (fun x => (nationalDays y).contains x) z = true ↔ z ∈ restDays y := by
  have hc : checkYear y = true := by
    have := checkAll
    rw [List.all_eq_true] at this
    have := this (y - Data.firstYear).toNat (by rw [List.mem_range]; omega)
    rwa [show Data.firstYear + (((y - Data.firstYear).toNat : Nat) : Int) = y by omega] at this
  simp only [checkYear, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hc
  obtain ⟨hrest, hnat⟩ := hc
  constructor
  · intro hz
    have hp := isRestDayAt_pred _ z hz
    have hmem : z - 1 ∈ nationalDays y := by simpa using hp
    have := hnat (z - 1) hmem
    rw [show z - 1 + 1 = z by omega, hz] at this
    simpa using this.symm
  · intro hz
    exact hrest z hz

end Ritsuryo.Holiday
