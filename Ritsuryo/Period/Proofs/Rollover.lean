module

public import Ritsuryo.Period.Rollover
public import Ritsuryo.Period.Proofs.Lemmas
meta import Ritsuryo.Basis

public section

namespace Ritsuryo.Period

open Date

theorem rolloverDays_spec (H : Int → Bool) (fuel : Nat) (z z' : Int)
    (h : rolloverDays H fuel z = some z') :
    z ≤ z' ∧ H z' = false ∧ ∀ x, z ≤ x → x < z' → H x = true := by
  induction fuel generalizing z with
  | zero => simp [rolloverDays] at h
  | succ fuel ih =>
    simp only [rolloverDays] at h
    split at h
    · rename_i hz
      obtain ⟨h1, h2, h3⟩ := ih (z + 1) h
      refine ⟨by omega, h2, fun x hx1 hx2 => ?_⟩
      by_cases hx : x = z
      · subst hx
        exact hz
      · exact h3 x (by omega) hx2
    · rename_i hz
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨Int.le_refl _, by simpa using hz, fun x hx1 hx2 => by omega⟩

@[ritsuryo_proof "ROL-1", ritsuryo_basis "民法" "第142条",
  ritsuryo_basis "民事訴訟法" "第95条第3項", ritsuryo_basis "国税通則法" "第10条第2項"]
theorem rol1_least_non_holiday (H : Date → Bool) (fuel : Nat) (d d' : Date)
    (h : rollover H fuel d = some d') :
    toDays d ≤ toDays d' ∧ H d' = false ∧ d'.Valid ∧
      ∀ x : Date, x.Valid → toDays d ≤ toDays x → toDays x < toDays d' → H x = true := by
  simp only [rollover, Option.map_eq_some_iff] at h
  obtain ⟨z', hz, he⟩ := h
  subst he
  obtain ⟨h1, h2, h3⟩ := rolloverDays_spec _ fuel _ _ hz
  refine ⟨by rw [(toDays_ofDays z').1]; exact h1, h2, (toDays_ofDays z').2, fun x hx a b => ?_⟩
  rw [(toDays_ofDays z').1] at b
  have := h3 (toDays x) a b
  rwa [ofDays_toDays x hx] at this

theorem rolloverDays_of_not_holiday (H : Int → Bool) (fuel : Nat) (z : Int) (h : H z = false) :
    rolloverDays H (fuel + 1) z = some z := by
  simp [rolloverDays, h]

@[ritsuryo_proof "ROL-2", ritsuryo_basis "民法" "第142条",
  ritsuryo_basis "民事訴訟法" "第95条第3項", ritsuryo_basis "国税通則法" "第10条第2項"]
theorem rol2_idempotent_monotone (H : Int → Bool) (fuel : Nat) :
    (∀ z z', rolloverDays H fuel z = some z' → ∀ fuel', rolloverDays H (fuel' + 1) z' = some z') ∧
    (∀ z1 z2 r1 r2, z1 ≤ z2 → rolloverDays H fuel z1 = some r1 →
      rolloverDays H fuel z2 = some r2 → r1 ≤ r2) ∧
    (∀ (H' : Int → Bool) z r r', (∀ x, H x = true → H' x = true) →
      rolloverDays H fuel z = some r → rolloverDays H' fuel z = some r' → r ≤ r') := by
  refine ⟨fun z z' h fuel' => ?_, fun z1 z2 r1 r2 hz h1 h2 => ?_, fun H' z r r' hsub h1 h2 => ?_⟩
  · exact rolloverDays_of_not_holiday H fuel' z' (rolloverDays_spec H fuel z z' h).2.1
  · obtain ⟨a1, a2, a3⟩ := rolloverDays_spec H fuel z1 r1 h1
    obtain ⟨b1, b2, b3⟩ := rolloverDays_spec H fuel z2 r2 h2
    by_cases hlt : r2 < r1
    · have := a3 r2 (by omega) hlt
      rw [this] at b2
      contradiction
    · omega
  · obtain ⟨a1, a2, a3⟩ := rolloverDays_spec H fuel z r h1
    obtain ⟨b1, b2, b3⟩ := rolloverDays_spec H' fuel z r' h2
    by_cases hlt : r' < r
    · have := hsub r' (a3 r' b1 hlt)
      rw [this] at b2
      contradiction
    · omega

@[ritsuryo_proof "ROL-3", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "国税通則法" "第10条第2項", ritsuryo_basis "国税通則法施行令" "第2条第2項"]
theorem rol3_procedure_vs_tax (national : Date → Bool) (d : Date) :
    TaxGeneral.isHolidaySpec national true d = CivilProcedure.isHolidaySpec national d ∧
      ∀ general : Bool, HolidayClass.holds national d .newYear = false →
        TaxGeneral.isHolidaySpec national general d = CivilProcedure.isHolidaySpec national d := by
  refine ⟨?_, fun general hny => ?_⟩
  · simp only [TaxGeneral.isHolidaySpec, CivilProcedure.isHolidaySpec, Bool.true_and]
    cases HolidayClass.holds national d .sunday <;>
      cases HolidayClass.holds national d .saturday <;>
      cases HolidayClass.holds national d .nationalHoliday <;>
      cases HolidayClass.holds national d .newYear <;>
      cases HolidayClass.holds national d .yearEnd <;> rfl
  · simp only [TaxGeneral.isHolidaySpec, CivilProcedure.isHolidaySpec, hny, Bool.and_false,
      Bool.or_false]
    cases HolidayClass.holds national d .sunday <;>
      cases HolidayClass.holds national d .saturday <;>
      cases HolidayClass.holds national d .nationalHoliday <;>
      cases HolidayClass.holds national d .yearEnd <;> rfl

end Ritsuryo.Period
