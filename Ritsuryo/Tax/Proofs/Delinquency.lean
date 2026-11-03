module

public import Ritsuryo.Tax.Delinquency
meta import Ritsuryo.Basis

/-!
# 延滞税・利子税の証明（DEL-1、DEL-2）
-/

public section

namespace Ritsuryo.Tax.Delinquency

/-- 延滞税・利子税の割合の特例は本則を超えない（DEL-1）。どの特例基準割合でも、2月以内の割合は年7.3%以下、
その後の割合は年14.6%以下で、2月以内の割合はその後の割合以下。利子税の割合も年7.3%以下。 -/
@[ritsuryo_proof "DEL-1", ritsuryo_basis "国税通則法" "第60条第2項",
  ritsuryo_basis "租税特別措置法" "第94条第1項", ritsuryo_basis "租税特別措置法" "第93条第1項"]
theorem del1_special_rates_le (s : Nat) (y : Int) :
    lowerRate s ≤ 73 ∧ higherRate s ≤ 146 ∧ lowerRate s ≤ higherRate s ∧ interestRate y s ≤ 73 := by
  simp only [lowerRate, higherRate, interestRate]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> repeat' split
  all_goals omega

/-- 区間の並びの額（端数処理前、365,000 分の一円単位）。 -/
@[ritsuryo_basis "租税特別措置法" "第96条第2項"]
def segmentsRaw (base : Nat) (segs : List Segment) : Nat :=
  (segs.map fun s => base * s.rate * s.days).sum

theorem segmentsRaw_addDay (base : Nat) (segs : List Segment) (z : Int) (b : Bool) (r : Nat) :
    segmentsRaw base (addDay segs z b r) = segmentsRaw base segs + base * r := by
  unfold addDay
  split
  · rename_i s rest
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨-, hr⟩ := h
      simp only [segmentsRaw, List.map_cons, List.sum_cons, hr, Nat.mul_succ]
      omega
    · simp only [segmentsRaw, List.map_cons, List.sum_cons, Nat.mul_one]
      omega
  · simp [segmentsRaw]

theorem segmentsRaw_foldl (base : Nat) (bandAt : Int → Bool) (rateAt : Int → Nat) (start : Int)
    (n : Nat) (acc : List Segment) :
    segmentsRaw base ((List.range n).foldl
      (fun acc (i : Nat) => addDay acc (start + i) (bandAt (start + i)) (rateAt (start + i))) acc) =
      segmentsRaw base acc + rawSpec base rateAt start n := by
  induction n with
  | zero => simp [rawSpec]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, segmentsRaw_addDay, ih]
    simp only [rawSpec, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- 延滞税の端数処理前の額の性質（DEL-2）。
日ごとの合計（仕様）は期間を前後に分けると前と後の和になり（加法性）、税額と日数について単調。
区間に分けた計算の端数処理前の額は、日ごとの合計と一致する。 -/
@[ritsuryo_proof "DEL-2", ritsuryo_basis "国税通則法" "第60条第2項",
  ritsuryo_basis "利率等の表示の年利建て移行に関する法律" "第25条"]
theorem del2_additive_monotone (base base' : Nat) (rateAt : Int → Nat) (bandAt : Int → Bool)
    (start : Int) (n m : Nat) :
    rawSpec base rateAt start (n + m) =
        rawSpec base rateAt start n + rawSpec base rateAt (start + n) m ∧
      (base ≤ base' → rawSpec base rateAt start n ≤ rawSpec base' rateAt start n) ∧
      rawSpec base rateAt start n ≤ rawSpec base rateAt start (n + m) ∧
      segmentsRaw base (segments bandAt rateAt start n) = rawSpec base rateAt start n := by
  have hadd : rawSpec base rateAt start (n + m) =
      rawSpec base rateAt start n + rawSpec base rateAt (start + n) m := by
    simp only [rawSpec, List.range_add, List.map_append, List.sum_append, List.map_map]
    congr 2
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 2
    push_cast
    omega
  refine ⟨hadd, fun h => ?_, by omega, ?_⟩
  · simp only [rawSpec]
    induction (List.range n) with
    | nil => simp
    | cons i is ih =>
      simp only [List.map_cons, List.sum_cons]
      have := Nat.mul_le_mul_right (rateAt (start + i)) h
      omega
  · simp only [segments, segmentsRaw, List.map_reverse, List.sum_reverse_nat]
    have := segmentsRaw_foldl base bandAt rateAt start n []
    simpa [segmentsRaw] using this

end Ritsuryo.Tax.Delinquency
