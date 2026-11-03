module

public import Ritsuryo.Holiday.Lookup
meta import Ritsuryo.Basis

/-!
# HOL-C1: 内閣府 CSV の「休日」の行と、第3条からの導出の一致

内閣府 CSV の各年について、名称が「休日」でない行を「国民の祝日」として、その日に施行されていた
第3条第2項（振替休日）・第3項（国民の休日）を当てはめると、名称が「休日」の行がちょうど得られる。
これを、CSV の全年（`Data.firstYear` から `Data.lastYear` まで）について定理 `holc1_csv_rest_days` にする。

証明は 2 段に分かれる。

1. `checkAll`: 全年の `checkYear` が `true` になることを `decide +kernel` でカーネルに評価させる。
   `checkYear` は国民の祝日の翌日だけを調べるので、評価は数秒で終わる。
2. `holc1_csv_rest_days`: 導かれる休日は必ず国民の祝日の翌日になる（`isRestDayAt_pred`）ことを使い、
   `checkYear` の結果をすべての日についての同値に広げる。
-/

public section

namespace Ritsuryo.Holiday

/-- `isRestDayAt` が休日と判定する日の前日は、必ず国民の祝日になる。`isRestDayAt` を展開し、
振替休日と国民の休日のそれぞれで、現行の版と改正前の版に場合分けして前日の条件を取り出す。 -/
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

/-- CSV の全年で `checkYear` が `true` になる。`decide +kernel` で、カーネルが表を直接評価して確かめる。 -/
theorem checkAll :
    (List.range (Data.lastYear - Data.firstYear + 1).toNat).all
      (fun i => checkYear (Data.firstYear + i)) = true := by
  decide +kernel

/-- HOL-C1: CSV の範囲の `y` 年について、`y` 年の国民の祝日から導いた休日と、CSV の「休日」の行が一致する。
`checkAll` から `y` 年の `checkYear` を取り出す。CSV の行から休日への向きはその前半から直接出る。
導いた休日から CSV の行への向きは、`isRestDayAt_pred` で前日が国民の祝日になることを使い、後半を当てはめる。 -/
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
