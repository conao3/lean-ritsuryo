module

public import Ritsuryo.Holiday.Article2
meta import Ritsuryo.Basis

/-!
# HOL-C2 の検査

`checkArticle2Year` を CSV のすべての年について Lean のカーネルで評価する（`decide +kernel`）。
コンパイラを信頼の範囲に入れる `native_decide` は使わない。
-/

public section

namespace Ritsuryo.Holiday

theorem checkArticle2All :
    (List.range (Data.lastYear - Data.firstYear + 1).toNat).all
      (fun i => checkArticle2Year (Data.firstYear + i)) = true := by
  decide +kernel

/-- 第2条の規則（施行期間つき）から生成した祝日の月日は、CSV のすべての年で「国民の祝日」の行の月日と一致する。
春分の日・秋分の日の行は各年の 3 月と 9 月に 1 行ずつある。 -/
@[ritsuryo_proof "HOL-C2", ritsuryo_basis "国民の祝日に関する法律" "第2条"]
theorem holc2_csv_article2 (y : Int) (h1 : Data.firstYear ≤ y) (h2 : y ≤ Data.lastYear) :
    (∀ md ∈ article2Days y, md ∈ csvNationalDays y) ∧
      (∀ md ∈ csvNationalDays y, md ∈ article2Days y) ∧
      (equinoxDays y 3).length = 1 ∧ (equinoxDays y 9).length = 1 := by
  have hc : checkArticle2Year y = true := by
    have := checkArticle2All
    rw [List.all_eq_true] at this
    have := this (y - Data.firstYear).toNat (by rw [List.mem_range]; omega)
    rwa [show Data.firstYear + (((y - Data.firstYear).toNat : Nat) : Int) = y by omega] at this
  simp only [checkArticle2Year, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨h3, h9⟩, -⟩, hg⟩, hcsv⟩ := hc
  exact ⟨hg, hcsv, h3, h9⟩

end Ritsuryo.Holiday
