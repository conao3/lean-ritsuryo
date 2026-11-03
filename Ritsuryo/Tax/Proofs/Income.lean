module

public import Ritsuryo.Tax.Income
meta import Ritsuryo.Basis

/-!
# 所得税の証明（TAX-1、TAX-3〜TAX-5）

速算表の式（`quickCents`）は金額の区間ごとに 1 次式なので、区間で場合分けすると各場合は `omega`
（線形算術の決定手続き）で閉じる。
-/

public section

namespace Ritsuryo.Tax.Income

/-- 速算表の税額は、金額が 200 円の倍数なら百分の一円単位で 100 の倍数（＝円で割り切れる）。
千円未満を切り捨てた金額とその五分の一は 200 円の倍数なので、`taxOn` と `timberTaxOn` の割り算は端数を出さない。 -/
theorem quickCents_dvd (x : Nat) (h : x % 200 = 0) : quickCents x % 100 = 0 := by
  unfold quickCents
  repeat' split
  all_goals omega

theorem quickCents_le (x : Nat) : quickCents x ≤ 45 * x := by
  unfold quickCents
  repeat' split
  all_goals omega

/-- 速算表の式と、第89条の区分ごとの積み上げが、すべての金額で一致する。
実装の `taxOn` は、千円未満を切り捨てた金額に対する積み上げの税額（を円にしたもの）と等しい。 -/
@[ritsuryo_proof "TAX-1", ritsuryo_basis "所得税法" "第89条第1項"]
theorem tax1_quick_eq_spec (x : Nat) :
    quickCents x = incomeTaxCentsSpec x ∧ 100 * taxOn x = incomeTaxCentsSpec (taxBase x) := by
  refine ⟨(congrFun incomeTaxCentsSpec_eq_quickCents x).symm, ?_⟩
  have := quickCents_dvd (taxBase x) (by simp only [taxBase, floorTo]; omega)
  simp only [taxOn, incomeTaxCentsSpec_eq_quickCents]
  omega

/-- 限界税率の上下界: 金額が `y - x` 増えると、税額（百分の一円単位）は百分の五から百分の四十五の割合で増える。 -/
theorem quickCents_bounds (x y : Nat) (h : x ≤ y) :
    quickCents x + 5 * (y - x) ≤ quickCents y ∧ quickCents y ≤ quickCents x + 45 * (y - x) := by
  refine ⟨?_, ?_⟩ <;> unfold quickCents <;> repeat' split
  all_goals omega

/-- 限界税率の上下界（TAX-4）。積み上げの税額は、金額 1 円あたり百分の五以上・百分の四十五以下で増える。
千円未満の切捨てを挟んだ `taxOn` では、切り捨てられる 999 円分だけ幅が広がる。 -/
@[ritsuryo_proof "TAX-4", ritsuryo_basis "所得税法" "第89条第1項"]
theorem tax4_marginal_rate (x y : Nat) (h : x ≤ y) :
    incomeTaxCentsSpec x + 5 * (y - x) ≤ incomeTaxCentsSpec y ∧
      incomeTaxCentsSpec y ≤ incomeTaxCentsSpec x + 45 * (y - x) ∧
      100 * taxOn y ≤ 100 * taxOn x + 45 * (y - x + 999) ∧
      100 * taxOn x + 5 * (y - x) ≤ 100 * taxOn y + 5 * 999 := by
  rw [← (tax1_quick_eq_spec x).1, ← (tax1_quick_eq_spec y).1]
  have hb := quickCents_bounds x y h
  have hbx := (tax1_quick_eq_spec x).2
  have hby := (tax1_quick_eq_spec y).2
  rw [← (tax1_quick_eq_spec (taxBase x)).1] at hbx
  rw [← (tax1_quick_eq_spec (taxBase y)).1] at hby
  have hxy : taxBase x ≤ taxBase y := floorTo_mono 1000 h
  have hB := quickCents_bounds (taxBase x) (taxBase y) hxy
  have hx := floorTo_le 1000 x
  have hy := sub_floorTo 1000 y
  have hy' := Nat.mod_lt y (show 0 < 1000 by decide)
  have hx' := sub_floorTo 1000 x
  simp only [taxBase, floorTo] at *
  omega

/-- 税額と税引き後の額の単調性（TAX-3）。
課税標準（千円未満を切り捨てた額）が大きいほど税額は大きく、課税標準から税額を引いた額も小さくならない。
確定金額の百円未満の切捨て（国税通則法第119条第1項）を挟んでも同じ。 -/
@[ritsuryo_proof "TAX-3", ritsuryo_basis "所得税法" "第89条第1項",
  ritsuryo_basis "国税通則法" "第118条第1項", ritsuryo_basis "国税通則法" "第119条第1項"]
theorem tax3_monotone (x y : Nat) (h : x ≤ y) :
    taxOn x ≤ taxOn y ∧ taxBase x - taxOn x ≤ taxBase y - taxOn y ∧
      taxBase x - finalAmount (taxOn x) ≤ taxBase y - finalAmount (taxOn y) := by
  have hxy : taxBase x ≤ taxBase y := floorTo_mono 1000 h
  have hB := quickCents_bounds (taxBase x) (taxBase y) hxy
  have hdx := quickCents_dvd (taxBase x) (by simp only [taxBase, floorTo]; omega)
  have hdy := quickCents_dvd (taxBase y) (by simp only [taxBase, floorTo]; omega)
  have hlx := quickCents_le (taxBase x)
  have hly := quickCents_le (taxBase y)
  simp only [taxOn, incomeTaxCentsSpec_eq_quickCents, finalAmount, floorTo, taxBase] at *
  omega

/-- 5 分 5 乗（TAX-5）。実装の `timberTaxOn` は、第89条第1項の「課税山林所得金額の五分の一に相当する金額を
…区分して…合計した金額に五を乗じて計算した金額」と一致する。千円未満を切り捨てた金額は 5 で割り切れるので、
五分の一に端数は出ない。 -/
@[ritsuryo_proof "TAX-5", ritsuryo_basis "所得税法" "第89条第1項"]
theorem tax5_timber (x : Nat) :
    100 * timberTaxOn x = timberTaxCentsSpec (taxBase x) ∧ 5 * (taxBase x / 5) = taxBase x := by
  have hd := quickCents_dvd (taxBase x / 5) (by simp only [taxBase, floorTo]; omega)
  have hq := (tax1_quick_eq_spec (taxBase x / 5)).1
  simp only [timberTaxOn, timberTaxCentsSpec, incomeTaxCentsSpec] at *
  refine ⟨?_, by simp only [taxBase, floorTo]; omega⟩
  rw [← hq]
  omega

end Ritsuryo.Tax.Income
