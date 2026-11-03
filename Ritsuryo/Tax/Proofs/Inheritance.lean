module

public import Ritsuryo.Tax.Inheritance
meta import Ritsuryo.Basis

/-!
# 相続税の証明（TAX-2、INH-1）
-/

public section

namespace Ritsuryo.Tax.Inheritance

theorem quickCents_dvd (x : Nat) (h : x % 200 = 0) : quickCents x % 100 = 0 := by
  unfold quickCents
  repeat' split
  all_goals omega

/-- 速算表の式と第16条の区分ごとの積み上げが、すべての取得金額で一致する。千円の倍数の取得金額では、
CLI の `taxOn`（円）は積み上げの額を円にしたものと等しい。 -/
@[ritsuryo_proof "TAX-2", ritsuryo_basis "相続税法" "第16条"]
theorem tax2_quick_eq_spec (x : Nat) :
    quickCents x = taxCentsSpec x ∧ (x % 1000 = 0 → 100 * taxOn x = taxCentsSpec x) := by
  have hq : quickCents x = taxCentsSpec x := by
    simp only [taxCentsSpec, table, progressiveCents, quickCents]
    repeat' split
    all_goals omega
  refine ⟨hq, fun h => ?_⟩
  have := quickCents_dvd x (by omega)
  rw [← hq]
  simp only [taxOn]
  omega

/-- 順位の人数が正であること（`rankOf` の結果はいつもこれを満たす）。 -/
@[ritsuryo_basis "民法" "第889条第1項"]
def Rank.Valid : Rank → Prop
  | .children n => 0 < n
  | .ascendants n => 0 < n
  | .siblings f s => 0 < f + s
  | .none => True

theorem rankOf_valid (h : Heirs) : (rankOf h).Valid := by
  simp only [rankOf]
  repeat' split
  all_goals simp_all [Rank.Valid]

theorem sum_map_mul (g : Nat) (xs : List (HeirKind × Nat)) :
    ((xs.map fun (k, w) => (k, g * w)).map (·.2)).sum = g * (xs.map (·.2)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at *
    rw [ih, Nat.mul_add]

/-- 法定相続分の性質を、順位ごとに場合分けして示す。 -/
theorem shares_props (spouse : Bool) (r : Rank) (hv : r.Valid)
    (hsome : spouse = true ∨ r ≠ .none) :
    let sh := statutoryShares spouse r
    (sh.shares.map (·.2)).sum = sh.denominator ∧ 0 < sh.denominator ∧
      (∀ p ∈ sh.shares, 0 < p.2) ∧
      (∀ a b, (HeirKind.fullSibling, a) ∈ sh.shares → (HeirKind.halfSibling, b) ∈ sh.shares →
        a = 2 * b) := by
  cases r <;> cases spouse <;> simp at hsome <;>
    simp [Rank.Valid, statutoryShares, groupShares, members, totalWeight, List.sum_replicate_nat,
      List.mem_replicate] at hv ⊢ <;>
    first
      | omega
      | (refine ⟨?_, ?_⟩ <;> intros <;> simp_all <;> omega)
      | (refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all <;> omega)
      | (refine ⟨by omega, by omega, ⟨by omega, ?_⟩, by omega⟩
         intro _ _ h
         rcases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> omega)

/-- 法定相続分（INH-1）。相続人がいれば、各自の相続分は正で、合計はちょうど 1（分子の合計が分母に等しい）。
半血の兄弟姉妹の相続分は全血の兄弟姉妹の二分の一。 -/
@[ritsuryo_proof "INH-1", ritsuryo_basis "民法" "第900条"]
theorem inh1_statutory_shares (h : Heirs) (hsome : h.spouse = true ∨ rankOf h ≠ .none) :
    let sh := statutoryShares h.spouse (rankOf h)
    (sh.shares.map (·.2)).sum = sh.denominator ∧ 0 < sh.denominator ∧
      (∀ p ∈ sh.shares, 0 < p.2) ∧
      (∀ a b, (HeirKind.fullSibling, a) ∈ sh.shares → (HeirKind.halfSibling, b) ∈ sh.shares →
        a = 2 * b) :=
  shares_props h.spouse (rankOf h) (rankOf_valid h) hsome

end Ritsuryo.Tax.Inheritance
