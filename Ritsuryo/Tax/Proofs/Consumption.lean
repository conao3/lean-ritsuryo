module

public import Ritsuryo.Tax.Consumption
meta import Ritsuryo.Basis

/-!
# 消費税の証明（CON-1、CON-2）

CON-2 の証明では、3 つの端数処理をどれも `(α * a + β) / γ`（`β ≤ γ`）の形に直す。
切捨ては `(a + 0) / d`、切上げは `(a + (d - 1)) / d`、四捨五入は `(2a + d) / (2d)`。
この形の割り算は `γ * q ≤ α * a + β ≤ γ * q + (γ - 1)` を満たすので、品目ごとに足した誤差と
合計に一度だけ掛けた誤差の差を、品目の数で抑えられる。
-/

public section

namespace Ritsuryo.Tax.Consumption

/-- 税率の合成（CON-1）。国の消費税の税率に、その七十八分の二十二の地方消費税を足すと、
標準税率は百分の七・八から百分の十に、軽減税率は百分の六・二四から百分の八になる。
`税率 × (1 + 22/78) = 百分率 / 100` を分母を払って自然数の等式で書いている。 -/
@[ritsuryo_proof "CON-1", ritsuryo_basis "消費税法" "第29条",
  ritsuryo_basis "地方税法" "第72条の83"]
theorem con1_combined_rate (r : Rate) :
    r.nationalPerTenThousand * (78 + 22) * 100 = r.percent * 10000 * 78 := by
  cases r <;> decide

/-- `(α * a + β) / γ` の形の割り算を品目ごとに行って足すと、`γ` 倍した合計は
`α × 価額の合計 + β × 品目数` から `(γ - 1) × 品目数` の幅に収まる。 -/
theorem sum_div_bounds (α β γ : Nat) (hγ : 0 < γ) (as : List Nat) :
    γ * (as.map fun a => (α * a + β) / γ).sum ≤ α * as.sum + β * as.length ∧
      α * as.sum + β * as.length ≤
        γ * (as.map fun a => (α * a + β) / γ).sum + (γ - 1) * as.length := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have hd := Nat.div_add_mod (α * a + β) γ
    have hm : (α * a + β) % γ ≤ γ - 1 := by
      have := Nat.mod_lt (α * a + β) hγ
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_succ] at *
    omega

/-- 割り算 1 回の誤差。 -/
theorem div_bounds (α β γ : Nat) (hγ : 0 < γ) (a : Nat) :
    γ * ((α * a + β) / γ) ≤ α * a + β ∧ α * a + β ≤ γ * ((α * a + β) / γ) + (γ - 1) := by
  have := sum_div_bounds α β γ hγ [a]
  simpa using this

/-- 品目ごとに丸めて足した額と合計を一度だけ丸めた額の差は、品目数 `n` より小さい。 -/
theorem sum_div_close (α β γ : Nat) (hβ : β ≤ γ) (hγ : 0 < γ) (as : List Nat) (hne : as ≠ []) :
    (as.map fun a => (α * a + β) / γ).sum ≤ (α * as.sum + β) / γ + (as.length - 1) ∧
      (α * as.sum + β) / γ ≤ (as.map fun a => (α * a + β) / γ).sum + (as.length - 1) := by
  have hs := sum_div_bounds α β γ hγ as
  have h1 := div_bounds α β γ hγ as.sum
  generalize hS : (as.map fun a => (α * a + β) / γ).sum = S at *
  generalize hQ : (α * as.sum + β) / γ = Q at *
  generalize hn : as.length = n at *
  have hn1 : 1 ≤ n := by
    cases as with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at hn; omega
  have hβn : β * (n - 1) ≤ γ * (n - 1) := Nat.mul_le_mul_right _ hβ
  have hγn : (γ - 1) * n + n = γ * n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hγ]
  have hsplit : β * n = β * (n - 1) + β := by
    rw [show n = (n - 1) + 1 by omega, Nat.mul_succ, Nat.add_sub_cancel]
  have hsplit' : γ * n = γ * (n - 1) + γ := by
    rw [show n = (n - 1) + 1 by omega, Nat.mul_succ, Nat.add_sub_cancel]
  constructor
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : Q + (n - 1) + 1 ≤ S := hlt
    have := Nat.mul_le_mul_left γ h2
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
    omega
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : S + (n - 1) + 1 ≤ Q := hlt
    have := Nat.mul_le_mul_left γ h2
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
    omega

/-- 適格請求書の端数処理の差（CON-2）。同じ税率の品目が `n` 個（`n ≥ 1`）あるとき、品目ごとに端数を処理して
足した税額と、価額の合計に一度だけ割合を掛けて端数を処理した税額（消費税法施行令第70条の10の方法）の差は
`n - 1` 円以下。切捨て・切上げ・四捨五入、税抜・税込のどの組み合わせでも成り立つ。 -/
@[ritsuryo_proof "CON-2", ritsuryo_basis "消費税法施行令" "第70条の10"]
theorem con2_per_rate_rounding (mode : Rounding) (basis : PriceBasis) (rate : Rate)
    (prices : List Nat) (hne : prices ≠ []) :
    (prices.map (taxOf mode basis rate)).sum ≤
        taxOf mode basis rate prices.sum + (prices.length - 1) ∧
      taxOf mode basis rate prices.sum ≤
        (prices.map (taxOf mode basis rate)).sum + (prices.length - 1) := by
  obtain ⟨n, d, hf, hd⟩ : ∃ n d, factor basis rate = (n, d) ∧ 0 < d := by
    cases basis <;> cases rate <;> exact ⟨_, _, rfl, by decide⟩
  have hsum : ∀ ps : List Nat, (ps.map fun p => p * n).sum = ps.sum * n := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]
  have ht : taxOf mode basis rate = fun p => roundDiv mode (p * n) d := by
    funext p
    simp [taxOf, hf]
  rw [ht]
  have key : ∀ (α β γ : Nat), β ≤ γ → 0 < γ →
      (∀ a, roundDiv mode (a * n) d = (α * (a * n) + β) / γ) →
      (prices.map fun p => roundDiv mode (p * n) d).sum ≤
          roundDiv mode (prices.sum * n) d + (prices.length - 1) ∧
        roundDiv mode (prices.sum * n) d ≤
          (prices.map fun p => roundDiv mode (p * n) d).sum + (prices.length - 1) := by
    intro α β γ hβ hγ heq
    have hc := sum_div_close α β γ hβ hγ (prices.map fun p => p * n) (by simpa using hne)
    simp only [List.map_map, List.length_map, hsum prices] at hc
    simp only [heq]
    exact hc
  cases mode with
  | floor =>
    exact key 1 0 d (Nat.zero_le _) hd fun a => by simp [roundDiv]
  | ceil =>
    exact key 1 (d - 1) d (Nat.sub_le d 1) hd fun a => by simp [roundDiv]; congr 1; omega
  | halfUp =>
    exact key 2 d (2 * d) (by omega) (by omega) fun a => by simp [roundDiv]

end Ritsuryo.Tax.Consumption
