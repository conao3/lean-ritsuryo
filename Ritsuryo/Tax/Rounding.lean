module

meta import Ritsuryo.Basis

/-!
# 国税の端数処理（国税通則法 第118条・第119条）

国税の計算では、税率を掛ける前の金額（課税標準）と、確定した税額の両方で端数を切り捨てる。
このファイルは、その切捨てをすべて `floorTo k x`（`x` の `k` 円未満を切り捨てる）で表し、
条文ごとに `k` と「全額を切り捨てる」下限を決めた関数を置く。

e-Gov 法令履歴 `337AC0000000066_20261101_507AC0000000013`。

> 第百十八条　国税（印紙税及び附帯税を除く。以下この条において同じ。）の課税標準（その税率の適用上課税標準から控除する金額があるときは、これを控除した金額。以下この条において同じ。）を計算する場合において、その額に千円未満の端数があるとき、又はその全額が千円未満であるときは、その端数金額又はその全額を切り捨てる。
>
> ３　附帯税の額を計算する場合において、その計算の基礎となる税額に一万円未満の端数があるとき、又はその税額の全額が一万円未満であるときは、その端数金額又はその全額を切り捨てる。
>
> 第百十九条　国税（自動車重量税、印紙税及び附帯税を除く。以下この条において同じ。）の確定金額に百円未満の端数があるとき、又はその全額が百円未満であるときは、その端数金額又はその全額を切り捨てる。
>
> ４　附帯税の確定金額に百円未満の端数があるとき、又はその全額が千円未満（加算税に係るものについては、五千円未満）であるときは、その端数金額又はその全額を切り捨てる。

附帯税は延滞税・利子税・加算税をまとめた呼び名（国税通則法第2条第4号）。金額はすべて円の自然数で持つ。
-/

@[expose] public section

namespace Ritsuryo.Tax

/-- `x` 円の `k` 円未満の端数を切り捨てた額。`k` の倍数のうち `x` 以下で最大のものになる。
全額が `k` 円未満のときは 0 になり、条文の「その全額を切り捨てる」もこの式に含まれる。 -/
@[ritsuryo_basis "国税通則法" "第118条第1項", ritsuryo_basis "国税通則法" "第118条第3項",
  ritsuryo_basis "国税通則法" "第119条第1項", ritsuryo_basis "国税通則法" "第119条第4項"]
def floorTo (k x : Nat) : Nat :=
  x / k * k

/-- 課税標準の千円未満を切り捨てる（第118条第1項）。所得税の課税総所得金額などに使う。 -/
@[ritsuryo_basis "国税通則法" "第118条第1項"]
def taxBase (x : Nat) : Nat :=
  floorTo 1000 x

/-- 附帯税（延滞税・利子税・加算税）の計算の基礎となる税額の一万円未満を切り捨てる（第118条第3項）。 -/
@[ritsuryo_basis "国税通則法" "第118条第3項"]
def incidentalBase (x : Nat) : Nat :=
  floorTo 10000 x

/-- 国税の確定金額の百円未満を切り捨てる（第119条第1項）。 -/
@[ritsuryo_basis "国税通則法" "第119条第1項"]
def finalAmount (x : Nat) : Nat :=
  floorTo 100 x

/-- 附帯税の確定金額の端数処理（第119条第4項）。百円未満を切り捨て、全額が `minimum` 円未満なら 0 にする。
`minimum` は延滞税・利子税で 1,000、加算税で 5,000。 -/
@[ritsuryo_basis "国税通則法" "第119条第4項"]
def incidentalFinal (minimum x : Nat) : Nat :=
  if x < minimum then 0 else floorTo 100 x

/-- 延滞税・利子税の確定金額（第119条第4項。全額が千円未満なら切り捨てる）。 -/
@[ritsuryo_basis "国税通則法" "第119条第4項"]
def interestFinal (x : Nat) : Nat :=
  incidentalFinal 1000 x

/-- 加算税の確定金額（第119条第4項かっこ書。全額が五千円未満なら切り捨てる）。 -/
@[ritsuryo_basis "国税通則法" "第119条第4項"]
def penaltyFinal (x : Nat) : Nat :=
  incidentalFinal 5000 x

/-- `floorTo` は `x` を超えない。 -/
theorem floorTo_le (k x : Nat) : floorTo k x ≤ x :=
  Nat.div_mul_le_self x k

/-- 切り捨てた差は `k` 円未満（`k` が正のとき）。差はちょうど `x % k`。 -/
theorem sub_floorTo (k x : Nat) : x - floorTo k x = x % k := by
  have := Nat.mod_add_div x k
  simp only [floorTo, Nat.mul_comm (x / k) k]
  omega

theorem floorTo_mono (k : Nat) {x y : Nat} (h : x ≤ y) : floorTo k x ≤ floorTo k y :=
  Nat.mul_le_mul_right k (Nat.div_le_div_right h)

theorem floorTo_dvd (k x : Nat) : k ∣ floorTo k x :=
  Nat.dvd_mul_left k (x / k)

theorem floorTo_floorTo (k x : Nat) : floorTo k (floorTo k x) = floorTo k x := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · simp [floorTo, hk]
  · simp [floorTo, Nat.mul_div_cancel _ hk]

/-- 端数処理の基本性質: 切り捨てた額は元の額以下で、差は `k` 円未満、`k` の倍数になり、
2 回切り捨てても 1 回と同じ（冪等）で、元の額について単調。 -/
@[ritsuryo_proof "RND-1", ritsuryo_basis "国税通則法" "第118条第1項",
  ritsuryo_basis "国税通則法" "第119条第1項"]
theorem rnd1_floorTo (k : Nat) (hk : 0 < k) (x y : Nat) :
    floorTo k x ≤ x ∧ x - floorTo k x < k ∧ k ∣ floorTo k x ∧
      floorTo k (floorTo k x) = floorTo k x ∧ (x ≤ y → floorTo k x ≤ floorTo k y) := by
  refine ⟨floorTo_le k x, ?_, floorTo_dvd k x, floorTo_floorTo k x, floorTo_mono k⟩
  rw [sub_floorTo]
  exact Nat.mod_lt x hk

/-- 附帯税の端数処理（全額が下限未満なら 0）も単調で、元の額を超えない。
下限が百円の倍数なら、結果は 0 か下限以上の百円の倍数になる。 -/
@[ritsuryo_proof "RND-2", ritsuryo_basis "国税通則法" "第119条第4項"]
theorem rnd2_incidentalFinal (m : Nat) (hm : 100 ∣ m) (x y : Nat) :
    (x ≤ y → incidentalFinal m x ≤ incidentalFinal m y) ∧ incidentalFinal m x ≤ x ∧
      100 ∣ incidentalFinal m x ∧ (incidentalFinal m x = 0 ∨ m ≤ incidentalFinal m x) := by
  obtain ⟨c, rfl⟩ := hm
  simp only [incidentalFinal, floorTo]
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · split <;> split <;> omega
  · split <;> omega
  · split
    · exact Nat.dvd_zero 100
    · exact Nat.dvd_mul_left 100 (x / 100)
  · split <;> omega

end Ritsuryo.Tax
