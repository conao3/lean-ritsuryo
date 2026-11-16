module

public import Ritsuryo.Tax.Income
meta import Ritsuryo.Basis

/-!
# 令和7年分の居住者の基礎控除

e-Gov 法令履歴 `340AC0000000033_20251201_507AC0000000013` 第86条第1項と
`332AC0000000026_20251201_507AC0000000013` 第41条の16の2第1項。

> 合計所得金額が二千五百万円以下である居住者については、その者のその年分の総所得金額、退職所得金額又は山林所得金額から次の各号に掲げる場合の区分に応じ当該各号に定める金額を控除する。

本則の区分は、2,350万円以下58万円、2,400万円以下48万円、2,450万円以下32万円、
2,500万円以下16万円。特例の加算は、132万円以下37万円、336万円以下30万円、
489万円以下10万円、655万円以下5万円。

`spec` は本則と特例の加算を別々に計算し、`table` は国税庁 No.1199 の令和7年分の表を写す。
`spec_eq_table` は全所得額での一致を場合分けで証明する。`tax` は仕様をそのまま呼ぶ。
入力は給与収入でなく所得。総所得と合計所得が同額で、退職所得、山林所得、分離課税所得、
税額控除、源泉徴収税額が0という限定モデル。その他の所得控除は別入力にする。
年分は2025年に固定し、他の年の税制はこの関数の対象に含めない。
-/

@[expose] public section

namespace Ritsuryo.Tax.BasicDeduction2025

/-- 仕様: 所得税法第86条第1項各号の本則の金額。 -/
@[ritsuryo_basis "所得税法" "第86条第1項"]
def ordinary (income : Nat) : Nat :=
  if income ≤ 23500000 then 580000
  else if income ≤ 24000000 then 480000
  else if income ≤ 24500000 then 320000
  else if income ≤ 25000000 then 160000
  else 0

/-- 仕様: 措置法の適用所得要件と第1号イからニの加算額。 -/
@[ritsuryo_basis "租税特別措置法" "第41条の16の2第1項第1号"]
def addition (income : Nat) : Nat :=
  if income ≤ 6550000 then
    if income ≤ 1320000 then 370000
    else if income ≤ 3360000 then 300000
    else if income ≤ 4890000 then 100000
    else 50000
  else 0

/-- 仕様: 本則に特例の額を加算する。 -/
@[ritsuryo_basis "所得税法" "第86条第1項",
  ritsuryo_basis "租税特別措置法" "第41条の16の2第1項第1号"]
def spec (income : Nat) : Nat := ordinary income + addition income

/-- 国税庁 No.1199 の令和7年分の表による独立した表現。 -/
@[ritsuryo_basis "所得税法" "第86条第1項",
  ritsuryo_basis "租税特別措置法" "第41条の16の2第1項第1号"]
def table (income : Nat) : Nat :=
  if income ≤ 1320000 then 950000
  else if income ≤ 3360000 then 880000
  else if income ≤ 4890000 then 680000
  else if income ≤ 6550000 then 630000
  else if income ≤ 23500000 then 580000
  else if income ≤ 24000000 then 480000
  else if income ≤ 24500000 then 320000
  else if income ≤ 25000000 then 160000
  else 0

/-- 条文を合成した仕様は、全所得額で国税庁の表と一致する。区分ごとに線形算術で示す。 -/
theorem spec_eq_table (income : Nat) : spec income = table income := by
  unfold spec ordinary addition table
  repeat' split
  all_goals omega

/-- 基礎控除と他の所得控除を差し引き、既存の証明付き税率計算を呼ぶ。 -/
@[ritsuryo_basis "所得税法" "第86条第1項・第89条第1項",
  ritsuryo_basis "租税特別措置法" "第41条の16の2第1項第1号"]
def tax (income otherDeductions : Nat) : Nat :=
  Income.taxOn (income - (spec income + otherDeductions))

/-- 所得と他の控除額のすべてで、合成した税計算は国税庁の控除表を使う計算と一致する。 -/
theorem tax_eq_table (income otherDeductions : Nat) :
    tax income otherDeductions =
      Income.taxOn (income - (table income + otherDeductions)) := by
  rw [tax, spec_eq_table]

/-- 本体所得税を差し引いた所得。控除済みの所得金額を入力する限定モデル。 -/
@[ritsuryo_basis "所得税法" "第86条第1項・第89条第1項"]
def net (income otherDeductions : Nat) : Int :=
  (income : Int) - (tax income otherDeductions : Int)

/-- 本体所得税が1円の所得増に対して1,000円以上増えることを検査する述語。 -/
@[ritsuryo_basis "所得税法" "第86条第1項・第89条第1項",
  ritsuryo_basis "租税特別措置法" "第41条の16の2第1項第1号"]
def largeJump (income : Nat) : Bool :=
  tax (income + 1) 0 ≥ tax income 0 + 1000

/-- 大きな税額増の検出結果は、税引後所得の逆転を意味する。整数の引算として示す。 -/
theorem largeJump_sound (income : Nat) (h : largeJump income = true) :
    net (income + 1) 0 < net income 0 := by
  simp only [largeJump, decide_eq_true_eq] at h
  unfold net
  omega

/-- 探索から得た8例の税額はカーネルで再計算できる。 -/
theorem certified_jumps :
    ([1320000, 3360000, 4890000, 6550000, 23500000, 24000000, 24500000, 25000000].map
      fun x => (tax x 0, tax (x + 1) 0)) =
    [(18500, 22000), (150500, 170500), (414500, 424500), (756500, 766500),
      (6372000, 6412000), (6612000, 6676000), (6876000, 6940000), (7140000, 7204000)] := by
  decide +kernel

/-- 同じ8例すべてで税引後所得が減ることを、標本実行とは別にカーネルで確認する。 -/
theorem certified_reversals :
    ∀ x ∈ [1320000, 3360000, 4890000, 6550000, 23500000, 24000000, 24500000, 25000000],
      net (x + 1) 0 < net x 0 := by
  decide +kernel

/-- 132万円の境界では、所得増が1円以上3,650円未満なら税引後所得が下がる。
3,650円増で境界直前の税引後所得と一致する。定義を展開して線形算術で示す。 -/
theorem first_cliff_recovery (delta : Nat) (hpos : 1 ≤ delta) (hlt : delta < 3650) :
    net (1320000 + delta) 0 < net 1320000 0 := by
  have ht : table (1320000 + delta) = 880000 := by
    unfold table
    split
    · omega
    · split
      · rfl
      · omega
  have hb : net 1320000 0 = 1301500 := by decide +kernel
  rw [hb]
  simp only [net, tax, spec_eq_table, ht, Nat.add_zero, Income.taxOn,
    Income.incomeTaxCentsSpec_eq_quickCents]
  have hx : taxBase (1320000 + delta - 880000) ≤ 1950000 := by
    unfold taxBase floorTo
    omega
  unfold Income.quickCents
  rw [ite_eq_left hx]
  unfold taxBase floorTo
  omega

/-- 132万円から3,650円増えた点で、本体所得税を差し引いた所得が一致する。 -/
theorem first_cliff_recovered : net 1323650 0 = net 1320000 0 := by
  decide +kernel

end Ritsuryo.Tax.BasicDeduction2025
