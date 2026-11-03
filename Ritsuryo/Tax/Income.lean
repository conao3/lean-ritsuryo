module

public import Ritsuryo.Tax.Rounding
public import Ritsuryo.Tax.Progressive
meta import Ritsuryo.Basis

/-!
# 所得税の税額（所得税法 第89条）と復興特別所得税・防衛特別所得税

所得税法第89条は、課税総所得金額などを税率表の区分に分けて積み上げる形で税額を定める。国税庁の
「所得税の速算表」（税率 × 課税所得 − 控除額）はこの積み上げを 1 本の式にまとめたもので、
このファイルでは両方を書き、すべての金額で一致することを `@[csimp]` の定理で証明する。税額の関数は条文を写した
積み上げ（`incomeTaxCentsSpec`）を呼び、コンパイラがこの定理で速算表（`quickCents`）の式に置き換える。

e-Gov 法令履歴 `340AC0000000033_20261001_507AC0000000070`。

> 第八十九条　居住者に対して課する所得税の額は、その年分の課税総所得金額又は課税退職所得金額をそれぞれ次の表の上欄に掲げる金額に区分してそれぞれの金額に同表の下欄に掲げる税率を乗じて計算した金額を合計した金額と、その年分の課税山林所得金額の五分の一に相当する金額を同表の上欄に掲げる金額に区分してそれぞれの金額に同表の下欄に掲げる税率を乗じて計算した金額を合計した金額に五を乗じて計算した金額との合計額とする。
>
> | 百九十五万円以下の金額 | 百分の五 |
> | 百九十五万円を超え三百三十万円以下の金額 | 百分の十 |
> | 三百三十万円を超え六百九十五万円以下の金額 | 百分の二十 |
> | 六百九十五万円を超え九百万円以下の金額 | 百分の二十三 |
> | 九百万円を超え千八百万円以下の金額 | 百分の三十三 |
> | 千八百万円を超え四千万円以下の金額 | 百分の四十 |
> | 四千万円を超える金額 | 百分の四十五 |

この表は平成27年分以後の所得税に適用される。CLI は 2015 年分より前を扱わない。

## 復興特別所得税と防衛特別所得税

どちらも、その年分の基準所得税額（ここでは第89条の税額）に税率を掛ける。

- 復興特別所得税（東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法
  第9条・第13条）: 平成25年分（2013 年分）から令和8年分（2026 年分）までは百分の二・一。
  令和8年法律第12号の改正後は、令和9年分（2027 年分）から令和29年分（2047 年分）まで百分の一・一
  （同改正法附則第88条第1項）。
- 防衛特別所得税（我が国の防衛力の抜本的な強化等のために必要な財源の確保に関する特別措置法
  第5条の5・第5条の9、令和9年1月1日施行）: 令和9年分（2027 年分）以後、百分の一。
-/

@[expose] public section

namespace Ritsuryo.Tax.Income

/-- 第89条第1項の表。平成27年分以後。 -/
@[ritsuryo_basis "所得税法" "第89条第1項"]
def table : List Bracket := [
  ⟨some 1950000, 5⟩, ⟨some 3300000, 10⟩, ⟨some 6950000, 20⟩, ⟨some 9000000, 23⟩,
  ⟨some 18000000, 33⟩, ⟨some 40000000, 40⟩, ⟨none, 45⟩]

/-- 仕様: 第89条第1項の文言どおり、`x` 円を表の区分に分けて税率を掛け、合計する（百分の一円単位）。 -/
@[ritsuryo_basis "所得税法" "第89条第1項"]
def incomeTaxCentsSpec (x : Nat) : Nat :=
  progressiveCents table 0 x

/-- 実装: 国税庁の所得税の速算表（税率 × 金額 − 控除額）を百分の一円単位で書いたもの。
控除額は 0、97,500、427,500、636,000、1,536,000、2,796,000、4,796,000 円。 -/
@[ritsuryo_basis "所得税法" "第89条第1項"]
def quickCents (x : Nat) : Nat :=
  if x ≤ 1950000 then 5 * x
  else if x ≤ 3300000 then 10 * x - 9750000
  else if x ≤ 6950000 then 20 * x - 42750000
  else if x ≤ 9000000 then 23 * x - 63600000
  else if x ≤ 18000000 then 33 * x - 153600000
  else if x ≤ 40000000 then 40 * x - 279600000
  else 45 * x - 479600000

/-- 速算表の式と第89条の区分ごとの積み上げは、すべての金額で等しい（TAX-1 の前半）。
`@[csimp]` により、`incomeTaxCentsSpec` を呼ぶコードはコンパイルのときに `quickCents` を呼ぶコードになる。
証明は金額を区分で場合分けし、区分ごとに 1 次式の等式を `omega` で閉じる。 -/
@[csimp]
theorem incomeTaxCentsSpec_eq_quickCents : @incomeTaxCentsSpec = @quickCents := by
  funext x
  simp only [incomeTaxCentsSpec, table, progressiveCents, quickCents]
  repeat' split
  all_goals omega

/-- 課税総所得金額（または課税退職所得金額）に対する税額。金額の千円未満を切り捨ててから
（国税通則法第118条第1項）第89条の区分ごとの積み上げを当てる。切捨て後の金額は千円の倍数なので、
税額は円で割り切れる。 -/
@[ritsuryo_basis "所得税法" "第89条第1項", ritsuryo_basis "国税通則法" "第118条第1項"]
def taxOn (x : Nat) : Nat :=
  incomeTaxCentsSpec (taxBase x) / 100

/-- 仕様: 課税山林所得金額の税額（いわゆる 5 分 5 乗）。五分の一の金額を区分して積み上げ、五を掛ける。 -/
@[ritsuryo_basis "所得税法" "第89条第1項"]
def timberTaxCentsSpec (x : Nat) : Nat :=
  5 * progressiveCents table 0 (x / 5)

/-- 課税山林所得金額の税額。千円未満を切り捨てた金額の五分の一に第89条の積み上げを当て、五を掛ける。 -/
@[ritsuryo_basis "所得税法" "第89条第1項", ritsuryo_basis "国税通則法" "第118条第1項"]
def timberTaxOn (x : Nat) : Nat :=
  5 * (incomeTaxCentsSpec (taxBase x / 5) / 100)

/-- 第89条第1項の所得税の額。課税総所得金額・課税退職所得金額・課税山林所得金額それぞれの税額の合計。 -/
@[ritsuryo_basis "所得税法" "第89条第1項"]
def incomeTax (ordinary retirement timber : Nat) : Nat :=
  taxOn ordinary + taxOn retirement + timberTaxOn timber

/-- 復興特別所得税の税率（千分の一単位）。2013〜2026 年分は 21（百分の二・一）、2027〜2047 年分は 11
（百分の一・一）、それ以外の年分は 0。 -/
@[ritsuryo_basis "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法"
    "第9条第1項",
  ritsuryo_basis "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法"
    "第13条",
  ritsuryo_basis "所得税法等の一部を改正する法律（令和8年法律第12号）" "附則第88条第1項"]
def reconstructionPermille (year : Nat) : Nat :=
  if 2013 ≤ year ∧ year ≤ 2026 then 21
  else if 2027 ≤ year ∧ year ≤ 2047 then 11
  else 0

/-- 防衛特別所得税の税率（千分の一単位）。2027 年分以後は 10（百分の一）、それより前は 0。 -/
@[ritsuryo_basis "我が国の防衛力の抜本的な強化等のために必要な財源の確保に関する特別措置法" "第5条の5第1項",
  ritsuryo_basis "我が国の防衛力の抜本的な強化等のために必要な財源の確保に関する特別措置法" "第5条の9"]
def defensePermille (year : Nat) : Nat :=
  if 2027 ≤ year then 10 else 0

/-- 基準所得税額に千分の `permille` を掛け、一円未満を切り捨てた額。 -/
@[ritsuryo_basis "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法"
    "第13条",
  ritsuryo_basis "我が国の防衛力の抜本的な強化等のために必要な財源の確保に関する特別措置法" "第5条の9"]
def surtax (permille base : Nat) : Nat :=
  base * permille / 1000

/-- 所得税の計算の途中の値と結果。 -/
structure Result where
  ordinaryBase : Nat
  retirementBase : Nat
  timberBase : Nat
  ordinaryTax : Nat
  retirementTax : Nat
  timberTax : Nat
  incomeTax : Nat
  reconstructionTax : Nat
  defenseTax : Nat
  total : Nat
  payable : Nat
  deriving Repr

/-- `year` 年分の所得税と特別所得税。`payable` は合計の百円未満を切り捨てた額（国税通則法第119条第1項）で、
税額控除と源泉徴収税額がないものとした申告納税額に当たる。 -/
@[ritsuryo_basis "所得税法" "第89条第1項", ritsuryo_basis "国税通則法" "第119条第1項"]
def compute (year ordinary retirement timber : Nat) : Result :=
  let it := incomeTax ordinary retirement timber
  let rt := surtax (reconstructionPermille year) it
  let dt := surtax (defensePermille year) it
  { ordinaryBase := taxBase ordinary
    retirementBase := taxBase retirement
    timberBase := taxBase timber
    ordinaryTax := taxOn ordinary
    retirementTax := taxOn retirement
    timberTax := timberTaxOn timber
    incomeTax := it
    reconstructionTax := rt
    defenseTax := dt
    total := it + rt + dt
    payable := finalAmount (it + rt + dt) }

end Ritsuryo.Tax.Income
