module

public import Ritsuryo.Tax.Rounding
public import Ritsuryo.Tax.Progressive
meta import Ritsuryo.Basis

/-!
# 相続税の総額（相続税法 第15条・第16条）と法定相続分（民法 第900条）

相続税の総額は次の順で計算する。

1. 課税価格の合計額から遺産に係る基礎控除額（3,000 万円 + 600 万円 × 相続人の数）を引く（第15条）。
2. 残り（課税遺産総額）を、相続人が民法第900条の法定相続分どおりに取得したものとして分ける（第16条）。
3. 相続人ごとの取得金額を税率表の区分に分けて積み上げ、全員分を合計する（第16条）。

相続人の数に入れる養子は、実子があれば 1 人、なければ 2 人までに限る（第15条第2項）。第16条の按分も
この数の相続人で行うので、法定相続分の計算にも同じ制限をかけた人数を使う。

端数は、相続人ごとの取得金額の千円未満と、相続税の総額の百円未満を切り捨てる
（国税庁 相続税法基本通達16-3。国税庁タックスアンサー No.4152 の計算順と同じ）。

e-Gov 法令履歴 `325AC0000000073_20260401_506AC0000000008`（相続税法）、
`129AC0000000089_20260624_508AC0000000045`（民法）。

> 相続税法 第十五条　相続税の総額を計算する場合においては、同一の被相続人から相続又は遺贈により財産を取得した全ての者に係る相続税の課税価格…の合計額から、三千万円と六百万円に当該被相続人の相続人の数を乗じて算出した金額との合計額（以下「遺産に係る基礎控除額」という。）を控除する。
>
> ２　前項の相続人の数は、同項に規定する被相続人の民法第五編第二章（相続人）の規定による相続人の数（当該被相続人に養子がある場合の当該相続人の数に算入する当該被相続人の養子の数は、次の各号に掲げる場合の区分に応じ当該各号に定める養子の数に限るものとし、相続の放棄があつた場合には、その放棄がなかつたものとした場合における相続人の数とする。）とする。
> 　一　当該被相続人に実子がある場合又は当該被相続人に実子がなく、養子の数が一人である場合　一人
> 　二　当該被相続人に実子がなく、養子の数が二人以上である場合　二人
>
> 第十六条　相続税の総額は、…課税価格に相当する金額の合計額からその遺産に係る基礎控除額を控除した残額を当該被相続人の前条第二項に規定する相続人の数に応じた相続人が民法第九百条（法定相続分）及び第九百一条（代襲相続人の相続分）の規定による相続分に応じて取得したものとした場合におけるその各取得金額（当該相続人が、一人である場合又はない場合には、当該控除した残額）につきそれぞれその金額を次の表の上欄に掲げる金額に区分してそれぞれの金額に同表の下欄に掲げる税率を乗じて計算した金額を合計した金額とする。
>
> | 千万円以下の金額 | 百分の十 |
> | 千万円を超え三千万円以下の金額 | 百分の十五 |
> | 三千万円を超え五千万円以下の金額 | 百分の二十 |
> | 五千万円を超え一億円以下の金額 | 百分の三十 |
> | 一億円を超え二億円以下の金額 | 百分の四十 |
> | 二億円を超え三億円以下の金額 | 百分の四十五 |
> | 三億円を超え六億円以下の金額 | 百分の五十 |
> | 六億円を超える金額 | 百分の五十五 |
>
> 民法 第九百条　同順位の相続人が数人あるときは、その相続分は、次の各号の定めるところによる。
> 　一　子及び配偶者が相続人であるときは、子の相続分及び配偶者の相続分は、各二分の一とする。
> 　二　配偶者及び直系尊属が相続人であるときは、配偶者の相続分は、三分の二とし、直系尊属の相続分は、三分の一とする。
> 　三　配偶者及び兄弟姉妹が相続人であるときは、配偶者の相続分は、四分の三とし、兄弟姉妹の相続分は、四分の一とする。
> 　四　子、直系尊属又は兄弟姉妹が数人あるときは、各自の相続分は、相等しいものとする。ただし、父母の一方のみを同じくする兄弟姉妹の相続分は、父母の双方を同じくする兄弟姉妹の相続分の二分の一とする。

この表は平成27年1月1日以後の相続に適用される。代襲相続（民法第901条）は扱わない。
-/

@[expose] public section

namespace Ritsuryo.Tax.Inheritance

/-- 第16条の表。 -/
@[ritsuryo_basis "相続税法" "第16条"]
def table : List Bracket := [
  ⟨some 10000000, 10⟩, ⟨some 30000000, 15⟩, ⟨some 50000000, 20⟩, ⟨some 100000000, 30⟩,
  ⟨some 200000000, 40⟩, ⟨some 300000000, 45⟩, ⟨some 600000000, 50⟩, ⟨none, 55⟩]

/-- 仕様: 第16条の文言どおり、取得金額を区分して税率を掛け、合計する（百分の一円単位）。 -/
@[ritsuryo_basis "相続税法" "第16条"]
def taxCentsSpec (x : Nat) : Nat :=
  progressiveCents table 0 x

/-- 実装: 国税庁の相続税の速算表（税率 × 金額 − 控除額）を百分の一円単位で書いたもの。
控除額は 0、50 万、200 万、700 万、1,700 万、2,700 万、4,200 万、7,200 万円。 -/
@[ritsuryo_basis "相続税法" "第16条"]
def quickCents (x : Nat) : Nat :=
  if x ≤ 10000000 then 10 * x
  else if x ≤ 30000000 then 15 * x - 50000000
  else if x ≤ 50000000 then 20 * x - 200000000
  else if x ≤ 100000000 then 30 * x - 700000000
  else if x ≤ 200000000 then 40 * x - 1700000000
  else if x ≤ 300000000 then 45 * x - 2700000000
  else if x ≤ 600000000 then 50 * x - 4200000000
  else 55 * x - 7200000000

/-- 相続人の構成。人数は相続の放棄がなかったものとして数える（第15条第2項）。
直系尊属は親等の最も近い者だけを数える（民法第889条第1項第1号ただし書）。 -/
structure Heirs where
  spouse : Bool
  biologicalChildren : Nat
  adoptedChildren : Nat
  ascendants : Nat
  fullSiblings : Nat
  halfSiblings : Nat
  deriving Repr, DecidableEq

/-- 相続人の数に入れる養子の数（第15条第2項）。実子があれば 1 人、なければ 2 人まで。 -/
@[ritsuryo_basis "相続税法" "第15条第2項"]
def countedAdopted (h : Heirs) : Nat :=
  if h.biologicalChildren > 0 then min h.adoptedChildren 1 else min h.adoptedChildren 2

/-- 相続人の区分。 -/
inductive HeirKind where
  | spouse
  | child
  | ascendant
  | fullSibling
  | halfSibling
  deriving Repr, DecidableEq

/-- 同順位の血族相続人の区分（民法第887条・第889条）。子がいれば子、いなければ直系尊属、
それもいなければ兄弟姉妹。 -/
inductive Rank where
  | children (n : Nat)
  | ascendants (n : Nat)
  | siblings (full half : Nat)
  | none
  deriving Repr, DecidableEq

/-- 第15条第2項の人数で数えた血族相続人の順位。 -/
@[ritsuryo_basis "民法" "第887条第1項", ritsuryo_basis "民法" "第889条第1項",
  ritsuryo_basis "相続税法" "第15条第2項"]
def rankOf (h : Heirs) : Rank :=
  let children := h.biologicalChildren + countedAdopted h
  if children > 0 then .children children
  else if h.ascendants > 0 then .ascendants h.ascendants
  else if h.fullSiblings + h.halfSiblings > 0 then .siblings h.fullSiblings h.halfSiblings
  else .none

/-- 遺産に係る基礎控除額の計算に使う相続人の数（第15条第2項）。 -/
@[ritsuryo_basis "相続税法" "第15条第2項"]
def heirCount (h : Heirs) : Nat :=
  (if h.spouse then 1 else 0) +
    match rankOf h with
    | .children n => n
    | .ascendants n => n
    | .siblings f s => f + s
    | .none => 0

/-- 遺産に係る基礎控除額（第15条第1項）。 -/
@[ritsuryo_basis "相続税法" "第15条第1項"]
def basicDeduction (h : Heirs) : Nat :=
  30000000 + 6000000 * heirCount h

/-- 配偶者と血族相続人の組の相続分を `(配偶者の分子, 血族全体の分子, 分母)` で返す（民法第900条第1号〜第3号、
第890条）。配偶者だけなら配偶者が全部、配偶者がいなければ血族相続人が全部を取る。 -/
@[ritsuryo_basis "民法" "第890条", ritsuryo_basis "民法" "第900条第1号",
  ritsuryo_basis "民法" "第900条第2号", ritsuryo_basis "民法" "第900条第3号"]
def groupShares (spouse : Bool) : Rank → Nat × Nat × Nat
  | .none => if spouse then (1, 0, 1) else (0, 0, 1)
  | .children _ => if spouse then (1, 1, 2) else (0, 1, 1)
  | .ascendants _ => if spouse then (2, 1, 3) else (0, 1, 1)
  | .siblings _ _ => if spouse then (3, 1, 4) else (0, 1, 1)

/-- 血族相続人の各自の重み（民法第900条第4号）。各自の相続分は相等しく、
父母の一方のみを同じくする兄弟姉妹（半血）は父母の双方を同じくする兄弟姉妹（全血）の二分の一。 -/
@[ritsuryo_basis "民法" "第900条第4号"]
def members : Rank → List (HeirKind × Nat)
  | .children n => List.replicate n (.child, 1)
  | .ascendants n => List.replicate n (.ascendant, 1)
  | .siblings f s => List.replicate f (.fullSibling, 2) ++ List.replicate s (.halfSibling, 1)
  | .none => []

/-- 重みの合計。 -/
@[ritsuryo_basis "民法" "第900条第4号"]
def totalWeight (r : Rank) : Nat :=
  ((members r).map (·.2)).sum

/-- 法定相続分。共通の分母と、相続人ごとの `(区分, 分子)` を返す。
分母は `組の分母 × 重みの合計`。配偶者の分子は `配偶者の分子 × 重みの合計`、
血族相続人の分子は `血族全体の分子 × 各自の重み`。 -/
structure Shares where
  denominator : Nat
  shares : List (HeirKind × Nat)
  deriving Repr

@[ritsuryo_basis "民法" "第900条"]
def statutoryShares (spouse : Bool) (r : Rank) : Shares :=
  let (s, g, d) := groupShares spouse r
  let w := max (totalWeight r) 1
  { denominator := d * w
    shares := (if spouse then [(.spouse, s * w)] else []) ++
      (members r).map fun (k, wk) => (k, g * wk) }

/-- 相続人ごとの取得金額（千円未満切捨て）と税額。 -/
structure HeirTax where
  kind : HeirKind
  numerator : Nat
  acquired : Nat
  tax : Nat
  deriving Repr

/-- 相続税の総額の計算の途中の値と結果。 -/
structure Result where
  heirCount : Nat
  basicDeduction : Nat
  taxableEstate : Nat
  denominator : Nat
  heirs : List HeirTax
  totalBeforeRounding : Nat
  total : Nat
  deriving Repr

/-- 取得金額 `x` 円に対する税額（円）。`x` は千円の倍数なので割り切れる。 -/
@[ritsuryo_basis "相続税法" "第16条"]
def taxOn (x : Nat) : Nat :=
  quickCents x / 100

/-- 相続税の総額。`value` は課税価格の合計額。相続人がいないときは課税遺産総額をそのまま表に当てる
（第16条かっこ書。相続人が 1 人のときも同じ結果になる）。 -/
@[ritsuryo_basis "相続税法" "第15条第1項", ritsuryo_basis "相続税法" "第16条"]
def compute (value : Nat) (h : Heirs) : Result :=
  let deduction := basicDeduction h
  let estate := value - deduction
  let sh := statutoryShares h.spouse (rankOf h)
  let heirs := sh.shares.map fun (k, num) =>
    let acquired := floorTo 1000 (estate * num / sh.denominator)
    { kind := k, numerator := num, acquired, tax := taxOn acquired : HeirTax }
  let raw := if sh.shares.isEmpty then taxOn (floorTo 1000 estate)
    else (heirs.map (·.tax)).sum
  { heirCount := heirCount h
    basicDeduction := deduction
    taxableEstate := estate
    denominator := sh.denominator
    heirs
    totalBeforeRounding := raw
    total := floorTo 100 raw }

end Ritsuryo.Tax.Inheritance
