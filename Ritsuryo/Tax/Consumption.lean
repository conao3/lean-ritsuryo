module

meta import Ritsuryo.Basis

/-!
# 消費税の税率と適格請求書の税額（消費税法 第29条、地方税法 第72条の83、消費税法施行令 第70条の10）

消費税の税率は国の消費税（消費税法第29条）と地方消費税（地方税法第72条の83、消費税額の七十八分の二十二）を
合わせて、標準税率 10%・軽減税率 8% になる。CON-1 はこの合成を有理数として確かめる。

適格請求書（インボイス）に書く消費税額等は、税率ごとに税抜価額か税込価額を合計し、その合計に一度だけ
百分の十（軽減は百分の八）か百十分の十（軽減は百八分の八）を掛けて、一円未満の端数を処理する
（消費税法施行令第70条の10）。端数の処理（切捨て・切上げ・四捨五入）は発行者が選ぶ。
品目ごとに端数を処理して足すことは認められておらず、CON-2 はその差が品目の数より小さいことを示す。

e-Gov 法令履歴 `363AC0000000108_20261101_507AC0000000013`（消費税法）、
`363CO0000000360_20261101_507CO0000000125`（消費税法施行令）、`325AC0000000226_20261101_508AC0000000002`（地方税法）。

> 消費税法 第二十九条　消費税の税率は、次の各号に掲げる区分に応じ当該各号に定める率とする。
> 　一　課税資産の譲渡等（軽減対象課税資産の譲渡等を除く。）、特定課税仕入れ及び保税地域から引き取られる課税貨物（軽減対象課税貨物を除く。）　百分の七・八
> 　二　軽減対象課税資産の譲渡等及び保税地域から引き取られる軽減対象課税貨物　百分の六・二四
>
> 地方税法 第七十二条の八十三　地方消費税の税率は、七十八分の二十二とする。
>
> 消費税法施行令 第七十条の十　法第五十七条の四第一項第五号に規定する政令で定める方法は、次の各号に掲げる方法のいずれかとする。この場合において、当該各号に掲げる方法により算出した金額に一円未満の端数が生じたときは、当該端数を処理するものとする。
> 　一　法第五十七条の四第一項第四号に規定する課税資産の譲渡等に係る税抜価額を税率の異なるごとに区分して合計した金額に百分の十（当該合計した金額が軽減対象課税資産の譲渡等に係るものである場合には、百分の八）を乗じて算出する方法
> 　二　法第五十七条の四第一項第四号に規定する課税資産の譲渡等に係る税込価額を税率の異なるごとに区分して合計した金額に百十分の十（当該合計した金額が軽減対象課税資産の譲渡等に係るものである場合には、百八分の八）を乗じて算出する方法
-/

@[expose] public section

namespace Ritsuryo.Tax.Consumption

/-- 税率の区分。 -/
inductive Rate where
  /-- 標準税率（消費税法第29条第1号） -/
  | standard
  /-- 軽減税率（消費税法第29条第2号） -/
  | reduced
  deriving Repr, DecidableEq, Inhabited

/-- 国の消費税の税率を一万分の一単位で表したもの。百分の七・八は 780、百分の六・二四は 624。 -/
@[ritsuryo_basis "消費税法" "第29条"]
def Rate.nationalPerTenThousand : Rate → Nat
  | .standard => 780
  | .reduced => 624

/-- 消費税と地方消費税を合わせた税率（百分率）。標準 10、軽減 8。 -/
@[ritsuryo_basis "消費税法" "第29条", ritsuryo_basis "地方税法" "第72条の83"]
def Rate.percent : Rate → Nat
  | .standard => 10
  | .reduced => 8

/-- 適格請求書に書く価額の種類（消費税法施行令第70条の10第1号・第2号）。 -/
inductive PriceBasis where
  /-- 税抜価額の合計に百分の十（百分の八）を掛ける -/
  | exclusive
  /-- 税込価額の合計に百十分の十（百八分の八）を掛ける -/
  | inclusive
  deriving Repr, DecidableEq, Inhabited

/-- 一円未満の端数の処理方法。 -/
inductive Rounding where
  | floor
  | ceil
  | halfUp
  deriving Repr, DecidableEq, Inhabited

/-- `a / d` の一円未満を `mode` で処理した額。四捨五入は 0.5 円以上を切り上げる。 -/
@[ritsuryo_basis "消費税法施行令" "第70条の10"]
def roundDiv (mode : Rounding) (a d : Nat) : Nat :=
  match mode with
  | .floor => a / d
  | .ceil => (a + d - 1) / d
  | .halfUp => (2 * a + d) / (2 * d)

/-- 価額 `price` に掛ける割合を `分子 / 分母` で返す。税抜は 10/100（8/100）、税込は 10/110（8/108）。 -/
@[ritsuryo_basis "消費税法施行令" "第70条の10第1号", ritsuryo_basis "消費税法施行令" "第70条の10第2号"]
def factor (basis : PriceBasis) (rate : Rate) : Nat × Nat :=
  match basis with
  | .exclusive => (rate.percent, 100)
  | .inclusive => (rate.percent, 100 + rate.percent)

/-- 価額に割合を掛けて端数を処理した税額。 -/
@[ritsuryo_basis "消費税法施行令" "第70条の10"]
def taxOf (mode : Rounding) (basis : PriceBasis) (rate : Rate) (price : Nat) : Nat :=
  let (n, d) := factor basis rate
  roundDiv mode (price * n) d

/-- 請求書の 1 行。 -/
structure Item where
  price : Nat
  rate : Rate
  deriving Repr, DecidableEq

/-- 税率ごとの合計と税額。 -/
structure RateTotal where
  rate : Rate
  priceTotal : Nat
  tax : Nat
  perItemTax : Nat
  deriving Repr

/-- 適格請求書の税率ごとの税額（消費税法施行令第70条の10）。価額を税率ごとに合計し、合計に一度だけ割合を掛けて
端数を処理する。`perItemTax` は比較のために品目ごとに端数を処理して足した額で、請求書には使わない。 -/
@[ritsuryo_basis "消費税法施行令" "第70条の10"]
def invoiceTax (mode : Rounding) (basis : PriceBasis) (items : List Item) : List RateTotal :=
  [Rate.standard, Rate.reduced].filterMap fun r =>
    let xs := items.filter (·.rate == r)
    if xs.isEmpty then none
    else
      let total := (xs.map (·.price)).sum
      some { rate := r, priceTotal := total, tax := taxOf mode basis r total
             perItemTax := (xs.map fun i => taxOf mode basis r i.price).sum }

end Ritsuryo.Tax.Consumption
