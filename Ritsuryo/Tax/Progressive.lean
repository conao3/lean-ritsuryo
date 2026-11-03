module

meta import Ritsuryo.Basis

/-!
# 超過累進の税率表

所得税法第89条と相続税法第16条は、どちらも「金額を表の上欄の区分に分け、区分ごとに下欄の税率を掛けて合計する」
という超過累進の形で書かれている。このファイルはその共通の形を、税率表 `List Bracket` と積み上げの関数
`progressiveCents` で表す。

税率は「百分の五」のように百分率で書かれるので、積み上げの結果は百分の一円（銭）単位の自然数で持ち、
割り算による端数を出さない。
-/

@[expose] public section

namespace Ritsuryo.Tax

/-- 税率表の 1 行。前の行の上限を超え `upper` 円以下の部分に、百分の `rate` を掛ける。
最後の行は `upper = none`（「…を超える金額」）。 -/
structure Bracket where
  upper : Option Nat
  rate : Nat
  deriving Repr, DecidableEq

/-- 条文どおりの積み上げ。`x` 円を区分に分け、区分ごとの金額に税率を掛けて合計する（百分の一円単位）。
`lower` はその行の下限（前の行の上限）。`x` が下限以下の行は、自然数の引き算が 0 になって何も足さない。 -/
@[ritsuryo_basis "所得税法" "第89条第1項", ritsuryo_basis "相続税法" "第16条"]
def progressiveCents : List Bracket → Nat → Nat → Nat
  | [], _, _ => 0
  | b :: bs, lower, x =>
    match b.upper with
    | some u => (min x u - lower) * b.rate + progressiveCents bs u x
    | none => (x - lower) * b.rate

end Ritsuryo.Tax
