module

public import Ritsuryo.Tax.Penalty
meta import Ritsuryo.Basis

/-!
# 加算税の証明（PEN-1）
-/

public section

namespace Ritsuryo.Tax.Penalty

/-- 無申告加算税の第66条第2項と第3項の一致（PEN-1）。実装は第3項の区分の式（加算後累積納付税額の区分ごとの額 −
累積納付税額の区分ごとの額）で計算する。加算後累積納付税額が300万円以下なら、この式は第2項の文言
（納付すべき税額 × 割合 + 50万円を超える部分 × 百分の五）と同じ額になる。300万円を超えても、
区分ごとの額は納付すべき税額について単調に増える。割合は第1項の百分の十五（予知の後）と百分の十（予知の前）。 -/
@[ritsuryo_proof "PEN-1", ritsuryo_basis "国税通則法" "第66条第2項",
  ritsuryo_basis "国税通則法" "第66条第3項"]
theorem pen1_no_return_tiers (rate tax tax' prior : Nat) (hr : rate = 10 ∨ rate = 15) :
    (tax + prior ≤ 3000000 → noReturnCents rate tax prior = noReturnCentsArt2 rate tax prior) ∧
      (tax ≤ tax' → noReturnCents rate tax prior ≤ noReturnCents rate tax' prior) := by
  unfold noReturnCents noReturnCentsArt2 tieredCents
  rcases hr with rfl | rfl <;> constructor <;> intro h <;> omega

end Ritsuryo.Tax.Penalty
