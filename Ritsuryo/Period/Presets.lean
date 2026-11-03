module

public import Ritsuryo.Period.Impl
public import Ritsuryo.Period.Rollover
meta import Ritsuryo.Basis

/-!
# 個別の期間（控訴・上告・即時抗告・所得税の確定申告の期限）

個別の法律が定める期間の長さと起算点を、民法・民事訴訟法・国税通則法の期間計算と繰り下げに当てはめる。
計算そのものは `Period.compute`（PER-1 で民法第140条・第143条の仕様と一致を証明済み）と
`Period.rollover`（ROL-1 で最小性を証明済み）が行う。

民事訴訟法の期間は民法に従って計算し（民事訴訟法第95条第1項）、末日が日曜日・土曜日・国民の祝日に関する法律に
規定する休日・1月2日・1月3日・12月29日から12月31日までに当たるときは、その翌日に満了する（同条第3項）。
控訴期間・即時抗告期間は不変期間で、裁判所は伸縮できない（同法第96条第1項ただし書）。

e-Gov 法令履歴 `408AC0000000109_20260624_508AC0000000046`（民事訴訟法）、
`340AC0000000033_20261001_507AC0000000070`（所得税法）。

> 民事訴訟法 第二百八十五条　控訴は、電子判決書又は第二百五十四条第二項の規定により当事者及び法定代理人、主文、請求並びに理由の要旨が記録された電子調書の送達を受けた日から二週間の不変期間内に提起しなければならない。ただし、その期間前に提起した控訴の効力を妨げない。
>
> 民事訴訟法 第三百十三条　前章の規定は、特別の定めがある場合を除き、上告及び上告審の訴訟手続について準用する。
>
> 民事訴訟法 第三百三十二条　即時抗告は、裁判の告知を受けた日から一週間の不変期間内にしなければならない。
>
> 所得税法 第百二十条　居住者は、…第三期（その年の翌年二月十六日から三月十五日までの期間をいう。以下この節において同じ。）において、税務署長に対し、次に掲げる事項を記載した申告書を提出しなければならない。
-/

@[expose] public section

namespace Ritsuryo.Period

/-- 民事訴訟法の個別の期間。 -/
structure CourtPeriod where
  /-- CLI のサブコマンドなどで使う名前 -/
  name : String
  /-- 期間の名称 -/
  title : String
  /-- 期間を定める規定（法令名、条） -/
  provisions : List (String × String)
  /-- 起算点となる事実 -/
  event : String
  length : Length
  /-- 不変期間か（民事訴訟法第96条第1項ただし書） -/
  invariable : Bool
  deriving Repr

/-- 控訴期間（民事訴訟法第285条）。判決書の送達を受けた日から2週間。 -/
@[ritsuryo_basis "民事訴訟法" "第285条"]
def appealPeriod : CourtPeriod :=
  { name := "appeal", title := "控訴期間", provisions := [("民事訴訟法", "第285条")]
    event := "電子判決書（または判決に代わる電子調書）の送達を受けた日", length := .weeks 2
    invariable := true }

/-- 上告期間（民事訴訟法第313条で第285条を準用）。判決書の送達を受けた日から2週間。 -/
@[ritsuryo_basis "民事訴訟法" "第313条", ritsuryo_basis "民事訴訟法" "第285条"]
def finalAppealPeriod : CourtPeriod :=
  { name := "final-appeal", title := "上告期間"
    provisions := [("民事訴訟法", "第313条"), ("民事訴訟法", "第285条")]
    event := "電子判決書（または判決に代わる電子調書）の送達を受けた日", length := .weeks 2
    invariable := true }

/-- 即時抗告期間（民事訴訟法第332条）。裁判の告知を受けた日から1週間。 -/
@[ritsuryo_basis "民事訴訟法" "第332条"]
def immediateAppealPeriod : CourtPeriod :=
  { name := "immediate-appeal", title := "即時抗告期間", provisions := [("民事訴訟法", "第332条")]
    event := "裁判の告知を受けた日", length := .weeks 1, invariable := true }

/-- 民事訴訟法の期間の末日。初日を算入せず（民法第140条）、末日が休日なら繰り下げる（民事訴訟法第95条第3項）。
`national` は国民の祝日に関する法律に規定する休日の判定。繰り下げ先が366日以内に見つからなければ `none`。 -/
@[ritsuryo_basis "民事訴訟法" "第95条第1項", ritsuryo_basis "民事訴訟法" "第95条第3項",
  ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
def courtDeadline (national : Date → Bool) (p : CourtPeriod) (event : Date) :
    Expiry × Option Date :=
  let e := compute event false p.length
  (e, rollover (RolloverRule.civilProcedure95.isHoliday national) 366 e.expiry)

/-- 所得税の確定申告の期限（第三期の末日）。その年の翌年三月十五日で、休日などに当たるときは国税通則法第10条第2項で
繰り下げる。 -/
@[ritsuryo_basis "所得税法" "第120条第1項"]
def incomeTaxReturnDue (year : Int) : Date :=
  ⟨year + 1, 3, 15⟩

/-- 所得税の確定申告の期限を国税通則法第10条第2項で繰り下げた日。`general` は1月2日・3日を一般の休日とするか。 -/
@[ritsuryo_basis "所得税法" "第120条第1項", ritsuryo_basis "国税通則法" "第10条第2項"]
def incomeTaxReturnDeadline (national : Date → Bool) (general : Bool) (year : Int) : Option Date :=
  rollover ((RolloverRule.nationalTax10 general).isHoliday national) 366 (incomeTaxReturnDue year)

end Ritsuryo.Period
