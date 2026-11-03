module

public import Ritsuryo.Tax.Rounding
meta import Ritsuryo.Basis

/-!
# 加算税（国税通則法 第65条〜第68条）

加算税は、納付すべき税額に割合を掛けた額で、割合は加算税の種類と、修正申告・期限後申告・納付が
いつ行われたか（調査の通知の前か、通知の後で更正・決定を予知する前か、予知の後か）で決まる。
「調査があったことにより更正があるべきことを予知して」いたかどうかは事実の判断なので、利用者が `Timing` で渡す。

計算の基礎となる税額は一万円未満を切り捨て（国税通則法第118条第3項）、加算税の額は百円未満を切り捨て、
全額が五千円未満なら 0 にする（第119条第4項）。

このファイルが扱わないもの: 帳簿の提示がない場合などの加重（第65条第4項、第66条第5項）、正当な理由がある
事実の控除（第65条第5項）、期限内申告の意思があった場合の無申告加算税の不適用（第66条第9項）。
いずれも事実の判断を含む。正当な理由などで計算から外す税額は、利用者が `tax` から除いて渡す。

e-Gov 法令履歴 `337AC0000000066_20261101_507AC0000000013`。

> 第六十五条　期限内申告書…が提出された場合…において、修正申告書の提出又は更正があつたときは、当該納税者に対し、その修正申告又は更正に基づき第三十五条第二項…の規定により納付すべき税額に百分の十の割合（修正申告書の提出が、その申告に係る国税についての調査があつたことにより当該国税について更正があるべきことを予知してされたものでないときは、百分の五の割合）を乗じて計算した金額に相当する過少申告加算税を課する。
> ２　前項の規定に該当する場合…において、前項に規定する納付すべき税額（同項の修正申告又は更正前に当該修正申告又は更正に係る国税について修正申告書の提出又は更正があつたときは、その国税に係る累積増差税額を加算した金額）がその国税に係る期限内申告税額に相当する金額と五十万円とのいずれか多い金額を超えるときは、同項の過少申告加算税の額は、同項の規定にかかわらず、同項の規定により計算した金額に、その超える部分に相当する税額（同項に規定する納付すべき税額が当該超える部分に相当する税額に満たないときは、当該納付すべき税額）に百分の五の割合を乗じて計算した金額を加算した金額とする。
> ６　第一項の規定は、修正申告書の提出が、その申告に係る国税についての調査があつたことにより当該国税について更正があるべきことを予知してされたものでない場合において、その申告に係る国税についての調査に係る…通知（…「調査通知」という。）がある前に行われたものであるときは、適用しない。
>
> 第六十六条　…納付すべき税額に百分の十五の割合（期限後申告書又は第二号の修正申告書の提出が、その申告に係る国税についての調査があつたことにより当該国税について更正又は決定があるべきことを予知してされたものでないときは、百分の十の割合）を乗じて計算した金額に相当する無申告加算税を課する。…
> ２　前項の規定に該当する場合…において、前項に規定する納付すべき税額（…累積納付税額を加算した金額。…「加算後累積納付税額」という。）が五十万円を超えるときは、…その超える部分に相当する税額（…）に百分の五の割合を乗じて計算した金額を加算した金額とする。
> ３　第一項の規定に該当する場合において、加算後累積納付税額…が三百万円を超えるときは、…加算後累積納付税額を次の各号に掲げる税額に区分してそれぞれの税額に当該各号に定める割合（…予知してされたものでないときは、その割合から百分の五の割合を減じた割合。…）を乗じて計算した金額の合計額から累積納付税額を当該各号に掲げる税額に区分してそれぞれの税額に当該各号に定める割合を乗じて計算した金額の合計額を控除した金額とする。
> 　一　五十万円以下の部分に相当する税額　百分の十五の割合
> 　二　五十万円を超え三百万円以下の部分に相当する税額　百分の二十の割合
> 　三　三百万円を超える部分に相当する税額　百分の三十の割合
> ６　第一項の規定に該当する場合において、次の各号のいずれかに該当するときは、…納付すべき税額に百分の十の割合を乗じて計算した金額を加算した金額とする。（過去5年以内の無申告加算税・重加算税など）
> ８　期限後申告書又は第一項第二号の修正申告書の提出が、…予知してされたものでない場合において、その申告に係る国税についての調査通知がある前に行われたものであるときは、…当該納付すべき税額に百分の五の割合を乗じて計算した金額とする。
>
> 第六十七条　源泉徴収等による国税がその法定納期限までに完納されなかつた場合には、…納付された税額に百分の十の割合を乗じて計算した金額に相当する不納付加算税を徴収する。…
> ２　…その納付が、当該国税についての調査があつたことにより当該国税について当該告知があるべきことを予知してされたものでないときは、…当該納付された税額に百分の五の割合を乗じて計算した金額とする。
>
> 第六十八条　第六十五条第一項…の規定に該当する場合（修正申告書の提出が、…予知してされたものでない場合を除く。）において、納税者が…隠蔽し、又は仮装し…ていたときは、…過少申告加算税に代え、当該基礎となるべき税額に百分の三十五の割合を乗じて計算した金額に相当する重加算税を課する。
> ２　第六十六条第一項…の規定に該当する場合（…予知してされたものでない場合を除く。）において、…無申告加算税に代え、当該基礎となるべき税額に百分の四十の割合を乗じて計算した金額に相当する重加算税を課する。
> ３　前条第一項の規定に該当する場合（…）において、…不納付加算税に代え、当該基礎となるべき税額に百分の三十五の割合を乗じて計算した金額に相当する重加算税を徴収する。
> ４　前三項の規定に該当する場合において、次の各号のいずれか…に該当するときは、…基礎となるべき税額に百分の十の割合を乗じて計算した金額を加算した金額とする。（過去5年以内の無申告加算税等など）
-/

@[expose] public section

namespace Ritsuryo.Tax.Penalty

/-- 加算税の種類。 -/
inductive Kind where
  /-- 過少申告加算税（第65条） -/
  | underpayment
  /-- 無申告加算税（第66条） -/
  | noReturn
  /-- 不納付加算税（第67条） -/
  | nonWithholding
  deriving Repr, DecidableEq, Inhabited

/-- 修正申告・期限後申告・納付の時期。 -/
inductive Timing where
  /-- 調査通知の前に、更正・決定・告知を予知せずにした（第65条第6項、第66条第8項、第67条第2項） -/
  | beforeNotice
  /-- 調査通知の後、更正・決定・告知を予知する前にした -/
  | afterNotice
  /-- 更正・決定・告知を予知してした、または更正・決定・告知を受けた -/
  | afterPrediction
  deriving Repr, DecidableEq, Inhabited

/-- 入力。金額はすべて円。 -/
structure Input where
  kind : Kind
  timing : Timing
  /-- 今回の修正申告・期限後申告・更正・決定・納付で納付すべき税額 -/
  tax : Nat
  /-- それより前の修正申告・更正などで納付すべきだった税額の合計（累積増差税額・累積納付税額） -/
  priorTax : Nat := 0
  /-- 期限内申告税額（過少申告加算税の第65条第2項に使う） -/
  timelyTax : Nat := 0
  /-- 隠蔽・仮装があり、重加算税を課す（第68条） -/
  fraud : Bool := false
  /-- 過去5年以内に無申告加算税・重加算税を課されたなど、第66条第6項・第68条第4項の加重に当たる -/
  repeated : Bool := false
  deriving Repr

/-- 百分の `rate` を掛けた額（一円未満切捨て）。 -/
@[ritsuryo_basis "国税通則法" "第65条第1項"]
def pct (rate x : Nat) : Nat :=
  x * rate / 100

/-- 仕様: 第66条第2項の文言どおりの無申告加算税（300万円以下の場合）。
納付すべき税額に `rate` の割合を掛け、加算後累積納付税額が50万円を超える部分（納付すべき税額が限度）に
百分の五を掛けて足す（百分の一円単位）。 -/
@[ritsuryo_basis "国税通則法" "第66条第1項", ritsuryo_basis "国税通則法" "第66条第2項"]
def noReturnCentsArt2 (rate tax prior : Nat) : Nat :=
  tax * rate + min tax (tax + prior - 500000) * 5

/-- 第66条第3項の区分（50万円以下、50万円超300万円以下、300万円超）に分けて割合を掛けた額（百分の一円単位）。
`rate` は第1号の割合（予知の後は 15、予知の前は 10）で、第2号・第3号はそれぞれ 5・15 を足す。 -/
@[ritsuryo_basis "国税通則法" "第66条第3項"]
def tieredCents (rate x : Nat) : Nat :=
  min x 500000 * rate + (min x 3000000 - 500000) * (rate + 5) + (x - 3000000) * (rate + 15)

/-- 実装: 第66条第3項の形の無申告加算税（百分の一円単位）。加算後累積納付税額の区分ごとの額から、
累積納付税額の区分ごとの額を引く。300万円以下では第2項と一致する（PEN-1）。 -/
@[ritsuryo_basis "国税通則法" "第66条第3項"]
def noReturnCents (rate tax prior : Nat) : Nat :=
  tieredCents rate (tax + prior) - tieredCents rate prior

/-- 計算の途中の値と結果。 -/
structure Result where
  /-- 割合を掛ける税額（一万円未満切捨て後） -/
  base : Nat
  /-- 過少申告加算税の第65条第2項で百分の五を加える部分（一万円未満切捨て後） -/
  excess : Nat
  /-- 適用した規定 -/
  provisions : List String
  totalBeforeRounding : Nat
  total : Nat
  deriving Repr

/-- 加算税の額。重加算税（`fraud`）は予知の後だけに当てる。入力の組み合わせが条文に当たらないときは
`Except.error` で理由を返す。 -/
@[ritsuryo_basis "国税通則法" "第65条第1項", ritsuryo_basis "国税通則法" "第65条第2項",
  ritsuryo_basis "国税通則法" "第65条第6項", ritsuryo_basis "国税通則法" "第66条第1項",
  ritsuryo_basis "国税通則法" "第66条第3項", ritsuryo_basis "国税通則法" "第66条第6項",
  ritsuryo_basis "国税通則法" "第66条第8項", ritsuryo_basis "国税通則法" "第67条第1項",
  ritsuryo_basis "国税通則法" "第67条第2項", ritsuryo_basis "国税通則法" "第68条第1項",
  ritsuryo_basis "国税通則法" "第68条第2項", ritsuryo_basis "国税通則法" "第68条第3項",
  ritsuryo_basis "国税通則法" "第68条第4項", ritsuryo_basis "国税通則法" "第118条第3項",
  ritsuryo_basis "国税通則法" "第119条第4項"]
def compute (i : Input) : Except String Result := do
  let base := incidentalBase i.tax
  let prior := incidentalBase i.priorTax
  if i.fraud && i.timing != .afterPrediction then
    throw "重加算税は、更正・決定・告知を予知した後の申告・納付と、更正・決定・告知にだけ課される（第68条）"
  let finish (excess raw : Nat) (provisions : List String) : Result :=
    { base, excess, provisions, totalBeforeRounding := raw, total := penaltyFinal raw }
  let extra (yes : Bool) (provision : String) : Nat × List String :=
    if yes then (pct 10 base, [provision]) else (0, [])
  match i.kind with
  | .underpayment =>
    if i.repeated && !i.fraud then
      throw "過少申告加算税には過去の加算税による加重がない。重加算税（--fraud）のときだけ使える（第68条第4項）"
    if i.fraud then
      let (e, ps) := extra i.repeated "国税通則法 第68条第4項"
      return finish 0 (pct 35 base + e) (["国税通則法 第68条第1項"] ++ ps)
    match i.timing with
    | .beforeNotice => return finish 0 0 ["国税通則法 第65条第6項"]
    | t =>
      let rate := if t == .afterPrediction then 10 else 5
      let excess := incidentalBase (min i.tax (i.tax + i.priorTax - max i.timelyTax 500000))
      return finish excess (pct rate base + pct 5 excess)
        (["国税通則法 第65条第1項"] ++ (if excess > 0 then ["国税通則法 第65条第2項"] else []))
  | .noReturn =>
    if i.fraud then
      let (e, ps) := extra i.repeated "国税通則法 第68条第4項"
      return finish 0 (pct 40 base + e) (["国税通則法 第68条第2項"] ++ ps)
    match i.timing with
    | .beforeNotice =>
      if i.repeated then throw "調査通知の前の自主的な期限後申告には第66条第6項の加重がない"
      return finish 0 (pct 5 base) ["国税通則法 第66条第8項"]
    | t =>
      let rate := if t == .afterPrediction then 15 else 10
      let (e, ps) := extra i.repeated "国税通則法 第66条第6項"
      let tiers : List String :=
        if base + prior > 3000000 then ["国税通則法 第66条第3項"]
        else if base + prior > 500000 then ["国税通則法 第66条第2項"] else []
      return finish 0 (noReturnCents rate base prior / 100 + e)
        (["国税通則法 第66条第1項"] ++ tiers ++ ps)
  | .nonWithholding =>
    if i.fraud then
      let (e, ps) := extra i.repeated "国税通則法 第68条第4項"
      return finish 0 (pct 35 base + e) (["国税通則法 第68条第3項"] ++ ps)
    if i.repeated then
      throw "不納付加算税には過去の加算税による加重がない。重加算税（--fraud）のときだけ使える（第68条第4項）"
    match i.timing with
    | .afterPrediction => return finish 0 (pct 10 base) ["国税通則法 第67条第1項"]
    | _ => return finish 0 (pct 5 base) ["国税通則法 第67条第2項"]

end Ritsuryo.Tax.Penalty
