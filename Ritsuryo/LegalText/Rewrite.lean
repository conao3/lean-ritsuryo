module

public import Ritsuryo.LegalText.Data
meta import Ritsuryo.Basis

/-!
# 読替えの完全一致と適用順序

入管法第13条第7項が引用する第41条第1項の「但し」は、2024年6月10日施行版では
「ただし」になっている。取得した2版と引用文のUnicode符号位置列で完全一致を検査する。
水産業協同組合法第92条第5項と第105条第5項の指定は、第70条第3項による読替えを
適用した文を対象とする。元の第34条の2第3項に直接当てる場合との差を示す。

`replaceChecked` は最初の完全一致を置換し、一致が0件なら失敗する実装。
法的な準用の意味全体を定める仕様ではなく、表記の整合を検査するための仕様。
`immigration_*` は改正前後の一致、不一致、表記を揃えた場合の一致を証明する。
`fish_*` は中間の文字列が必要なこと、適用順を入れ替えると結果が変わることを証明する。
法的効力や個別事件への適用はこれらの符号位置列の定理の対象に含めない。
原文と符号位置列の対応は `scripts/gen_read_as.py --check` で検査する。
-/

@[expose] public section

namespace Ritsuryo.LegalText

/-- 最初の完全一致を置換する。空の検索語と、一致が0件の場合は失敗する。
末尾への構造的再帰なので、ネイティブの文字列探索を信頼せずカーネルで評価できる。 -/
def replaceChecked (source needle replacement : List Nat) : Option (List Nat) :=
  match source with
  | [] => none
  | c :: cs =>
    if needle.isEmpty then none
    else if needle.isPrefixOf source then some (replacement ++ source.drop needle.length)
    else (replaceChecked cs needle replacement).map (c :: ·)

/-- 完全一致の出現を、純粋な置換の成功として判定する。 -/
def containsText (source needle : List Nat) : Bool :=
  (replaceChecked source needle []).isSome

/-- 一致が0件の場合は原文を返す、比較実験用の置換。 -/
def replaceOrKeep (source needle replacement : List Nat) : List Nat :=
  (replaceChecked source needle replacement).getD source

/-- 検査に使う読替え前後の文字列は、引用元の条文にそのまま現れる。 -/
theorem immigration_quote_verified :
    containsText immigrationReadAsTokens immigrationQuoteTokens = true := by
  decide +kernel

/-- 2024年4月1日版の第41条第1項には引用文字列が存在する。 -/
theorem immigration_before_matches :
    (replaceChecked immigrationBeforeTokens immigrationNeedleTokens
      immigrationReplacementTokens).isSome = true := by
  decide +kernel

/-- 2024年6月10日版では、完全一致する引用文字列が存在しない。 -/
theorem immigration_after_missing :
    replaceChecked immigrationAfterTokens immigrationNeedleTokens
      immigrationReplacementTokens = none := by
  decide +kernel

/-- この2版の第41条第1項の差は、「但し」を「ただし」に置換したものと一致する。 -/
theorem immigration_change_is_spelling :
    replaceOrKeep immigrationBeforeTokens kanjiButTokens kanaButTokens =
      immigrationAfterTokens := by
  decide +kernel

/-- 引用文の当該表記も揃えると、この版では完全一致する。検査用の比較として示す。 -/
theorem immigration_normalized_matches :
    (replaceChecked immigrationAfterTokens
      (replaceOrKeep immigrationNeedleTokens kanjiButTokens kanaButTokens)
      immigrationReplacementTokens).isSome = true := by
  decide +kernel

/-- 第70条第3項を先に適用した第34条の2第3項。 -/
@[ritsuryo_basis "水産業協同組合法" "第34条の2第3項・第70条第3項"]
def fishIntermediate : List Nat :=
  replaceOrKeep fishBaseTokens fishInnerNeedleTokens fishInnerReplacementTokens

/-- 第92条第5項と第105条第5項の指定、先行する第70条の指定を原文で確認する。 -/
theorem fish_outer_quotes_verified :
    containsText fishOuter92Tokens fishOuterQuoteTokens = true ∧
    containsText fishOuter105Tokens fishOuterQuoteTokens = true ∧
    containsText fishInnerTokens fishInnerQuoteTokens = true := by
  decide +kernel

/-- 元の条文には存在しない文字列が、指定された先行読替え後には存在する。 -/
theorem fish_intermediate_required :
    replaceChecked fishBaseTokens fishOuterNeedleTokens fishOuterReplacementTokens = none ∧
    (replaceChecked fishIntermediate fishOuterNeedleTokens
      fishOuterReplacementTokens).isSome = true := by
  decide +kernel

/-- 指定どおりの二段階の読替えで、列挙される第12項の引用がなくなる。 -/
theorem fish_final_text :
    replaceOrKeep fishIntermediate fishOuterNeedleTokens fishOuterReplacementTokens =
      fishExpectedTokens := by
  decide +kernel

/-- 二つの完全一致置換は可換でない。失敗を無視する単純な置換でも、逆順だと結果が違う。 -/
theorem fish_rewrites_do_not_commute :
    replaceOrKeep
      (replaceOrKeep fishBaseTokens fishInnerNeedleTokens fishInnerReplacementTokens)
      fishOuterNeedleTokens fishOuterReplacementTokens ≠
    replaceOrKeep
      (replaceOrKeep fishBaseTokens fishOuterNeedleTokens fishOuterReplacementTokens)
      fishInnerNeedleTokens fishInnerReplacementTokens := by
  decide +kernel

end Ritsuryo.LegalText
