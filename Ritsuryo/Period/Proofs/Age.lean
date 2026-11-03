module

public import Ritsuryo.Period.Age
public import Ritsuryo.Period.Proofs.Properties
meta import Ritsuryo.Basis

/-!
# 年齢計算の証明（AGE-1、AGE-2）

- AGE-1（`age1_attainment`）: 実装の `attainmentDate`（通算日による計算）が仕様 `attainmentSpec` と一致し、
  `n` 年後の誕生日の前日（その月に誕生日の日付がなければ月の末日）になる。2月29日生まれは毎年2月28日に年を取る。
- AGE-2（`age2_monotone_and_steps`）: `ageOn` が返す年齢 `n` について、`n` 歳に達する日 ≤ その日 < `n + 1` 歳に達する日が
  成り立ち、年齢は日付について単調で、達する日ごとにちょうど 1 増える。

証明の中心は、`n` 歳に達する日の年が「出生年 + n」（1月1日生まれだけ前年の12月31日なので 1 引く）になること
（`attainment_year`）。年が違えば通算日の大小が決まる（CAL-3）ので、達する日が `n` について狭義単調増加になり
（`attainment_strict`）、`ageOn` が年の差 `k` の前後 3 通り（`k - 1`・`k`・`k + 1`）だけを調べれば足りることが分かる。
-/

public section

namespace Ritsuryo.Period.Age

open Date

/-- `n` 歳に達する日の仕様を展開した式。`n` 年後の誕生日がその月にあればその前日、なければその月の末日になる。 -/
theorem attainment_formula (birth : Date) (n : Nat) :
    attainmentSpec birth n =
      if birth.day ≤ daysInMonth (birth.year + n) birth.month then
        prevDate ⟨birth.year + n, birth.month, birth.day⟩
      else (⟨birth.year + n, birth.month⟩ : YearMonth).lastDay := by
  simp only [attainmentSpec, Civil.expiryFromStartSpec, Civil.correspondingDaySpec,
    Civil.lastMonthSpec, YearMonth.daysInMonth]
  by_cases hd : birth.day ≤ daysInMonth (birth.year + n) birth.month <;> simp [hd]

/-- 有効な出生の日について、年齢に達する日は有効な日付になる。 -/
theorem attainment_valid (birth : Date) (h : birth.Valid) (n : Nat) :
    (attainmentSpec birth n).Valid :=
  spec_valid birth h (.years n)

/-- 年齢に達する日の実装 `attainmentDate` は仕様 `attainmentSpec` と等しい。PER-1 の `expiryFromStart_spec` を年の期間に当てる。 -/
theorem attainmentDate_eq (birth : Date) (h : birth.Valid) (n : Nat) :
    attainmentDate birth n = attainmentSpec birth n :=
  expiryFromStart_spec birth h (.years n)

/-- 実装の通算日 `attainmentDays` は、仕様の日の通算日と等しい。 -/
theorem attainmentDays_eq (birth : Date) (h : birth.Valid) (n : Nat) :
    attainmentDays birth n = toDays (attainmentSpec birth n) :=
  (spec_toDays birth h (.years n)).symm

/-- `n` 歳に達する日の年は、出生年 + `n`。1月1日生まれだけは前日が前年の12月31日になるので、出生年 + `n` - 1 になる。
`attainment_formula` を展開し、前日が月や年をまたぐかで場合分けする。 -/
theorem attainment_year (birth : Date) (h : birth.Valid) (n : Nat) :
    (attainmentSpec birth n).year =
      birth.year + n - (if birth.month = 1 ∧ birth.day = 1 then 1 else 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [attainment_formula]
  have hb := daysInMonth_ge (birth.year + n) birth.month h1 h2
  by_cases hd : birth.day ≤ daysInMonth (birth.year + n) birth.month
  · simp only [hd, ↓reduceIte, prevDate]
    by_cases hd1 : 1 < birth.day
    · simp only [hd1, ↓reduceIte]
      split <;> omega
    · simp only [hd1, ↓reduceIte]
      by_cases hm1 : 1 < birth.month
      · simp only [hm1, ↓reduceIte]
        split <;> omega
      · simp only [hm1, ↓reduceIte]
        split <;> omega
  · simp only [hd, ↓reduceIte, YearMonth.lastDay]
    split <;> omega

/-- 有効な日付どうしで年が小さいほうは、通算日も小さい（CAL-3 の順序の一致から）。 -/
theorem toDays_lt_of_year_lt (a b : Date) (ha : a.Valid) (hb : b.Valid) (h : a.year < b.year) :
    toDays a < toDays b :=
  (toDays_lt_iff a b ha hb).mp (Or.inl h)

/-- `n + 1` 歳に達する日は、`n` 歳に達する日より後にある。`attainment_year` で年が 1 違うことによる。 -/
theorem attainment_strict (birth : Date) (h : birth.Valid) (n : Nat) :
    attainmentDays birth n < attainmentDays birth (n + 1) := by
  rw [attainmentDays_eq birth h, attainmentDays_eq birth h]
  apply toDays_lt_of_year_lt _ _ (attainment_valid birth h n) (attainment_valid birth h (n + 1))
  rw [attainment_year birth h, attainment_year birth h]
  split <;> omega

/-- 年齢に達する日は年齢について単調。`attainment_strict` を `b` についての帰納法でつなぐ。 -/
theorem attainment_mono (birth : Date) (h : birth.Valid) (a b : Nat) (hab : a ≤ b) :
    attainmentDays birth a ≤ attainmentDays birth b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    omega
  | succ b ih =>
    by_cases he : a = b + 1
    · subst he
      omega
    · have := ih (by omega)
      have := attainment_strict birth h b
      omega

/-- 年齢に達する日は年齢について狭義単調。 -/
theorem attainment_strict_mono (birth : Date) (h : birth.Valid) (a b : Nat) (hab : a < b) :
    attainmentDays birth a < attainmentDays birth b := by
  have h1 := attainment_strict birth h a
  have h2 := attainment_mono birth h (a + 1) b hab
  omega

/-- 0 歳に「達する日」は出生の日の前日になる（0 年の期間の応当日は出生の日そのもの）。 -/
theorem attainment_zero (birth : Date) (h : birth.Valid) :
    attainmentDays birth 0 = toDays birth - 1 := by
  rw [attainmentDays_eq birth h, attainment_formula]
  have hy : birth.year + ((0 : Nat) : Int) = birth.year := by omega
  rw [hy]
  simp only [h.2.2.2, ↓reduceIte]
  rw [(toDays_prevDate birth h).1]

/-- 出生の日以後の日 `asOf` について、`ageOn` の年齢 `n` は「`n` 歳に達する日 ≤ `asOf` < `n + 1` 歳に達する日」を満たす。
年の差を `k` とすると、`k + 2` 歳に達する日は `asOf` の翌年以後、`k - 1` 歳に達する日は `asOf` の前年以前にある
（`attainment_year`）。これで `ageOn` の三つの分岐それぞれで上下の不等式が成り立つ。 -/
theorem ageOn_spec (birth asOf : Date) (hb : birth.Valid) (hd : asOf.Valid)
    (hle : toDays birth ≤ toDays asOf) :
    attainmentDays birth (ageOn birth asOf) ≤ toDays asOf ∧
      toDays asOf < attainmentDays birth (ageOn birth asOf + 1) := by
  have hyear : birth.year ≤ asOf.year := by
    by_cases hy : asOf.year < birth.year
    · have := toDays_lt_of_year_lt asOf birth hd hb hy
      omega
    · omega
  have hk : ((asOf.year - birth.year).toNat : Int) = asOf.year - birth.year := by omega
  generalize hkdef : (asOf.year - birth.year).toNat = k at hk
  have hlt (n : Nat) (hn : (attainmentSpec birth n).year < asOf.year) :
      attainmentDays birth n < toDays asOf := by
    rw [attainmentDays_eq birth hb]
    exact toDays_lt_of_year_lt _ _ (attainment_valid birth hb n) hd hn
  have hgt (n : Nat) (hn : asOf.year < (attainmentSpec birth n).year) :
      toDays asOf < attainmentDays birth n := by
    rw [attainmentDays_eq birth hb]
    exact toDays_lt_of_year_lt _ _ hd (attainment_valid birth hb n) hn
  have h2 : toDays asOf < attainmentDays birth (k + 2) := by
    apply hgt
    rw [attainment_year birth hb]
    split <;> omega
  have h0 := attainment_zero birth hb
  simp only [ageOn, hkdef]
  split
  · rename_i c1
    exact ⟨c1, h2⟩
  · rename_i c1
    split
    · rename_i c2
      exact ⟨c2, by omega⟩
    · rename_i c2
      have hk1 : 1 ≤ k := by
        by_cases hk0 : k = 0
        · subst hk0
          omega
        · omega
      have : k - 1 + 1 = k := by omega
      rw [this]
      refine ⟨?_, by omega⟩
      have := hlt (k - 1) (by rw [attainment_year birth hb]; split <;> omega)
      omega

/-- 1 歳に達する日は出生の日より後にある。1月1日生まれは同じ年の12月31日、それ以外は翌年の日になる。 -/
theorem birth_lt_attainment_one (birth : Date) (h : birth.Valid) :
    toDays birth < attainmentDays birth 1 := by
  rw [attainmentDays_eq birth h]
  by_cases hc : birth.month = 1 ∧ birth.day = 1
  · have ha : attainmentSpec birth 1 = ⟨birth.year, 12, 31⟩ := by
      rw [attainment_formula, hc.1, hc.2]
      simp [daysInMonth, prevDate]
    rw [ha]
    have hv : (⟨birth.year, 12, 31⟩ : Date).Valid := by
      simp [Valid, daysInMonth]
    apply (toDays_lt_iff _ _ h hv).mp
    change Lt _ _
    simp [Lt, hc.1]
  · apply toDays_lt_of_year_lt _ _ h (attainment_valid birth h 1)
    rw [attainment_year birth h]
    simp only [hc, ↓reduceIte]
    omega

/-- 「`n` 歳に達する日 ≤ `asOf` < `n + 1` 歳に達する日」を満たす `n` は一つしかなく、`ageOn` の値に等しい。
`ageOn` の値と `n` が違えば、`attainment_mono` で区間が重ならないことに反する。 -/
theorem ageOn_unique (birth asOf : Date) (hb : birth.Valid) (hd : asOf.Valid)
    (hle : toDays birth ≤ toDays asOf) (n : Nat) (h1 : attainmentDays birth n ≤ toDays asOf)
    (h2 : toDays asOf < attainmentDays birth (n + 1)) : ageOn birth asOf = n := by
  obtain ⟨s1, s2⟩ := ageOn_spec birth asOf hb hd hle
  by_cases hlt : ageOn birth asOf < n
  · have := attainment_mono birth hb (ageOn birth asOf + 1) n hlt
    omega
  · by_cases hgt : n < ageOn birth asOf
    · have := attainment_mono birth hb (n + 1) (ageOn birth asOf) hgt
      omega
    · omega

/-- AGE-1: 実装の `attainmentDate` は仕様 `attainmentSpec` と等しく、`n` 年後の誕生日の前日（その月に誕生日の日付が
なければ月の末日）になる。2月29日生まれは、閏年には2月29日の前日、平年には2月の末日として、どちらも2月28日に `n` 歳になる。
前半は `attainmentDate_eq` と `attainment_formula`、2月29日は `n` 年後が閏年かで場合分けする。 -/
@[ritsuryo_proof "AGE-1", ritsuryo_basis "年齢計算ニ関スル法律" "第2項",
  ritsuryo_basis "民法" "第143条第2項"]
theorem age1_attainment (birth : Date) (h : birth.Valid) (n : Nat) :
    attainmentDate birth n = attainmentSpec birth n ∧
      attainmentDate birth n =
        (if birth.day ≤ daysInMonth (birth.year + n) birth.month then
          prevDate ⟨birth.year + n, birth.month, birth.day⟩
        else (⟨birth.year + n, birth.month⟩ : YearMonth).lastDay) ∧
      (birth.month = 2 → birth.day = 29 → attainmentDate birth n = ⟨birth.year + n, 2, 28⟩) := by
  have he := attainmentDate_eq birth h n
  refine ⟨he, by rw [he, attainment_formula], fun hm hd => ?_⟩
  rw [he, attainment_formula, hm, hd]
  by_cases hl : isLeapYear (birth.year + n) = true
  · simp [daysInMonth, hl, prevDate]
  · simp [daysInMonth, hl, YearMonth.lastDay, YearMonth.daysInMonth]

/-- AGE-2: 出生の日以後の日について、
`ageOn` の年齢 `n` は `n` 歳に達する日以後かつ `n + 1` 歳に達する日の前にあり（年齢がその区間で正しい）、
年齢は日付について単調で、`n` 歳に達する日には `n` 歳、その前日には `n - 1` 歳になる（達する日ごとにちょうど 1 増える）。
一つめは `ageOn_spec`、二つめは区間の大小、三つめは `ageOn_unique` に達する日とその前日を当てて示す。 -/
@[ritsuryo_proof "AGE-2", ritsuryo_basis "年齢計算ニ関スル法律" "第1項",
  ritsuryo_basis "年齢計算ニ関スル法律" "第2項"]
theorem age2_monotone_and_steps (birth : Date) (h : birth.Valid) :
    (∀ asOf : Date, asOf.Valid → toDays birth ≤ toDays asOf →
      toDays (attainmentDate birth (ageOn birth asOf)) ≤ toDays asOf ∧
        toDays asOf < toDays (attainmentDate birth (ageOn birth asOf + 1))) ∧
    (∀ d1 d2 : Date, d1.Valid → d2.Valid → toDays birth ≤ toDays d1 → toDays d1 ≤ toDays d2 →
      ageOn birth d1 ≤ ageOn birth d2) ∧
    (∀ n : Nat, 1 ≤ n →
      ageOn birth (attainmentDate birth n) = n ∧
        ageOn birth (prevDate (attainmentDate birth n)) = n - 1) := by
  have hdays (n : Nat) : toDays (attainmentDate birth n) = attainmentDays birth n := by
    rw [attainmentDate_eq birth h, attainmentDays_eq birth h]
  have hval (n : Nat) : (attainmentDate birth n).Valid := by
    rw [attainmentDate_eq birth h]
    exact attainment_valid birth h n
  have h0 := attainment_zero birth h
  refine ⟨fun asOf hd hle => ?_, fun d1 d2 hv1 hv2 hle1 hle2 => ?_, fun n hn => ?_⟩
  · rw [hdays, hdays]
    exact ageOn_spec birth asOf h hd hle
  · obtain ⟨a1, a2⟩ := ageOn_spec birth d1 h hv1 hle1
    obtain ⟨b1, b2⟩ := ageOn_spec birth d2 h hv2 (by omega)
    by_cases hc : ageOn birth d2 < ageOn birth d1
    · have := attainment_mono birth h (ageOn birth d2 + 1) (ageOn birth d1) hc
      omega
    · omega
  · have hs1 := attainment_strict_mono birth h 0 n hn
    have hs2 := attainment_strict birth h n
    have hs3 := attainment_strict birth h (n - 1)
    rw [show n - 1 + 1 = n by omega] at hs3
    have hp := toDays_prevDate _ (hval n)
    have hb1 := birth_lt_attainment_one birth h
    have hm1 := attainment_mono birth h 1 n hn
    refine ⟨ageOn_unique birth _ h (hval n) (by rw [hdays]; omega) n (by rw [hdays]; omega) (by
      rw [hdays]; omega), ?_⟩
    have hge : toDays birth ≤ toDays (prevDate (attainmentDate birth n)) := by
      rw [hp.1, hdays]
      omega
    exact ageOn_unique birth _ h hp.2 hge (n - 1) (by rw [hp.1, hdays]; omega)
      (by rw [hp.1, hdays, show n - 1 + 1 = n by omega]; omega)

end Ritsuryo.Period.Age
