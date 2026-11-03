module

public import Ritsuryo.Period.Proofs.Civil
meta import Ritsuryo.Basis

/-!
# 期間の計算の性質（PER-2〜PER-7）

民法第140条・第143条の期間の計算について、条文から期待される性質を示す。

- PER-2（`per2_from_beginning`）: 月・年・週の初めから起算する期間（第143条第1項）も、第2項の式で暦どおりの結果になる。
- PER-3（`per3_weeks_years`）: n 週は 7n 日、n 年は 12n か月と同じ末日になる。
- PER-4（`per4_not_additive`・`per4_bound`）: 1 か月の期間を 2 回つなぐと 2 か月の期間と一致しないことがあり、ずれは 0〜3 日。
- PER-5（`per5_monotone`）: 末日は出来事の日と期間の長さについて単調。
- PER-6（`per6_months_from_event`）: 出来事から n か月の末日の閉じた式（月末の出来事は n か月後の月末）。
- PER-7（`per7_national_tax_general`）: 国税通則法第10条第1項の仕様は民法の仕様と同じ末日になる。

月の期間の証明は、末日の通算日を最後の月の1日の通算日で表す式（`months_formula`）と、末日がその月の中に収まること
（`months_bounds`）を土台にし、あとは通算日の不等式を `omega`（線形算術の決定手続き）で閉じる。
仕様についての主張は、PER-1 の補題（`expiryFromStart_spec`）で実装の通算日についての主張に移してから示す。
-/

public section

namespace Ritsuryo.Period

open Date

/-- 起算日 `s` から `n` か月の期間の末日の通算日を、最後の月（`n` か月後の月）の1日の通算日で表す式。
応当日があれば「1日の通算日 + 起算日の日 - 2」（応当日の前日）、なければ「1日の通算日 + 月の日数 - 1」（月の末日）になる。 -/
theorem months_formula (s : Date) (n : Nat) :
    expiryFromStartDays s (.months n) =
      if s.day ≤ (s.yearMonth.addMonths n).daysInMonth then
        toDays (s.yearMonth.addMonths n).firstDay + s.day - 2
      else
        toDays (s.yearMonth.addMonths n).firstDay + (s.yearMonth.addMonths n).daysInMonth - 1 := by
  unfold expiryFromStartDays correspondingDays lastMonth
  by_cases hd : s.day ≤ (s.yearMonth.addMonths n).daysInMonth
  · simp only [hd, ↓reduceIte]
    rw [toDays_day ⟨_, _, s.day⟩]
    simp only [YearMonth.firstDay]
    omega
  · simp only [hd, ↓reduceIte]
    rw [toDays_lastDay]

/-- `n` か月の期間の末日は、最後の月の前月の末日から最後の月の末日までの間にある。
応当日が1日のとき末日は前月の末日になるので、下限は最後の月の1日の前日になる。 -/
theorem months_bounds (s : Date) (h : s.Valid) (n : Nat) :
    toDays (s.yearMonth.addMonths n).firstDay - 1 ≤ expiryFromStartDays s (.months n) ∧
      expiryFromStartDays s (.months n) ≤
        toDays (s.yearMonth.addMonths n).firstDay + (s.yearMonth.addMonths n).daysInMonth - 1 := by
  rw [months_formula]
  have := h.2.2.1
  split <;> omega

/-- `a < b` なら、`a` か月後の月の末日の翌日は `b` か月後の月の1日以前にある。 -/
theorem firstDay_addMonths_lt (ym : YearMonth) (a b : Nat) (hab : a < b) :
    toDays (ym.addMonths a).firstDay + (ym.addMonths a).daysInMonth ≤
      toDays (ym.addMonths b).firstDay := by
  simp only [YearMonth.addMonths]
  exact firstDay_ofIndex_lt _ _ (by omega)

/-- 月の期間の末日は、月数について単調。月数が違えば最後の月が違い、`months_bounds` の範囲が重ならないことによる。 -/
theorem months_mono_length (s : Date) (h : s.Valid) (a b : Nat) (hab : a ≤ b) :
    expiryFromStartDays s (.months a) ≤ expiryFromStartDays s (.months b) := by
  by_cases he : a = b
  · subst he
    omega
  · have hl := firstDay_addMonths_lt s.yearMonth a b (by omega)
    have ha := months_bounds s h a
    have hb := months_bounds s h b
    omega

/-- 通算日で `s1` が `s2` 以前なら、`s1` の年月の通し番号は `s2` の年月の通し番号以下になる。背理法で、
`s2` の月が先なら `s2` の月の末日より後に `s1` があることになり矛盾する。 -/
theorem index_le_of_toDays_le (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) : s1.yearMonth.index ≤ s2.yearMonth.index := by
  by_cases hi : s2.yearMonth.index < s1.yearMonth.index
  · exfalso
    have hl := firstDay_ofIndex_lt _ _ hi
    rw [YearMonth.ofIndex_index s1.yearMonth h1.1 h1.2.1,
      YearMonth.ofIndex_index s2.yearMonth h2.1 h2.2.1] at hl
    have hd1 := toDays_day s1
    have hd2 := toDays_day s2
    simp only [yearMonth, YearMonth.firstDay, YearMonth.daysInMonth] at hl
    have := h1.2.2.1
    have := h2.2.2.2
    omega
  · omega

/-- 月の期間の末日は、起算日について単調。起算日が同じ月なら日の大小と `months_formula` で比べ、
違う月なら最後の月も違うので `months_bounds` の範囲で比べる。 -/
theorem months_mono_start (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) (n : Nat) :
    expiryFromStartDays s1 (.months n) ≤ expiryFromStartDays s2 (.months n) := by
  have hi := index_le_of_toDays_le s1 s2 h1 h2 h
  by_cases he : s1.yearMonth.index = s2.yearMonth.index
  · have hym : s1.yearMonth = s2.yearMonth := by
      rw [← YearMonth.ofIndex_index s1.yearMonth h1.1 h1.2.1,
        ← YearMonth.ofIndex_index s2.yearMonth h2.1 h2.2.1, he]
    have hd1 := toDays_day s1
    have hd2 := toDays_day s2
    have hy : s1.year = s2.year := congrArg YearMonth.year hym
    have hm : s1.month = s2.month := congrArg YearMonth.month hym
    have hday : s1.day ≤ s2.day := by
      rw [hy, hm] at hd1
      omega
    rw [months_formula, months_formula, hym]
    split <;> split <;> omega
  · have hlt : s1.yearMonth.index + n < s2.yearMonth.index + n := by omega
    have hl := firstDay_ofIndex_lt _ _ hlt
    have ha := months_bounds s1 h1 n
    have hb := months_bounds s2 h2 n
    simp only [YearMonth.addMonths] at ha hb
    omega

/-- 期間の末日は、すべての単位で起算日について単調。日・週は通算日の足し算、月・年は `months_mono_start` による。 -/
theorem expiryFromStart_mono_start (s1 s2 : Date) (h1 : s1.Valid) (h2 : s2.Valid)
    (h : toDays s1 ≤ toDays s2) (len : Length) :
    expiryFromStartDays s1 len ≤ expiryFromStartDays s2 len := by
  cases len with
  | days n => simp only [expiryFromStartDays, correspondingDays]; omega
  | weeks n => simp only [expiryFromStartDays, correspondingDays]; omega
  | months n => exact months_mono_start s1 s2 h1 h2 h n
  | years n => exact months_mono_start s1 s2 h1 h2 h (12 * n)

/-- PER-2: 第143条第1項の「週、月又は年の初めから期間を起算する」場合も、第2項の式で暦どおりの末日になる。
1日に起算する `n` か月の期間は `n - 1` か月後の月の末日、1月1日に起算する `n` 年の期間は `n - 1` 年後の12月31日、
日曜日に起算する `n` 週の期間は `7 * n - 1` 日後の土曜日に満了する。
月は `months_formula` と、末日の翌日が翌月の1日であること（`toDays_lastDay_next`）で示す。
年は仕様を展開して計算し、週は通算日を 7 で割った余りで曜日を出す。 -/
@[ritsuryo_proof "PER-2", ritsuryo_basis "民法" "第143条第1項",
  ritsuryo_basis "民法" "第143条第2項"]
theorem per2_from_beginning (start : Date) (h : start.Valid) (n : Nat) (hn : 1 ≤ n) :
    (start.day = 1 →
      Civil.expiryFromStartSpec start (.months n) =
        (start.yearMonth.addMonthsNaive (n - 1)).lastDay) ∧
    (start.month = 1 → start.day = 1 →
      Civil.expiryFromStartSpec start (.years n) = ⟨start.year + n - 1, 12, 31⟩) ∧
    (start.weekday = .sunday →
      (Civil.expiryFromStartSpec start (.weeks n)).weekday = .saturday ∧
        toDays (Civil.expiryFromStartSpec start (.weeks n)) = toDays start + 7 * n - 1) := by
  refine ⟨fun hd => ?_, fun hm hd => ?_, fun hw => ?_⟩
  · rw [← expiryFromStart_spec start h, months_formula]
    have hb := daysInMonth_ge (start.yearMonth.addMonths n).year
      (start.yearMonth.addMonths n).month (YearMonth.addMonths_valid start.yearMonth n).1
      (YearMonth.addMonths_valid start.yearMonth n).2
    have hle : start.day ≤ (start.yearMonth.addMonths n).daysInMonth := by
      simp only [YearMonth.daysInMonth]
      omega
    simp only [hle, ↓reduceIte]
    have hv := YearMonth.addMonths_valid start.yearMonth (n - 1)
    have key : toDays (start.yearMonth.addMonths n).firstDay =
        toDays (start.yearMonth.addMonths (n - 1)).lastDay + 1 := by
      rw [toDays_lastDay_next _ hv.1 hv.2, YearMonth.addMonths_next,
        show n - 1 + 1 = n by omega]
    rw [key, hd, YearMonth.addMonthsNaive_eq _ h.1 h.2.1]
    rw [show toDays (start.yearMonth.addMonths (n - 1)).lastDay + 1 + ((1 : Nat) : Int) - 2 =
      toDays (start.yearMonth.addMonths (n - 1)).lastDay by omega]
    exact ofDays_toDays _ (lastDay_valid _ hv.1 hv.2)
  · simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, Civil.lastMonthSpec, hm, hd,
      YearMonth.daysInMonth, daysInMonth]
    simp only [show (1 : Nat) ≤ 31 by decide, ↓reduceIte, prevDate]
    simp only [Nat.lt_irrefl, ↓reduceIte]
  · rw [← expiryFromStart_spec start h]
    have hs : (toDays start + 4) % 7 = 0 := by
      have := Weekday.ofIndex_inj ((toDays start + 4) % 7).toNat 0 (by omega) (by decide) hw
      omega
    simp only [expiryFromStartDays, correspondingDays]
    refine ⟨?_, (toDays_ofDays _).1⟩
    simp only [weekday, (toDays_ofDays _).1, Weekday.ofDays]
    rw [show ((toDays start + 7 * n - 1 + 4) % 7).toNat = 6 by omega]
    rfl

/-- PER-3: `n` 週の期間は `7 * n` 日の期間と、`n` 年の期間は `12 * n` か月の期間と同じ末日になる。
週は `weekCorresponding_eq`、年は最後の月が同じになること（`lastMonth_eq`）による。 -/
@[ritsuryo_proof "PER-3", ritsuryo_basis "民法" "第143条第2項"]
theorem per3_weeks_years (start : Date) (h : start.Valid) (n : Nat) :
    Civil.expiryFromStartSpec start (.weeks n) = Civil.expiryFromStartSpec start (.days (7 * n)) ∧
      Civil.expiryFromStartSpec start (.years n) =
        Civil.expiryFromStartSpec start (.months (12 * n)) := by
  refine ⟨?_, ?_⟩
  · simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, weekCorresponding_eq start h]
  · have hy := lastMonth_eq start h (.years n)
    have hm := lastMonth_eq start h (.months (12 * n))
    have : Civil.lastMonthSpec start (.years n) = Civil.lastMonthSpec start (.months (12 * n)) := by
      rw [← hy, ← hm]
      rfl
    simp only [Civil.expiryFromStartSpec, Civil.correspondingDaySpec, this]

/-- PER-4 の例: 2025年1月31日に起算する 1 か月の期間は2月28日に満了し（2月に31日がないので月の末日）、
その翌日の3月1日から 1 か月の期間は3月31日に満了する。一方、1月31日に起算する 2 か月の期間は3月30日に満了する。
1 か月の期間を 2 回つないだ結果と 2 か月の期間は一致しない。具体的な日付なので `decide` で計算して確かめる。 -/
@[ritsuryo_proof "PER-4", ritsuryo_basis "民法" "第143条第2項"]
theorem per4_not_additive :
    Civil.expiryFromStartSpec
        (nextDate (Civil.expiryFromStartSpec ⟨2025, 1, 31⟩ (.months 1))) (.months 1) =
      ⟨2025, 3, 31⟩ ∧
    Civil.expiryFromStartSpec ⟨2025, 1, 31⟩ (.months 2) = ⟨2025, 3, 30⟩ := by
  decide

/-- 月が 1〜12 なら、その月の1日は有効な日付になる。 -/
theorem firstDay_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ym.firstDay.Valid := by
  have := daysInMonth_ge ym.year ym.month h1 h2
  exact ⟨h1, h2, by simp [YearMonth.firstDay], by simp only [YearMonth.firstDay]; omega⟩

/-- 月が 1〜12 なら、翌月の月も 1〜12 になる。 -/
theorem next_month_valid (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    1 ≤ ym.next.month ∧ ym.next.month ≤ 12 := by
  simp only [YearMonth.next]
  split <;> simp <;> omega

/-- 末日の仕様の通算日は、実装 `expiryFromStartDays` の値と等しい。仕様についての主張を通算日の計算に移すのに使う。 -/
theorem spec_toDays (s : Date) (h : s.Valid) (len : Length) :
    toDays (Civil.expiryFromStartSpec s len) = expiryFromStartDays s len := by
  rw [← expiryFromStart_spec s h, (toDays_ofDays _).1]

/-- 有効な起算日から出した末日の仕様は、有効な日付になる。 -/
theorem spec_valid (s : Date) (h : s.Valid) (len : Length) :
    (Civil.expiryFromStartSpec s len).Valid := by
  rw [← expiryFromStart_spec s h]
  exact (toDays_ofDays _).2

/-- PER-4: 起算日 `s` から `a` か月の期間の満了の翌日を起算日として `b` か月の期間をつなぐと、その末日は
`a + b` か月の期間の末日と同じか、0〜3 日後になる。ずれは、途中の月に応当日がなく月の末日で満了したときに生じ、
月の日数の差（最大で31日と28日の差の 3 日）を超えない。
`months_formula` で両辺を最後の月の1日の通算日で表し、途中の月に応当日があるかで場合分けして `omega` で閉じる。 -/
@[ritsuryo_proof "PER-4", ritsuryo_basis "民法" "第143条第2項"]
theorem per4_bound (s : Date) (h : s.Valid) (a b : Nat) :
    0 ≤ toDays (Civil.expiryFromStartSpec
          (nextDate (Civil.expiryFromStartSpec s (.months a))) (.months b)) -
        toDays (Civil.expiryFromStartSpec s (.months (a + b))) ∧
      toDays (Civil.expiryFromStartSpec
          (nextDate (Civil.expiryFromStartSpec s (.months a))) (.months b)) -
        toDays (Civil.expiryFromStartSpec s (.months (a + b))) ≤ 3 := by
  have hv1 := spec_valid s h (.months a)
  have hs2 := (toDays_nextDate _ hv1).2
  rw [spec_toDays _ hs2, spec_toDays s h, nextDate_eq_ofDays _ hv1, spec_toDays s h]
  rw [nextDate_eq_ofDays _ hv1, spec_toDays s h] at hs2
  have hym1 := YearMonth.addMonths_valid s.yearMonth a
  have hym2 := YearMonth.addMonths_valid s.yearMonth (a + b)
  have hb1 := daysInMonth_ge (s.yearMonth.addMonths a).year _ hym1.1 hym1.2
  have hb2 := daysInMonth_ge (s.yearMonth.addMonths (a + b)).year _ hym2.1 hym2.2
  rw [months_formula s a]
  by_cases hd : s.day ≤ (s.yearMonth.addMonths a).daysInMonth
  · simp only [hd, ↓reduceIte] at hs2 ⊢
    have he : toDays (s.yearMonth.addMonths a).firstDay + s.day - 2 + 1 =
        toDays ⟨(s.yearMonth.addMonths a).year, (s.yearMonth.addMonths a).month, s.day⟩ := by
      rw [toDays_day ⟨_, _, s.day⟩]
      simp only [YearMonth.firstDay]
      omega
    rw [he, ofDays_toDays _ (valid_of_le _ hym1.1 hym1.2 _ h.2.2.1 hd)]
    rw [months_formula, months_formula s (a + b)]
    have hym : (⟨(s.yearMonth.addMonths a).year, (s.yearMonth.addMonths a).month, s.day⟩ :
        Date).yearMonth = s.yearMonth.addMonths a := rfl
    simp only [hym, YearMonth.addMonths_add]
    split <;> omega
  · simp only [hd, ↓reduceIte] at hs2 ⊢
    rw [show toDays (s.yearMonth.addMonths a).firstDay +
        ((s.yearMonth.addMonths a).daysInMonth : Int) - 1 + 1 =
        toDays (s.yearMonth.addMonths a).next.firstDay by
      rw [toDays_firstDay_next _ hym1.1 hym1.2]
      omega]
    have hn := next_month_valid _ hym1.1 hym1.2
    rw [ofDays_toDays _ (firstDay_valid _ hn.1 hn.2), months_formula, months_formula s (a + b)]
    have hym : (s.yearMonth.addMonths a).next.firstDay.yearMonth = (s.yearMonth.addMonths a).next :=
      rfl
    have hday : (s.yearMonth.addMonths a).next.firstDay.day = 1 := rfl
    rw [hym, hday, YearMonth.next_addMonths _ hym1.1 hym1.2, YearMonth.addMonths_add,
      show a + (b + 1) = a + b + 1 by omega, ← YearMonth.addMonths_next]
    have hn2 := next_month_valid _ hym2.1 hym2.2
    have hb3 := daysInMonth_ge (s.yearMonth.addMonths (a + b)).next.year _ hn2.1 hn2.2
    have hf := toDays_firstDay_next _ hym2.1 hym2.2
    simp only [YearMonth.daysInMonth] at hd hf ⊢
    have h1le : 1 ≤ daysInMonth (s.yearMonth.addMonths (a + b)).next.year
        (s.yearMonth.addMonths (a + b)).next.month := by omega
    simp only [h1le, ↓reduceIte]
    by_cases hd2 : s.day ≤ daysInMonth (s.yearMonth.addMonths (a + b)).year
        (s.yearMonth.addMonths (a + b)).month
    · simp only [hd2, ↓reduceIte]
      omega
    · simp only [hd2, ↓reduceIte]
      omega

/-- PER-5: 実装の `compute` の末日は、出来事の日について単調で（出来事が遅いほど末日も遅いか同じ）、
同じ単位の期間の長さについても単調。日付は有効性を仮定せず、通算日を日付に戻した起算日（常に有効）について示す。
出来事の日については `expiryFromStart_mono_start`、長さについては日・週は通算日の足し算、月・年は `months_mono_length` による。 -/
@[ritsuryo_proof "PER-5", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per5_monotone (e1 e2 : Date) (startAtMidnight : Bool) :
    (toDays e1 ≤ toDays e2 → ∀ len,
      toDays (compute e1 startAtMidnight len).expiry ≤
        toDays (compute e2 startAtMidnight len).expiry) ∧
    (∀ a b : Nat, a ≤ b →
      toDays (compute e1 startAtMidnight (.days a)).expiry ≤
          toDays (compute e1 startAtMidnight (.days b)).expiry ∧
        toDays (compute e1 startAtMidnight (.weeks a)).expiry ≤
          toDays (compute e1 startAtMidnight (.weeks b)).expiry ∧
        toDays (compute e1 startAtMidnight (.months a)).expiry ≤
          toDays (compute e1 startAtMidnight (.months b)).expiry ∧
        toDays (compute e1 startAtMidnight (.years a)).expiry ≤
          toDays (compute e1 startAtMidnight (.years b)).expiry) := by
  have hs1 := toDays_ofDays (startDays e1 startAtMidnight)
  have hs2 := toDays_ofDays (startDays e2 startAtMidnight)
  simp only [compute, (toDays_ofDays _).1]
  refine ⟨fun hle len => ?_, fun a b hab => ?_⟩
  · apply expiryFromStart_mono_start _ _ hs1.2 hs2.2
    rw [hs1.1, hs2.1]
    cases startAtMidnight <;> simp only [startDays, Bool.false_eq_true, ↓reduceIte] <;> omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [expiryFromStartDays, correspondingDays]
      omega
    · simp only [expiryFromStartDays, correspondingDays]
      omega
    · exact months_mono_length _ hs1.2 a b hab
    · exact months_mono_length _ hs1.2 (12 * a) (12 * b) (by omega)

/-- PER-6: 出来事の日 `event` から（初日不算入で）`n` か月の期間の末日の閉じた式。
出来事が月の末日なら、起算日は翌月の1日になり、末日は `n` か月後の月の末日になる。
それ以外なら、起算日は同じ月の翌日で、末日は `n` か月後の月の出来事と同じ日付の日（その日付がなければその月の末日）になる。
二つの場合それぞれで起算日を具体的に出し、`months_formula` に当てはめる。 -/
@[ritsuryo_proof "PER-6", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per6_months_from_event (event : Date) (h : event.Valid) (n : Nat) :
    (compute event false (.months n)).expiry =
      if event.day = daysInMonth event.year event.month then
        (event.yearMonth.addMonths n).lastDay
      else
        ⟨(event.yearMonth.addMonths n).year, (event.yearMonth.addMonths n).month,
          min event.day (event.yearMonth.addMonths n).daysInMonth⟩ := by
  have hT := YearMonth.addMonths_valid event.yearMonth n
  have hbT := daysInMonth_ge (event.yearMonth.addMonths n).year _ hT.1 hT.2
  obtain ⟨e1, e2, e3, e4⟩ := h
  simp only [compute, startDays, Bool.false_eq_true, ↓reduceIte]
  by_cases hlast : event.day = daysInMonth event.year event.month
  · simp only [hlast, ↓reduceIte]
    have hl : toDays event = toDays event.yearMonth.lastDay := by
      rw [toDays_day event]
      rw [toDays_day event.yearMonth.lastDay]
      simp only [yearMonth, YearMonth.lastDay, YearMonth.daysInMonth]
      omega
    have hn := next_month_valid event.yearMonth e1 e2
    rw [hl, toDays_lastDay_next _ e1 e2, ofDays_toDays _ (firstDay_valid _ hn.1 hn.2),
      months_formula]
    have hym : event.yearMonth.next.firstDay.yearMonth = event.yearMonth.next := rfl
    have hday : event.yearMonth.next.firstDay.day = 1 := rfl
    rw [hym, hday, YearMonth.next_addMonths _ e1 e2, ← YearMonth.addMonths_next]
    have hn2 := next_month_valid _ hT.1 hT.2
    have hb3 := daysInMonth_ge (event.yearMonth.addMonths n).next.year _ hn2.1 hn2.2
    have h1le : 1 ≤ (event.yearMonth.addMonths n).next.daysInMonth := by
      simp only [YearMonth.daysInMonth]
      omega
    simp only [h1le, ↓reduceIte]
    rw [← toDays_lastDay_next _ hT.1 hT.2,
      show toDays (event.yearMonth.addMonths n).lastDay + 1 + ((1 : Nat) : Int) - 2 =
        toDays (event.yearMonth.addMonths n).lastDay by omega]
    exact ofDays_toDays _ (lastDay_valid _ hT.1 hT.2)
  · simp only [hlast, ↓reduceIte]
    have hlt : event.day < daysInMonth event.year event.month := by omega
    have hnext : ofDays (toDays event + 1) = ⟨event.year, event.month, event.day + 1⟩ := by
      rw [← nextDate_eq_ofDays event ⟨e1, e2, e3, e4⟩]
      simp only [nextDate, hlt, ↓reduceIte]
    rw [hnext, months_formula]
    have hym : (⟨event.year, event.month, event.day + 1⟩ : Date).yearMonth = event.yearMonth := rfl
    simp only [hym]
    split
    · rename_i hd
      have he : toDays (event.yearMonth.addMonths n).firstDay + ((event.day + 1 : Nat) : Int) - 2 =
          toDays ⟨(event.yearMonth.addMonths n).year, (event.yearMonth.addMonths n).month,
            event.day⟩ := by
        rw [toDays_day ⟨_, _, event.day⟩]
        simp only [YearMonth.firstDay]
        omega
      have hmin : min event.day (event.yearMonth.addMonths n).daysInMonth = event.day := by
        omega
      rw [he, hmin]
      exact ofDays_toDays _ (valid_of_le _ hT.1 hT.2 _ e3 (by omega))
    · rename_i hd
      have hmin : min event.day (event.yearMonth.addMonths n).daysInMonth =
          (event.yearMonth.addMonths n).daysInMonth := by
        omega
      rw [hmin, ← toDays_lastDay]
      exact ofDays_toDays _ (lastDay_valid _ hT.1 hT.2)

/-- 同じ起算日から数えると、国税通則法第10条第1項の末日の仕様は民法の末日の仕様と等しい。
両方の定義を展開し、応当日があるかで場合分けする。 -/
theorem taxGeneral_fromStart (start : Date) (len : TaxLength) :
    TaxGeneral.expiryFromStartSpec start len = Civil.expiryFromStartSpec start len.toLength := by
  cases len with
  | days n => rfl
  | months n =>
    simp only [TaxGeneral.expiryFromStartSpec, Civil.expiryFromStartSpec,
      Civil.correspondingDaySpec, Civil.lastMonthSpec, TaxLength.toLength]
    by_cases hd : start.day ≤ (start.yearMonth.addMonthsNaive n).daysInMonth <;> simp [hd]
  | years n =>
    simp only [TaxGeneral.expiryFromStartSpec, Civil.expiryFromStartSpec,
      Civil.correspondingDaySpec, Civil.lastMonthSpec, TaxLength.toLength]
    by_cases hd : start.day ≤ (⟨start.year + n, start.month⟩ : YearMonth).daysInMonth <;> simp [hd]

/-- PER-7: 国税通則法第10条第1項の仕様は、日・月・年の期間について民法の仕様と同じ末日になり、
実装の `computeTax` の末日は国税通則法の仕様と一致する。起算日の定義が同じなので `taxGeneral_fromStart` で前半を示し、
後半は前半と PER-1 を組み合わせる。 -/
@[ritsuryo_proof "PER-7", ritsuryo_basis "国税通則法" "第10条第1項"]
theorem per7_national_tax_general (event : Date) (h : event.Valid) (startAtMidnight : Bool)
    (len : TaxLength) :
    TaxGeneral.expirySpec event startAtMidnight len =
        Civil.expirySpec event startAtMidnight len.toLength ∧
      (computeTax event startAtMidnight len).expiry =
        TaxGeneral.expirySpec event startAtMidnight len := by
  have heq : TaxGeneral.expirySpec event startAtMidnight len =
      Civil.expirySpec event startAtMidnight len.toLength := by
    simp only [TaxGeneral.expirySpec, Civil.expirySpec, taxGeneral_fromStart]
    rfl
  refine ⟨heq, ?_⟩
  rw [heq]
  exact (per1_compute_eq_spec event h startAtMidnight len.toLength).2.2

end Ritsuryo.Period
