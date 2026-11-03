module

public import Ritsuryo.Calendar.Arith
public import Ritsuryo.Calendar.Weekday
meta import Ritsuryo.Basis

/-!
# 暦の証明（CAL-1〜CAL-6）

日付と 1970-01-01 からの日数（`Ritsuryo.Calendar.Days`）の対応について、期間計算や祝日の証明が前提にする
性質を証明する。ファイルの末尾に、設計の ID を付けた定理 `cal1_ofDays_toDays`〜`cal6_daysInMonth` を置き、
それより前の定理はその材料になる。

- CAL-1・CAL-2: `toDays` と `ofDays` は互いに逆で、実在する日付と整数が 1 対 1 に対応する。
- CAL-3: 日付の辞書式の前後と、日数の大小が一致する。
- CAL-4: 月末・年末で繰り上がる素朴な翌日 `nextDate` は、日数で 1 進めた日と同じになる。
- CAL-5: 曜日は日数を 7 で割った余りで決まり、翌日の曜日は次の曜日になる。
- CAL-6: 各月の日数は、翌月 1 日との日数の差と一致し、2 月が 29 日になるのは閏年ニ関スル件の文言
  （皇紀で判定する `IsLeapYearSpec`）で閏年になる年に限る。

証明は、月の 12 通りの場合分けと `Ritsuryo.Calendar.Arith` の補題を組み合わせ、
残りを `omega` で閉じる。
-/

public section

namespace Ritsuryo.Date

/-- 実在する日付 `d` について、3 月始まりの月 `marchMonth d.month` が 0〜11 に入り、
暦の月に戻せること、1・2 月かどうかと対応すること、
年の中の日（`monthStart` + 日 − 1）から `monthOf` で同じ月に戻ること、
年の中の日が 0〜364 か、閏年の 2 月 29 日に限り 365 になることをまとめて述べる。
月の 12 通りで場合分けし、各場合を `omega` で閉じる。2 月は閏年かどうかでさらに分ける。 -/
theorem valid_month (d : Date) (h : d.Valid) :
    0 ≤ marchMonth d.month ∧ marchMonth d.month ≤ 11 ∧
      (if marchMonth d.month < 10 then marchMonth d.month + 3 else marchMonth d.month - 9) =
        (d.month : Int) ∧
      (marchMonth d.month < 10 ↔ 3 ≤ d.month) ∧
      monthOf (monthStart (marchMonth d.month) + d.day - 1) = marchMonth d.month ∧
      0 ≤ monthStart (marchMonth d.month) + d.day - 1 ∧
      (monthStart (marchMonth d.month) + d.day - 1 ≤ 364 ∨
        (monthStart (marchMonth d.month) + d.day - 1 = 365 ∧ d.month = 2 ∧
          isLeapYear d.year = true)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hm : d.month = 1 ∨ d.month = 2 ∨ d.month = 3 ∨ d.month = 4 ∨ d.month = 5 ∨
      d.month = 6 ∨ d.month = 7 ∨ d.month = 8 ∨ d.month = 9 ∨ d.month = 10 ∨
      d.month = 11 ∨ d.month = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    simp only [hm, daysInMonth] at h4 <;>
    simp only [hm, marchMonth, monthStart, monthOf] <;>
    try omega
  split at h4 <;> simp_all <;> omega

/-- `ofDays z` の計算の途中の値（周期の番号 `era`、周期の中の年 `yoe`、
年の中の日 `doy`）が分かっているとき、`ofDays z` の結果をそれらで書き下す。
`ofDays` の `let` を展開するための補題。 -/
theorem ofDays_eq (z era yoe doy : Int) (hera : (z + 719468) / 146097 = era)
    (hdoe : (z + 719468) % 146097 = yearStart yoe + doy)
    (hyoe : yoeOf (yearStart yoe + doy) = yoe) :
    ofDays z =
      ⟨era * 400 + yoe + (if monthOf doy < 10 then 0 else 1),
        (if monthOf doy < 10 then monthOf doy + 3 else monthOf doy - 9).toNat,
        (doy - monthStart (monthOf doy) + 1).toNat⟩ := by
  simp only [ofDays, hera, hdoe, hyoe]
  have : yearStart yoe + doy - yearStart yoe = doy := by omega
  simp only [this]

/-- 実在する日付を日数にして戻すと、元の日付になる（CAL-1 の本体）。
`toDays d + 719468` を「3 月始まりの年の周期の番号 × 146,097 + 周期の中の年の始まり + 年の中の日」に分け、
`ofDays` がその周期の番号・年・日をそのまま取り出すこと（`yoeOf_yearStart`）を使う。
最後に年・月・日の 3 つがそれぞれ元に戻ることを `omega` で確かめる。 -/
theorem ofDays_toDays (d : Date) (h : d.Valid) : ofDays (toDays d) = d := by
  obtain ⟨hm0, hm1, hmonth, hlt, hmo, hdoy0, hdoy1⟩ := valid_month d h
  have hy : marchYear d = if d.month ≤ 2 then d.year - 1 else d.year := rfl
  generalize hmp : marchMonth d.month = mp at *
  generalize hdoy : monthStart mp + d.day - 1 = doy at *
  have hys : 0 ≤ yearStart (marchYear d % 400) ∧
      yearStart (marchYear d % 400) + 365 ≤ 146096 := by
    simp only [yearStart]
    omega
  have hcond : doy ≤ 364 ∨
      (doy = 365 ∧ marchYear d % 400 % 4 = 3 ∧
        (marchYear d % 400 % 100 ≠ 99 ∨ marchYear d % 400 = 399)) := by
    rcases hdoy1 with h' | ⟨h365, hfeb, hl⟩
    · exact Or.inl h'
    · have hl := (isLeapYear_iff d.year).mp hl
      have hmy : marchYear d = d.year - 1 := by
        rw [hy]
        simp [hfeb]
      right
      rw [hmy]
      omega
  have hz : toDays d + 719468 =
      marchYear d / 400 * 146097 + (yearStart (marchYear d % 400) + doy) := by
    simp only [toDays, marchYearStart, hmp]
    omega
  have hera : (toDays d + 719468) / 146097 = marchYear d / 400 := by
    rw [hz]
    omega
  have hdoe : (toDays d + 719468) % 146097 = yearStart (marchYear d % 400) + doy := by
    rw [hz]
    omega
  have hyoe := yoeOf_yearStart (marchYear d % 400) doy (by omega) (by omega) hdoy0 hcond
  rw [ofDays_eq _ _ _ _ hera hdoe hyoe, hmo]
  have hY : marchYear d / 400 * 400 + marchYear d % 400 + (if mp < 10 then 0 else 1) =
      d.year := by
    rw [hy]
    split <;> split <;> omega
  have hM : (if mp < 10 then mp + 3 else mp - 9).toNat = d.month := by
    rw [hmonth]
    omega
  have hD : (doy - monthStart mp + 1).toNat = d.day := by
    omega
  rw [hY, hM, hD]

/-- 3 月始まりの月 `mp`（0〜11）を暦の月に戻すと 1〜12 に入り、
`marchMonth` で `mp` に戻ること、1・2 月かどうかと `mp` ≥ 10 が対応すること、
月の長さが次の月の `monthStart` との差に等しいこと（最後の 2 月だけは年の長さで決まるので、
`monthStart` が 337 で日数が 28 か 29 であること）をまとめて述べる。
12 通りの場合分けをして `simp` で計算する。 -/
theorem marchMonth_inv (y : Int) (mp : Int) (h0 : 0 ≤ mp) (h1 : mp ≤ 11) :
    1 ≤ (if mp < 10 then mp + 3 else mp - 9) ∧ (if mp < 10 then mp + 3 else mp - 9) ≤ 12 ∧
      marchMonth (if mp < 10 then mp + 3 else mp - 9).toNat = mp ∧
      ((if mp < 10 then mp + 3 else mp - 9).toNat ≤ 2 ↔ ¬mp < 10) ∧
      (mp ≠ 11 → monthStart (mp + 1) - monthStart mp =
        daysInMonth y (if mp < 10 then mp + 3 else mp - 9).toNat) ∧
      (mp = 11 → monthStart mp = 337 ∧
        daysInMonth y (if mp < 10 then mp + 3 else mp - 9).toNat =
          if isLeapYear y then 29 else 28) ∧
      monthStart mp = (153 * mp + 2) / 5 := by
  have hm : mp = 0 ∨ mp = 1 ∨ mp = 2 ∨ mp = 3 ∨ mp = 4 ∨ mp = 5 ∨ mp = 6 ∨ mp = 7 ∨
      mp = 8 ∨ mp = 9 ∨ mp = 10 ∨ mp = 11 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;> simp [marchMonth, monthStart, daysInMonth]

/-- どの整数 `z` についても、`ofDays z` は実在する日付で、それを日数に戻すと `z` になる（CAL-2 の本体）。
`z + 719468` を周期の番号と周期の中の日に分け、
`yoeOf_spec` と `monthOf_spec` で年・月・日の範囲を出す。日が月の日数以下であることは、
2 月（`mp` = 11）だけ別に扱い、日が 29 日になるのは閏年に限ることを示す。 -/
theorem toDays_ofDays (z : Int) : toDays (ofDays z) = z ∧ (ofDays z).Valid := by
  generalize hera : (z + 719468) / 146097 = era
  generalize hdoe' : (z + 719468) % 146097 = doe
  have hz : z + 719468 = era * 146097 + doe := by omega
  have hdoeb : 0 ≤ doe ∧ doe ≤ 146096 := by omega
  obtain ⟨hy0, hy1, hys, hcond⟩ := yoeOf_spec doe hdoeb.1 hdoeb.2
  generalize hyoe : yoeOf doe = yoe at *
  generalize hdoy : doe - yearStart yoe = doy at *
  have hdoe : (z + 719468) % 146097 = yearStart yoe + doy := by omega
  have hyoe' : yoeOf (yearStart yoe + doy) = yoe := by
    have : yearStart yoe + doy = doe := by omega
    rw [this, hyoe]
  rw [ofDays_eq z era yoe doy hera hdoe hyoe']
  have hdoy365 : doy ≤ 365 := by omega
  obtain ⟨hmp0, hmp1, hms, hms'⟩ := monthOf_spec doy (by omega) hdoy365
  generalize hmp : monthOf doy = mp at *
  have hY : era * 400 + yoe + (if mp < 10 then 0 else 1) =
      (if mp < 10 then 0 else 1) + (era * 400 + yoe) := by omega
  obtain ⟨hM1, hM2, hmm, hle, hlen, hfeb, _⟩ :=
    marchMonth_inv (era * 400 + yoe + (if mp < 10 then 0 else 1)) mp hmp0 hmp1
  generalize hM : (if mp < 10 then mp + 3 else mp - 9) = M at *
  have hmy : marchYear ⟨era * 400 + yoe + (if mp < 10 then 0 else 1), M.toNat,
      (doy - monthStart mp + 1).toNat⟩ = era * 400 + yoe := by
    simp only [marchYear]
    split <;> split <;> omega
  have hmys : marchYearStart (era * 400 + yoe) = era * 146097 + yearStart yoe := by
    simp only [marchYearStart]
    have h1 : (era * 400 + yoe) / 400 = era := by omega
    have h2 : (era * 400 + yoe) % 400 = yoe := by omega
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · simp only [toDays, hmy, hmys, hmm]
    omega
  · dsimp only [Valid]
    refine ⟨by omega, by omega, by omega, ?_⟩
    by_cases h11 : mp = 11
    · subst h11
      obtain ⟨hl337, hdim⟩ := hfeb rfl
      have h10 : ¬((11 : Int) < 10) := by decide
      simp only [h10, ↓reduceIte] at hdim ⊢
      rw [hdim]
      split
      · omega
      · rename_i hnl
        rcases hcond with hc | ⟨h365, hc4, hc100⟩
        · omega
        · exfalso
          apply hnl
          rw [isLeapYear_iff]
          omega
    · have := hlen h11
      omega

/-- 日付の日数は、その月の 1 日の日数に「日 − 1」を足したものになる。 -/
theorem toDays_day (d : Date) : toDays d = toDays ⟨d.year, d.month, 1⟩ + d.day - 1 := by
  simp only [toDays, marchYear]
  omega

/-- 1〜12 月の日数は 28 日以上 31 日以下。 -/
theorem daysInMonth_ge (y : Int) (m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) :
    28 ≤ daysInMonth y m ∧ daysInMonth y m ≤ 31 := by
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;> simp only [daysInMonth] <;> (try split) <;> omega

/-- 翌月 1 日の日数は、その月の 1 日の日数に月の日数を足したものになる。
12 月から翌年 1 月、2 月から 3 月への移り目では 3 月始まりの年が変わるので、
`marchYearStart_succ` で年の長さ（閏年なら 366 日）を出し、
月の 12 通りで場合分けして確かめる。 -/
theorem toDays_firstDay_next (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.next.firstDay = toDays ym.firstDay + ym.daysInMonth := by
  obtain ⟨y, m⟩ := ym
  simp only at h1 h2
  have hstep := marchYearStart_succ (y - 1)
  have hy : y - 1 + 1 = y := by omega
  rw [hy] at hstep
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨
      m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
    subst hm <;>
    simp only [YearMonth.next, YearMonth.firstDay, YearMonth.daysInMonth, toDays, marchYear,
      marchMonth, monthStart, daysInMonth] <;>
    simp <;>
    (try split) <;>
    simp_all <;>
    omega

/-- 実在する日付の素朴な翌日 `nextDate` は、日数で 1 進んだ実在する日付になる。
月末かどうか、12 月かどうかで `nextDate` の場合分けに合わせ、
月末の場合は `toDays_firstDay_next` を使う。 -/
theorem toDays_nextDate (d : Date) (h : d.Valid) :
    toDays (nextDate d) = toDays d + 1 ∧ (nextDate d).Valid := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hday := toDays_day d
  have hfirst := toDays_firstDay_next ⟨d.year, d.month⟩ h1 h2
  simp only [YearMonth.firstDay, YearMonth.daysInMonth, YearMonth.next] at hfirst
  unfold nextDate
  by_cases hlt : d.day < daysInMonth d.year d.month
  · simp only [hlt, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [toDays_day { d with day := d.day + 1 }]
      simp only
      omega
    · simp only [Valid]
      omega
  · simp only [hlt, ↓reduceIte]
    by_cases hm : d.month < 12
    · simp only [hm, ↓reduceIte] at hfirst ⊢
      have := daysInMonth_ge d.year (d.month + 1) (by omega) (by omega)
      refine ⟨by omega, ?_⟩
      simp only [Valid]
      omega
    · simp only [hm, ↓reduceIte] at hfirst ⊢
      refine ⟨by omega, ?_⟩
      simp only [Valid, daysInMonth]
      omega

/-- 実在する日付の素朴な前日 `prevDate` は、日数で 1 戻った実在する日付になる。
`toDays_nextDate` と同じ場合分けで、
月初めの場合は前月（1 月なら前年 12 月）の `toDays_firstDay_next` を使う。 -/
theorem toDays_prevDate (d : Date) (h : d.Valid) :
    toDays (prevDate d) = toDays d - 1 ∧ (prevDate d).Valid := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hday := toDays_day d
  unfold prevDate
  by_cases hd : 1 < d.day
  · simp only [hd, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [toDays_day { d with day := d.day - 1 }]
      simp only
      omega
    · simp only [Valid]
      omega
  · simp only [hd, ↓reduceIte]
    by_cases hm : 1 < d.month
    · simp only [hm, ↓reduceIte]
      have hf := toDays_firstDay_next ⟨d.year, d.month - 1⟩ (by simp only; omega)
        (by simp only; omega)
      have hn : (⟨d.year, d.month - 1⟩ : YearMonth).next = ⟨d.year, d.month⟩ := by
        have h12 : d.month - 1 < 12 := by omega
        simp only [YearMonth.next, h12, ↓reduceIte]
        congr 1
        omega
      rw [hn] at hf
      simp only [YearMonth.firstDay, YearMonth.daysInMonth] at hf
      have hb := daysInMonth_ge d.year (d.month - 1) (by omega) (by omega)
      refine ⟨?_, ?_⟩
      · rw [toDays_day ⟨d.year, d.month - 1, daysInMonth d.year (d.month - 1)⟩]
        simp only
        omega
      · simp only [Valid]
        omega
    · simp only [hm, ↓reduceIte]
      have hf := toDays_firstDay_next ⟨d.year - 1, 12⟩ (by simp) (by simp)
      have hn : (⟨d.year - 1, 12⟩ : YearMonth).next = ⟨d.year, 1⟩ := by
        simp [YearMonth.next]
      rw [hn] at hf
      simp only [YearMonth.firstDay, YearMonth.daysInMonth, daysInMonth] at hf
      have hm1 : d.month = 1 := by omega
      have hd1 : d.day = 1 := by omega
      refine ⟨?_, ?_⟩
      · rw [toDays_day ⟨d.year - 1, 12, 31⟩]
        simp only
        rw [hday, hm1, hd1]
        omega
      · simp only [Valid, daysInMonth]
        omega

/-- 素朴な翌日は、日数に 1 を足して日付に戻したものと同じになる。 -/
theorem nextDate_eq_ofDays (d : Date) (h : d.Valid) : nextDate d = ofDays (toDays d + 1) := by
  obtain ⟨he, hv⟩ := toDays_nextDate d h
  rw [← he, ofDays_toDays _ hv]

/-- 素朴な前日は、日数から 1 を引いて日付に戻したものと同じになる。 -/
theorem prevDate_eq_ofDays (d : Date) (h : d.Valid) : prevDate d = ofDays (toDays d - 1) := by
  obtain ⟨he, hv⟩ := toDays_prevDate d h
  rw [← he, ofDays_toDays _ hv]
end Ritsuryo.Date

namespace Ritsuryo.YearMonth

/-- 1〜12 月の年月を通し番号にして戻すと、元の年月になる。 -/
theorem ofIndex_index (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    ofIndex ym.index = ym := by
  obtain ⟨y, m⟩ := ym
  simp only [ofIndex, index, mk.injEq] at *
  omega

/-- 通し番号から戻した年月の月は 1〜12 に入る。 -/
theorem ofIndex_valid (k : Int) : 1 ≤ (ofIndex k).month ∧ (ofIndex k).month ≤ 12 := by
  simp only [ofIndex]
  omega

/-- 通し番号から年月に戻し、また通し番号にすると元の番号になる。 -/
theorem index_ofIndex (k : Int) : (ofIndex k).index = k := by
  simp only [ofIndex, index]
  omega

/-- 通し番号 `k` の年月の翌月は、通し番号 `k + 1` の年月になる。12 月かどうかで場合分けする。 -/
theorem next_ofIndex (k : Int) : (ofIndex k).next = ofIndex (k + 1) := by
  simp only [ofIndex, next]
  by_cases h : (k % 12).toNat + 1 < 12
  · simp only [h, ↓reduceIte, mk.injEq]
    omega
  · simp only [h, ↓reduceIte, mk.injEq]
    omega

/-- `next` を `n` 回繰り返す素朴な月の移動 `addMonthsNaive` は、
通し番号に `n` を足す `addMonths` と同じ年月になる。
期間計算の仕様（月を 1 つずつ数える）と実装（足し算）をつなぐ。`n` についての帰納法で、
1 月進めることが通し番号で 1 足すこと（`next_ofIndex`）を使う。 -/
theorem addMonthsNaive_eq (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) (n : Nat) :
    ym.addMonthsNaive n = ym.addMonths n := by
  induction n generalizing ym with
  | zero => simp [addMonthsNaive, addMonths, ofIndex_index ym h1 h2]
  | succ n ih =>
    simp only [addMonthsNaive]
    have hv := ofIndex_valid (ym.index + 1)
    rw [← ofIndex_index ym h1 h2, next_ofIndex, ih _ hv.1 hv.2]
    simp only [addMonths, index_ofIndex, ofIndex_index ym h1 h2]
    congr 1
    omega

end Ritsuryo.YearMonth

namespace Ritsuryo.Date

open YearMonth

/-- 通し番号 `k + 1` の年月の 1 日は、通し番号 `k` の年月の 1 日に、その月の日数を足した日になる。 -/
theorem firstDay_ofIndex_succ (k : Int) :
    toDays (ofIndex (k + 1)).firstDay = toDays (ofIndex k).firstDay + (ofIndex k).daysInMonth := by
  have hv := ofIndex_valid k
  rw [← next_ofIndex, toDays_firstDay_next _ hv.1 hv.2]

/-- `n` 月後の 1 日は、少なくとも 28 × `n` 日後にある。`n` についての帰納法で、
どの月も 28 日以上あること（`daysInMonth_ge`）を使う。 -/
theorem firstDay_ofIndex_add (k : Int) (n : Nat) :
    toDays (ofIndex k).firstDay + 28 * n ≤ toDays (ofIndex (k + n)).firstDay := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := firstDay_ofIndex_succ (k + n)
    have hv := ofIndex_valid (k + n)
    have hb := daysInMonth_ge (ofIndex (k + n)).year (ofIndex (k + n)).month hv.1 hv.2
    simp only [YearMonth.daysInMonth] at h
    have : k + ((n + 1 : Nat) : Int) = k + n + 1 := by omega
    rw [this]
    omega

/-- 通し番号 `i` < `j` なら、`j` の年月の 1 日は、`i` の年月の末日の翌日以後にある。 -/
theorem firstDay_ofIndex_lt (i j : Int) (h : i < j) :
    toDays (ofIndex i).firstDay + (ofIndex i).daysInMonth ≤ toDays (ofIndex j).firstDay := by
  have h1 := firstDay_ofIndex_succ i
  have h2 := firstDay_ofIndex_add (i + 1) (j - (i + 1)).toNat
  have : i + 1 + ((j - (i + 1)).toNat : Int) = j := by omega
  rw [this] at h2
  omega

/-- 実在する日付 `a` が `b` より前（辞書式）なら、`a` の日数は `b` の日数より小さい。
年月が違う場合は、前の年月の末日が後の年月の 1 日より前にあること（`firstDay_ofIndex_lt`）を使い、
年月が同じ場合は日の差がそのまま日数の差になること（`toDays_day`）を使う。 -/
theorem lt_of_toDays_lt (a b : Date) (ha : a.Valid) (hb : b.Valid) (h : a < b) :
    a.toDays < b.toDays := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  rw [toDays_day a, toDays_day b]
  change Lt a b at h
  simp only [Lt] at h
  by_cases hym : a.yearMonth.index < b.yearMonth.index
  · have hl := firstDay_ofIndex_lt _ _ hym
    rw [ofIndex_index _ a1 a2, ofIndex_index _ b1 b2] at hl
    simp only [yearMonth, YearMonth.daysInMonth, YearMonth.firstDay] at hl
    omega
  · have hy : a.year = b.year := by
      simp only [yearMonth, index] at hym
      omega
    have hm : a.month = b.month := by
      simp only [yearMonth, index] at hym
      omega
    rw [hy, hm]
    omega

/-- 実在する日付どうしでは、辞書式の前後と日数の大小が一致する（CAL-3 の本体）。
逆向きは、辞書式の順序が全順序であることから、
`a` < `b` でなければ `b` < `a` か `a` = `b` になり、どちらも日数の大小と矛盾することで示す。 -/
theorem toDays_lt_iff (a b : Date) (ha : a.Valid) (hb : b.Valid) :
    a < b ↔ a.toDays < b.toDays := by
  refine ⟨lt_of_toDays_lt a b ha hb, fun h => ?_⟩
  by_cases hab : a < b
  · exact hab
  · exfalso
    have : b < a ∨ a = b := by
      change ¬Lt a b at hab
      change Lt b a ∨ a = b
      simp only [Lt] at *
      by_cases he : a = b
      · exact Or.inr he
      · left
        obtain ⟨ay, am, ad⟩ := a
        obtain ⟨by', bm, bd⟩ := b
        simp only [Date.mk.injEq] at *
        omega
    rcases this with hlt | heq
    · have := lt_of_toDays_lt b a hb ha hlt
      omega
    · subst heq
      omega

/-- 実在する日付どうしで日数が等しければ、日付も等しい。`ofDays_toDays` から従う。 -/
theorem toDays_inj (a b : Date) (ha : a.Valid) (hb : b.Valid) (h : a.toDays = b.toDays) :
    a = b := by
  rw [← ofDays_toDays a ha, ← ofDays_toDays b hb, h]

end Ritsuryo.Date

namespace Ritsuryo.Weekday

/-- 日数を 1 進めると、曜日は次の曜日になる。`(z + 4) % 7` の 7 通りで場合分けする。 -/
theorem ofDays_succ (z : Int) : ofDays (z + 1) = (ofDays z).next := by
  simp only [ofDays]
  have h : (z + 4) % 7 = 0 ∨ (z + 4) % 7 = 1 ∨ (z + 4) % 7 = 2 ∨ (z + 4) % 7 = 3 ∨
      (z + 4) % 7 = 4 ∨ (z + 4) % 7 = 5 ∨ (z + 4) % 7 = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;>
    rw [h, show (z + 1 + 4) % 7 = ((z + 4) % 7 + 1) % 7 by omega, h] <;> rfl

end Ritsuryo.Weekday

namespace Ritsuryo.Date

/-- 日付の曜日は、日数に 4 を足して 7 で割った余りの番号の曜日になる（定義から）。 -/
theorem weekday_eq (d : Date) : d.weekday = Weekday.ofIndex ((d.toDays + 4) % 7).toNat := rfl

/-- 実在する日付の素朴な翌日の曜日は、その日の曜日の次の曜日になる。 -/
theorem weekday_nextDate (d : Date) (h : d.Valid) : (nextDate d).weekday = d.weekday.next := by
  simp only [weekday, (toDays_nextDate d h).1, Weekday.ofDays_succ]

/-- 西暦で書いた `isLeapYear` は、閏年ニ関スル件の文言どおり皇紀で判定する `IsLeapYearSpec` と一致する。
皇紀は西暦 + 660 で、660 は 4 の倍数なので、剰余の条件を `omega` で言い換えられる。 -/
theorem isLeapYear_iff_spec (y : Int) : isLeapYear y = true ↔ IsLeapYearSpec y := by
  rw [isLeapYear_iff]
  simp only [IsLeapYearSpec]
  omega

/-- 翌年 1 月 1 日は、その年の 1 月 1 日の 365 日後で、閏年なら 366 日後になる。
1 月 1 日はどちらも前の 3 月始まりの年に属するので、`marchYearStart_succ` から従う。 -/
theorem toDays_newYear_succ (y : Int) :
    toDays ⟨y + 1, 1, 1⟩ - toDays ⟨y, 1, 1⟩ = if isLeapYear y then 366 else 365 := by
  have h := marchYearStart_succ (y - 1)
  have hy : y - 1 + 1 = y := by omega
  rw [hy] at h
  simp only [toDays, marchYear, marchMonth, monthStart]
  simp only [show (1 : Nat) ≤ 2 by decide, ↓reduceIte, show y + 1 - 1 = y by omega]
  by_cases hl : isLeapYear y = true
  · simp only [hl, ↓reduceIte] at h ⊢
    omega
  · simp only [hl] at h ⊢
    simp at h ⊢
    omega

end Ritsuryo.Date

namespace Ritsuryo.Date

/-- CAL-1: 実在する日付（先発グレゴリオ暦、年は `Int`）を日数にして戻すと、元の日付になる。 -/
@[ritsuryo_proof "CAL-1", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal1_ofDays_toDays (d : Date) (h : d.Valid) : ofDays (toDays d) = d :=
  ofDays_toDays d h

/-- CAL-2: どの整数も、ある実在する日付の日数になる。`ofDays z` は実在する日付で、日数に戻すと `z` になる。 -/
@[ritsuryo_proof "CAL-2", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal2_toDays_ofDays (z : Int) : toDays (ofDays z) = z ∧ (ofDays z).Valid :=
  toDays_ofDays z

/-- CAL-3: 実在する日付どうしの辞書式の前後は、日数の大小と一致する。 -/
@[ritsuryo_proof "CAL-3", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal3_lt_iff (a b : Date) (ha : a.Valid) (hb : b.Valid) :
    a < b ↔ a.toDays < b.toDays :=
  toDays_lt_iff a b ha hb

/-- CAL-4: 月末・年末・閏年を場合分けする素朴な翌日 `nextDate` は、日数に 1 を足した日と同じで、
実在する日付になる。期間計算の仕様（`nextDate` を繰り返す）と実装（日数の足し算）をつなぐ。 -/
@[ritsuryo_proof "CAL-4", ritsuryo_basis "改暦ノ布告" "本則"]
theorem cal4_nextDate (d : Date) (h : d.Valid) :
    nextDate d = ofDays (toDays d + 1) ∧ (nextDate d).Valid :=
  ⟨nextDate_eq_ofDays d h, (toDays_nextDate d h).2⟩

/-- CAL-5: 日付の曜日は日数に 4 を足して 7 で割った余りで決まり、翌日の曜日は次の曜日になる。
民法第142条の「日曜日」の判定はこの曜日による。 -/
@[ritsuryo_proof "CAL-5", ritsuryo_basis "民法" "第142条"]
theorem cal5_weekday (d : Date) (h : d.Valid) :
    d.weekday = Weekday.ofIndex ((d.toDays + 4) % 7).toNat ∧
      (nextDate d).weekday = d.weekday.next :=
  ⟨weekday_eq d, weekday_nextDate d h⟩

/-- CAL-6: 各月の日数は、翌月 1 日と当月 1 日の日数の差に等しい。2 月が 29 日になるのは、
閏年ニ関スル件の文言どおり皇紀で判定して閏年になる年に限る。
前半は `toDays_firstDay_next`、後半は `isLeapYear_iff_spec` から従う。 -/
@[ritsuryo_proof "CAL-6", ritsuryo_basis "閏年ニ関スル件" "本則"]
theorem cal6_daysInMonth (ym : YearMonth) (h1 : 1 ≤ ym.month) (h2 : ym.month ≤ 12) :
    toDays ym.next.firstDay - toDays ym.firstDay = ym.daysInMonth ∧
      (ym.month = 2 → (ym.daysInMonth = 29 ↔ IsLeapYearSpec ym.year)) := by
  refine ⟨by rw [toDays_firstDay_next ym h1 h2]; omega, fun hm => ?_⟩
  rw [← isLeapYear_iff_spec]
  simp only [YearMonth.daysInMonth, hm, daysInMonth]
  split <;> simp_all

end Ritsuryo.Date
