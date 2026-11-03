module

public import Ritsuryo.Period.Proofs.Lemmas
meta import Ritsuryo.Basis

/-!
# 民法 第140条・第143条の実装と仕様の一致（PER-1）

CLI が実行する `compute`（通算日による計算）が、民法第140条・第143条第2項の言葉どおりに書いた仕様
（`Civil.startDateSpec`・`Civil.correspondingDaySpec`・`Civil.expirySpec`）と、有効なすべての日付で一致することを示す。

証明は仕様の部品ごとに実装との等式を作り、最後に組み合わせる。

1. 週の応当日: 同じ曜日の日を探す仕様（`sameWeekdayAfterSpec`）が、7 日後で止まることを示す（`sameWeekdayAfter_eq`）。
   曜日は通算日を 7 で割った余りで決まる（`Weekday.ofDays_eq_iff`）ので、1〜6 日後は曜日が違い、7 日後は同じになる。
   これで週の応当日は 7n 日後になる（`weekCorresponding_eq`）。
2. 最後の月: 1 か月ずつ進める仕様と通し番号で進める実装が同じ月になる（`lastMonth_eq`）。
3. 応当日（`correspondingDays_spec`）、末日（`expiryFromStart_spec`）、起算日（`start_spec`）の順に一致を示す。
   日付を通算日に移して戻すと元に戻る（`ofDays_toDays`、CAL-1）ことを各所で使う。
-/

public section

namespace Ritsuryo.Weekday

/-- 0〜6 の番号から曜日を作る `ofIndex` は単射。番号を 7 通りずつ場合分けして確かめる。 -/
theorem ofIndex_inj (a b : Nat) (ha : a < 7) (hb : b < 7) (h : ofIndex a = ofIndex b) :
    a = b := by
  have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by omega
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by omega
  rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' | hb' | hb' | hb' | hb' <;>
    subst ha' hb' <;> simp_all [ofIndex]

/-- 二つの通算日の曜日が同じであることと、通算日を 7 で割った余りが同じであることは同値。 -/
theorem ofDays_eq_iff (a b : Int) : ofDays a = ofDays b ↔ a % 7 = b % 7 := by
  simp only [ofDays]
  constructor
  · intro h
    have := ofIndex_inj _ _ (by omega) (by omega) h
    omega
  · intro h
    have : (a + 4) % 7 = (b + 4) % 7 := by omega
    rw [this]

end Ritsuryo.Weekday

namespace Ritsuryo.Period

open Date

/-- `d` から `k` 日進めた日の曜日は、通算日 `toDays d + k` の曜日になる。 -/
theorem weekday_addDaysNaive (d : Date) (h : d.Valid) (k : Nat) :
    (d.addDaysNaive k).weekday = Weekday.ofDays (toDays d + k) := by
  simp only [weekday, (addDaysNaive_toDays d h k).1]

/-- `k` 日進めた日の翌日は、`k + 1` 日進めた日になる。両辺を通算日に移して比べる。 -/
theorem nextDate_addDaysNaive (d : Date) (h : d.Valid) (k : Nat) :
    nextDate (d.addDaysNaive k) = d.addDaysNaive (k + 1) := by
  obtain ⟨_, hv⟩ := addDaysNaive_toDays d h k
  rw [nextDate_eq_ofDays _ hv, addDaysNaive_eq_ofDays d h, addDaysNaive_eq_ofDays d h,
    (toDays_ofDays _).1]
  congr 1
  omega

/-- `d` の `k` 日後（1 ≤ k ≤ 7）から同じ曜日の日を探すと、`d` の 7 日後で止まる。`fuel + k = 8` は、7 日後に着くまで
探索が打ち切られないことを表す。`fuel` についての帰納法で、`k < 7` なら曜日が違うので 1 日進み、`k = 7` で止まる。 -/
theorem sameWeekdayAfter_eq (d : Date) (h : d.Valid) (fuel k : Nat) (hk1 : 1 ≤ k) (hk7 : k ≤ 7)
    (hf : fuel + k = 8) :
    Civil.sameWeekdayAfterSpec d fuel (d.addDaysNaive k) = d.addDaysNaive 7 := by
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    simp only [Civil.sameWeekdayAfterSpec]
    by_cases h7 : k = 7
    · subst h7
      have : (d.addDaysNaive 7).weekday = d.weekday := by
        rw [weekday_addDaysNaive d h, weekday, Weekday.ofDays_eq_iff]
        omega
      simp [this]
    · have : ¬(d.addDaysNaive k).weekday = d.weekday := by
        rw [weekday_addDaysNaive d h, weekday, Weekday.ofDays_eq_iff]
        omega
      simp only [this, ↓reduceIte]
      rw [nextDate_addDaysNaive d h]
      exact ih (k + 1) (by omega) (by omega) (by omega)

/-- 週の応当日の仕様（同じ曜日の日へ `n` 回進む）は、起算日の `7 * n` 日後と等しい。
`n` についての帰納法で、各段階で `sameWeekdayAfter_eq` を使って 7 日進むことを示す。 -/
theorem weekCorresponding_eq (start : Date) (h : start.Valid) (n : Nat) :
    Civil.weekCorrespondingSpec start n = start.addDaysNaive (7 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Civil.weekCorrespondingSpec, ih]
    obtain ⟨_, hv⟩ := addDaysNaive_toDays start h (7 * n)
    have hs := sameWeekdayAfter_eq _ hv 7 1 (by omega) (by omega) (by omega)
    have h1 : (start.addDaysNaive (7 * n)).addDaysNaive 1 =
        nextDate (start.addDaysNaive (7 * n)) := rfl
    rw [← h1, hs, addDaysNaive_eq_ofDays _ hv, addDaysNaive_eq_ofDays _ h,
      addDaysNaive_eq_ofDays _ h, (toDays_ofDays _).1]
    congr 1
    omega

/-- 最後の月の実装（通し番号で進める）と仕様（1 か月ずつ進める、`n` 年後の同じ月）は等しい。
月は `addMonthsNaive_eq`、年は `addMonths_years` による。 -/
theorem lastMonth_eq (start : Date) (h : start.Valid) (len : Length) :
    lastMonth start len = Civil.lastMonthSpec start len := by
  obtain ⟨h1, h2, _, _⟩ := h
  cases len with
  | days n => rfl
  | weeks n => rfl
  | months n =>
    simp only [lastMonth, Civil.lastMonthSpec]
    rw [YearMonth.addMonthsNaive_eq _ h1 h2]
  | years n =>
    simp only [lastMonth, Civil.lastMonthSpec]
    exact YearMonth.addMonths_years _ h1 h2 n

/-- 最後の月の月は 1〜12 になる。 -/
theorem lastMonth_valid (start : Date) (h : start.Valid) (len : Length) :
    1 ≤ (lastMonth start len).month ∧ (lastMonth start len).month ≤ 12 := by
  obtain ⟨h1, h2, _, _⟩ := h
  cases len with
  | days n => exact ⟨h1, h2⟩
  | weeks n => exact ⟨h1, h2⟩
  | months n => exact YearMonth.addMonths_valid _ _
  | years n => exact YearMonth.addMonths_valid _ _

/-- 応当日の実装（通算日）を日付に戻すと、応当日の仕様と等しい。応当日がない場合（`none`）も一致する。
単位ごとに場合分けし、月・年では応当日の日付が有効なので通算日に移して戻しても変わらないことを使う。 -/
theorem correspondingDays_spec (start : Date) (h : start.Valid) (len : Length) :
    (correspondingDays start len).map ofDays = Civil.correspondingDaySpec start len := by
  have hlm := lastMonth_eq start h len
  have hv := lastMonth_valid start h len
  cases len with
  | days n =>
    simp [correspondingDays, Civil.correspondingDaySpec, addDaysNaive_eq_ofDays start h]
  | weeks n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, weekCorresponding_eq start h,
      addDaysNaive_eq_ofDays start h, Option.map_some]
    congr 2
  | months n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, ← hlm]
    split
    · rename_i hd
      simp only [Option.map_some]
      rw [ofDays_toDays _ (valid_of_le _ hv.1 hv.2 _ h.2.2.1 hd)]
    · rfl
  | years n =>
    simp only [correspondingDays, Civil.correspondingDaySpec, ← hlm]
    split
    · rename_i hd
      simp only [Option.map_some]
      rw [ofDays_toDays _ (valid_of_le _ hv.1 hv.2 _ h.2.2.1 hd)]
    · rfl

/-- 起算日から数えた末日の実装（通算日）を日付に戻すと、末日の仕様と等しい。
応当日があるときは前日（通算日から 1 を引く）が `prevDate` と一致し、ないときは最後の月の末日どうしが一致する。 -/
theorem expiryFromStart_spec (start : Date) (h : start.Valid) (len : Length) :
    ofDays (expiryFromStartDays start len) = Civil.expiryFromStartSpec start len := by
  have hc := correspondingDays_spec start h len
  unfold expiryFromStartDays Civil.expiryFromStartSpec
  rw [← hc]
  cases hcd : correspondingDays start len with
  | some c =>
    simp only [Option.map_some]
    rw [prevDate_eq_ofDays _ (toDays_ofDays c).2, (toDays_ofDays c).1]
  | none =>
    simp only [Option.map_none]
    have hv := lastMonth_valid start h len
    rw [ofDays_toDays _ (lastDay_valid _ hv.1 hv.2), lastMonth_eq start h len]

/-- 起算日の実装（通算日）を日付に戻すと起算日の仕様と等しく、起算日は有効な日付になる。
初日不算入のときは、通算日に 1 を足すことと翌日（`nextDate`）が一致することによる。 -/
theorem start_spec (event : Date) (h : event.Valid) (startAtMidnight : Bool) :
    ofDays (startDays event startAtMidnight) = Civil.startDateSpec event startAtMidnight ∧
      (Civil.startDateSpec event startAtMidnight).Valid := by
  cases startAtMidnight with
  | true => exact ⟨ofDays_toDays event h, h⟩
  | false =>
    simp only [startDays, Civil.startDateSpec, Bool.false_eq_true, ↓reduceIte]
    exact ⟨(nextDate_eq_ofDays event h).symm, (toDays_nextDate event h).2⟩

/-- PER-1: 有効な日付 `event` について、CLI の `compute` が返す起算日・応当日・末日は、民法第140条・第143条第2項の
仕様と一致する。`start_spec` で起算日を揃え、その起算日に `correspondingDays_spec` と `expiryFromStart_spec` を当てる。 -/
@[ritsuryo_proof "PER-1", ritsuryo_basis "民法" "第140条", ritsuryo_basis "民法" "第143条第2項"]
theorem per1_compute_eq_spec (event : Date) (h : event.Valid) (startAtMidnight : Bool)
    (len : Length) :
    (compute event startAtMidnight len).start = Civil.startDateSpec event startAtMidnight ∧
      (compute event startAtMidnight len).corresponding =
        Civil.correspondingDaySpec (Civil.startDateSpec event startAtMidnight) len ∧
      (compute event startAtMidnight len).expiry = Civil.expirySpec event startAtMidnight len := by
  obtain ⟨hs, hv⟩ := start_spec event h startAtMidnight
  simp only [compute, Civil.expirySpec]
  rw [hs]
  exact ⟨rfl, correspondingDays_spec _ hv len, expiryFromStart_spec _ hv len⟩

end Ritsuryo.Period
