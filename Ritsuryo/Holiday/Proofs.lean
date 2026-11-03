module

public import Ritsuryo.Holiday.Spec
public import Ritsuryo.Period.Proofs.Civil
meta import Ritsuryo.Basis

/-!
# 祝日法 第2条・第3条の証明（HOL-1、HOL-2）

- HOL-1（`hol1_derivation`）: 実装の `isSubstitute`・`isCitizens` が、第3条第2項・第3項の文言を写した
  `SubstituteSpec`・`CitizensSpec` と、国民の祝日の集合 `H` によらず一致する。
- HOL-2（`hol2_nthMonday`）: 第2条の「第 n 月曜日」を計算する `nthMonday` が、有効な日付の月曜日を返し、
  その日が月の第 `n` 週（`7 * (n - 1)` 日より後で `7 * n` 日以前）に入る。
-/

public section

namespace Ritsuryo.Holiday

open Date

/-- 日番号 `x` の日が日曜日であることは、`(x + 4) % 7 = 0` と同値になる。 -/
theorem ofDays_sunday_iff (x : Int) : Weekday.ofDays x = .sunday ↔ (x + 4) % 7 = 0 := by
  constructor
  · intro h
    have := Weekday.ofIndex_inj ((x + 4) % 7).toNat 0 (by omega) (by decide) h
    omega
  · intro h
    simp only [Weekday.ofDays, h]
    rfl

/-- `sundayRun H k x` は、`x` から `j` 日前（`j < k`）が日曜日で、その間の日がすべて国民の祝日であることと
同値になる。`k` についての帰納法で、`x` 自身が日曜日の場合（`j = 0`）と前日へ進む場合に分けて示す。 -/
theorem sundayRun_iff (H : Int → Bool) (k : Nat) (x : Int) :
    sundayRun H k x = true ↔
      ∃ j : Nat, j < k ∧ Weekday.ofDays (x - j) = .sunday ∧
        ∀ i : Nat, i ≤ j → H (x - i) = true := by
  induction k generalizing x with
  | zero => simp [sundayRun]
  | succ k ih =>
    simp only [sundayRun, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨hx, hs | ⟨j, hj, hw, hall⟩⟩
      · exact ⟨0, by omega, by simpa using hs, fun i hi => by
          have : i = 0 := by omega
          subst this
          simpa using hx⟩
      · refine ⟨j + 1, by omega,
          by rw [show x - ((j + 1 : Nat) : Int) = x - 1 - j by omega]; exact hw, fun i hi => ?_⟩
        by_cases hi0 : i = 0
        · subst hi0
          simpa using hx
        · have := hall (i - 1) (by omega)
          rwa [show x - 1 - ((i - 1 : Nat) : Int) = x - i by omega] at this
    · rintro ⟨j, hj, hw, hall⟩
      refine ⟨by simpa using hall 0 (by omega), ?_⟩
      by_cases hj0 : j = 0
      · subst hj0
        left
        simpa using hw
      · right
        refine ⟨j - 1, by omega,
          by rw [show x - 1 - ((j - 1 : Nat) : Int) = x - j by omega]; exact hw, fun i hi => ?_⟩
        have := hall (i + 1) (by omega)
        rwa [show x - ((i + 1 : Nat) : Int) = x - 1 - i by omega] at this

/-- HOL-1: 振替休日と国民の休日の実装が、第3条第2項・第3項の仕様と一致する。
振替休日は `sundayRun_iff` で 7 日のさかのぼりを存在命題に直す。仕様の日曜日 `s` が 7 日より前にあっても、
`z` の前日から数えて最初の日曜日が 7 日以内にあり、その間はすべて祝日なので、実装の条件を満たす。
国民の休日は、両辺が同じ連言なので並べ替えるだけで示せる。 -/
@[ritsuryo_proof "HOL-1", ritsuryo_basis "国民の祝日に関する法律" "第3条第2項",
  ritsuryo_basis "国民の祝日に関する法律" "第3条第3項"]
theorem hol1_derivation (H : Int → Bool) (z : Int) :
    (isSubstitute H z = true ↔ SubstituteSpec H z) ∧
      (isCitizens H z = true ↔ CitizensSpec H z) := by
  refine ⟨?_, ?_⟩
  · simp only [isSubstitute, SubstituteSpec, Bool.and_eq_true, Bool.not_eq_true', sundayRun_iff]
    constructor
    · rintro ⟨hz, j, hj, hw, hall⟩
      refine ⟨hz, z - 1 - j, by omega, by simpa using hall j (Nat.le_refl j), hw,
        fun x hx1 hx2 => ?_⟩
      have := hall (z - 1 - x).toNat (by omega)
      rwa [show z - 1 - (((z - 1 - x).toNat : Nat) : Int) = x by omega] at this
    · rintro ⟨hz, s, hs, hH, hw, hall⟩
      refine ⟨hz, ((z - 1 + 4) % 7).toNat, by omega, ?_, fun i hi => ?_⟩
      · rw [ofDays_sunday_iff]
        omega
      · rw [ofDays_sunday_iff] at hw
        by_cases he : z - 1 - i = s
        · rw [he]
          exact hH
        · exact hall _ (by omega) (by omega)
  · simp only [isCitizens, CitizensSpec, Bool.and_eq_true, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩

/-- HOL-2: `1 ≤ m ≤ 12` かつ `1 ≤ n ≤ 4` のとき、`nthMonday y m n` は有効な日付で、曜日は月曜日、日は第 `n` 週に入る。
1 日の曜日 `w` を変数に置き、日 `1 + (8 - w) % 7 + 7 * (n - 1)` と日番号の関係を `omega` で解く。 -/
@[ritsuryo_proof "HOL-2", ritsuryo_basis "国民の祝日に関する法律" "第2条"]
theorem hol2_nthMonday (y : Int) (m n : Nat) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hn1 : 1 ≤ n)
    (hn4 : n ≤ 4) :
    (nthMonday y m n).Valid ∧ (nthMonday y m n).weekday = .monday ∧
      7 * (n - 1) < (nthMonday y m n).day ∧ (nthMonday y m n).day ≤ 7 * n := by
  have hb := daysInMonth_ge y m hm1 hm2
  have hd := toDays_day (nthMonday y m n)
  generalize hw : ((toDays ⟨y, m, 1⟩ + 4) % 7).toNat = w
  have hday : (nthMonday y m n).day = 1 + (8 - w) % 7 + 7 * (n - 1) := by
    simp only [nthMonday, hw]
  have hym : (⟨(nthMonday y m n).year, (nthMonday y m n).month, 1⟩ : Date) = ⟨y, m, 1⟩ := rfl
  have hmo : (nthMonday y m n).month = m := rfl
  have hyr : (nthMonday y m n).year = y := rfl
  rw [hym, hday] at hd
  refine ⟨⟨by rw [hmo]; exact hm1, by rw [hmo]; exact hm2, by rw [hday]; omega, ?_⟩, ?_,
    by rw [hday]; omega, by rw [hday]; omega⟩
  · rw [hday, hmo, hyr]
    omega
  · simp only [weekday, Weekday.ofDays, hd]
    rw [show ((toDays ⟨y, m, 1⟩ + ((1 + (8 - w) % 7 + 7 * (n - 1) : Nat) : Int) - 1 + 4) %
      7).toNat = 1 by omega]
    rfl

end Ritsuryo.Holiday
