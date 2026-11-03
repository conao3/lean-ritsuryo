module

public import Ritsuryo.Calendar.Days
meta import Ritsuryo.Basis

/-!
# 日数の計算式の補題

`Ritsuryo.Calendar.Days` の計算式（400 年周期・100 年・4 年・1 年への分解と、3 月始まりの月の 1 次式）について、
分解と組み立てが互いに逆になることを示す補題を置く。`Ritsuryo.Calendar.Proofs` の CAL-1〜CAL-6 はこれらを組み合わせる。

どの補題も、割り算と剰余を含む式を、商と余りの範囲を仮定に足したうえで `omega`（整数の線形算術の決定手続き）
で閉じる形になる。`omega` は定数による割り算と剰余を扱えるので、場合分けの多くを自動で済ませられる。
-/

public section

namespace Ritsuryo.Date

/-- 周期の中の年を 100 年 `c` 回・4 年 `q` 回・1 年 `r` 回に分けると、その年の始まりまでの日数は
36,524 日 × `c` + 1,461 日 × `q` + 365 日 × `r` になる。`(100c + 4q + r) / 4` と `/ 100` の値を `omega` で
出してから展開する。 -/
theorem yearStart_decomp (c q r : Int) (hq : 0 ≤ q ∧ q ≤ 24) (hr : 0 ≤ r ∧ r ≤ 3) :
    yearStart (100 * c + 4 * q + r) = 36524 * c + 1461 * q + 365 * r := by
  have h4 : (100 * c + 4 * q + r) / 4 = 25 * c + q := by omega
  have h100 : (100 * c + 4 * q + r) / 100 = c := by omega
  simp only [yearStart, h4, h100]
  omega

/-- 周期の中の日 `doe`（0〜146,096）を `centOf`・`quadOf`・`yrOf` で分けたときの範囲。
100 年の番号は 0〜3、4 年の番号は 0〜24、年の番号は 0〜3 で、残りの日（年の中の日）は 0〜364 になる。
残りがちょうど 365 になるのは閏日を含む年の最後の日だけで、そのとき年の番号は 3 で、
100 年の最後の 4 年（番号 24）ではないか、周期の最後の 100 年（番号 3）に入る。
先に `centOf` の範囲を `omega` で出し、それを変数に置き換えてから残りを `omega` で閉じる。 -/
theorem decomp_bounds (doe : Int) (h0 : 0 ≤ doe) (h1 : doe ≤ 146096) :
    (0 ≤ centOf doe ∧ centOf doe ≤ 3) ∧ (0 ≤ quadOf doe ∧ quadOf doe ≤ 24) ∧
    (0 ≤ yrOf doe ∧ yrOf doe ≤ 3) ∧
    0 ≤ doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) ∧
    (doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) ≤ 364 ∨
     (doe - (36524 * centOf doe + 1461 * quadOf doe + 365 * yrOf doe) = 365 ∧
      yrOf doe = 3 ∧ (quadOf doe ≠ 24 ∨ centOf doe = 3))) := by
  have hc : 0 ≤ centOf doe ∧ centOf doe ≤ 3 ∧ 0 ≤ doe - 36524 * centOf doe ∧
      (doe - 36524 * centOf doe ≤ 36523 ∨ (centOf doe = 3 ∧ doe = 146096)) := by
    simp only [centOf]
    omega
  simp only [quadOf, yrOf]
  generalize centOf doe = c at *
  omega

/-- `yoeOf` が周期の中の年を正しく出すこと。結果は 0〜399 で、その年の始まり以後の日であり、
年の中の日は 0〜364 か、閏日を含む年（3 月始まりの年 `yoe` の翌年 2 月が閏月になる年、つまり `yoe + 1` が
閏年になる年）の最後の日 365 になる。`decomp_bounds` と `yearStart_decomp` から従う。 -/
theorem yoeOf_spec (doe : Int) (h0 : 0 ≤ doe) (h1 : doe ≤ 146096) :
    0 ≤ yoeOf doe ∧ yoeOf doe ≤ 399 ∧ yearStart (yoeOf doe) ≤ doe ∧
    (doe - yearStart (yoeOf doe) ≤ 364 ∨
      (doe - yearStart (yoeOf doe) = 365 ∧ yoeOf doe % 4 = 3 ∧
        (yoeOf doe % 100 ≠ 99 ∨ yoeOf doe = 399))) := by
  have h := decomp_bounds doe h0 h1
  simp only [yoeOf]
  rw [yearStart_decomp _ _ _ h.2.1 h.2.2.1]
  omega

/-- `yoeOf` は `yearStart` の逆になる。周期の中の年 `yoe` の始まりから `doy` 日目（その年に収まる範囲）を
`yoeOf` に渡すと `yoe` に戻る。`yoe` を 100 年・4 年・1 年の回数に分け、`centOf`・`quadOf`・`yrOf` が
それぞれの回数を返すことを順に `omega` で確かめる。 -/
theorem yoeOf_yearStart (yoe doy : Int) (h0 : 0 ≤ yoe) (h1 : yoe ≤ 399) (h2 : 0 ≤ doy)
    (h3 : doy ≤ 364 ∨ (doy = 365 ∧ yoe % 4 = 3 ∧ (yoe % 100 ≠ 99 ∨ yoe = 399))) :
    yoeOf (yearStart yoe + doy) = yoe := by
  have hy : yoe = 100 * (yoe / 100) + 4 * (yoe % 100 / 4) + yoe % 4 := by omega
  have hs := yearStart_decomp (yoe / 100) (yoe % 100 / 4) (yoe % 4) (by omega) (by omega)
  rw [← hy] at hs
  rw [hs]
  have hb : 0 ≤ yoe / 100 ∧ yoe / 100 ≤ 3 ∧ 0 ≤ yoe % 100 / 4 ∧ yoe % 100 / 4 ≤ 24 ∧
      0 ≤ yoe % 4 ∧ yoe % 4 ≤ 3 := by omega
  have hl : doy = 365 → yoe % 4 = 3 ∧ (yoe % 100 / 4 ≠ 24 ∨ yoe / 100 = 3) := by omega
  have hd : doy ≤ 365 := by omega
  clear h3
  generalize yoe / 100 = c at *
  generalize yoe % 100 / 4 = q at *
  generalize hr : yoe % 4 = r at *
  have hc : centOf (36524 * c + 1461 * q + 365 * r + doy) = c := by
    simp only [centOf]
    omega
  have hq : quadOf (36524 * c + 1461 * q + 365 * r + doy) = q := by
    simp only [quadOf, hc]
    omega
  have hm : (36524 * c + 1461 * q + 365 * r + doy - 36524 * c) % 1461 = 365 * r + doy := by
    omega
  have hr' : yrOf (36524 * c + 1461 * q + 365 * r + doy) = r := by
    simp only [yrOf, hc, hm]
    omega
  simp only [yoeOf, hc, hq, hr']
  omega

/-- 年の中の日 `doy`（0〜365）に対し、`monthOf` は 0〜11 の月を返し、`doy` はその月の 1 日以後、
翌月の 1 日より前にある。 -/
theorem monthOf_spec (doy : Int) (h0 : 0 ≤ doy) (h1 : doy ≤ 365) :
    0 ≤ monthOf doy ∧ monthOf doy ≤ 11 ∧ monthStart (monthOf doy) ≤ doy ∧
      doy < monthStart (monthOf doy + 1) := by
  simp only [monthOf, monthStart]
  omega

/-- `monthOf` は `monthStart` の逆になる。月 `mp` の 1 日から `k` 日目（その月に収まる範囲）を
`monthOf` に渡すと `mp` に戻る。 -/
theorem monthOf_monthStart (mp k : Int) (h2 : 0 ≤ k)
    (h3 : k < monthStart (mp + 1) - monthStart mp) : monthOf (monthStart mp + k) = mp := by
  simp only [monthOf, monthStart] at *
  omega

/-- `Bool` で書いた `isLeapYear` を、整数の剰余の条件（命題）に言い換える。 -/
theorem isLeapYear_iff (y : Int) :
    isLeapYear y = true ↔ y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0) := by
  simp [isLeapYear]

/-- 3 月始まりの年 `y + 1` の始まりは、年 `y` の始まりの 365 日後で、暦年 `y + 1` が閏年なら 366 日後。
3 月始まりの年 `y` は暦年 `y + 1` の 2 月を含むので、閏日が入るかどうかは `y + 1` で決まる。
`y` が 400 年周期の最後の年（`y % 400 = 399`）かどうかで場合分けし、周期をまたぐ場合は
146,097 − `yearStart 399` = 366 になることを、またがない場合は `yearStart` の差を `omega` で確かめる。 -/
theorem marchYearStart_succ (y : Int) :
    marchYearStart (y + 1) =
      marchYearStart y + 365 + (if isLeapYear (y + 1) then 1 else 0) := by
  simp only [marchYearStart, yearStart]
  by_cases h : y % 400 = 399
  · have h1 : (y + 1) / 400 = y / 400 + 1 := by omega
    have h2 : (y + 1) % 400 = 0 := by omega
    have h3 : isLeapYear (y + 1) = true := by
      rw [isLeapYear_iff]
      omega
    rw [h1, h2, h]
    simp only [h3, ↓reduceIte]
    omega
  · have h1 : (y + 1) / 400 = y / 400 := by omega
    have h2 : (y + 1) % 400 = y % 400 + 1 := by omega
    rw [h1, h2]
    split
    · rename_i hl
      rw [isLeapYear_iff] at hl
      omega
    · rename_i hl
      rw [isLeapYear_iff] at hl
      omega

end Ritsuryo.Date
