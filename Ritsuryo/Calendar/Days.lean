module

public import Ritsuryo.Calendar.Date
meta import Ritsuryo.Basis

/-!
# 日付と日数の変換

日付を 1970-01-01 からの日数（1970-01-01 が 0、その翌日が 1、前日が −1）の整数で表す変換 `toDays` と、
その逆の `ofDays` を定める。暦の規則（大の月・小の月、改暦ノ布告と閏年ニ関スル件による閏年）は
`Ritsuryo.Calendar.Date` のとおりで、このファイルはそれを日数の計算式に置き換える。

## なぜ日数を使うか

日付を日数に直すと、「`n` 日後」は足し算、「前後」は整数の大小、「何日離れているか」は引き算になる。
期間計算や祝日の証明は日付をこの整数に移して述べ、線形算術の決定手続き `omega` で閉じる。
そのために、変換が全単射であること（CAL-1、CAL-2）、日付の順序と日数の順序が一致すること（CAL-3）、
素朴な翌日 `nextDate` が日数で 1 進むこと（CAL-4）を `Ritsuryo.Calendar.Proofs` で証明する。
CLI は `ofDays (toDays d + n)` で `n` 日後を求め、期間計算の仕様は `nextDate` を `n` 回繰り返す。
この 2 つが同じ日になることが上の定理から従う。

## 計算のしかた

Howard Hinnant の `days_from_civil` / `civil_from_days` と同じ考え方で、次の 3 つの工夫をする。

1. 年の始まりを 3 月 1 日にずらす（`marchYear`、`marchMonth`）。1 月・2 月は前年の続きとして扱い、
   3 月を 0 月、翌年 2 月を 11 月と数える。閏日（2 月 29 日）がその年の最後の日になるので、
   月の始まりの日が閏年かどうかによらない。
2. 3 月始まりの年の中で、`m` 月（0〜11）の 1 日が 3 月 1 日から何日目かは `(153 * m + 2) / 5`
   （`monthStart`）で出る。3 月〜7 月の 5 か月が 31・30・31・30・31 日で計 153 日、8 月〜12 月も同じ並びに
   なるので、端数を切り捨てる 1 次式で 0、31、61、92、122、153、184、214、245、275、306、337 が得られる。
3. 400 年を 1 つの周期（era）にする。400 年には閏年が 97 回あり、日数は 400 × 365 + 97 = 146,097 日で
   いつも同じになる。周期の中の年（`yoe`、0〜399）の始まりまでの日数は `365 * yoe + yoe / 4 - yoe / 100`
   （`yearStart`）で、400 で割り切れる年の閏日は周期の最後の日（周期内の日 146,096）に来る。

西暦 0 年 3 月 1 日からの日数を `marchYearStart (marchYear d) + monthStart (marchMonth d.month) + d.day - 1`
で出し、そこから 719,468 を引くと 1970-01-01 からの日数になる。719,468 は西暦 0 年 3 月 1 日から
1970 年 1 月 1 日までの日数（4 周期 584,388 日 + 周期内 369 年 134,774 日 + 3 月から 12 月までの 306 日）。

逆向きの `ofDays` は、日数に 719,468 を足して周期の番号（`/ 146097`）と周期内の日（`% 146097`）に分け、
周期内の日を 100 年（36,524 日）、4 年（1,461 日）、1 年（365 日）の順に割って周期内の年を出し、
年の中の日から月と日を戻す。`Int` の `/` と `%` は除数が正なら剰余が 0 以上になる（ユークリッド除算）ので、
1970 年より前や紀元前の日付にも同じ式が当てはまる。
-/

@[expose] public section

namespace Ritsuryo

namespace Date

/-- 3 月始まりで数えた年。1 月・2 月は前年に、3 月〜12 月はその年に属する。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def marchYear (d : Date) : Int :=
  if d.month ≤ 2 then d.year - 1 else d.year

/-- 3 月始まりで数えた月（0〜11）。3 月が 0、12 月が 9、1 月が 10、2 月が 11 になる。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def marchMonth (m : Nat) : Int :=
  if m ≤ 2 then (m : Int) + 9 else (m : Int) - 3

/-- 3 月始まりの年で、`mp` 月（0〜11）の 1 日が 3 月 1 日から何日目か（3 月 1 日が 0）。
`mp` = 0〜11 に対して 0、31、61、92、122、153、184、214、245、275、306、337 になる。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def monthStart (mp : Int) : Int :=
  (153 * mp + 2) / 5

/-- 400 年周期の中の年 `yoe`（0〜399）の 3 月 1 日が、周期の始まりから何日目か。
1 年 365 日に、それまでの閏日の数（4 年に 1 回、100 年ごとに除く）を足す。
`yoe` は 400 未満なので、400 で割り切れる年の扱いはこの式に出てこない。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yearStart (yoe : Int) : Int :=
  365 * yoe + yoe / 4 - yoe / 100

/-- 3 月始まりの年 `y` の 3 月 1 日が、西暦 0 年 3 月 1 日から何日目か。
完全な 400 年周期の数 × 146,097 日に、周期の中の年の始まりまでの日数を足す。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def marchYearStart (y : Int) : Int :=
  (y / 400) * 146097 + yearStart (y % 400)

/-- 日付 `d` の 1970-01-01 からの日数。西暦 0 年 3 月 1 日からの日数を出し、
1970-01-01 までの日数 719,468 を引く。範囲外の月日にも値は出るが、意味を持つのは `d.Valid` のときだけ。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def toDays (d : Date) : Int :=
  marchYearStart (marchYear d) + monthStart (marchMonth d.month) + d.day - 1 - 719468

/-- 400 年周期の中の日 `doe`（0〜146,096）が、周期の中の何番目の 100 年（0〜3）に入るか。
100 年は 36,524 日だが、周期の最後の 100 年だけは 400 で割り切れる年の閏日を含んで 36,525 日になるので、
最後の 1 日（`doe` = 146,096）が 4 にならないよう 3 で頭打ちにする。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def centOf (doe : Int) : Int :=
  min (doe / 36524) 3

/-- 100 年の中で何番目の 4 年（0〜24）に入るか。4 年は閏日を 1 回含んで 1,461 日。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def quadOf (doe : Int) : Int :=
  (doe - 36524 * centOf doe) / 1461

/-- 4 年の中で何番目の年（0〜3）に入るか。4 年目は閏日を含んで 366 日なので、
その最後の日（4 年の中の日 1,460）が 4 にならないよう 3 で頭打ちにする。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yrOf (doe : Int) : Int :=
  min ((doe - 36524 * centOf doe) % 1461 / 365) 3

/-- 400 年周期の中の日 `doe` から、周期の中の年（0〜399）を出す。`yearStart` の逆になる。 -/
@[ritsuryo_basis "閏年ニ関スル件" "本則"]
def yoeOf (doe : Int) : Int :=
  100 * centOf doe + 4 * quadOf doe + yrOf doe

/-- 3 月始まりの年の中の日 `doy`（0〜365）から、3 月始まりの月（0〜11）を出す。`monthStart` の逆になる。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def monthOf (doy : Int) : Int :=
  (5 * doy + 2) / 153

/-- 1970-01-01 からの日数 `z` の日付。`toDays` の逆で、どの整数に対しても実在する日付を返す（CAL-2）。 -/
@[ritsuryo_basis "改暦ノ布告" "本則"]
def ofDays (z : Int) : Date :=
  -- 西暦 0 年 3 月 1 日からの日数にし、400 年周期の番号と周期の中の日に分ける
  let z' := z + 719468
  let era := z' / 146097
  let doe := z' % 146097
  let yoe := yoeOf doe
  let doy := doe - yearStart yoe
  let mp := monthOf doy
  let day := doy - monthStart mp + 1
  -- 3 月始まりの月を暦の月に戻す。1 月・2 月（`mp` が 10・11）は翌年に属する
  let month := if mp < 10 then mp + 3 else mp - 9
  ⟨era * 400 + yoe + (if mp < 10 then 0 else 1), month.toNat, day.toNat⟩

end Date

end Ritsuryo
