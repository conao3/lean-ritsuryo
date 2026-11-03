module

public import Ritsuryo.Period.Impl
meta import Ritsuryo.Basis

/-!
# 年齢計算ニ関スル法律（年齢の計算）

年齢は出生の日から起算し（第1項。初日算入）、民法第143条を準用して暦に従って数える（第2項）。
n 歳に達するのは、出生の日から n 年の期間が満了する日、つまり n 年後の誕生日の前日になる。
2月29日生まれの人は、閏年には誕生日の前日の2月28日に、平年には応当日がないので2月の末日の2月28日に年を取る。

- 仕様: `attainmentSpec`。民法第143条第2項の仕様 `Civil.expiryFromStartSpec` に、出生の日を起算日として渡す。
- 実装: `attainmentDays`・`attainmentDate`（通算日による計算 `expiryFromStartDays` を使う）と、
  ある日の年齢を返す `ageOn`。CLI の `age get-attainment-date`・`age compute-age` が実行する。
- 証明: AGE-1（`age1_attainment`）が実装と仕様の一致と2月29日生まれの扱いを、AGE-2（`age2_monotone_and_steps`）が
  `ageOn` の正しさ（年齢に達する日の間で一定、日付について単調、達する日ごとに 1 ずつ増える）を示す。

明治三十五年法律第五十号、e-Gov 法令履歴 `135AC1000000050_19021222_000000000000000`。

> １　年齢ハ出生ノ日ヨリ之ヲ起算ス
> ２　民法第百四十三条ノ規定ハ年齢ノ計算ニ之ヲ準用ス
-/

@[expose] public section

namespace Ritsuryo.Period.Age

open Date

/-- 年齢ハ出生ノ日ヨリ之ヲ起算ス。民法第百四十三条ノ規定ハ年齢ノ計算ニ之ヲ準用ス。

出生の日 `birth` の人が `age` 歳に達する日（仕様）。出生の日を起算日とする `age` 年の期間の末日で、
`age` 年後の誕生日の前日、その月に誕生日の日付がないときはその月の末日になる。 -/
@[ritsuryo_basis "年齢計算ニ関スル法律" "第1項", ritsuryo_basis "年齢計算ニ関スル法律" "第2項",
  ritsuryo_basis "民法" "第143条第2項"]
def attainmentSpec (birth : Date) (age : Nat) : Date :=
  Civil.expiryFromStartSpec birth (.years age)

/-- `age` 歳に達する日の通算日（実装）。出生の日を起算日として `expiryFromStartDays` で `age` 年の末日を出す。 -/
@[ritsuryo_basis "年齢計算ニ関スル法律" "第2項", ritsuryo_basis "民法" "第143条第2項"]
def attainmentDays (birth : Date) (age : Nat) : Int :=
  expiryFromStartDays birth (.years age)

/-- `age` 歳に達する日（実装）。`attainmentDays` の通算日を日付に戻す。 -/
@[ritsuryo_basis "年齢計算ニ関スル法律" "第2項", ritsuryo_basis "民法" "第143条第2項"]
def attainmentDate (birth : Date) (age : Nat) : Date :=
  ofDays (attainmentDays birth age)

/-- 日 `asOf` の終わりの年齢。年齢に達する日が `asOf` 以前である最大の `n` を返す。年齢に達する日の当日は `n` 歳と数える。
年の差 `k` を目安にし、答えは `k + 1`・`k`・`k - 1` のどれかになる（1月1日生まれは前年の12月31日に年を取るので
`k + 1` がありうる）。AGE-2 が、出生の日以後の `asOf` についてこの値が正しいことを示す。 -/
@[ritsuryo_basis "年齢計算ニ関スル法律" "第1項", ritsuryo_basis "年齢計算ニ関スル法律" "第2項"]
def ageOn (birth asOf : Date) : Nat :=
  let k := (asOf.year - birth.year).toNat
  if attainmentDays birth (k + 1) ≤ asOf.toDays then k + 1
  else if attainmentDays birth k ≤ asOf.toDays then k
  else k - 1

end Ritsuryo.Period.Age
