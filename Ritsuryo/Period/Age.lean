module

public import Ritsuryo.Period.Impl
meta import Ritsuryo.Basis

/-!
# 年齢計算ニ関スル法律

明治三十五年法律第五十号、e-Gov 法令履歴 `135AC1000000050_19021222_000000000000000`。

> １　年齢ハ出生ノ日ヨリ之ヲ起算ス
> ２　民法第百四十三条ノ規定ハ年齢ノ計算ニ之ヲ準用ス
-/

@[expose] public section

namespace Ritsuryo.Period.Age

open Date

/-- 年齢ハ出生ノ日ヨリ之ヲ起算ス。民法第百四十三条ノ規定ハ年齢ノ計算ニ之ヲ準用ス。 -/
@[ritsuryo_basis "年齢計算ニ関スル法律" "第1項", ritsuryo_basis "年齢計算ニ関スル法律" "第2項",
  ritsuryo_basis "民法" "第143条第2項"]
def attainmentSpec (birth : Date) (age : Nat) : Date :=
  Civil.expiryFromStartSpec birth (.years age)

@[ritsuryo_basis "年齢計算ニ関スル法律" "第2項", ritsuryo_basis "民法" "第143条第2項"]
def attainmentDays (birth : Date) (age : Nat) : Int :=
  expiryFromStartDays birth (.years age)

@[ritsuryo_basis "年齢計算ニ関スル法律" "第2項", ritsuryo_basis "民法" "第143条第2項"]
def attainmentDate (birth : Date) (age : Nat) : Date :=
  ofDays (attainmentDays birth age)

@[ritsuryo_basis "年齢計算ニ関スル法律" "第1項", ritsuryo_basis "年齢計算ニ関スル法律" "第2項"]
def ageOn (birth asOf : Date) : Nat :=
  let k := (asOf.year - birth.year).toNat
  if attainmentDays birth (k + 1) ≤ asOf.toDays then k + 1
  else if attainmentDays birth k ≤ asOf.toDays then k
  else k - 1

end Ritsuryo.Period.Age
