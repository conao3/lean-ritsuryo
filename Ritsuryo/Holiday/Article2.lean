module

public import Ritsuryo.Holiday.Lookup
meta import Ritsuryo.Basis

/-!
# 祝日法 第2条の規則と、その改正の経過（HOL-C2 の検査）

第2条は「国民の祝日」を名称と日付の規則（固定日、第 n 月曜日、春分日・秋分日）で定める。このファイルは、
第2条の規則を施行期間つきの表 `rules` にし、各年の祝日の日付を生成する。生成した日付が内閣府 CSV の
「国民の祝日」の行と全年で一致することを HOL-C2 で検査する。

春分日・秋分日は毎年の官報（国立天文台の暦要項）で決まり、規則から計算できないので、CSV の「春分の日」
「秋分の日」の行を使う。検査では、その行が各年に 3 月と 9 月に 1 行ずつあることだけを確かめる。

現行の第2条（e-Gov 法令履歴 `323AC1000000178_20200101_430AC1000000057`）:

> 第二条　「国民の祝日」を次のように定める。
>
> | 元日 | 一月一日 |
> | 成人の日 | 一月の第二月曜日 |
> | 建国記念の日 | 政令で定める日 |
> | 天皇誕生日 | 二月二十三日 |
> | 春分の日 | 春分日 |
> | 昭和の日 | 四月二十九日 |
> | 憲法記念日 | 五月三日 |
> | みどりの日 | 五月四日 |
> | こどもの日 | 五月五日 |
> | 海の日 | 七月の第三月曜日 |
> | 山の日 | 八月十一日 |
> | 敬老の日 | 九月の第三月曜日 |
> | 秋分の日 | 秋分日 |
> | スポーツの日 | 十月の第二月曜日 |
> | 文化の日 | 十一月三日 |
> | 勤労感謝の日 | 十一月二十三日 |

改正の経過（各行の施行期間）は `rules` の各行に書く。建国記念の日の「政令で定める日」は、建国記念の日となる日を
定める政令（昭和四十一年政令第三百七十六号）により二月十一日。令和2年と令和3年の海の日・スポーツの日・山の日は、
令和三年東京オリンピック競技大会・東京パラリンピック競技大会特別措置法による。
-/

@[expose] public section

namespace Ritsuryo.Holiday

open Date

/-- 祝日の日付の決め方。 -/
inductive DayRule where
  /-- 毎年同じ月日 -/
  | fixed (month day : Nat)
  /-- `month` 月の第 `n` 月曜日 -/
  | nthMonday (month n : Nat)
  /-- 春分日・秋分日（CSV から取る） -/
  | equinox (month : Nat)
  deriving Repr, DecidableEq

/-- 第2条の 1 行と、その規則が使われた年の範囲（両端を含む）。 -/
structure Rule where
  name : String
  firstYear : Int
  lastYear : Int
  day : DayRule
  deriving Repr

/-- 第2条の規則を、改正ごとの施行期間で分けた表。CSV の範囲（1955 年以後）に必要な分だけ書く。
令和2年・令和3年の海の日・スポーツの日・山の日は `olympicOverrides` で置き換える。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def rules : List Rule := [
  ⟨"元日", 1949, 9999, .fixed 1 1⟩,
  -- 平成10年法律第141号で、平成12年から一月十五日を一月の第二月曜日に改めた。
  ⟨"成人の日", 1949, 1999, .fixed 1 15⟩,
  ⟨"成人の日", 2000, 9999, .nthMonday 1 2⟩,
  -- 昭和41年法律第86号で追加。日付は建国記念の日となる日を定める政令（昭和41年政令第376号）。
  ⟨"建国記念の日", 1967, 9999, .fixed 2 11⟩,
  -- 天皇誕生日は昭和の間は四月二十九日、平成元年法律第5号で十二月二十三日、
  -- 天皇の退位等に関する皇室典範特例法（平成29年法律第63号）の附則による改正で令和2年から二月二十三日。
  ⟨"天皇誕生日", 1949, 1988, .fixed 4 29⟩,
  ⟨"天皇誕生日", 1989, 2018, .fixed 12 23⟩,
  ⟨"天皇誕生日", 2020, 9999, .fixed 2 23⟩,
  ⟨"春分の日", 1949, 9999, .equinox 3⟩,
  -- 四月二十九日は平成元年からみどりの日、平成17年法律第43号で平成19年から昭和の日。
  -- みどりの日は平成19年から五月四日。
  ⟨"みどりの日", 1989, 2006, .fixed 4 29⟩,
  ⟨"昭和の日", 2007, 9999, .fixed 4 29⟩,
  ⟨"憲法記念日", 1949, 9999, .fixed 5 3⟩,
  ⟨"みどりの日", 2007, 9999, .fixed 5 4⟩,
  ⟨"こどもの日", 1949, 9999, .fixed 5 5⟩,
  -- 平成7年法律第22号で平成8年から七月二十日、平成13年法律第59号で平成15年から七月の第三月曜日。
  ⟨"海の日", 1996, 2002, .fixed 7 20⟩,
  ⟨"海の日", 2003, 9999, .nthMonday 7 3⟩,
  -- 平成26年法律第43号で平成28年から追加。
  ⟨"山の日", 2016, 9999, .fixed 8 11⟩,
  -- 昭和41年法律第86号で九月十五日、平成13年法律第59号で平成15年から九月の第三月曜日。
  ⟨"敬老の日", 1966, 2002, .fixed 9 15⟩,
  ⟨"敬老の日", 2003, 9999, .nthMonday 9 3⟩,
  ⟨"秋分の日", 1949, 9999, .equinox 9⟩,
  -- 体育の日は昭和41年法律第86号で十月十日、平成10年法律第141号で平成12年から十月の第二月曜日、
  -- 平成30年法律第57号で令和2年からスポーツの日。
  ⟨"体育の日", 1966, 1999, .fixed 10 10⟩,
  ⟨"体育の日", 2000, 2019, .nthMonday 10 2⟩,
  ⟨"スポーツの日", 2020, 9999, .nthMonday 10 2⟩,
  ⟨"文化の日", 1949, 9999, .fixed 11 3⟩,
  ⟨"勤労感謝の日", 1949, 9999, .fixed 11 23⟩]

/-- 令和三年東京オリンピック競技大会・東京パラリンピック競技大会特別措置法第32条による令和2年・令和3年の
海の日・スポーツの日・山の日。年ごとに `(名称, 月, 日)`。 -/
@[ritsuryo_basis "令和三年東京オリンピック競技大会・東京パラリンピック競技大会特別措置法" "第32条"]
def olympicOverrides : List (Int × List (String × Nat × Nat)) := [
  (2020, [("海の日", 7, 23), ("スポーツの日", 7, 24), ("山の日", 8, 10)]),
  (2021, [("海の日", 7, 22), ("スポーツの日", 7, 23), ("山の日", 8, 8)])]

/-- CSV から春分の日・秋分の日の行の日（`month` 月のもの）を取る。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def equinoxDays (y : Int) (month : Nat) : List Nat :=
  ((entriesOf y).filter fun e => e.kind == .national && e.month == month &&
    (e.name == "春分の日" || e.name == "秋分の日")).map (·.day)

/-- `y` 年の第2条の祝日の月日を、規則の表から生成する（春分日・秋分日は CSV の行）。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def article2Days (y : Int) : List (Nat × Nat) :=
  let overridden := (olympicOverrides.find? (·.1 == y)).map (·.2) |>.getD []
  let fromRules := (rules.filter fun r => r.firstYear ≤ y && y ≤ r.lastYear &&
      !(overridden.any (·.1 == r.name))).flatMap fun r =>
    match r.day with
    | .fixed m d => [(m, d)]
    | .nthMonday m n => [((nthMonday y m n).month, (nthMonday y m n).day)]
    | .equinox m => (equinoxDays y m).map (m, ·)
  fromRules ++ overridden.map fun (_, m, d) => (m, d)

/-- CSV の「国民の祝日」の行（特例法による休日と第3条の休日を除く）の月日。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def csvNationalDays (y : Int) : List (Nat × Nat) :=
  ((entriesOf y).filter (·.kind == .national)).map fun e => (e.month, e.day)

/-- `y` 年の検査。春分の日・秋分日の行が 3 月・9 月に 1 行ずつあり、規則から生成した月日と CSV の月日が
（順序を除いて）一致する。 -/
@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]
def checkArticle2Year (y : Int) : Bool :=
  let gen := article2Days y
  let csv := csvNationalDays y
  (equinoxDays y 3).length == 1 && (equinoxDays y 9).length == 1 &&
    gen.length == csv.length && gen.all csv.contains && csv.all gen.contains

end Ritsuryo.Holiday
