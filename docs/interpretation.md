# Reading of the statutes

This document records how each provision is read into a definition. The proofs show that the implementation agrees with these definitions; whether the definitions are the right reading of the statute is a judgment written down here, with the sources it relies on. Choices that a user may want to make differently are CLI inputs and are echoed in `Assumptions`.

Statute texts are quoted from e-Gov 法令検索. The revision IDs are in the module docstrings.

## 民法 第140条〜第143条

| Provision | Definition | Reading |
|---|---|---|
| 第140条 | `Period.Civil.startDateSpec` | The start date (起算日) is the day after the event unless the period starts at midnight. Whether it starts at midnight is a fact about the case and is the `--start-at-midnight` input. |
| 第141条 | `Period.Civil.expirySpec` | The period ends at the end of the last day; the library returns that last day. |
| 第143条第1項・第2項 | `Period.Civil.expiryFromStartSpec` | For weeks, months, and years the last day is the day before the day in the last week, month, or year that corresponds to the start date. If the last month has no such day, the last day is the end of that month. |

- Days: the last day of an n-day period is the n-th day counted with the start date as day 1. The definition writes it as the day before the start date plus n days, so the same "day before the corresponding day" shape covers all four units.
- Weeks: the corresponding day is the day with the start date's weekday, n weeks later (`weekCorrespondingSpec` walks to the next same-weekday day n times). PER-3 proves this is the 7n-day period.
- Months: the last month is the start month advanced n times by one month (`lastMonthSpec`). Years: the last month is the start month in the year n years later. PER-3 proves a year period equals the 12n-month period.
- Counting from the beginning of a week, month, or year (第143条第1項) needs no separate rule: PER-2 proves the 第2項 formula gives the calendar result (a period starting on the 1st ends at the end of the (n-1)-th following month, a period starting on 1 January ends on 31 December, a period starting on Sunday ends on Saturday).
- 第138条 (other statutes or juristic acts may provide otherwise) and 第139条 (periods by hours) are outside the library.

## 民法 第142条

> 期間の末日が日曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日その他の休日に当たるときは、その日に取引をしない慣習がある場合に限り、期間は、その翌日に満了する。

- Whether a custom of not trading exists is a fact. Without `--assume-no-trade-custom` the CLI does not roll over and says so in `Assumptions`.
- Which days are "その他の休日" depends on the custom. `--holiday-classes` selects them from `sunday`, `saturday`, `national-holiday`, `new-year` (1/2, 1/3), `year-end` (12/29〜12/31); the default is `sunday national-holiday`.

## 民事訴訟法 第95条

> 期間の末日が日曜日、土曜日、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する休日、一月二日、一月三日又は十二月二十九日から十二月三十一日までの日に当たるときは、期間は、その翌日に満了する。

第1項 applies the 民法 rules, so the period itself is computed with `--rule civil`. The set in 第3項 is closed and needs no input.

## 国税通則法 第10条

- 第1項 has the same three steps as 民法 140・143 条 for days, months, and years and does not define weeks; `--rule national-tax-general` rejects `--weeks`. PER-7 proves the two give the same last day. 第1項第1号 "国税に関する法律に別段の定めがあるとき" is outside the library.
- 第2項 and 施行令第2条第2項 make the next day the deadline when the deadline falls on Sunday, a holiday under 祝日法, "その他一般の休日", Saturday, or 12/29〜12/31. 国税通則法基本通達（徴収部関係）第10条関係4 reads 一般の休日 as follows, so the CLI counts 1/2 and 1/3 by default (`--no-new-year-general-holiday` turns this off):

  > 法第10条第2項の「一般の休日」とは、日曜日、国民の祝日に関する法律に規定する休日以外の全国的な休日をいうものとする。なお、行政機関の休日に関する法律第１条第１項第３号《行政機関の休日》に掲げる日のうち、１月２日及び３日は、法第10条第２項の「一般の休日」に該当する（昭和33.6.2最高判参照）。

  Source: https://www.nta.go.jp/law/tsutatsu/kihon/tsusoku/01/03/10.htm
- 施行令第2条第1項 lists deadlines that 第2項 does not move (deadlines set by a time, the day before a payment, and others). Whether a deadline is one of them is outside the library.
- ROL-3 proves that, with 1/2 and 1/3 counted as general holidays, the 国税通則法 set equals the 民事訴訟法 第95条第3項 set, and that the two agree on every other day regardless of that choice.

## Repeated rollover

The three provisions say the period ends on "the next day" (その翌日) and do not say what happens when the next day is also a holiday. The library moves to the first day that is not a holiday (under 民事訴訟法 第95条第3項 a last day of 12/29 moves to 1/4) and records this in `Assumptions`. ROL-1 proves the result is the least non-holiday on or after the original day.

## 年齢計算ニ関スル法律

> １　年齢ハ出生ノ日ヨリ之ヲ起算ス
> ２　民法第百四十三条ノ規定ハ年齢ノ計算ニ之ヲ準用ス

- The birth date is the start date (the first day is counted), and n years end on the day before the n-year corresponding day, or at the end of February when that day is 29 February in a common year (`Age.attainmentSpec`). AGE-1 proves that someone born on 29 February attains every age on 28 February.
- `age compute-age --as-of D` returns the age at the end of D: the largest n whose attainment date is on or before D. On the attainment date itself the person is counted as n years old. AGE-2 proves the result is exact between consecutive attainment dates.

## 国民の祝日に関する法律

- 第2条's dates are not derived: 春分日・秋分日 and the special laws (2019, 2020, 2021) move them. The holidays come from the Cabinet Office CSV (`data/syukujitsu.csv`, generated into `Ritsuryo/Holiday/Data/Generated.lean` by `scripts/gen_holidays.py`). HOL-2 proves the n-th Monday rule used by 成人の日・海の日・敬老の日・スポーツの日.
- Rows named "休日" are 第3条第2項 (振替休日) or 第3条第3項 (国民の休日). Every other row, including "休日（祝日扱い）" and the special-law days (結婚の儀, 大喪の礼, 即位礼正殿の儀), is treated as a 国民の祝日 for 第3条 and as a "国民の祝日に関する法律に規定する休日" for the rollover rules. For 2019 this follows 天皇の即位の日及び即位礼正殿の儀の行われる日を休日とする法律 附則第2条:

  > 本則の規定により休日となる日は、国民の祝日に関する法律（昭和二十三年法律第百七十八号）に規定する国民の祝日として、同法第三条第二項及び第三項の規定の適用があるものとする。
  > ２　本則及び前項の規定により休日となる日は、他の法令（国民の祝日に関する法律を除く。）の規定の適用については、同法に規定する休日とする。

  The special laws of 1959, 1989, 1990, and 1993 are not on e-Gov; they are treated the same way.
- 第3条第2項 and 第3項 changed over time. The derivation applies the version in force on each day:

  | Period | 第3条第2項 | 第3条第3項 |
  |---|---|---|
  | until 1973-04-11 | none | none |
  | 1973-04-12 (昭和48年法律第10号) to 2006-12-31 | the day after a 国民の祝日 that is a Sunday | none until 1985-12-26 |
  | 1985-12-27 (昭和60年法律第103号) to 2006-12-31 | as above | a day between two 国民の祝日, except a Sunday or a 振替休日 |
  | from 2007-01-01 (平成17年法律第43号) | the nearest day after a Sunday 国民の祝日 that is not a 国民の祝日 | a day between two 国民の祝日 that is not itself a 国民の祝日 |

  HOL-1 proves the current-version functions equal the wording of 第3条第2項・第3項. HOL-C1 is a check on the data: for every year in the CSV, applying the derivation to the non-"休日" rows yields exactly the "休日" rows. The derivation can only produce a day that follows a 国民の祝日, so the check evaluates those days (`isRestDayAt_pred`), which keeps it within a few seconds under `decide`.
- Dates outside the CSV (before 1955 or after its last year) end with exit code 254 whenever a rule needs the national-holiday set.
