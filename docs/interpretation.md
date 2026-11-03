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

- The holidays the computations use come from the Cabinet Office CSV (`data/syukujitsu.csv`, generated into `Ritsuryo/Holiday/Data/Generated.lean` by `scripts/gen_holidays.py`), because 春分日・秋分日 are set each year by the official gazette and special laws move days. HOL-2 proves the n-th Monday rule used by 成人の日・海の日・敬老の日・スポーツの日.
- `Ritsuryo/Holiday/Article2.lean` writes 第2条 as rules with the years each was in force (the amendments of 1966, 1989, 1995, 1998, 2001, 2005, 2014, 2017, and 2018, and the 2020 and 2021 dates under 令和三年東京オリンピック競技大会・東京パラリンピック競技大会特別措置法 第32条). HOL-C2 checks, for every year in the CSV, that the rules generate exactly the CSV's 国民の祝日 rows, taking 春分の日 and 秋分の日 from the CSV and checking there is one of each per year.
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

## 期間のプリセット（民事訴訟法 第285条・第313条・第332条、所得税法 第120条）

- 控訴期間 (第285条) and 上告期間 (第313条, applying 第285条) are two weeks from the day the judgment is served; 即時抗告期間 (第332条) is one week from notice. The day of service or notice is not counted (第95条第1項 → 民法 第140条), and the last day rolls over under 第95条第3項. All three are 不変期間 (第96条第1項ただし書); the 付加期間 a court may add for distant parties (第96条第2項) is not included.
- The 所得税 final return is due on 15 March of the following year (the end of 第三期, 所得税法 第120条第1項), rolled over under 国税通則法 第10条第2項.

## 国税通則法 第118条・第119条（端数処理）

- 第118条第1項: the 課税標準 is floored to 1,000 yen (所得税 inputs: 課税総所得金額, 課税退職所得金額, 課税山林所得金額).
- 第118条第3項: the tax amount on which 附帯税 (延滞税, 利子税, 加算税) is computed is floored to 10,000 yen. For 過少申告加算税 第65条第2項 the part that gets the extra 5% is floored separately; for 無申告加算税 the 累積納付税額 is floored too.
- 第119条第1項: the final amount is floored to 100 yen. For 所得税 the CLI's `Payable` floors the sum of 所得税, 復興特別所得税, and 防衛特別所得税, before withholding and prepayments.
- 第119条第4項: 附帯税 are floored to 100 yen and dropped when below 1,000 yen (5,000 yen for 加算税).

## 所得税法 第89条

- The tax is the sum over the brackets of the table (`incomeTaxCentsSpec`); the NTA quick formula (税率 × 金額 − 控除額, `quickCents`) is the implementation. TAX-1 proves they agree on every amount, and the `@[csimp]` theorem `incomeTaxCentsSpec_eq_quickCents` makes the compiler run the quick formula wherever the library calls the bracket sum. The table applies from 平成27年分 (2015); earlier years exit with 254.
- 課税山林所得金額: one fifth of the amount is taxed by the table and the result multiplied by five (TAX-5). A 1,000-yen-floored amount is divisible by five, so the fifth has no fraction.
- 基準所得税額 is taken to be the 第89条 tax: tax credits (配当控除, 外国税額控除) and the 特定の基準所得金額の課税の特例 (租税特別措置法 第41条の19) are outside the library.
- 復興特別所得税 is 2.1% for 2013〜2026 (復興財源確保法 第9条・第13条) and 1.1% for 2027〜2047 (the same law as amended by 令和8年法律第12号, whose 附則第88条第1項 applies the new rate from 令和9年分). 防衛特別所得税 is 1% from 2027 (防衛財源確保法 第5条の5・第5条の9). Each is floored to 1 yen.

## 相続税法 第15条・第16条、民法 第900条

- The 相続人の数 counts heirs as if no one renounced, and counts at most one adopted child when there is a biological child and two otherwise (第15条第2項). Persons treated as biological children (特別養子, a spouse's child adopted by the deceased, 代襲相続人; 第15条第3項) go in `--biological-children`.
- 第16条 distributes the 課税遺産総額 among "the heirs according to the number in 第15条第2項", so the shares in `compute-total-tax` use the limited count. `compute-statutory-shares` gives the 民法 shares and counts every adopted child as a child (民法 第809条).
- Each heir's 取得金額 is floored to 1,000 yen and the 相続税の総額 to 100 yen (相続税法基本通達16-3; NTA タックスアンサー No.4152).
- 民法 第900条: spouse with children 1/2, with ascendants 2/3, with siblings 3/4; the rest is shared equally, a half-blood sibling getting half of a full-blood sibling's share (第4号). INH-1 proves the shares are positive and sum to 1. 代襲相続 (第901条), 欠格, and 廃除 are outside the library.

## 消費税法 第29条、地方税法 第72条の83、消費税法施行令 第70条の10

- The national rates are 7.8% and 6.24%; 地方消費税 is 22/78 of the national tax, so the combined rates are 10% and 8% (CON-1).
- For an 適格請求書 the tax is computed once per rate on the sum of the prices, tax-exclusive × 10/100 (8/100) or tax-inclusive × 10/110 (8/108), and the fraction is rounded by the issuer's choice of floor, ceiling, or half-up. CON-2 proves that rounding each item instead differs by at most n − 1 yen for n items.

## 延滞税・利子税（国税通則法 第60条第2項・第64条、租税特別措置法 第93条・第94条・第96条）

- The period runs from the day after the 法定納期限 to the day of full payment. "納期限の翌日から二月を経過する日" is computed as a two-month period whose first day is the day after the 納期限 (`Period.compute` with the 初日 not counted), and the lower rate applies up to and including that day.
- Rates by year: the 延滞税特例基準割合 (from 2021) and 特例基準割合 (2014〜2020) are recovered from the NTA's published rates (タックスアンサー No.9205) as the within-two-months rate minus 1%. Years outside 2014〜2026 must be given with `--special-base-rates`. DEL-1 proves the special rates never exceed 7.3% and 14.6%.
- 利子税: 利子税特例基準割合 is 平均貸付割合 + 0.5% (租税特別措置法 第93条第2項), i.e. the 延滞税特例基準割合 − 0.5%, from 2021; for 2020 and earlier it is the 特例基準割合 itself. The 相続税 延納 adjustment (第93条第3項) is outside the library.
- 措置法 第96条第2項 floors every amount in the course of the computation to 1 yen. The library splits the period wherever the rate changes (a new year with a different rate, or the end of the two months) and floors each part. 年利建て移行法 第25条 makes every year 365 days for the rate, leap years included. DEL-2 proves the unfloored amount equals the sum over days of tax × rate, which is additive over splitting the period.
- 一部納付 (第62条), the 計算期間の特例 (第61条), and 免除 (第63条) are outside the library.

## 加算税（国税通則法 第65条〜第68条）

- Whether a return or payment was made before the 調査通知, after it but before the 更正・決定・告知 was foreseen (予知), or after that is a finding of fact; it is the `--timing` input.
- 過少申告加算税: 10% (5% before 予知), plus 5% on the part of the tax (with prior increases) above the larger of the 期限内申告税額 and 500,000 yen (第65条第2項); none before the 調査通知 (第6項).
- 無申告加算税: 15% (10% before 予知), with the 50万円 and 300万円 tiers of 第66条第2項・第3項, computed as the tiers applied to the cumulative amount minus the tiers applied to the earlier amount. PEN-1 proves this equals the 第2項 wording up to 300万円. 5% flat before the 調査通知 (第8項). `--repeated` adds 10% for 第66条第6項.
- 不納付加算税: 10%, 5% when paid without foreseeing the 告知 (第67条第2項).
- 重加算税 replaces the above at 35% (過少申告, 不納付) or 40% (無申告), only after 予知 (第68条), plus 10% with `--repeated` (第68条第4項).
- The 帳簿 surcharges (第65条第4項, 第66条第5項), deductions for 正当な理由 (第65条第5項), and the exceptions of 第66条第9項 and 第67条第3項 are findings of fact outside the library; amounts excluded for those reasons should be left out of `--tax`.
