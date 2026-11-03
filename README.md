# lean-ritsuryo

[日本語](README-ja.md)

lean-ritsuryo is a library and CLI that computes periods and taxes under Japanese law, written in Lean 4. The library's functions come with proofs that they compute what the provisions say, and the CLI calls those same functions. The Lake package and the CLI are both named `ritsuryo`.

It covers these provisions:

- Periods: 民法 第140条〜第143条, 年齢計算ニ関スル法律, 国税通則法 第10条, 民事訴訟法 第95条, 第285条, 第313条, 第332条, 所得税法 第120条
- Holidays: 国民の祝日に関する法律 第2条, 第3条
- 所得税: 所得税法 第89条, with 復興特別所得税 and 防衛特別所得税
- 相続税: 相続税法 第15条, 第16条, with the shares of 民法 第900条
- 消費税: 消費税法 第29条, 消費税法施行令 第70条の10
- 延滞税 and 利子税: 国税通則法 第60条, 租税特別措置法 第93条, 第94条
- 加算税: 国税通則法 第65条〜第68条
- Rounding: 国税通則法 第118条, 第119条

Each computation has 2 definitions. One is the spec, which copies the structure of the provision as it is and is used only in proofs. The other is the implementation used for the actual computation, which both programs using the library and the CLI call.

The theorems prove that the spec and the implementation return the same value on every input. They also prove other properties, such as monotonicity, that the rollover rules return the first day that isn't a holiday, and an upper bound on the difference rounding makes.

The comments in the source are in Japanese. The header of each file lists the provisions it implements, which definitions are the spec, and the theorem that proves the spec and the implementation agree.

`docs/basis.md` is a table from each provision to its spec, implementation, and theorems. `docs/interpretation.md` records how each provision was read when it was implemented.

## Install

Download the archive for your platform from the [releases](https://github.com/conao3/lean-ritsuryo/releases). There are 3: x86_64-linux, aarch64-linux, and aarch64-darwin. The `ritsuryo` binary inside runs as long as the C library is there.

```console
$ curl -sSfL https://github.com/conao3/lean-ritsuryo/releases/download/v0.5.0/ritsuryo-x86_64-linux.tar.gz | tar -xz
$ ./ritsuryo --version
ritsuryo 0.5.0
```

With Nix, `nix run github:conao3/lean-ritsuryo -- help` runs it.

## Examples

Every command prints a JSON object with `Result`, `Steps`, `Basis`, `Assumptions`, `Data`, and `SchemaVersion` (see [Output](#output)).

The examples below use `--query` to pick out only part of the output. The outputs are copied as the CLI printed them.

### 所得税

For 2026 年分 with 課税総所得金額 7,000,000 円, the 所得税 is 974,000 円. That's the same as the amount computed with the NTA quick table (7,000,000 × 23% − 636,000).

復興特別所得税 is 2.1% of the 所得税, rounded down to the yen. `Payable` is the sum of the two, rounded down to 100 yen.

```console
$ ritsuryo income-tax compute-tax --tax-year 2026 --taxable-income 7000000
{
    "Result": {
        "IncomeTax": 974000,
        "ReconstructionTax": 20454,
        "DefenseTax": 0,
        "Total": 994454,
        "Payable": 994400
    },
    "Steps": {
        "TaxYear": 2026,
        "TaxableIncome": {
            "Input": 7000000,
            "Base": 7000000,
            "Tax": 974000
        },
        "TaxableRetirementIncome": {
            "Input": 0,
            "Base": 0,
            "Tax": 0
        },
        "TaxableTimberIncome": {
            "Input": 0,
            "Base": 0,
            "Tax": 0
        },
        "ReconstructionRate": "2.1%",
        "DefenseRate": "0.0%"
    },
    "Basis": [
        {
            "Law": "所得税法",
            "Article": "第89条第1項",
            "LawId": "340AC0000000033"
        },
        {
            "Law": "国税通則法",
            "Article": "第118条第1項",
            "LawId": "337AC0000000066"
        },
        {
            "Law": "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法",
            "Article": "第9条第1項",
            "LawId": "423AC0000000117"
        },
        {
            "Law": "東日本大震災からの復興のための施策を実施するために必要な財源の確保に関する特別措置法",
            "Article": "第13条",
            "LawId": "423AC0000000117"
        },
        {
            "Law": "国税通則法",
            "Article": "第119条第1項",
            "LawId": "337AC0000000066"
        }
    ],
    "Assumptions": [
        "入力は所得控除の後の課税総所得金額・課税退職所得金額・課税山林所得金額で、千円未満を切り捨てて税率表を当てる",
        "課税山林所得金額は、五分の一の金額に税率表を当てて五を掛ける（5 分 5 乗）",
        "基準所得税額は第89条の税額とし、税額控除（配当控除・外国税額控除など）はないものとする",
        "復興特別所得税・防衛特別所得税は一円未満を切り捨てる",
        "Payable は所得税と特別所得税の合計の百円未満を切り捨てた額で、源泉徴収税額・予定納税額を引く前の額"
    ],
    "Data": {},
    "SchemaVersion": "1"
}
```

From 2027 年分, the 復興特別所得税 is 1.1% and the 防衛特別所得税 is 1%.

```console
$ ritsuryo income-tax compute-tax --tax-year 2027 --taxable-income 7000000 --query Result
{
    "IncomeTax": 974000,
    "ReconstructionTax": 10714,
    "DefenseTax": 9740,
    "Total": 994454,
    "Payable": 994400
}
```

Passing a year the computation doesn't cover ends the CLI with exit code 254.

```console
$ ritsuryo income-tax compute-tax --tax-year 2014 --taxable-income 7000000
ritsuryo: error: 2014 年分は扱えない。所得税法第89条の現行の税率表は平成27年分（2015 年分）以後に適用される
$ echo $?
254
```

### 相続税

An example where 課税価格の合計 is 2 億円 and the heirs are a spouse and two children. The 基礎控除 is 3,000 万円 + 600 万円 × 3 heirs = 4,800 万円.

課税価格の合計 minus the 基礎控除, 1 億 5,200 万円, is split by the 法定相続分, and the 16 条 rates are applied to each heir's amount. Adding up those taxes gives the 相続税の総額.

```console
$ ritsuryo inheritance-tax compute-total-tax --taxable-value-total 200000000 --spouse --biological-children 2 --query '{Result: Result, Steps: Steps}'
{
    "Result": {
        "TotalTax": 27000000
    },
    "Steps": {
        "TaxableValueTotal": 200000000,
        "HeirCount": 3,
        "BasicDeduction": 48000000,
        "TaxableEstate": 152000000,
        "Heirs": [
            {
                "Heir": "spouse",
                "Share": "1/2",
                "Acquired": 76000000,
                "Tax": 15800000
            },
            {
                "Heir": "child",
                "Share": "1/4",
                "Acquired": 38000000,
                "Tax": 5600000
            },
            {
                "Heir": "child",
                "Share": "1/4",
                "Acquired": 38000000,
                "Tax": 5600000
            }
        ],
        "TotalBeforeRounding": 27000000
    }
}
```

Next, the 法定相続分 when the heirs are a spouse, two full-blood siblings, and one half-blood sibling (民法 第900条第3号, 第4号).

```console
$ ritsuryo inheritance-tax compute-statutory-shares --spouse --full-siblings 2 --half-siblings 1 --query 'Result.Shares[].[Heir, Share]' --output text
spouse	3/4
full-sibling	1/10
full-sibling	1/10
half-sibling	1/20
```

### 消費税

This computes the tax to print on an 適格請求書, per rate. Pass the items to `--items` in the shorthand syntax. Add `--price-basis inclusive` when passing tax-inclusive prices.

```console
$ ritsuryo consumption-tax compute-invoice-tax --items Price=1000,Rate=standard Price=540,Rate=reduced --rounding half-up --query Result
{
    "Taxes": [
        {
            "Rate": "standard",
            "RatePercent": 10,
            "PriceTotal": 1000,
            "Tax": 100
        },
        {
            "Rate": "reduced",
            "RatePercent": 8,
            "PriceTotal": 540,
            "Tax": 43
        }
    ],
    "TotalTax": 143
}
```

### 延滞税, 利子税, and 加算税

The 延滞税 on a tax of 1,000,000 円 with 法定納期限 2026-03-16 and payment on 2026-07-31. The 延滞税 rate goes up once 2 months have passed from the day after the 納期限, so the CLI splits the period on that day.

Each segment's amount is rounded down to the yen, and their sum is rounded down to 100 yen.

```console
$ ritsuryo delinquency-tax compute-tax --tax 1000000 --legal-due-date 2026-03-16 --payment-date 2026-07-31 --query Result
{
    "DelinquencyTax": 23600
}
$ ritsuryo delinquency-tax compute-tax --tax 1000000 --legal-due-date 2026-03-16 --payment-date 2026-07-31 --output table --query Steps.Segments
+----------------------------------------------------------------------+
|                              ComputeTax                              |
+----------------------------------------------------------------------+
|  From       | To         | Days | Rate | Band              | Amount  |
|+--------------------------------------------------------------------+|
|  2026-03-17 | 2026-05-16 | 61   | 2.8% | within-two-months | 4679    |
|  2026-05-17 | 2026-07-31 | 76   | 9.1% | after-two-months  | 18947   |
+----------------------------------------------------------------------+
```

Next, the 利子税 when the 納期限 is extended from 2026-03-16 to 2026-06-15.

```console
$ ritsuryo interest-tax compute-tax --tax 1000000 --from-date 2026-03-16 --to-date 2026-06-15 --query Result
{
    "InterestTax": 3200
}
```

The 無申告加算税 on a tax of 4,000,000 円. `--timing` is left at its default, `after-prediction` (a return filed after the 決定 was foreseen, or the 決定 itself).

The rate is 15% on the part of the tax up to 50 万円, 20% on the part up to 300 万円, and 30% on the part above 300 万円 (国税通則法 第66条第1項, 第3項).

```console
$ ritsuryo penalty-tax compute-tax --kind no-return --tax 4000000 --query Result
{
    "PenaltyTax": 875000
}
```

### Periods and deadlines

The 控訴期間 when a judgment is served on 2026-12-15. The last day of the 2 weeks is 2026-12-29, but that day falls in the 年末年始. 民事訴訟法 第95条第3項 therefore moves the last day to 2027-01-04.

```console
$ ritsuryo deadline compute-appeal-deadline --served-date 2026-12-15 --query '{Result: Result, RolledOver: Steps.RolledOverDays[].Date}'
{
    "Result": {
        "Deadline": "2027-01-04",
        "Period": "控訴期間",
        "Invariable": true
    },
    "RolledOver": [
        "2026-12-29",
        "2026-12-30",
        "2026-12-31",
        "2027-01-01",
        "2027-01-02",
        "2027-01-03"
    ]
}
```

A period of 1 month from 2026-01-31 ends on 2026-02-28. The 応当日 would be 2026-02-31, which doesn't exist, so the period ends on the last day of that month (民法 第143条第2項ただし書).

```console
$ ritsuryo period compute-expiry --event-date 2026-01-31 --months 1 --query Result
{
    "ExpiryDate": "2026-02-28"
}
```

The 所得税 確定申告期限 for 2026 年分 is as follows (所得税法 第120条第1項).

```console
$ ritsuryo deadline get-income-tax-return-deadline --tax-year 2026 --query Result
{
    "Deadline": "2027-03-15"
}
```

A person born on 29 February attains 18 on 28 February (年齢計算ニ関スル法律, 民法 第143条).

```console
$ ritsuryo age get-attainment-date --birth-date 2008-02-29 --age 18 --query Result
{
    "AttainmentDate": "2026-02-28"
}
```

### Holidays

This lists the holidays of 2027 with their class and the provision behind each.

```console
$ ritsuryo holiday list-holidays --year 2027 --output text --query Result.Holidays
2027-01-01	元日	national-holiday	国民の祝日に関する法律 第2条
2027-01-11	成人の日	national-holiday	国民の祝日に関する法律 第2条
2027-02-11	建国記念の日	national-holiday	国民の祝日に関する法律 第2条
2027-02-23	天皇誕生日	national-holiday	国民の祝日に関する法律 第2条
2027-03-21	春分の日	national-holiday	国民の祝日に関する法律 第2条
2027-03-22	休日	substitute-holiday	国民の祝日に関する法律 第3条第2項
2027-04-29	昭和の日	national-holiday	国民の祝日に関する法律 第2条
2027-05-03	憲法記念日	national-holiday	国民の祝日に関する法律 第2条
2027-05-04	みどりの日	national-holiday	国民の祝日に関する法律 第2条
2027-05-05	こどもの日	national-holiday	国民の祝日に関する法律 第2条
2027-07-19	海の日	national-holiday	国民の祝日に関する法律 第2条
2027-08-11	山の日	national-holiday	国民の祝日に関する法律 第2条
2027-09-20	敬老の日	national-holiday	国民の祝日に関する法律 第2条
2027-09-23	秋分の日	national-holiday	国民の祝日に関する法律 第2条
2027-10-11	スポーツの日	national-holiday	国民の祝日に関する法律 第2条
2027-11-03	文化の日	national-holiday	国民の祝日に関する法律 第2条
2027-11-23	勤労感謝の日	national-holiday	国民の祝日に関する法律 第2条
```

### Input from a file

With `--generate-cli-skeleton input`, the CLI prints a JSON template listing every parameter. With `--cli-input-json`, you can pass the parameters as JSON. Parameters left out of the JSON take their defaults.

```console
$ cat input.json
{"EventDate": "2026-12-15", "Weeks": 2, "RolloverRule": "civil-procedure-95"}
$ ritsuryo period compute-expiry --cli-input-json file://input.json --query Result
{
    "ExpiryDate": "2027-01-04"
}
```

## Development

```console
$ nix develop                # Lean 4.35.0 (lake), make, python3, hyperfine
$ make check                 # format, lint, holiday data check, lake build (proofs), tests, basis report and axiom audit
$ make basis                 # regenerate docs/basis.md from the @[ritsuryo_basis] attributes
$ make holidays              # regenerate Ritsuryo/Holiday/Data/Generated.lean from data/syukujitsu.csv
$ make fetch-holidays        # download the Cabinet Office CSV, then regenerate
$ nix build                  # build the CLI into ./result/bin/ritsuryo
$ nix run . -- help
```

Running `lake build` after deleting the build output checks every proof in about 26 s.

## CLI

The CLI arguments are written in the same grammar as the AWS CLI.

```console
$ ritsuryo [global options] <command> <subcommand> [--parameter value ...]
```

- Parameters are `--kebab-case`. Booleans are `--flag` / `--no-flag`, and lists are space-separated.
- A value starting with `file://` is read from that file.
- Structure lists take the shorthand syntax (`--items Price=1000,Rate=standard Price=540,Rate=reduced`) or JSON.
- `--cli-input-json` takes every parameter as one JSON object, keyed by the PascalCase parameter names.
- `--generate-cli-skeleton input|output` prints the input or output template.
- `--query` picks out part of the output with a JMESPath expression.
- `help` works at every level: `ritsuryo help`, `ritsuryo period help`, `ritsuryo period compute-expiry help`.

The JMESPath syntax `--query` accepts is identifiers, sub-expressions, indexes, slices, list and object projections, flatten, filters, multi-select lists and hashes, pipes, comparisons, `||` `&&` `!`, and literals. The functions it accepts are `length` `keys` `values` `sort` `reverse` `max` `min` `sum` `join` `contains` `starts_with` `ends_with` `type` `to_string` `not_null`.

| command | subcommand | Computes |
|---|---|---|
| `period` | `compute-expiry` | The last day of a period in days, weeks, months, or years (`--rule civil` for 民法 140〜143 条, `--rule national-tax-general` for 国税通則法 10 条 1 項), optionally rolled over with `--rollover-rule` |
| `period` | `compute-rollover` | Rollover of a date under `civil-142`, `civil-procedure-95`, or `national-tax-10` |
| `age` | `get-attainment-date` | The day a person attains an age |
| `age` | `compute-age` | The age at the end of a day |
| `holiday` | `list-holidays` | The year's holidays with their class (祝日法 2 条, 3 条 2 項, 3 条 3 項, special laws) |
| `holiday` | `check-holiday` | Which holiday classes and rollover rules apply to a date |
| `deadline` | `compute-appeal-deadline` | 控訴期間 (民事訴訟法 285 条): two weeks from service, rolled over under 95 条 3 項 |
| `deadline` | `compute-final-appeal-deadline` | 上告期間 (313 条, 285 条) |
| `deadline` | `compute-immediate-appeal-deadline` | 即時抗告期間 (332 条): one week from notice |
| `deadline` | `get-income-tax-return-deadline` | The 所得税 final return deadline (所得税法 120 条 1 項, 国税通則法 10 条 2 項) |
| `income-tax` | `compute-tax` | 所得税 on 課税総所得金額, 課税退職所得金額, and 課税山林所得金額 (5 分 5 乗), with 復興特別所得税 and 防衛特別所得税 by tax year (2015 年分 and later) |
| `inheritance-tax` | `compute-total-tax` | 相続税の総額 from the total 課税価格 and the heirs (基礎控除, 法定相続分, 16 条 table) |
| `inheritance-tax` | `compute-statutory-shares` | 法定相続分 under 民法 900 条 |
| `consumption-tax` | `compute-invoice-tax` | The tax per rate on an 適格請求書, tax-exclusive or tax-inclusive, rounded down, up, or half up |
| `delinquency-tax` | `compute-tax` | 延滞税 from the 法定納期限, 納期限, and payment day, split where the rate changes |
| `interest-tax` | `compute-tax` | 利子税 over a period |
| `penalty-tax` | `compute-tax` | 過少申告加算税, 無申告加算税, 不納付加算税, and 重加算税 by the timing of the return or payment |

### Output

The CLI prints a JSON object whose keys are PascalCase.

- `Result`: the result of the computation.
- `Steps`: the intermediate values, such as the start date, corresponding day, last day before rollover, skipped days, and tax per bracket.
- `Basis`: the statute, provision, and e-Gov law ID behind the result.
- `Assumptions`: the readings and inputs the result depends on.
- `Data`: the holiday CSV's source, Last-Modified, SHA-256, and year range when holidays were used, and `{}` otherwise.
- `SchemaVersion`.

`--output` picks the output format from `json` (default), `text`, and `table`. `text` is tab-separated like the AWS CLI, and top-level scalars such as `SchemaVersion` are printed last as `KEY<TAB>value` lines.

### Exit codes

| Code | Meaning |
|---|---|
| 0 | Success |
| 252 | Command or parameter error, including a combination the statute doesn't cover (重加算税 before the 調査通知) |
| 254 | Input outside what the computation covers: a nonexistent date, a year outside the holiday data, an as-of date before the birth date, a tax year before 2015, a year without a 特例基準割合 |
| 255 | Any other failure |

## Proved properties

Lean checks every theorem during `lake build`. No theorem's proof uses `sorry`, `admit`, or `native_decide`.

`lake exe basis-report --check` fails if a public theorem depends on an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, or if a design ID below has no theorem.

| ID | Theorem | Statement |
|---|---|---|
| CAL-1 | `Date.cal1_ofDays_toDays` | date → day number → date is the identity on valid proleptic Gregorian dates (`Int` years) |
| CAL-2 | `Date.cal2_toDays_ofDays` | day number → date → day number is the identity on all `Int`, and the date is valid |
| CAL-3 | `Date.cal3_lt_iff` | lexicographic date order equals day-number order |
| CAL-4 | `Date.cal4_nextDate` | the naive next day (month end, year end, leap years by cases) is day number + 1 |
| CAL-5 | `Date.cal5_weekday` | the weekday is the day number mod 7, and the next day has the next weekday |
| CAL-6 | `Date.cal6_daysInMonth` | month lengths match the day numbers, and February has 29 days exactly when 閏年ニ関スル件 (in 皇紀) makes the year a leap year |
| PER-1 | `Period.per1_compute_eq_spec` | the implementation's start date, corresponding day, and last day equal the 民法 140・143 条 spec |
| PER-2 | `Period.per2_from_beginning` | the 143 条 2 項 formula gives the calendar result for periods starting on the 1st, on 1 January, and on Sunday |
| PER-3 | `Period.per3_weeks_years` | n weeks equals 7n days; n years equals 12n months |
| PER-4 | `Period.per4_not_additive`, `Period.per4_bound` | 1 month + 1 month from 2025-01-31 ends on 03-31 but 2 months ends on 03-30; chaining is always 0〜3 days later |
| PER-5 | `Period.per5_monotone` | the last day is monotone in the event date and in the length |
| PER-6 | `Period.per6_months_from_event` | n months after an event end at the end of the month if the event is a month end, else on the event's day n months later (or that month's end) |
| PER-7 | `Period.per7_national_tax_general` | 国税通則法 10 条 1 項 gives the same last day as 民法 for days, months, and years |
| AGE-1 | `Period.Age.age1_attainment` | the attainment day is the day before the corresponding day; 29 February births attain on 28 February |
| AGE-2 | `Period.Age.age2_monotone_and_steps` | the age is exact between attainment days, monotone in the date, and steps by exactly 1 at each attainment day |
| ROL-1 | `Period.rol1_least_non_holiday` | the rollover result is on or after the date, not a holiday, and every day in between is a holiday |
| ROL-2 | `Period.rol2_idempotent_monotone` | rollover is idempotent, monotone in the date, and monotone in the holiday set |
| ROL-3 | `Period.rol3_procedure_vs_tax` | 国税通則法 10 条 2 項 with 1/2・1/3 as general holidays equals 民事訴訟法 95 条 3 項, and they agree on every other day either way |
| HOL-1 | `Holiday.hol1_derivation` | the 振替休日 and 国民の休日 functions equal the wording of 祝日法 3 条 2 項・3 項 |
| HOL-2 | `Holiday.hol2_nthMonday` | `nthMonday` returns a Monday whose day is in the n-th 7-day block of the month |
| HOL-C1 (check) | `Holiday.holc1_csv_rest_days` | for every year in the CSV, deriving 3 条 2 項・3 項 (in the version in force on each day) from the non-"休日" rows yields exactly the "休日" rows; decided by the kernel |
| HOL-C2 (check) | `Holiday.holc2_csv_article2` | for every year in the CSV, the 2 条 rules with their periods in force (and the 2020・2021 Olympic dates) generate exactly the CSV's 国民の祝日 rows, with one 春分の日 and one 秋分の日 taken from the CSV; decided by the kernel |
| TAX-1 | `Tax.Income.tax1_quick_eq_spec` | the NTA quick formula for 所得税 equals the 89 条 sum over brackets for every amount, and the implementation's tax equals the bracket sum on the 1,000-yen-floored amount |
| TAX-2 | `Tax.Inheritance.tax2_quick_eq_spec` | the same for the 相続税法 16 条 table |
| TAX-3 | `Tax.Income.tax3_monotone` | the tax, the base minus the tax, and the base minus the 100-yen-floored tax are monotone in the income |
| TAX-4 | `Tax.Income.tax4_marginal_rate` | the bracket sum grows by 5% to 45% of the increase; the implementation's tax within 999 yen of slack |
| TAX-5 | `Tax.Income.tax5_timber` | the implementation's 山林所得 tax equals five times the bracket sum on one fifth of the amount, which has no fraction |
| RND-1 | `Tax.rnd1_floorTo` | flooring to k yen is at most the amount, less than k below it, a multiple of k, idempotent, and monotone |
| RND-2 | `Tax.rnd2_incidentalFinal` | the 附帯税 rounding (dropped below 1,000 or 5,000 yen) is monotone, at most the amount, and 0 or at least the minimum |
| CON-1 | `Tax.Consumption.con1_combined_rate` | 7.8% and 6.24% plus 22/78 of themselves are 10% and 8% |
| CON-2 | `Tax.Consumption.con2_per_rate_rounding` | rounding each of n items and rounding the total differ by at most n − 1 yen, for every rounding mode and price basis |
| DEL-1 | `Tax.Delinquency.del1_special_rates_le` | the special 延滞税 rates never exceed 7.3% and 14.6%, and the 利子税 rate never exceeds 7.3% |
| DEL-2 | `Tax.Delinquency.del2_additive_monotone` | the unfloored amount (the sum over days of tax × rate) is additive over splitting the period, monotone in the tax and the length, and equals the sum over the implementation's segments |
| PEN-1 | `Tax.Penalty.pen1_no_return_tiers` | the 無申告加算税 tiers of 66 条 3 項 equal the 2 項 wording up to 300万円 and are monotone in the tax |
| INH-1 | `Tax.Inheritance.inh1_statutory_shares` | the 民法 900 条 shares are positive and sum to 1, and a half-blood sibling gets half of a full-blood sibling |

## Holiday data

`data/syukujitsu.csv` is the CSV the Cabinet Office publishes (https://www8.cao.go.jp/chosei/shukujitsu/syukujitsu.csv, Shift_JIS, Last-Modified 2026-02-02T00:30:17Z). It has 1,067 rows from 1955-01-01 to 2027-11-23. Of these, 116 are "休日", 2 are "休日（祝日扱い）", and 4 are days a special law made holidays (結婚の儀 ×2, 大喪の礼, 即位礼正殿の儀).

`scripts/gen_holidays.py` turns this CSV into per-year tables and writes them to `Ritsuryo/Holiday/Data/Generated.lean`. The build therefore needs no network access.

The `Holiday data` workflow downloads the CSV again every month and runs `make check` on it. If the CSV changed, the workflow opens a pull request.

## Speed and binary size

The released `ritsuryo` is one 3.4 MB executable (x86_64-linux). The Lean runtime, GMP, and libuv are inside this file, and the only other thing it needs is the C library.

A run finishes in about 6 ms and uses at most about 10 MiB of memory. For example, calling `income-tax compute-tax` 10,000 times in a row finishes in about 64 s.

| Command | Time |
|---|---|
| `--version` | 4.5 ms ± 1.3 ms |
| `income-tax compute-tax` | 6.4 ms ± 1.2 ms |
| `deadline compute-appeal-deadline` (rolls over 6 days) | 6.2 ms ± 1.5 ms |
| `delinquency-tax compute-tax` (290 days) | 5.9 ms ± 1.3 ms |
| `holiday list-holidays --output table` | 6.3 ms ± 1.2 ms |

These were measured by running the v0.5.0 x86_64-linux release under `hyperfine -N --warmup 20 --runs 300` on NixOS (14 hardware threads). Peak memory, measured with `time -f %M`, is 8.4〜10.5 MiB.

The measurements used to decide how to build (binary size by import style, the difference between toolchains, the time the holiday check takes, and build time) are in `docs/measurements.md`.

## How releases are built

The `Release` workflow makes the GitHub releases. The workflow builds the CLI with the upstream toolchain on GitHub-hosted runners (x86_64-linux, aarch64-linux, aarch64-darwin) and runs the library and CLI tests. When a `v*` tag is pushed, it attaches the built archives to a release.

## Layout

```
Ritsuryo/
  Law.lean, Basis.lean, Audit.lean   statutes and e-Gov IDs, @[ritsuryo_basis], report and audit
  Calendar/                          Date, day numbers, weekday, CAL proofs
  Period/
    Spec/                            民法 138〜143 条, 142 条, 民事訴訟法 95 条, 国税通則法 10 条
    HolidayClass.lean, Impl.lean, Age.lean, Rollover.lean
    Presets.lean                     控訴, 上告, 即時抗告, the 所得税 return deadline
    Proofs/                          PER, AGE, ROL proofs
  Holiday/
    Spec.lean, Proofs.lean           祝日法 2 条・3 条, HOL proofs
    Data.lean, Data/Generated.lean   CSV tables
    Lookup.lean, Check.lean          lookup, era-aware derivation, HOL-C1
    Article2.lean, Article2Check.lean  2 条 rules by period in force, HOL-C2
  Tax/
    Rounding.lean, Progressive.lean  国税通則法 118・119 条, bracket tables
    Income.lean, Inheritance.lean    所得税法 89 条, 相続税法 15・16 条 and 民法 900 条
    Consumption.lean                 消費税法 29 条, 施行令 70 条の 10
    Delinquency.lean, Penalty.lean   延滞税・利子税, 加算税
    Proofs/                          TAX, RND, CON, DEL, PEN, INH proofs
  Cli/                               JSON, argument parsing, --query, rendering, command tables
Main.lean                            the ritsuryo CLI
BasisReport.lean                     lake exe basis-report
Tests/, TestMain.lean                lake test
scripts/                             CSV generator, lint, CLI tests
data/                                the Cabinet Office CSV
docs/                                basis.md (generated), interpretation.md, measurements.md
```

## License

Apache-2.0
