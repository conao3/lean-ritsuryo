# lean-ritsuryo

[English](README.md)

lean-ritsuryo は日本の法令が定める期間と税額の計算を Lean 4 で実装したライブラリと CLI である。ライブラリの関数には条文どおりに計算することの証明を付けていて、CLI はこの関数をそのまま呼ぶ。Lake のパッケージ名と CLI の名前はどちらも `ritsuryo` である。

扱う条文は次のとおりである。

- 期間：民法 第140条〜第143条、年齢計算ニ関スル法律、国税通則法 第10条、民事訴訟法 第95条、第285条、第313条、第332条、所得税法 第120条
- 祝日：国民の祝日に関する法律 第2条、第3条
- 所得税：所得税法 第89条と、復興特別所得税、防衛特別所得税
- 相続税：相続税法 第15条、第16条と、民法 第900条の法定相続分
- 消費税：消費税法 第29条、消費税法施行令 第70条の10
- 延滞税と利子税：国税通則法 第60条、租税特別措置法 第93条、第94条
- 加算税：国税通則法 第65条〜第68条
- 端数計算：国税通則法 第118条、第119条

計算ごとに定義を 2 つ書いている。1 つは条文の構造をそのまま写した仕様で、証明にだけ使う。もう 1 つは実際の計算に使う実装で、ライブラリを使うプログラムも CLI もこれを呼ぶ。

定理は仕様と実装がすべての入力で同じ値を返すことを示す。ほかに、単調性、繰り下げの規定が休日でない最初の日を返すこと、端数処理で生じる差の上限なども示す。

ソースのコメントは日本語で書いている。各ファイルの冒頭にはそのファイルが実装する条文、仕様にあたる定義、仕様と実装が一致することを示す定理を書いている。

`docs/basis.md` には条文ごとに仕様、実装、定理を対応づけた表がある。`docs/interpretation.md` には各条文をどう読んで実装したかを書いている。

## インストール

[リリース](https://github.com/conao3/lean-ritsuryo/releases)から、使う環境に合うアーカイブをダウンロードする。アーカイブは x86_64-linux、aarch64-linux、aarch64-darwin の 3 種類がある。中の `ritsuryo` は C ライブラリがあれば動く。

```console
$ curl -sSfL https://github.com/conao3/lean-ritsuryo/releases/download/v0.5.0/ritsuryo-x86_64-linux.tar.gz | tar -xz
$ ./ritsuryo --version
ritsuryo 0.5.0
```

Nix を使う場合は `nix run github:conao3/lean-ritsuryo -- help` で実行できる。

## 使用例

どのコマンドも `Result`、`Steps`、`Basis`、`Assumptions`、`Data`、`SchemaVersion` を持つ JSON を出す（[出力](#出力)を参照）。

以下の例では `--query` で出力の一部だけを取り出している。出力は CLI が出したものをそのまま写している。

### 所得税

2026 年分で課税総所得金額が 7,000,000 円のとき、所得税は 974,000 円になる。これは国税庁の速算表で求めた額（7,000,000 × 23% − 636,000）と同じである。

復興特別所得税は所得税の 2.1% で、一円未満を切り捨てる。`Payable` は所得税と復興特別所得税の合計から百円未満を切り捨てた額である。

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

2027 年分からは、復興特別所得税が 1.1%、防衛特別所得税が 1% になる。

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

計算が扱わない年を渡すと、終了コード 254 で終了する。

```console
$ ritsuryo income-tax compute-tax --tax-year 2014 --taxable-income 7000000
ritsuryo: error: 2014 年分は扱えない。所得税法第89条の現行の税率表は平成27年分（2015 年分）以後に適用される
$ echo $?
254
```

### 相続税

課税価格の合計が 2 億円で、相続人が配偶者と子 2 人の例である。基礎控除は 3,000 万円 + 600 万円 × 3 人 = 4,800 万円になる。

課税価格の合計から基礎控除を引いた 1 億 5,200 万円を法定相続分で分け、各人の取得金額に第16条の税率をかける。これらの税額を足した額が相続税の総額になる。

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

次は相続人が配偶者、全血の兄弟姉妹 2 人、半血の兄弟姉妹 1 人のときの法定相続分である（民法 第900条第3号、第4号）。

```console
$ ritsuryo inheritance-tax compute-statutory-shares --spouse --full-siblings 2 --half-siblings 1 --query 'Result.Shares[].[Heir, Share]' --output text
spouse	3/4
full-sibling	1/10
full-sibling	1/10
half-sibling	1/20
```

### 消費税

適格請求書に記載する消費税額を、税率ごとに求める。品目は `--items` に shorthand 構文で渡す。税込価額で渡すときは `--price-basis inclusive` を付ける。

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

### 延滞税、利子税、加算税

税額 1,000,000 円、法定納期限 2026-03-16、納付日 2026-07-31 のときの延滞税である。延滞税の割合は納期限の翌日から 2 か月を過ぎると上がるので、CLI はその日で期間を分けて計算する。

区間ごとの額は一円未満を切り捨て、その合計から百円未満を切り捨てる。

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

次は納期限を 2026-03-16 から 2026-06-15 まで延長したときの利子税である。

```console
$ ritsuryo interest-tax compute-tax --tax 1000000 --from-date 2026-03-16 --to-date 2026-06-15 --query Result
{
    "InterestTax": 3200
}
```

税額 4,000,000 円のときの無申告加算税である。`--timing` は既定値の `after-prediction`（決定を予知した後の申告、または決定）のままにしている。

割合は税額のうち 50 万円までの部分が 15%、300 万円までの部分が 20%、300 万円を超える部分が 30% である（国税通則法 第66条第1項、第3項）。

```console
$ ritsuryo penalty-tax compute-tax --kind no-return --tax 4000000 --query Result
{
    "PenaltyTax": 875000
}
```

### 期間と期限

2026-12-15 に判決の送達を受けたときの控訴期間である。2 週間の末日は 2026-12-29 だが、この日は年末年始に当たる。そのため、民事訴訟法 第95条第3項により、末日は 2027-01-04 に繰り下がる。

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

2026-01-31 から 1 か月の期間は 2026-02-28 に満了する。応当日にあたる 2026-02-31 は存在しないので、その月の末日に満了する（民法 第143条第2項ただし書）。

```console
$ ritsuryo period compute-expiry --event-date 2026-01-31 --months 1 --query Result
{
    "ExpiryDate": "2026-02-28"
}
```

2026 年分の所得税の確定申告期限は、次のとおりである（所得税法 第120条第1項）。

```console
$ ritsuryo deadline get-income-tax-return-deadline --tax-year 2026 --query Result
{
    "Deadline": "2027-03-15"
}
```

2 月 29 日に生まれた人は、2 月 28 日に 18 歳に達する（年齢計算ニ関スル法律、民法 第143条）。

```console
$ ritsuryo age get-attainment-date --birth-date 2008-02-29 --age 18 --query Result
{
    "AttainmentDate": "2026-02-28"
}
```

### 祝日

2027 年の休日を、種別と根拠の条文とともに一覧にする。

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

### ファイルからの入力

`--generate-cli-skeleton input` を付けると、すべてのパラメータを並べた JSON の雛形を出力する。`--cli-input-json` を使うとパラメータを JSON で渡せる。JSON に書かなかったパラメータは既定値になる。

```console
$ cat input.json
{"EventDate": "2026-12-15", "Weeks": 2, "RolloverRule": "civil-procedure-95"}
$ ritsuryo period compute-expiry --cli-input-json file://input.json --query Result
{
    "ExpiryDate": "2027-01-04"
}
```

## 開発

```console
$ nix develop                # Lean 4.35.0 (lake), make, python3, hyperfine
$ make check                 # 整形、lint、祝日データの照合、lake build（証明の検査）、テスト、basis の表と公理の監査
$ make basis                 # @[ritsuryo_basis] から docs/basis.md を作り直す
$ make holidays              # data/syukujitsu.csv から Ritsuryo/Holiday/Data/Generated.lean を作り直す
$ make fetch-holidays        # 内閣府の CSV を取り直してから作り直す
$ nix build                  # CLI を ./result/bin/ritsuryo にビルドする
$ nix run . -- help
```

ビルドの成果物を消してから `lake build` を実行すると、すべての証明の検査が約 26 秒で終わる。

## CLI

CLI の引数は AWS CLI と同じ文法で書く。

```console
$ ritsuryo [global options] <command> <subcommand> [--parameter value ...]
```

- パラメータ名は `--kebab-case`。真偽値は `--flag` / `--no-flag`、リストは空白区切りで並べる。
- 値が `file://` で始まるときは、そのファイルを読む。
- 構造体のリストは shorthand 構文（`--items Price=1000,Rate=standard Price=540,Rate=reduced`）か JSON で渡す。
- `--cli-input-json` は、パラメータ名を PascalCase にしたキーの JSON オブジェクト 1 つで、すべてのパラメータを受け取る。
- `--generate-cli-skeleton input|output` は入力または出力の雛形を出力する。
- `--query` は JMESPath の式で出力の一部を取り出す。
- `help` はどの階層でも使える（`ritsuryo help`、`ritsuryo period help`、`ritsuryo period compute-expiry help`）。

`--query` で使える JMESPath の構文は識別子、サブ式、添字、スライス、リストとオブジェクトの射影、flatten、フィルタ、multi-select のリストとハッシュ、パイプ、比較、`||` `&&` `!`、リテラルである。使える関数は `length` `keys` `values` `sort` `reverse` `max` `min` `sum` `join` `contains` `starts_with` `ends_with` `type` `to_string` `not_null` である。

| command | subcommand | 計算するもの |
|---|---|---|
| `period` | `compute-expiry` | 日、週、月、年で定めた期間の末日（`--rule civil` は民法 140〜143 条、`--rule national-tax-general` は国税通則法 10 条 1 項）。`--rollover-rule` で繰り下げる |
| `period` | `compute-rollover` | `civil-142`、`civil-procedure-95`、`national-tax-10` による日の繰り下げ |
| `age` | `get-attainment-date` | ある年齢に達する日 |
| `age` | `compute-age` | ある日の終わりの年齢 |
| `holiday` | `list-holidays` | その年の休日と種別（祝日法 2 条、3 条 2 項、3 条 3 項、特例法） |
| `holiday` | `check-holiday` | ある日に当たる休日の種別と、各繰り下げ規定で休日に当たるか |
| `deadline` | `compute-appeal-deadline` | 控訴期間（民事訴訟法 285 条）。送達から 2 週間で、95 条 3 項で繰り下げる |
| `deadline` | `compute-final-appeal-deadline` | 上告期間（313 条、285 条） |
| `deadline` | `compute-immediate-appeal-deadline` | 即時抗告期間（332 条）。告知から 1 週間 |
| `deadline` | `get-income-tax-return-deadline` | 所得税の確定申告期限（所得税法 120 条 1 項、国税通則法 10 条 2 項） |
| `income-tax` | `compute-tax` | 課税総所得金額、課税退職所得金額、課税山林所得金額（5 分 5 乗）の所得税と、年分に応じた復興特別所得税と防衛特別所得税（2015 年分以後） |
| `inheritance-tax` | `compute-total-tax` | 課税価格の合計と相続人から出す相続税の総額（基礎控除、法定相続分、16 条の税率表） |
| `inheritance-tax` | `compute-statutory-shares` | 民法 900 条の法定相続分 |
| `consumption-tax` | `compute-invoice-tax` | 適格請求書の税率ごとの消費税額。税抜と税込、切捨てと切上げと四捨五入を選べる |
| `delinquency-tax` | `compute-tax` | 法定納期限、納期限、納付の日から出す延滞税。割合が変わる日で期間を分ける |
| `interest-tax` | `compute-tax` | 期間に対する利子税 |
| `penalty-tax` | `compute-tax` | 申告や納付の時期に応じた過少申告加算税、無申告加算税、不納付加算税、重加算税 |

### 出力

CLI はキーが PascalCase の JSON オブジェクトを出力する。

- `Result`：計算の結果。
- `Steps`：途中の値。起算日、応当日、繰り下げ前の末日、繰り下げた日、税率の区分ごとの税額など。
- `Basis`：結果の根拠の法令名、条項、e-Gov の法令 ID。
- `Assumptions`：結果が依拠する解釈と入力の前提。
- `Data`：祝日を使ったときの祝日 CSV の取得元、Last-Modified、SHA-256、収録年の範囲。使わなかったときは `{}`。
- `SchemaVersion`。

出力の形式は `--output` で `json`（既定）、`text`、`table` から選ぶ。`text` は AWS CLI と同じタブ区切りの形式で、`SchemaVersion` などの最上位のスカラーは末尾に `KEY<TAB>value` の行で出力する。

### 終了コード

| コード | 意味 |
|---|---|
| 0 | 成功 |
| 252 | コマンドかパラメータの誤り。条文が想定しない組み合わせ（調査通知の前の重加算税など）を含む |
| 254 | 計算が扱う範囲の外の入力。存在しない日付、祝日データの範囲外の年、生年月日より前の基準日、2015 年より前の年分、特例基準割合のない年 |
| 255 | それ以外の失敗 |

## 証明した性質

定理はすべて `lake build` のときに Lean が検査する。どの定理の証明も `sorry`、`admit`、`native_decide` を使っていない。

`lake exe basis-report --check` は、公開の定理が `propext`、`Classical.choice`、`Quot.sound` 以外の公理に依存するとき、または下の設計 ID に定理がないときに失敗する。

| ID | 定理 | 内容 |
|---|---|---|
| CAL-1 | `Date.cal1_ofDays_toDays` | 有効な先発グレゴリオ暦の日付（年は `Int`）で、日付 → 通日 → 日付が恒等になる |
| CAL-2 | `Date.cal2_toDays_ofDays` | すべての `Int` で通日 → 日付 → 通日が恒等になり、得た日付は有効 |
| CAL-3 | `Date.cal3_lt_iff` | 日付の辞書式順序と通日の順序が一致する |
| CAL-4 | `Date.cal4_nextDate` | 素朴な翌日（月末、年末、閏年を場合分け）は通日 + 1 |
| CAL-5 | `Date.cal5_weekday` | 曜日は通日の 7 の剰余で、翌日は次の曜日 |
| CAL-6 | `Date.cal6_daysInMonth` | 月の日数が通日と合い、2 月が 29 日になるのは閏年ニ関スル件（皇紀で定める）が閏年とする年に限る |
| PER-1 | `Period.per1_compute_eq_spec` | 実装の起算日、応当日、末日が民法 140 条、143 条の仕様と一致する |
| PER-2 | `Period.per2_from_beginning` | 1 日、1 月 1 日、日曜日に始まる期間で、143 条 2 項の式が暦の結果と一致する |
| PER-3 | `Period.per3_weeks_years` | n 週は 7n 日、n 年は 12n か月 |
| PER-4 | `Period.per4_not_additive`, `Period.per4_bound` | 2025-01-31 から 1 か月 + 1 か月は 03-31 に、2 か月は 03-30 に終わる。つないだ期間はいつも 0〜3 日遅い |
| PER-5 | `Period.per5_monotone` | 末日は起算点についても長さについても単調 |
| PER-6 | `Period.per6_months_from_event` | 起算点から n か月の期間は、起算点が月末なら月末に、そうでなければ n か月後の同じ日（なければその月の末日）に終わる |
| PER-7 | `Period.per7_national_tax_general` | 日、月、年の期間で、国税通則法 10 条 1 項は民法と同じ末日を出す |
| AGE-1 | `Period.Age.age1_attainment` | 年齢に達する日は応当日の前日。2 月 29 日生まれは 2 月 28 日に達する |
| AGE-2 | `Period.Age.age2_monotone_and_steps` | 年齢は達する日と達する日の間で一定で、日付について単調で、達する日ごとにちょうど 1 増える |
| ROL-1 | `Period.rol1_least_non_holiday` | 繰り下げた日はもとの日以後で休日でなく、その間の日はすべて休日 |
| ROL-2 | `Period.rol2_idempotent_monotone` | 繰り下げは冪等で、日付について単調で、休日の集合についても単調 |
| ROL-3 | `Period.rol3_procedure_vs_tax` | 1 月 2 日と 1 月 3 日を一般の休日とした国税通則法 10 条 2 項は民事訴訟法 95 条 3 項と一致する。そうしない場合も、それ以外の日では一致する |
| HOL-1 | `Holiday.hol1_derivation` | 振替休日と国民の休日の関数が祝日法 3 条 2 項、3 項の文言と一致する |
| HOL-2 | `Holiday.hol2_nthMonday` | `nthMonday` は月曜日を返し、その日はその月の n 番目の 7 日の区間にある |
| HOL-C1（検査） | `Holiday.holc1_csv_rest_days` | CSV のすべての年で、「休日」以外の行から 3 条 2 項、3 項（その日に施行されていた版）を導くと「休日」の行がちょうど得られる。カーネルで決定する |
| HOL-C2（検査） | `Holiday.holc2_csv_article2` | CSV のすべての年で、施行期間つきの 2 条の規定（と 2020 年、2021 年のオリンピックの日付）が CSV の国民の祝日の行をちょうど生成する。春分の日と秋分の日は CSV から 1 日ずつ取る。カーネルで決定する |
| TAX-1 | `Tax.Income.tax1_quick_eq_spec` | 国税庁の速算表の式が、すべての金額で 89 条の区分ごとの積み上げと一致する。実装の税額は、千円未満を切り捨てた金額での積み上げと一致する |
| TAX-2 | `Tax.Inheritance.tax2_quick_eq_spec` | 相続税法 16 条の税率表について同じことを示す |
| TAX-3 | `Tax.Income.tax3_monotone` | 税額、課税所得から税額を引いた額、課税所得から百円未満を切り捨てた税額を引いた額が、所得について単調 |
| TAX-4 | `Tax.Income.tax4_marginal_rate` | 積み上げの額は増えた分の 5%〜45% だけ増える。実装の税額は 999 円の幅を除いて同じ |
| TAX-5 | `Tax.Income.tax5_timber` | 実装の山林所得の税額は、五分の一の金額（端数は出ない）での積み上げの 5 倍 |
| RND-1 | `Tax.rnd1_floorTo` | k 円未満の切捨ては、もとの額以下で、差は k 未満で、k の倍数で、冪等で、単調 |
| RND-2 | `Tax.rnd2_incidentalFinal` | 附帯税の端数処理（千円未満、五千円未満は切り捨てて 0）は単調で、もとの額以下で、0 か最低額以上 |
| CON-1 | `Tax.Consumption.con1_combined_rate` | 7.8% と 6.24% に、その 22/78 を足すと 10% と 8% |
| CON-2 | `Tax.Consumption.con2_per_rate_rounding` | n 件をそれぞれ端数処理した合計と、合計を端数処理した額の差は、どの端数処理でも、税抜と税込のどちらでも n − 1 円以下 |
| DEL-1 | `Tax.Delinquency.del1_special_rates_le` | 延滞税の特例の割合は 7.3% と 14.6% を超えず、利子税の割合は 7.3% を超えない |
| DEL-2 | `Tax.Delinquency.del2_additive_monotone` | 端数処理前の額（日ごとの税額 × 割合の合計）は期間を分けても変わらず、税額と日数について単調で、実装の区間の合計と一致する |
| PEN-1 | `Tax.Penalty.pen1_no_return_tiers` | 66 条 3 項の無申告加算税の段階は 300 万円までは 2 項の文言と一致し、税額について単調 |
| INH-1 | `Tax.Inheritance.inh1_statutory_shares` | 民法 900 条の相続分は正で合計が 1 になり、半血の兄弟姉妹は全血の兄弟姉妹の二分の一 |

## 祝日データ

`data/syukujitsu.csv` は内閣府が公開している CSV（https://www8.cao.go.jp/chosei/shukujitsu/syukujitsu.csv、Shift_JIS、Last-Modified 2026-02-02T00:30:17Z）である。1955-01-01 から 2027-11-23 までの 1,067 行があり、そのうち 116 行が「休日」、2 行が「休日（祝日扱い）」、4 行が特例法で休日とした日（結婚の儀 ×2、大喪の礼、即位礼正殿の儀）である。

`scripts/gen_holidays.py` がこの CSV を年ごとの表にして `Ritsuryo/Holiday/Data/Generated.lean` に書き出す。そのため、ビルドのときにネットワークに接続する必要はない。

`Holiday data` ワークフローは毎月 CSV を取り直して `make check` を通し、変わっていればプルリクエストを作る。

## 実行時間とバイナリの大きさ

リリースの `ritsuryo` は 3.4 MB の実行ファイル 1 つである（x86_64-linux）。Lean のランタイム、GMP、libuv はこのファイルに含まれていて、ほかに必要なのは C ライブラリだけである。

1 回の実行は約 6 ms で終わり、使うメモリは最大で約 10 MiB である。たとえば `income-tax compute-tax` を 1 万回続けて呼んでも約 64 秒で終わる。

| コマンド | 時間 |
|---|---|
| `--version` | 4.5 ms ± 1.3 ms |
| `income-tax compute-tax` | 6.4 ms ± 1.2 ms |
| `deadline compute-appeal-deadline`（6 日繰り下げる） | 6.2 ms ± 1.5 ms |
| `delinquency-tax compute-tax`（290 日） | 5.9 ms ± 1.3 ms |
| `holiday list-holidays --output table` | 6.3 ms ± 1.2 ms |

v0.5.0 の x86_64-linux のリリースを NixOS（14 ハードウェアスレッド）で `hyperfine -N --warmup 20 --runs 300` にかけて計測した。最大メモリは `time -f %M` で計測し、8.4〜10.5 MiB だった。

ビルドの方法を決めるときに使った計測値（import の書き方によるバイナリの大きさ、ツールチェインの違い、祝日の検査にかかる時間、ビルド時間）は `docs/measurements.md` にまとめている。

## リリースの作り方

GitHub のリリースは `Release` ワークフローが作る。ワークフローは GitHub のランナー（x86_64-linux、aarch64-linux、aarch64-darwin）で上流のツールチェインを使って CLI をビルドし、ライブラリと CLI のテストを実行する。`v*` のタグを push すると、ビルドしたアーカイブをリリースに添付する。

## 構成

```
Ritsuryo/
  Law.lean, Basis.lean, Audit.lean   法令と e-Gov の ID、@[ritsuryo_basis]、表と監査
  Calendar/                          日付、通日、曜日、CAL の証明
  Period/
    Spec/                            民法 138〜143 条、142 条、民事訴訟法 95 条、国税通則法 10 条
    HolidayClass.lean, Impl.lean, Age.lean, Rollover.lean
    Presets.lean                     控訴、上告、即時抗告、所得税の確定申告期限
    Proofs/                          PER、AGE、ROL の証明
  Holiday/
    Spec.lean, Proofs.lean           祝日法 2 条、3 条、HOL の証明
    Data.lean, Data/Generated.lean   CSV の表
    Lookup.lean, Check.lean          検索、時期ごとの導出、HOL-C1
    Article2.lean, Article2Check.lean  施行期間ごとの 2 条の規定、HOL-C2
  Tax/
    Rounding.lean, Progressive.lean  国税通則法 118 条、119 条、税率表
    Income.lean, Inheritance.lean    所得税法 89 条、相続税法 15 条、16 条と民法 900 条
    Consumption.lean                 消費税法 29 条、施行令 70 条の 10
    Delinquency.lean, Penalty.lean   延滞税と利子税、加算税
    Proofs/                          TAX、RND、CON、DEL、PEN、INH の証明
  Cli/                               JSON、引数の解析、--query、出力の整形、コマンドの表
Main.lean                            ritsuryo の CLI
BasisReport.lean                     lake exe basis-report
Tests/, TestMain.lean                lake test
scripts/                             CSV の変換、lint、CLI のテスト
data/                                内閣府の CSV
docs/                                basis.md（生成）、interpretation.md、measurements.md
```

## ライセンス

Apache-2.0
