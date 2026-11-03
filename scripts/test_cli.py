"""ビルドした ritsuryo の CLI を実行して、出力と終了コードを確かめる。

使い方: python3 scripts/test_cli.py <ritsuryo の実行ファイルのパス>

CASES の各行は、名前、引数、期待する終了コード、出力の JSON のパス（Result.ExpiryDate など）と期待する値。
そのほか --cli-input-json と file:// の読み込み、--query、--generate-cli-skeleton、
--output text・table、help、--version を個別に確かめる。
"""

import json
import pathlib
import subprocess
import sys
import tempfile

BIN = pathlib.Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else None

CASES = [
    (
        "civil month with 142 rollover",
        "period compute-expiry --event-date 2026-11-02 --months 1 --rule civil "
        "--rollover-rule civil-142 --holiday-classes sunday national-holiday "
        "--assume-no-trade-custom",
        0,
        {"Result.ExpiryDate": "2026-12-02", "Steps.StartDate": "2026-11-03"},
    ),
    (
        "two weeks over the year end under 民訴 95 条",
        "period compute-expiry --event-date 2026-12-15 --weeks 2 --rollover-rule civil-procedure-95",
        0,
        {
            "Result.ExpiryDate": "2027-01-04",
            "Steps.ExpiryBeforeRollover": "2026-12-29",
        },
    ),
    (
        "national tax month",
        "period compute-expiry --event-date 2026-01-30 --months 1 --rule national-tax-general "
        "--rollover-rule national-tax-10",
        0,
        {"Result.ExpiryDate": "2026-03-02", "Steps.CorrespondingDate": None},
    ),
    (
        "rollover only",
        "period compute-rollover --date 2026-05-02 --rollover-rule civil-procedure-95",
        0,
        {"Result.Date": "2026-05-07"},
    ),
    (
        "attainment date for 2/29",
        "age get-attainment-date --birth-date 2008-02-29 --age 18",
        0,
        {"Result.AttainmentDate": "2026-02-28"},
    ),
    (
        "age on the attainment date",
        "age compute-age --birth-date 2008-02-29 --as-of 2026-02-28",
        0,
        {"Result.Age": 18, "Steps.NextAttainmentDate": "2027-02-28"},
    ),
    (
        "list holidays",
        "holiday list-holidays --year 2019",
        0,
        {"Result.Year": 2019},
    ),
    (
        "check holiday",
        "holiday check-holiday --date 2027-01-02",
        0,
        {"Result.Weekday": "saturday", "Result.NationalHoliday": None},
    ),
    ("missing command", "", 252, {}),
    ("unknown command", "tax compute-tax", 252, {}),
    ("unknown parameter", "age compute-age --birth-date 2000-01-01 --foo 1", 252, {}),
    ("missing required", "age compute-age --birth-date 2000-01-01", 252, {}),
    (
        "malformed date",
        "age compute-age --birth-date 2000/01/01 --as-of 2001-01-01",
        252,
        {},
    ),
    (
        "two lengths",
        "period compute-expiry --event-date 2026-01-01 --days 1 --weeks 1",
        252,
        {},
    ),
    (
        "weeks under national tax",
        "period compute-expiry --event-date 2026-01-01 --weeks 1 --rule national-tax-general",
        252,
        {},
    ),
    ("positional argument", "age compute-age 2000-01-01", 252, {}),
    (
        "income tax (NTA No.2260)",
        "income-tax compute-tax --tax-year 2026 --taxable-income 7000000",
        0,
        {"Result.IncomeTax": 974000, "Result.ReconstructionTax": 20454},
    ),
    (
        "income tax before 2015",
        "income-tax compute-tax --tax-year 2014 --taxable-income 7000000",
        254,
        {},
    ),
    (
        "inheritance tax (NTA No.4155)",
        "inheritance-tax compute-total-tax --taxable-value-total 200000000 --spouse "
        "--biological-children 2",
        0,
        {"Result.TotalTax": 27000000, "Steps.BasicDeduction": 48000000},
    ),
    (
        "statutory shares",
        "inheritance-tax compute-statutory-shares --spouse --ascendants 2",
        0,
        {"Result.Denominator": 6},
    ),
    (
        "invoice tax",
        "consumption-tax compute-invoice-tax --items Price=105,Rate=standard "
        "Price=105,Rate=standard Price=105,Rate=standard",
        0,
        {"Result.TotalTax": 31},
    ),
    (
        "invoice tax with a bad item",
        "consumption-tax compute-invoice-tax --items Price=105,Rate=luxury",
        252,
        {},
    ),
    (
        "delinquency tax",
        "delinquency-tax compute-tax --tax 1000000 --legal-due-date 2026-03-16 "
        "--payment-date 2026-07-31",
        0,
        {"Result.DelinquencyTax": 23600, "Steps.TwoMonthsEnd": "2026-05-16"},
    ),
    (
        "delinquency tax without the rate of the year",
        "delinquency-tax compute-tax --tax 1000000 --legal-due-date 2026-03-16 "
        "--payment-date 2027-01-10",
        254,
        {},
    ),
    (
        "delinquency tax with a given rate",
        "delinquency-tax compute-tax --tax 1000000 --legal-due-date 2026-03-16 "
        "--payment-date 2027-01-10 --special-base-rates Year=2027,Rate=1.8",
        0,
        {"Result.DelinquencyTax": 64200},
    ),
    (
        "interest tax",
        "interest-tax compute-tax --tax 3000000 --from-date 2026-03-16 --to-date 2026-05-31",
        0,
        {"Result.InterestTax": 8100},
    ),
    (
        "penalty tax",
        "penalty-tax compute-tax --kind underpayment --tax 1200000 --timely-tax 1000000",
        0,
        {"Result.PenaltyTax": 130000},
    ),
    (
        "fraud before notice",
        "penalty-tax compute-tax --kind no-return --timing before-notice --tax 100000 --fraud",
        252,
        {},
    ),
    (
        "appeal deadline",
        "deadline compute-appeal-deadline --served-date 2026-12-15",
        0,
        {"Result.Deadline": "2027-01-04", "Result.Invariable": True},
    ),
    (
        "income tax return deadline",
        "deadline get-income-tax-return-deadline --tax-year 2025",
        0,
        {"Result.Deadline": "2026-03-16"},
    ),
    (
        "malformed query",
        "holiday list-holidays --year 2026 --query Result.[",
        252,
        {},
    ),
    (
        "nonexistent date",
        "age compute-age --birth-date 2001-02-29 --as-of 2002-01-01",
        254,
        {},
    ),
    ("year outside the data", "holiday list-holidays --year 2030", 254, {}),
    (
        "rollover outside the data",
        "period compute-rollover --date 2027-12-29 --rollover-rule civil-procedure-95",
        254,
        {},
    ),
    (
        "as-of before birth",
        "age compute-age --birth-date 2001-01-02 --as-of 2001-01-01",
        254,
        {},
    ),
    (
        "missing input file",
        "age compute-age --cli-input-json file:///nonexistent.json",
        255,
        {},
    ),
]


def run(args, cwd=None):
    """CLI を引数 args で実行し、標準出力・標準エラー・終了コードを返す。"""
    return subprocess.run(
        [str(BIN), *args], capture_output=True, text=True, cwd=cwd, check=False
    )


def lookup(obj, path):
    """出力の JSON から、ドットでつないだキーのパスの値を取る。"""
    for key in path.split("."):
        obj = obj[key]
    return obj


def main():
    """すべてのケースを実行して結果を出し、失敗があれば 1 を返す。"""
    if BIN is None:
        sys.exit("usage: test_cli.py <path to ritsuryo>")
    failures = []
    for name, cmd, code, expect in CASES:
        p = run(cmd.split())
        if p.returncode != code:
            failures.append(
                f"{name}: exit {p.returncode}, expected {code}: {p.stderr.strip()}"
            )
            continue
        if expect:
            out = json.loads(p.stdout)
            for path, value in expect.items():
                if lookup(out, path) != value:
                    failures.append(
                        f"{name}: {path} = {lookup(out, path)!r}, expected {value!r}"
                    )
            if out.get("SchemaVersion") != "1":
                failures.append(f"{name}: SchemaVersion missing")
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        (tmp / "in.json").write_text(
            json.dumps({"BirthDate": "2008-04-01", "Age": 6}), encoding="utf-8"
        )
        (tmp / "bd.txt").write_text("2000-01-01\n", encoding="utf-8")
        checks = [
            (
                "cli-input-json",
                ["age", "get-attainment-date", "--cli-input-json", "file://in.json"],
                "2014-03-31",
            ),
            (
                "cli-input-json overridden by a parameter",
                [
                    "age",
                    "get-attainment-date",
                    "--cli-input-json",
                    "file://in.json",
                    "--age",
                    "7",
                ],
                "2015-03-31",
            ),
            (
                "file:// value",
                [
                    "age",
                    "get-attainment-date",
                    "--birth-date",
                    "file://bd.txt",
                    "--age",
                    "20",
                ],
                "2019-12-31",
            ),
        ]
        for name, args, value in checks:
            p = run(args, cwd=tmp)
            if p.returncode != 0:
                failures.append(f"{name}: exit {p.returncode}: {p.stderr.strip()}")
            elif json.loads(p.stdout)["Result"]["AttainmentDate"] != value:
                failures.append(f"{name}: unexpected {p.stdout}")
    queries = [
        (
            "query a field",
            "holiday list-holidays --year 2026 --query Result.Holidays[0].Name",
            "元日",
        ),
        (
            "query a filter",
            "holiday list-holidays --year 2026 "
            "--query Result.Holidays[?Class=='substitute-holiday'].Date",
            ["2026-05-06"],
        ),
        (
            "query a function",
            "holiday list-holidays --year 2026 --query length(Result.Holidays)",
            18,
        ),
    ]
    for name, cmd, value in queries:
        p = run(cmd.split())
        if p.returncode != 0:
            failures.append(f"{name}: exit {p.returncode}: {p.stderr.strip()}")
        elif json.loads(p.stdout) != value:
            failures.append(f"{name}: unexpected {p.stdout}")
    text = run(
        "age get-attainment-date --birth-date 2008-02-29 --age 18 --output text".split()
    )
    if text.stdout.splitlines()[0] != "RESULT\t2026-02-28":
        failures.append(f"text output starts with {text.stdout.splitlines()[0]!r}")
    skeleton = json.loads(
        run("period compute-expiry --generate-cli-skeleton input".split()).stdout
    )
    if "EventDate" not in skeleton or "RolloverRule" not in skeleton:
        failures.append("input skeleton lacks PascalCase keys")
    out_skeleton = json.loads(
        run("period compute-expiry --generate-cli-skeleton output".split()).stdout
    )
    if set(out_skeleton) != {
        "Result",
        "Steps",
        "Basis",
        "Assumptions",
        "Data",
        "SchemaVersion",
    }:
        failures.append(f"output skeleton keys: {sorted(out_skeleton)}")
    text = run(
        "age compute-age --birth-date 2008-02-29 --as-of 2026-02-28 --output text".split()
    )
    if "RESULT\t18" not in text.stdout:
        failures.append(f"text output: {text.stdout!r}")
    table = run("holiday list-holidays --year 2026 --output table".split())
    if "ListHolidays" not in table.stdout or "substitute-holiday" not in table.stdout:
        failures.append("table output")
    for path in [
        ["help"],
        ["period", "help"],
        ["period", "compute-expiry", "help"],
        ["--version"],
    ]:
        p = run(path)
        if p.returncode != 0 or not p.stdout:
            failures.append(f"{' '.join(path)}: exit {p.returncode}")
    total = len(CASES) + len(checks) + len(queries) + 9
    for f in failures:
        print(f"  FAIL {f}", file=sys.stderr)
    print(f"cli: {total - len(failures)} passed, {len(failures)} failed")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
