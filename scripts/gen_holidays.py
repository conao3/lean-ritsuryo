"""内閣府の「国民の祝日」CSV から Ritsuryo/Holiday/Data/Generated.lean を生成する。

CSV（data/syukujitsu.csv、Shift_JIS）の行を年ごとの Lean の表 y1955 ... にし、年の順に並べた byYear と、
取得元・Last-Modified・SHA-256・年の範囲・行数の定義を書き出す。行の種類は名称で決める（kind_of）。
"""

import argparse
import csv
import datetime
import email.utils
import hashlib
import io
import json
import pathlib
import sys
import urllib.request

URL = "https://www8.cao.go.jp/chosei/shukujitsu/syukujitsu.csv"
ROOT = pathlib.Path(__file__).resolve().parent.parent
CSV_PATH = ROOT / "data" / "syukujitsu.csv"
META_PATH = ROOT / "data" / "syukujitsu.json"
OUT_PATH = ROOT / "Ritsuryo" / "Holiday" / "Data" / "Generated.lean"

REST = "休日"
TREATED_AS_NATIONAL = "休日（祝日扱い）"
SPECIAL_LAW = {"結婚の儀", "大喪の礼", "即位礼正殿の儀"}
BASIS = '@[ritsuryo_basis "国民の祝日に関する法律" "第2条"]'


def fetch():
    """CSV を内閣府から取り直し、data/ に CSV と取得元・Last-Modified（UTC）の JSON を書く。"""
    with urllib.request.urlopen(URL) as response:
        body = response.read()
        last_modified = response.headers["Last-Modified"]
    CSV_PATH.write_bytes(body)
    parsed = email.utils.parsedate_to_datetime(last_modified)
    stamp = parsed.astimezone(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    META_PATH.write_text(
        json.dumps({"Source": URL, "LastModified": stamp}, indent=2) + "\n",
        encoding="utf-8",
    )


def kind_of(name):
    """CSV の名称から Lean の EntryKind の名前を決める。「休日」は第3条第2項・第3項の休日になる。"""
    if name == REST:
        return "rest"
    if name == TREATED_AS_NATIONAL:
        return "treatedAsNational"
    if name in SPECIAL_LAW:
        return "specialLaw"
    return "national"


def lean_string(s):
    """Lean の文字列リテラルにする。"""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def render():
    """CSV と data/syukujitsu.json から Generated.lean の中身を作る。年が連続していなければ止まる。"""
    raw = CSV_PATH.read_bytes()
    meta = json.loads(META_PATH.read_text(encoding="utf-8"))
    rows = list(csv.reader(io.StringIO(raw.decode("shift_jis"))))
    header, body = rows[0], [r for r in rows[1:] if r]
    if header != ["国民の祝日・休日月日", "国民の祝日・休日名称"]:
        sys.exit(f"unexpected header: {header}")
    by_year = {}
    for date, name in body:
        y, m, d = (int(x) for x in date.split("/"))
        by_year.setdefault(y, []).append((m, d, name))
    years = sorted(by_year)
    if years != list(range(years[0], years[-1] + 1)):
        sys.exit("years are not contiguous")
    out = [
        "module",
        "",
        "public import Ritsuryo.Holiday.Data",
        "meta import Ritsuryo.Basis",
        "",
        "@[expose] public section",
        "",
        "namespace Ritsuryo.Holiday.Data",
        "",
        BASIS,
        f"def source : String := {lean_string(meta['Source'])}",
        "",
        BASIS,
        f"def lastModified : String := {lean_string(meta['LastModified'])}",
        "",
        BASIS,
        f"def sha256 : String := {lean_string(hashlib.sha256(raw).hexdigest())}",
        "",
        BASIS,
        f"def firstYear : Int := {years[0]}",
        "",
        BASIS,
        f"def lastYear : Int := {years[-1]}",
        "",
        BASIS,
        f"def rowCount : Nat := {len(body)}",
    ]
    for y in years:
        out += ["", BASIS, f"def y{y} : List Entry := ["]
        entries = [
            f"  ⟨{m}, {d}, {lean_string(name)}, .{kind_of(name)}⟩"
            for m, d, name in by_year[y]
        ]
        out.append(",\n".join(entries))
        out.append("]")
    out += ["", BASIS, "def byYear : List (List Entry) := ["]
    out.append(",\n".join(f"  y{y}" for y in years))
    out += ["]", "", "end Ritsuryo.Holiday.Data", ""]
    return "\n".join(out)


def main():
    """--fetch で CSV を取り直し、--check で生成済みのファイルとの差を検査し、どちらもなければ書き出す。"""
    parser = argparse.ArgumentParser(
        description="Generate Ritsuryo/Holiday/Data/Generated.lean from the Cabinet Office CSV."
    )
    parser.add_argument(
        "--fetch",
        action="store_true",
        help="download the CSV into data/ before generating",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the committed Lean file differs from the CSV",
    )
    args = parser.parse_args()
    if args.fetch:
        fetch()
    text = render()
    if args.check:
        if OUT_PATH.read_text(encoding="utf-8") != text:
            sys.exit(f"{OUT_PATH.relative_to(ROOT)} is out of date; run make holidays")
        return
    OUT_PATH.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
