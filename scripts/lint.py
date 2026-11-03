"""リポジトリのファイルの書式を検査する。

git が追跡するファイル（と追跡前の新しいファイル）について、末尾の改行、行末の空白を検査し、
Lean のファイルではタブ文字と、ドキュメントコメントの外で 100 文字を超える行も検査する。
"""

import subprocess
import sys

SUFFIXES = (".lean", ".md", ".py", ".nix", ".toml", ".yml", ".json")
MAX_LEAN_LINE = 100


def tracked_files():
    """検査するファイル。git の追跡下と、.gitignore に当たらない未追跡のファイルのうち、対象の拡張子のもの。"""
    out = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return [f for f in out.splitlines() if f.endswith(SUFFIXES) or f == "Makefile"]


def check(path):
    """1 つのファイルの問題を「パス:行: 内容」の文字列の並びで返す。"""
    problems = []
    with open(path, encoding="utf-8") as f:
        text = f.read()
    if text and not text.endswith("\n"):
        problems.append(f"{path}: missing final newline")
    in_doc = False
    for i, line in enumerate(text.splitlines(), 1):
        if line != line.rstrip():
            problems.append(f"{path}:{i}: trailing whitespace")
        if path.endswith(".lean"):
            starts_doc = line.lstrip().startswith("/-")
            if "\t" in line:
                problems.append(f"{path}:{i}: tab character")
            if len(line) > MAX_LEAN_LINE and not (in_doc or starts_doc):
                problems.append(f"{path}:{i}: line longer than {MAX_LEAN_LINE}")
            if starts_doc:
                in_doc = True
            if "-/" in line:
                in_doc = False
    return problems


def main():
    """全ファイルを検査して問題を標準エラーに出し、問題があれば 1 を返す。"""
    problems = [p for f in tracked_files() for p in check(f)]
    for p in problems:
        print(p, file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
