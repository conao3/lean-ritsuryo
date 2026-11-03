import Ritsuryo
import Ritsuryo.Audit

/-!
# `lake exe basis-report`

引数なしで実行すると `docs/basis.md` の本文（条文ごとの仕様・実装・定理の対応表）を標準出力に書く。
`--check` を付けると監査（`Ritsuryo.Audit.audit`）の問題を標準エラーに書き、問題があれば終了コード 1 を返す。
対応表と監査の結果は、このファイルをコンパイルした時点のライブラリから計算して埋め込む。
-/

/-- コンパイル時に計算した `docs/basis.md` の本文。 -/
def report : String := ritsuryo_basis_report%

/-- コンパイル時に計算した監査の問題の一覧。 -/
def problems : List String := ritsuryo_audit%

/-- 引数なしなら対応表を出力し、`--check` なら監査の結果で終了コードを決める（0 は問題なし、1 は問題あり、2 は引数の誤り）。 -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.print report
    return 0
  | ["--check"] =>
    for p in problems do
      IO.eprintln p
    return if problems.isEmpty then 0 else 1
  | _ =>
    IO.eprintln "usage: basis-report [--check]"
    return 2
