module

/-!
# テストの土台

`lake test`（`TestMain.lean`）が実行するテストの小さな枠組み。各スイートは `TestM` の中で `check`・`checkEq` を
呼び、通った数と失敗の説明を `Outcome` にためる。`runSuites` がスイートごとの結果を出し、
1 つでも失敗があれば終了コード 1 を返す。
-/

public section

namespace Ritsuryo.Tests

/-- 1 つのスイートの結果。通った数と、失敗したテストの説明。 -/
structure Outcome where
  passed : Nat := 0
  failures : Array String := #[]

/-- テストを書くモナド。`Outcome` を状態に持ち、`IO` も使える。 -/
abbrev TestM := StateT Outcome IO

/-- `ok` が `true` なら通った数を足し、`false` なら `name`（と `detail`）を失敗に加える。 -/
def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit :=
  modify fun o =>
    if ok then { o with passed := o.passed + 1 }
    else
      let msg := if detail.isEmpty then name else s!"{name}: {detail}"
      { o with failures := o.failures.push msg }

/-- `actual` と `expected` が等しいかを確かめる。違えば両方の値を失敗の説明に入れる。 -/
def checkEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) : TestM Unit :=
  check name (actual == expected) s!"expected {expected}, got {actual}"

/-- スイートを順に実行して結果を出し、失敗がなければ 0、あれば 1 を返す。 -/
def runSuites (suites : List (String × TestM Unit)) : IO UInt32 := do
  let mut failed := 0
  for (name, suite) in suites do
    let (_, o) ← suite.run {}
    IO.println s!"{name}: {o.passed} passed, {o.failures.size} failed"
    for f in o.failures do
      IO.eprintln s!"  FAIL {f}"
    failed := failed + o.failures.size
  return if failed == 0 then 0 else 1

end Ritsuryo.Tests
