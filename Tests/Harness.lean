module

public section

namespace Ritsuryo.Tests

structure Outcome where
  passed : Nat := 0
  failures : Array String := #[]

abbrev TestM := StateT Outcome IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit :=
  modify fun o =>
    if ok then { o with passed := o.passed + 1 }
    else
      let msg := if detail.isEmpty then name else s!"{name}: {detail}"
      { o with failures := o.failures.push msg }

def checkEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) : TestM Unit :=
  check name (actual == expected) s!"expected {expected}, got {actual}"

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
