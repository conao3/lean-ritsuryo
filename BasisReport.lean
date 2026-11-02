import Ritsuryo
import Ritsuryo.Audit

def report : String := ritsuryo_basis_report%

def problems : List String := ritsuryo_audit%

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
