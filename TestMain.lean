import Tests.Calendar
import Tests.Period
import Tests.Tax

def main : IO UInt32 :=
  Ritsuryo.Tests.runSuites
    (Ritsuryo.Tests.Calendar.suites ++ Ritsuryo.Tests.Period.suites ++ Ritsuryo.Tests.Tax.suites)
