import Tests.Calendar
import Tests.Period

def main : IO UInt32 :=
  Ritsuryo.Tests.runSuites (Ritsuryo.Tests.Calendar.suites ++ Ritsuryo.Tests.Period.suites)
