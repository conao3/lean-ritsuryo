import Tests.Calendar

def main : IO UInt32 :=
  Ritsuryo.Tests.runSuites Ritsuryo.Tests.Calendar.suites
