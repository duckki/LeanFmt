import LeanFmt.Tests.Suite

def main (_args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← LeanFmt.Formatter.defaultEnvironment
  if (← IO.getEnv "LEANFMT_COMPATIBILITY_TEST") == some "1" then
    LeanFmt.Tests.runCompatibilityTests env
  else
    LeanFmt.Tests.runTestGroups env
  pure 0
