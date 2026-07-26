import LeanFmt.Cli

namespace LeanFmt.Main

@[extern "lean_internal_get_hardware_concurrency"]
opaque getHardwareConcurrency : Unit → UInt32

def run (args : List String) : IO UInt32 :=
  LeanFmt.Cli.runMain args (getHardwareConcurrency ()).toNat

end LeanFmt.Main

def main (args : List String) : IO UInt32 :=
  LeanFmt.Main.run args
