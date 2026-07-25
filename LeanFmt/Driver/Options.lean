import LeanFmt.Formatter

open System

namespace LeanFmt.Driver

structure Options where
  check : Bool := false
  checkException : Bool := false
  checkIdempotent : Bool := false
  profile : Bool := false
  importEnvFirst : Bool := false
  recursive : Bool := false
  includeHidden : Bool := false
  worker : Bool := false
  formatterOptions : Formatter.Options := {}
  workerBatchSize? : Option Nat := none
  environmentCacheSize : Nat := 1
  files : List FilePath := []
deriving Repr

end LeanFmt.Driver
