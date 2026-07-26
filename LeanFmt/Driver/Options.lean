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
  workerDefaultEnvironment : Bool := false
  hardwareConcurrency : Nat := 1
  formatterOptions : Formatter.Options := {}
  workerJobs? : Option Nat := none
  importPrefixCacheSize : Nat := 0
  files : List FilePath := []
deriving Repr

end LeanFmt.Driver
