import LeanFmt.Driver.Environment

open System

namespace LeanFmt.Driver

def sourceParsesWithDefaultEnvironment
    (loader : EnvironmentLoader) (source fileName : String)
    : IO Bool := do
  try
    discard
    <| SyntaxTree.parseModuleSyntaxWithoutParserStateUpdates loader.default
        (Formatter.Internal.normalizeSource source) fileName
    pure true
  catch _ =>
    pure false

private structure ClassifiedFile where
  path : FilePath
  usesDefaultEnvironment : Bool
  sourceSize : Nat

private partial def splitIntoBatchCount (batchCount : Nat) (items : List α)
    : List (List α) :=
  if batchCount == 0 || items.isEmpty then
    []
  else
    let batchSize := (items.length + batchCount - 1) / batchCount
    items.take batchSize :: splitIntoBatchCount (batchCount - 1) (items.drop batchSize)

private def classifyFiles (loader : EnvironmentLoader) (files : List FilePath)
    : IO (List ClassifiedFile) := do
  files.mapM
    fun file => do
      let source ← IO.FS.readFile file
      pure
        {
          path := file
          usesDefaultEnvironment :=
            ← sourceParsesWithDefaultEnvironment loader source file.toString
          sourceSize := source.length
        }

/--
During classification, read each file once to determine its required environment and
estimate its formatting cost. Classification batches share the immutable default
environment and run in parallel, while their results retain input order.
-/
def partitionDefaultEnvironmentFiles
    (loader : EnvironmentLoader) (workerJobs : Nat) (files : List FilePath)
    : IO (List (FilePath × Nat) × List FilePath) := do
  let batches := splitIntoBatchCount (min (max 1 workerJobs) files.length) files
  let tasks ←
    batches.mapM fun batch => IO.asTask (prio := .dedicated) (classifyFiles loader batch)
  let classifiedBatches ← tasks.mapM fun task => IO.ofExcept task.get
  let mut defaultFiles := []
  let mut importFiles := []
  for batch in classifiedBatches do
    for file in batch do
      if file.usesDefaultEnvironment then
        defaultFiles := (file.path, file.sourceSize) :: defaultFiles
      else
        importFiles := file.path :: importFiles
  pure (defaultFiles.reverse, importFiles.reverse)

def isLeanFile (path : FilePath) : Bool := path.extension == some "lean"

def isHiddenName (name : String) : Bool :=
  name.startsWith "." && name != "." && name != ".."

partial def leanFilesInDirectory (options : Options) (dir : FilePath)
    : IO (List FilePath) := do
  let mut files := []
  for entry in (← dir.readDir) do
    if options.includeHidden || !isHiddenName entry.fileName then
      if (← entry.path.isDir) then
        if options.recursive then
          files := files ++ (← leanFilesInDirectory options entry.path)
      else if isLeanFile entry.path then
        files := files ++ [entry.path]
  pure files

def expandInputPath (options : Options) (path : FilePath) : IO (List FilePath) := do
  if (← path.pathExists) && (← path.isDir) then
    leanFilesInDirectory options path
  else
    pure [path]

def expandInputPaths (options : Options) : IO (List FilePath) := do
  let mut files := []
  for path in options.files do
    files := files ++ (← expandInputPath options path)
  pure files

def isLakePackageRoot (path : FilePath) : IO Bool := do
  pure
  <| (← (path / "lakefile.lean").pathExists) || (← (path / "lakefile.toml").pathExists)

partial def findLakePackageRoot? (path : FilePath) : IO (Option FilePath) := do
  let currentDir ← IO.currentDir
  let path := if path.isAbsolute then path else currentDir / path
  let candidate ←
    if (← path.pathExists) && (← path.isDir) then
      pure path
    else
      match path.parent with
      | some parent => pure parent
      | none => pure "."
  if (← isLakePackageRoot candidate) then
    pure <| some candidate
  else
    match candidate.parent with
    | some parent =>
        if parent == candidate then
          pure none
        else
          findLakePackageRoot? parent
    | none => pure none

def workerCwd? (options : Options) : IO (Option FilePath) := do
  let rec commonRoot? (expected? : Option FilePath) : List FilePath → IO (Option FilePath)
    | [] => pure expected?
    | path :: rest => do
        let some root ←
          findLakePackageRoot? path
        | pure none
        match expected? with
        | none => commonRoot? (some root) rest
        | some expected =>
            if root.normalize == expected.normalize then
              commonRoot? expected? rest
            else
              pure none
  commonRoot? none options.files

end LeanFmt.Driver
