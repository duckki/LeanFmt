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

def partitionDefaultEnvironmentFiles (loader : EnvironmentLoader) (files : List FilePath)
    : IO (List FilePath × List FilePath) := do
  let mut defaultFiles := []
  let mut importFiles := []
  for file in files do
    let source ← IO.FS.readFile file
    if (← sourceParsesWithDefaultEnvironment loader source file.toString) then
      defaultFiles := file :: defaultFiles
    else
      importFiles := file :: importFiles
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
