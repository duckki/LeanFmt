import LeanFmt.Formatter.LineBreakRules
import LeanFmt.Formatter.SpaceRules

namespace LeanFmt
namespace Formatter
namespace Trace

structure Entry where
  lineNumber : Nat
  message : String
deriving Repr

structure State where
  enabled : Bool := false
  segmentPath : List Nat := []
  entries : List Entry := []
deriving Repr

def newlineCount (text : String) : Nat :=
  text.toList.foldl (fun count char => if char == '\n' then count + 1 else count) 0

def segmentPathString : List Nat → String
  | [] => "<root>"
  | path => String.intercalate "." (path.map fun index => toString index)

def treeKindString : SyntaxTree.Tree → String
  | .missing => "missing"
  | .leaf token => s!"leaf {token.lexeme}"
  | .node kind _ => s!"{repr kind}"

def optionNatString : Option Nat → String
  | none => "none"
  | some value => s!"some {value}"

def segmentFirstToken? (segment : LineBreakRules.Segment) : Option SyntaxTree.Token :=
  segment.indexes.foldl
    (fun found index =>
      match found with
      | some token => some token
      | none =>
          match segment.child? index with
          | some child => SyntaxTree.Tree.firstToken? child
          | none => none)
    none

def segmentLineNumber
    (output : String) (defaultWhitespace : SyntaxTree.Token → String)
    (segment : LineBreakRules.Segment)
    : Nat :=
  match segmentFirstToken? segment with
  | some token => newlineCount output + 1 + newlineCount (defaultWhitespace token)
  | none => newlineCount output + 1

def segmentMessage
    (state : State) (segment : LineBreakRules.Segment) (ruleName : String)
    (currentColumn currentIndent segmentIndentation : Nat)
    (pendingIndent? tailIndentation? : Option Nat)
    : String :=
  s!"path={segmentPathString state.segmentPath} "
  ++ s!"segment=[{segment.start},{segment.stop}) "
  ++ s!"kind={treeKindString segment.parent} "
  ++ s!"rule={ruleName} "
  ++ s!"currentColumn={currentColumn} "
  ++ s!"currentIndent={currentIndent} "
  ++ s!"segmentIndentation={segmentIndentation} "
  ++ s!"pendingIndent={optionNatString pendingIndent?} "
  ++ s!"tailIndentation={optionNatString tailIndentation?}"

def segmentEntry
    (state : State) (output : String)
    (defaultWhitespace : SyntaxTree.Token → String)
    (segment : LineBreakRules.Segment) (ruleName : String)
    (currentColumn currentIndent segmentIndentation : Nat)
    (pendingIndent? tailIndentation? : Option Nat)
    : Entry :=
  {
    lineNumber := segmentLineNumber output defaultWhitespace segment
    message :=
      segmentMessage state segment ruleName currentColumn currentIndent
        segmentIndentation pendingIndent? tailIndentation?
  }

def State.recordSegment
    (state : State) (output : String)
    (defaultWhitespace : SyntaxTree.Token → String)
    (segment : LineBreakRules.Segment) (ruleName : String)
    (currentColumn currentIndent segmentIndentation : Nat)
    (pendingIndent? tailIndentation? : Option Nat)
    : State :=
  if state.enabled then
    {
      state with
        entries :=
          state.entries
          ++ [segmentEntry state output defaultWhitespace segment ruleName currentColumn
                currentIndent segmentIndentation pendingIndent? tailIndentation?]
    }
  else
    state

def State.pushPath (state : State) (index : Nat) : State :=
  { state with segmentPath := state.segmentPath ++ [index] }

def State.restorePathFrom (state parent : State) : State :=
  { state with segmentPath := parent.segmentPath }

def State.shiftEntriesAfter (state : State) (entryCount lineOffset : Nat) : State :=
  if !state.enabled || lineOffset == 0 then
    state
  else
    {
      state with
        entries :=
          state.entries.take entryCount
          ++ (state.entries.drop entryCount).map
              fun entry => { entry with lineNumber := entry.lineNumber + lineOffset }
    }

def outputLines (formatted : String) : List String :=
  let text :=
    (SpaceRules.normalizeLineEndings formatted).dropEndWhile fun char => char == '\n'
  let text := text.toString
  if text.isEmpty then
    []
  else
    text.splitOn "\n"

def entryLinesForLine (entries : List Entry) (lineNumber : Nat) : List String :=
  entries.filterMap
    fun entry =>
      if entry.lineNumber == lineNumber then
        some s!"  {entry.message}"
      else
        none

def formatLinesAux (entries : List Entry) (lineNumber : Nat) : List String → List String
  | [] => []
  | line :: rest =>
      let current :=
        s!"line {lineNumber} | {line}" :: entryLinesForLine entries lineNumber
      current ++ formatLinesAux entries (lineNumber + 1) rest

def formatEntriesWithOutput (formatted : String) (entries : List Entry) : String :=
  String.intercalate "\n" <| formatLinesAux entries 1 (outputLines formatted)

def State.formatWithOutput (state : State) (formatted : String) : String :=
  formatEntriesWithOutput formatted state.entries

end Trace
end Formatter
end LeanFmt
