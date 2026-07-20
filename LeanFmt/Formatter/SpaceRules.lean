import LeanFmt.SyntaxTree

namespace LeanFmt
namespace Formatter
namespace SpaceRules

def maxPreservedNewlines : Nat :=
  2

def isHorizontalWhitespace : Char → Bool
  | ' ' => true
  | '\t' => true
  | _ => false

def normalizeLineEndings (text : String) : String :=
  (text.replace "\r\n" "\n").replace "\r" "\n"

def stripLineEndWhitespace (line : String) : String :=
  (line.dropEndWhile isHorizontalWhitespace).toString

def stripTrailingWhitespace (text : String) : String :=
  String.intercalate "\n"
  <| (normalizeLineEndings text).splitOn "\n" |>.map stripLineEndWhitespace

def stripWhitespaceBeforeNewlines (text : String) : String :=
  let lines := (normalizeLineEndings text).splitOn "\n"
  match lines.reverse with
  | [] => ""
  | last :: reversedPrefix =>
      String.intercalate "\n"
      <| (reversedPrefix.reverse.map stripLineEndWhitespace) ++ [last]

def collapseNewlineRunsAux : List Char → Nat → List Char → List Char
  | [], _, acc => acc.reverse
  | char :: rest, newlineCount, acc =>
      if char == '\n' then
        if newlineCount < maxPreservedNewlines then
          collapseNewlineRunsAux rest (newlineCount + 1) (char :: acc)
        else
          collapseNewlineRunsAux rest (newlineCount + 1) acc
      else
        collapseNewlineRunsAux rest 0 (char :: acc)

def collapseNewlineRuns (text : String) : String :=
  String.ofList <| collapseNewlineRunsAux text.toList 0 []

def cleanTrivia (text : String) : String :=
  collapseNewlineRuns <| stripWhitespaceBeforeNewlines text

def stripLeadingHorizontalWhitespace (line : String) : String :=
  (line.dropWhile isHorizontalWhitespace).toString

def containsSubstring (text needle : String) : Bool :=
  text.contains needle

def lineOpensBlockComment (line : String) : Bool :=
  let stripped := stripLeadingHorizontalWhitespace line
  stripped.startsWith "/-" && !containsSubstring stripped "-/"

def lineClosesBlockComment (line : String) : Bool :=
  containsSubstring line "-/"

def reindentCommentLine (insideBlock : Bool) (line indent : String) : String :=
  if insideBlock then
    line
  else
    let stripped := stripLeadingHorizontalWhitespace line
    if stripped.isEmpty then indent else indent ++ stripped

def reindentCommentLines (indent : String) : Bool → List String → List String
  | _, [] => []
  | insideBlock, line :: rest =>
      let adjusted := reindentCommentLine insideBlock line indent
      let insideBlock :=
        if insideBlock then
          !lineClosesBlockComment line
        else
          lineOpensBlockComment line
      adjusted :: reindentCommentLines indent insideBlock rest

def reindentCommentTrivia (text indent : String) : String :=
  match (cleanTrivia text).splitOn "\n" with
  | [] => ""
  | firstLine :: rest =>
      String.intercalate "\n"
      <| firstLine :: reindentCommentLines indent (lineOpensBlockComment firstLine) rest

def commentTriviaForBreak (text indent : String) : String :=
  let adjusted := reindentCommentTrivia text indent
  match (normalizeLineEndings adjusted).splitOn "\n" |>.reverse with
  | lastLine :: _ =>
      if (stripLeadingHorizontalWhitespace lastLine).isEmpty then
        adjusted
      else
        adjusted ++ "\n" ++ indent
  | [] => "\n" ++ indent

def cleanFinalTrivia (text : String) : String :=
  collapseNewlineRuns <| stripTrailingWhitespace text

def isFinalWhitespace : Char → Bool
  | '\n' => true
  | char => isHorizontalWhitespace char

def normalizeFinalNewline (text : String) : String :=
  let normalized := normalizeLineEndings text
  let withoutFinalWhitespace := (normalized.dropEndWhile isFinalWhitespace).toString
  if withoutFinalWhitespace.isEmpty then
    ""
  else
    withoutFinalWhitespace ++ "\n"

def hasLineStructure (text : String) : Bool :=
  text.contains '\n'

def hasCommentStart (text : String) : Bool :=
  containsSubstring text "--" || containsSubstring text "/-"

def isCommentLexeme (text : String) : Bool :=
  text.startsWith "--" || text.startsWith "/-" || containsSubstring text "-/"

def hasOnlyHorizontalTrivia (text : String) : Bool :=
  !text.isEmpty && !hasLineStructure text && !hasCommentStart text

def stringIn (value : String) (values : List String) : Bool :=
  values.any fun candidate => candidate == value

def stringEndsWithAny (value : String) (suffixes : List String) : Bool :=
  suffixes.any fun suffix => value.endsWith suffix

def stringStartsWithAny (value : String) (prefixes : List String) : Bool :=
  prefixes.any fun candidate => value.startsWith candidate

def noSpaceAfterToken (lexeme : String) : Bool :=
  lexeme == "@" || stringEndsWithAny lexeme ["(", "[", "⟨", "⟪", "⦃"]

def charCodeIn (char : Char) (lower upper : Nat) : Bool :=
  lower <= char.toNat && char.toNat <= upper

def isPostfixMarkerStart (char : Char) : Bool :=
  charCodeIn char 0x2070 0x209F
  || charCodeIn char 0x1D00 0x1D7F
  || charCodeIn char 0x1D80 0x1DBF

def isPostfixMarkerChar (char : Char) : Bool :=
  isPostfixMarkerStart char
  || char.toNat == 0x00B9
  || char.toNat == 0x00B2
  || char.toNat == 0x00B3

def isPostfixMarkerToken (lexeme : String) : Bool :=
  match lexeme.toList with
  | [] => false
  | chars => chars.all isPostfixMarkerChar

def noSpaceBeforeToken (lexeme : String) : Bool :=
  stringIn lexeme [",", ",*", ";"]
  || stringStartsWithAny lexeme [")", "]", "⟩", "⟫", "⦄"]
  || isPostfixMarkerToken lexeme

def preservesTightBraceSpacing (left right : SyntaxTree.Token) : Bool :=
  left.lexeme == "{" || right.lexeme == "}"

def dotPrefixCanAttach (lexeme : String) : Bool :=
  match lexeme.toList.reverse with
  | '.' :: previous :: _ =>
      previous.isAlphanum || previous == '_' || previous == '\'' || previous == '»'
  | _ => false

def preservesTightDotSpacing (left _right : SyntaxTree.Token) : Bool :=
  left.lexeme == "."
  || left.lexeme == "|>."
  || (left.lexeme.endsWith "." && left.lexeme != ".." && dotPrefixCanAttach left.lexeme)

def preservesTightPostfixSpacing (right : SyntaxTree.Token) : Bool :=
  right.lexeme == "[" || right.lexeme == "?"

def preservesTightInterpolationSpacing (left right : SyntaxTree.Token) : Bool :=
  left.lexeme == "s!"
  || (left.lexeme != "{" && left.lexeme.endsWith "{")
  || (right.lexeme != "}" && right.lexeme.startsWith "}")

def spaceBetweenTokens (left right : SyntaxTree.Token) : String :=
  if left.lexeme.isEmpty || right.lexeme.isEmpty then
    ""
  else if left.lexeme == "!" then
    if right.span.start == left.span.stop then "" else " "
  else if noSpaceAfterToken left.lexeme
          || noSpaceBeforeToken right.lexeme
          || preservesTightDotSpacing left right
          || preservesTightInterpolationSpacing left right then
    ""
  else
    " "

def interTokenWhitespace
    (source : String) (left right : SyntaxTree.Token) (preserveLines : Bool := true)
    : String :=
  let trivia := SyntaxTree.sourceText source left.span.stop right.span.start
  if hasCommentStart trivia then
    cleanTrivia trivia
  else if (isCommentLexeme left.lexeme || isCommentLexeme right.lexeme)
          && hasLineStructure trivia then
    cleanTrivia trivia
  else if preserveLines && hasLineStructure trivia then
    cleanTrivia trivia
  else if trivia.isEmpty then
    ""
  else
    spaceBetweenTokens left right

end SpaceRules
end Formatter
end LeanFmt
