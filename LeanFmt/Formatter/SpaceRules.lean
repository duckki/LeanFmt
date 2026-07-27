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

def cleanWhitespaceTrivia (text : String) : String :=
  collapseNewlineRuns <| stripWhitespaceBeforeNewlines text

partial def takeLineCommentTriviaAux (reversed : List Char)
    : List Char → List Char × List Char
  | [] => (reversed.reverse, [])
  | chars@('\n' :: _) => (reversed.reverse, chars)
  | char :: rest => takeLineCommentTriviaAux (char :: reversed) rest

partial def takeBlockCommentTriviaAux (depth : Nat) (reversed : List Char)
    : List Char → List Char × List Char
  | [] => (reversed.reverse, [])
  | '/' :: '-' :: rest =>
      takeBlockCommentTriviaAux (depth + 1) ('-' :: '/' :: reversed) rest
  | '-' :: '/' :: rest =>
      let reversed := '/' :: '-' :: reversed
      if depth == 1 then
        (reversed.reverse, rest)
      else
        takeBlockCommentTriviaAux (depth - 1) reversed rest
  | char :: rest => takeBlockCommentTriviaAux depth (char :: reversed) rest

def pushNonemptyString (text : String) (pieces : List String) : List String :=
  if text.isEmpty then pieces else text :: pieces

partial def cleanTriviaAux (outsideReversed : List Char) (piecesReversed : List String)
    : List Char → List String
  | [] =>
      (pushNonemptyString
        (cleanWhitespaceTrivia <| String.ofList outsideReversed.reverse)
        piecesReversed).reverse
  | '-' :: '-' :: rest =>
      let outside := cleanWhitespaceTrivia <| String.ofList outsideReversed.reverse
      let (comment, rest) := takeLineCommentTriviaAux ['-', '-'] rest
      let piecesReversed :=
        pushNonemptyString (String.ofList comment)
        <| pushNonemptyString outside piecesReversed
      cleanTriviaAux [] piecesReversed rest
  | '/' :: '-' :: rest =>
      let outside := cleanWhitespaceTrivia <| String.ofList outsideReversed.reverse
      let (comment, rest) := takeBlockCommentTriviaAux 1 ['-', '/'] rest
      let piecesReversed :=
        pushNonemptyString (String.ofList comment)
        <| pushNonemptyString outside piecesReversed
      cleanTriviaAux [] piecesReversed rest
  | char :: rest => cleanTriviaAux (char :: outsideReversed) piecesReversed rest

def cleanTrivia (text : String) : String :=
  String.join <| cleanTriviaAux [] [] (normalizeLineEndings text).toList

def stripLeadingHorizontalWhitespace (line : String) : String :=
  (line.dropWhile isHorizontalWhitespace).toString

def containsSubstring (text needle : String) : Bool :=
  text.contains needle

partial def blockCommentDepthAfterChars : Nat → List Char → Nat
  | depth, '/' :: '-' :: rest =>
      blockCommentDepthAfterChars (depth + 1) rest
  | depth, '-' :: '/' :: rest =>
      blockCommentDepthAfterChars (depth - 1) rest
  | depth, _ :: rest => blockCommentDepthAfterChars depth rest
  | depth, [] => depth

def blockCommentDepthAfterLine (depth : Nat) (line : String) : Nat :=
  if depth == 0 then
    let stripped := stripLeadingHorizontalWhitespace line
    if stripped.startsWith "/-" then
      blockCommentDepthAfterChars 0 stripped.toList
    else
      0
  else
    blockCommentDepthAfterChars depth line.toList

def lineOpensBlockComment (line : String) : Bool :=
  0 < blockCommentDepthAfterLine 0 line

def reindentCommentLine (blockCommentDepth : Nat) (line indent : String) : String :=
  if 0 < blockCommentDepth then
    line
  else
    let stripped := stripLeadingHorizontalWhitespace line
    if stripped.isEmpty then "" else indent ++ stripped

def reindentCommentLines (indent : String) : Nat → List String → List String
  | _, [] => []
  | blockCommentDepth, line :: rest =>
      let adjusted :=
        if rest.isEmpty
            && blockCommentDepth == 0
            && (stripLeadingHorizontalWhitespace line).isEmpty then
          indent
        else
          reindentCommentLine blockCommentDepth line indent
      let blockCommentDepth := blockCommentDepthAfterLine blockCommentDepth line
      adjusted :: reindentCommentLines indent blockCommentDepth rest

def reindentCommentTrivia (text indent : String) : String :=
  match (cleanTrivia text).splitOn "\n" with
  | [] => ""
  | firstLine :: rest =>
      String.intercalate "\n"
      <| firstLine
          :: reindentCommentLines indent (blockCommentDepthAfterLine 0 firstLine) rest

def reindentableCommentWidth (text : String) : Nat :=
  let rec loop (blockCommentDepth maximum : Nat) : List String → Nat
    | [] => maximum
    | line :: rest =>
        let stripped := stripLeadingHorizontalWhitespace line
        let maximum :=
          if blockCommentDepth == 0 && !stripped.isEmpty then
            max maximum stripped.length
          else
            maximum
        loop (blockCommentDepthAfterLine blockCommentDepth line) maximum rest
  match (cleanTrivia text).splitOn "\n" with
  | [] | [_] => 0
  | firstLine :: rest =>
      loop (blockCommentDepthAfterLine 0 firstLine) 0 rest

def sourceCommentIndentCapacity? (text : String) (lineWidth : Nat) : Option Nat :=
  let rec loop (blockCommentDepth capacity : Nat) (found : Bool)
      : List String → Option Nat
    | [] => if found then some capacity else none
    | line :: rest =>
        let stripped := stripLeadingHorizontalWhitespace line
        let blockCommentDepthAfter := blockCommentDepthAfterLine blockCommentDepth line
        if blockCommentDepth == 0 && !stripped.isEmpty then
          let sourceIndent := line.length - stripped.length
          if lineWidth < sourceIndent + stripped.length then
            none
          else
            loop blockCommentDepthAfter
              (min capacity (lineWidth - stripped.length)) true rest
        else
          loop blockCommentDepthAfter capacity found rest
  match (cleanTrivia text).splitOn "\n" with
  | [] | [_] => none
  | firstLine :: rest =>
      loop (blockCommentDepthAfterLine 0 firstLine) lineWidth false rest

def commentIndentForWidth (text : String) (desiredIndent lineWidth : Nat) : Nat :=
  let contentWidth := reindentableCommentWidth text
  if contentWidth + desiredIndent <= lineWidth then
    desiredIndent
  else
    match sourceCommentIndentCapacity? text lineWidth with
    | some capacity => min desiredIndent capacity
    | none => desiredIndent

def standaloneSourceCommentIndent? (text : String) : Option Nat :=
  match (normalizeLineEndings text).splitOn "\n" with
  | [] | [_] => none
  | _ :: rest =>
      rest.findSome?
        fun line =>
          let stripped := stripLeadingHorizontalWhitespace line
          if stripped.startsWith "--" || stripped.startsWith "/-" then
            some (line.length - stripped.length)
          else
            none

def commentTriviaForBreakWithFollowingIndent (text commentIndent followingIndent : String)
    : String :=
  let adjusted := reindentCommentTrivia text commentIndent
  match (normalizeLineEndings adjusted).splitOn "\n" |>.reverse with
  | lastLine :: rest =>
      if (stripLeadingHorizontalWhitespace lastLine).isEmpty then
        String.intercalate "\n" <| (followingIndent :: rest).reverse
      else
        adjusted ++ "\n" ++ followingIndent
  | [] => "\n" ++ followingIndent

def commentTriviaForBreak (text indent : String) : String :=
  commentTriviaForBreakWithFollowingIndent text indent indent

def cleanFinalTrivia (text : String) : String :=
  cleanTrivia text

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
  stringEndsWithAny lexeme ["(", "[", "⟨", "⟪", "⦃"]

def allowsHorizontalAlignmentAfterToken (lexeme : String) : Bool :=
  lexeme != "(" && lexeme != ":"

def isTrailingSeparatorToken (lexeme : String) : Bool :=
  stringIn lexeme [",", ",*", ";"]

def isClosingDelimiterToken (lexeme : String) : Bool :=
  stringStartsWithAny lexeme [")", "]", "⟩", "⟫", "⦄"]

def noSpaceBeforeToken (lexeme : String) : Bool :=
  isTrailingSeparatorToken lexeme || isClosingDelimiterToken lexeme

def isPlainIdentifierTail (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '\''

def isDelimiterCloserToken (lexeme : String) : Bool :=
  stringStartsWithAny lexeme [")", "]", "}", "⟩", "⟫", "⦄"]

def isOperatorLikeToken (lexeme : String) : Bool :=
  match lexeme.toList.reverse with
  | [] => false
  | last :: _ =>
      !isPlainIdentifierTail last
      && last != '"'
      && !isTrailingSeparatorToken lexeme
      && !isDelimiterCloserToken lexeme

def preservesSourceSpaceBeforeClosingToken (left right : SyntaxTree.Token) : Bool :=
  isClosingDelimiterToken right.lexeme && isOperatorLikeToken left.lexeme

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
  right.lexeme == "(" || right.lexeme == "[" || right.lexeme == "?" || right.lexeme == "%"

def preservesTightInterpolationSpacing (left right : SyntaxTree.Token) : Bool :=
  left.lexeme == "s!"
  || (left.lexeme != "{" && left.lexeme.endsWith "{")
  || (right.lexeme != "}" && right.lexeme.startsWith "}")

def preservesTightQuotedNameSpacing (left right : SyntaxTree.Token) : Bool :=
  left.lexeme == "`" && right.lexeme == "`"

def spaceBetweenTokens (left right : SyntaxTree.Token) : String :=
  if left.lexeme.isEmpty || right.lexeme.isEmpty then
    ""
  else if left.lexeme == "!" then
    if right.span.start == left.span.stop then "" else " "
  else if noSpaceAfterToken left.lexeme
          || noSpaceBeforeToken right.lexeme
          || preservesTightDotSpacing left right
          || preservesTightInterpolationSpacing left right
          || preservesTightQuotedNameSpacing left right then
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
  else if preservesSourceSpaceBeforeClosingToken left right then
    " "
  else
    spaceBetweenTokens left right

end SpaceRules
end Formatter
end LeanFmt
