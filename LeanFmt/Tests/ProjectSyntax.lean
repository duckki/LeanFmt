import Lean

syntax (name := projectSyntax) "project_syntax" : term

namespace BigOperators

syntax bigOpBinder := ident (" ∈ " term)?
syntax bigOpBinders := bigOpBinder
syntax (name := bigsum) "∑ " bigOpBinders ", " term:67 : term
syntax (name := projectIntegral) "∫ " ident " in " term ", " term " ∂" term : term

end BigOperators

syntax (name := projectIndexedSup) "⨆ " ident " : " term ", " term : term
syntax (name := projectModifiedForall) "∀ᵉ " ident " ∈ " term ", " term : term
