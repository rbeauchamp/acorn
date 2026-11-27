import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual

namespace AcornSite

block_extension Block.fenced (language shown : String) where
  data := Json.arr #[.str language, .str shown]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    some <| fun _ _ _ data _ => do
      let .arr #[.str language, .str shown] := data
        | Verso.reportError s!"Expected a language and a text, got {data}"; pure .empty
      return html%{<pre><code class={"language-" ++ language}>{shown}</code></pre>}

@[role]
def decl : RoleExpanderOf Unit
  | (), inlines => do
    let code ← Lean.Doc.onlyCode inlines
    let text := code.getVersoCode
    let written := text.toName
    let resolved ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom code written)
    unless resolved == written do
      throwErrorAt code "write the full name {resolved}"
    ``(Verso.Doc.Inline.code $(quote text))

@[role]
def leanModule : RoleExpanderOf Unit
  | (), inlines => do
    let code ← Lean.Doc.onlyCode inlines
    let text := code.getVersoCode
    let written := text.toName
    unless written.toString == text && ((← getEnv).getModuleIdx? written).isSome do
      throwErrorAt code "{text} is not a module this document imports"
    ``(Verso.Doc.Inline.code $(quote text))

@[role]
def splice : RoleExpanderOf Unit
  | (), inlines => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term (← Lean.Doc.onlyCode inlines)⟩
    ``(Verso.Doc.Inline.text ($term : String))

@[role]
def spliceCode : RoleExpanderOf Unit
  | (), inlines => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term (← Lean.Doc.onlyCode inlines)⟩
    ``(Verso.Doc.Inline.code ($term : String))

@[code_block]
def sh : CodeBlockExpanderOf Unit
  | (), text => ``(Verso.Doc.Block.other (Block.fenced "sh" $(quote text.getVersoCodeBlock)) #[])

structure SplicedArgs where
  language : Ident

instance : FromArgs SplicedArgs DocElabM where
  fromArgs := SplicedArgs.mk <$> .positional `language .ident

@[code_block]
def spliced : CodeBlockExpanderOf SplicedArgs
  | { language }, text => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term text⟩
    ``(Verso.Doc.Block.other (Block.fenced $(quote language.getId.toString) ($term : String)) #[])

structure StatementArgs where
  name : Ident

instance : FromArgs StatementArgs DocElabM where
  fromArgs := StatementArgs.mk <$> .positional `name .ident

@[block_command]
def statement : BlockCommandOf StatementArgs
  | { name } => do
    let resolved ← realizeGlobalConstNoOverloadWithInfo name
    unless resolved == name.getId do
      throwErrorAt name "write the full name {resolved}"
    unless (← getConstInfo resolved) matches .thmInfo _ do
      throwErrorAt name "{resolved} is not a theorem"
    let signature ← PrettyPrinter.ppSignature resolved
    let text := "theorem " ++ signature.fmt.pretty 100 ++ "\n"
    ``(Verso.Doc.Block.other (Block.fenced "lean" $(quote text)) #[])

end AcornSite
