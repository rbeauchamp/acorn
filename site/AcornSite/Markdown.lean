import AcornSite.Reference

open Verso Doc Genre

namespace AcornSite.Markdown

def escape (text : String) : String :=
  text.foldl (init := "") fun escaped char =>
    if "\\`*_[]<".contains char then (escaped.push '\\').push char else escaped.push char

def fence (language text : String) : Except String String := do
  if text.contains "```" then
    throw "a code block contains a Markdown fence"
  return "```" ++ language ++ "\n" ++ (text.dropEndWhile (· == '\n')).toString ++ "\n```\n"

def fenced : Lean.Json → Except String String
  | .arr #[.str language, .str text] => fence language text
  | data => throw s!"malformed code block data {data.compress}"

def inline : Doc.Inline Manual → Except String String
  | .text string => pure (escape string)
  | .linebreak string => pure string
  | .code string =>
    if string.contains '`' then throw s!"inline code contains a backtick: {string}"
    else pure ("`" ++ string ++ "`")
  | .emph content => do
    return "*" ++ String.join (← content.attach.mapM fun ⟨item, _⟩ => inline item).toList ++ "*"
  | .bold content => do
    return "**" ++ String.join (← content.attach.mapM fun ⟨item, _⟩ => inline item).toList ++ "**"
  | .link content url => do
    return "[" ++ String.join (← content.attach.mapM fun ⟨item, _⟩ => inline item).toList ++
      "](" ++ url ++ ")"
  | .concat content => do
    return String.join (← content.attach.mapM fun ⟨item, _⟩ => inline item).toList
  | .math .. => throw "mathematics has no Markdown rendering here"
  | .footnote .. => throw "a footnote has no Markdown rendering here"
  | .image .. => throw "an image has no Markdown rendering here"
  | .other container _ => throw s!"inline extension {container.name} has no Markdown rendering"

def block : Doc.Block Manual → Except String String
  | .para contents => do
    let text := String.join (← contents.mapM inline).toList
    return (text.dropEndWhile (· == '\n')).toString ++ "\n"
  | .code content => fence "" content
  | .concat content => do
    return "\n".intercalate (← content.attach.mapM fun ⟨item, _⟩ => block item).toList
  | .other container _ =>
    if container.name == ``AcornSite.Block.fenced then fenced container.data
    else throw s!"block extension {container.name} has no Markdown rendering"
  | .ul .. => throw "a list has no Markdown rendering here"
  | .ol .. => throw "a numbered list has no Markdown rendering here"
  | .dl .. => throw "a definition list has no Markdown rendering here"
  | .blockquote .. => throw "a quotation has no Markdown rendering here"

def part (depth : Nat) : Doc.Part Manual → Except String String
  | .mk title _ _ content subParts => do
    let heading := "".pushn '#' (depth + 1) ++ " " ++ String.join (← title.mapM inline).toList ++ "\n"
    let blocks ← content.mapM block
    let below ← subParts.attach.mapM fun ⟨sub, _⟩ => part (depth + 1) sub
    return "\n".intercalate (heading :: blocks.toList ++ below.toList)

def page (source : String) (document : Doc.Part Manual) : Except String String := do
  return s!"<!-- Generated from {source} by ./scripts/verify.sh site write. Edit that source, not this file. -->\n\n" ++
    (← part 0 document)

end AcornSite.Markdown
