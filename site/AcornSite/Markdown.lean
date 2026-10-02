/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSite.Reference

/-! # Markdown rendering of a document

A ported document keeps a Markdown rendering at its former path under `docs/`, so links to
it and readers on GitHub are served before the site is published. The rendering is a
function of the elaborated document: every spliced value appears in it as text, where the
existing lexical document gates still read it.

The rendering is total and refuses what it does not render: a construct outside the cases
below is an error naming the construct, never dropped or approximated. Lists, definition
lists, quotations, mathematics, footnotes and images are not rendered yet.
-/

open Verso Doc Genre

namespace AcornSite.Markdown

/-- Text with each character that could start Markdown markup escaped. -/
def escape (text : String) : String :=
  text.foldl (init := "") fun escaped char =>
    if "\\`*_[]<".contains char then (escaped.push '\\').push char else escaped.push char

/-- A fenced code block. The text may not contain a fence. -/
def fence (language text : String) : Except String String := do
  if text.contains "```" then
    throw "a code block contains a Markdown fence"
  return "```" ++ language ++ "\n" ++ (text.dropEndWhile (· == '\n')).toString ++ "\n```\n"

/-- The Markdown of a `Block.fenced` extension block, from its stored language and text. -/
def fenced : Lean.Json → Except String String
  | .arr #[.str language, .str text] => fence language text
  | data => throw s!"malformed code block data {data.compress}"

/-- Inline content as Markdown. -/
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

/-- A block as Markdown, ending in one newline. -/
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

/-- A part and the parts below it as Markdown: a heading, the blocks and the subparts, each
separated by a blank line. -/
def part (depth : Nat) : Doc.Part Manual → Except String String
  | .mk title _ _ content subParts => do
    let heading := "".pushn '#' (depth + 1) ++ " " ++ String.join (← title.mapM inline).toList ++ "\n"
    let blocks ← content.mapM block
    let below ← subParts.attach.mapM fun ⟨sub, _⟩ => part (depth + 1) sub
    return "\n".intercalate (heading :: blocks.toList ++ below.toList)

/-- The kept Markdown file of a document elaborated from `source`. -/
def page (source : String) (document : Doc.Part Manual) : Except String String := do
  return s!"<!-- Generated from {source} by ./scripts/verify.sh site write. Edit that source, not this file. -->\n\n" ++
    (← part 0 document)

end AcornSite.Markdown
