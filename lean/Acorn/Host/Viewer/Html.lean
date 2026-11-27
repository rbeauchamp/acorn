import Init

namespace Acorn.Host.Viewer.Html

inductive VoidTag where
  | metaTag
  | link
  | input
  deriving DecidableEq, BEq

inductive NormalTag where
  | html
  | head
  | title
  | body
  | section
  | div
  | span
  | p
  | h1
  | h2
  | h3
  | strong
  | b
  | sub
  | sup
  | pre
  | a
  | form
  | button
  | progress
  | details
  | summary
  | table
  | thead
  | tbody
  | tr
  | th
  | td
  | img
  | svg
  | rect
  | circle
  | line
  | polyline
  | polygon
  | text
  deriving DecidableEq, BEq

inductive AttrName where
  | lang
  | charset
  | name
  | content
  | httpEquiv
  | rel
  | href
  | id
  | cls
  | title
  | ariaLabel
  | role
  | action
  | method
  | type
  | value
  | min
  | max
  | disabled
  | openAttr
  | width
  | height
  | viewBox
  | x
  | y
  | x1
  | y1
  | x2
  | y2
  | cx
  | cy
  | r
  | points
  | fill
  | fillOpacity
  | stroke
  | strokeWidth
  | strokeDasharray
  | strokeOpacity
  | fontSize
  | fontWeight
  | textAnchor
  | src
  | alt
  deriving DecidableEq, BEq

def VoidTag.render : VoidTag → String
  | .metaTag => "meta"
  | .link => "link"
  | .input => "input"

def NormalTag.render : NormalTag → String
  | .html => "html"
  | .head => "head"
  | .title => "title"
  | .body => "body"
  | .section => "section"
  | .div => "div"
  | .span => "span"
  | .p => "p"
  | .h1 => "h1"
  | .h2 => "h2"
  | .h3 => "h3"
  | .strong => "strong"
  | .b => "b"
  | .sub => "sub"
  | .sup => "sup"
  | .pre => "pre"
  | .a => "a"
  | .form => "form"
  | .button => "button"
  | .progress => "progress"
  | .details => "details"
  | .summary => "summary"
  | .table => "table"
  | .thead => "thead"
  | .tbody => "tbody"
  | .tr => "tr"
  | .th => "th"
  | .td => "td"
  | .img => "img"
  | .svg => "svg"
  | .rect => "rect"
  | .circle => "circle"
  | .line => "line"
  | .polyline => "polyline"
  | .polygon => "polygon"
  | .text => "text"

def AttrName.render : AttrName → String
  | .lang => "lang"
  | .charset => "charset"
  | .name => "name"
  | .content => "content"
  | .httpEquiv => "http-equiv"
  | .rel => "rel"
  | .href => "href"
  | .id => "id"
  | .cls => "class"
  | .title => "title"
  | .ariaLabel => "aria-label"
  | .role => "role"
  | .action => "action"
  | .method => "method"
  | .type => "type"
  | .value => "value"
  | .min => "min"
  | .max => "max"
  | .disabled => "disabled"
  | .openAttr => "open"
  | .width => "width"
  | .height => "height"
  | .viewBox => "viewBox"
  | .x => "x"
  | .y => "y"
  | .x1 => "x1"
  | .y1 => "y1"
  | .x2 => "x2"
  | .y2 => "y2"
  | .cx => "cx"
  | .cy => "cy"
  | .r => "r"
  | .points => "points"
  | .fill => "fill"
  | .fillOpacity => "fill-opacity"
  | .stroke => "stroke"
  | .strokeWidth => "stroke-width"
  | .strokeDasharray => "stroke-dasharray"
  | .strokeOpacity => "stroke-opacity"
  | .fontSize => "font-size"
  | .fontWeight => "font-weight"
  | .textAnchor => "text-anchor"
  | .src => "src"
  | .alt => "alt"

def contentSecurityPolicy : String :=
  "default-src 'self'; script-src 'none'; style-src 'self'; img-src 'self'; object-src 'none'; base-uri 'none'; form-action 'self'; frame-ancestors 'none'"

def escapeTextChar (c : Char) : List Char :=
  if c == '&' then ['&', 'a', 'm', 'p', ';']
  else if c == '<' then ['&', 'l', 't', ';']
  else if c == '>' then ['&', 'g', 't', ';']
  else [c]

def escapeAttrChar (c : Char) : List Char :=
  if c == '&' then ['&', 'a', 'm', 'p', ';']
  else if c == '<' then ['&', 'l', 't', ';']
  else if c == '>' then ['&', 'g', 't', ';']
  else if c == '"' then ['&', 'q', 'u', 'o', 't', ';']
  else if c == '\'' then ['&', '#', '3', '9', ';']
  else [c]

def escapeTextChars (cs : List Char) : List Char :=
  cs.flatMap escapeTextChar

def escapeAttrChars (cs : List Char) : List Char :=
  cs.flatMap escapeAttrChar

inductive Attr where
  | kv (attrName : AttrName) (value : String)
  | flag (attrName : AttrName)
  deriving DecidableEq, BEq

def Attr.renderChars : Attr → List Char
  | .kv attrName value =>
    ' ' :: attrName.render.toList ++ ['=', '"'] ++ escapeAttrChars value.toList ++ ['"']
  | .flag attrName => ' ' :: attrName.render.toList

def renderAttrsChars (attrs : List Attr) : List Char :=
  attrs.flatMap Attr.renderChars

inductive Node where
  | empty
  | text (content : String)
  | void (tag : VoidTag) (attrs : List Attr)
  | elem (tag : NormalTag) (attrs : List Attr) (children : List Node)

mutual
  def Node.renderChars : Node → List Char
    | .empty => []
    | .text content => escapeTextChars content.toList
    | .void tag attrs => '<' :: tag.render.toList ++ renderAttrsChars attrs ++ ['>']
    | .elem tag attrs children =>
      '<' :: tag.render.toList ++ renderAttrsChars attrs ++ ['>'] ++
        renderNodesChars children ++ ['<', '/'] ++ tag.render.toList ++ ['>']

  def renderNodesChars : List Node → List Char
    | [] => []
    | node :: rest => node.renderChars ++ renderNodesChars rest
end

def Node.render (node : Node) : String :=
  String.ofList node.renderChars

structure Document where
  lang : String := "en"
  head : List Node
  body : List Node

def Document.renderChars (doc : Document) : List Char :=
  "<!DOCTYPE html>".toList ++
    (Node.elem .html [.kv .lang doc.lang]
      [.elem .head [] doc.head, .elem .body [] doc.body]).renderChars

def Document.render (doc : Document) : String :=
  String.ofList doc.renderChars

def el (tag : NormalTag) (attrs : List Attr := []) (children : List Node := []) : Node :=
  .elem tag attrs children

def vd (tag : VoidTag) (attrs : List Attr := []) : Node :=
  .void tag attrs

def txt (content : String) : Node :=
  .text content

def kv (attrName : AttrName) (value : String) : Attr :=
  .kv attrName value

def flg (attrName : AttrName) : Attr :=
  .flag attrName

def whenNode (cond : Bool) (node : Node) : Node :=
  if cond then node else .empty

def NoScTag (cs : List Char) : Prop :=
  ∀ before after, cs = before ++ '<' :: after →
    ∃ c₁ c₂ rest, after = c₁ :: c₂ :: rest ∧ (c₁.toLower ≠ 's' ∨ c₂.toLower ≠ 'c')

def scriptPrefix : List Char := ['<', 's', 'c', 'r', 'i', 'p', 't']

def ContainsScriptTag (cs : List Char) : Prop :=
  ∃ before after, cs = before ++ after ∧
    (after.take 7).map Char.toLower = scriptPrefix

theorem NoScTag.not_containsScriptTag {cs : List Char} (safe : NoScTag cs) :
    ¬ ContainsScriptTag cs := by
  rintro ⟨before, after, hEq, hPref⟩
  cases after with
  | nil => simp [scriptPrefix] at hPref
  | cons c0 tail =>
    simp only [List.take_succ_cons, List.map_cons, scriptPrefix, List.cons.injEq] at hPref
    obtain ⟨h0, hTail⟩ := hPref
    have hLt : c0 = '<' := by
      have hDec : ∀ c : Char, c.toLower = '<' → c = '<' := by
        intro c hc
        unfold Char.toLower at hc
        split at hc
        · rename_i hUpper
          have hVal : c.val + 32 = 60 := by
            have := congrArg Char.val hc
            simpa [Char.ofNat] using this
          have hNat := congrArg UInt32.toNat hVal
          have hGe : 65 ≤ c.val.toNat := hUpper.1
          have hLe : c.val.toNat ≤ 90 := hUpper.2
          rw [UInt32.toNat_add] at hNat
          change (c.val.toNat + 32) % 4294967296 = 60 at hNat
          omega
        · exact hc
      exact hDec c0 h0
    subst hLt
    obtain ⟨c1, c2, rest, hTailEq, hDiff⟩ := safe before tail hEq
    subst hTailEq
    simp only [List.take_succ_cons, List.map_cons, List.cons.injEq] at hTail
    rcases hDiff with h1 | h2
    · exact h1 hTail.1
    · exact h2 hTail.2.1

theorem NoScTag.of_no_lt {cs : List Char} (noLt : '<' ∉ cs) : NoScTag cs := by
  intro before after hEq
  exfalso
  apply noLt
  rw [hEq]
  simp

private theorem append_cons_split {α : Type} {xs ys before after : List α} {x : α}
    (h : xs ++ ys = before ++ x :: after) :
    (∃ r, xs = before ++ x :: r ∧ after = r ++ ys) ∨
      (∃ l, ys = l ++ x :: after ∧ before = xs ++ l) := by
  induction xs generalizing before with
  | nil =>
    right
    exact ⟨before, by simpa using h, rfl⟩
  | cons head tail ih =>
    cases before with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, hTail⟩ := h
      left
      exact ⟨tail, rfl, hTail.symm⟩
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, hTail⟩ := h
      rcases ih hTail with ⟨r, hXs, hAfter⟩ | ⟨l, hYs, hBefore⟩
      · left
        exact ⟨r, by simp [hXs], hAfter⟩
      · right
        exact ⟨l, hYs, by simp [hBefore]⟩

theorem NoScTag.append {xs ys : List Char} (hxs : NoScTag xs) (hys : NoScTag ys) :
    NoScTag (xs ++ ys) := by
  intro before after hEq
  rcases append_cons_split hEq with ⟨r, hXs, hAfter⟩ | ⟨l, hYs, _⟩
  · obtain ⟨c1, c2, rest, hR, hDiff⟩ := hxs before r hXs
    refine ⟨c1, c2, rest ++ ys, ?_, hDiff⟩
    rw [hAfter, hR]
    rfl
  · exact hys l after hYs

private theorem escapeTextChar_no_lt (c : Char) : '<' ∉ escapeTextChar c := by
  unfold escapeTextChar
  by_cases h1 : c == '&'
  · simp [h1]
  · by_cases h2 : c == '<'
    · simp [h1, h2]
    · by_cases h3 : c == '>'
      · simp [h1, h2, h3]
      · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
        intro hEq
        subst hEq
        exact h2 rfl

private theorem escapeAttrChar_no_lt (c : Char) : '<' ∉ escapeAttrChar c := by
  unfold escapeAttrChar
  by_cases h1 : c == '&'
  · simp [h1]
  · by_cases h2 : c == '<'
    · simp [h1, h2]
    · by_cases h3 : c == '>'
      · simp [h1, h2, h3]
      · by_cases h4 : c == '"'
        · simp [h1, h2, h3, h4]
        · by_cases h5 : c == '\''
          · simp [h1, h2, h3, h4, h5]
          · simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
            intro hEq
            subst hEq
            exact h2 rfl

private theorem escapeAttrChar_no_quote (c : Char) : '"' ∉ escapeAttrChar c := by
  unfold escapeAttrChar
  by_cases h1 : c == '&'
  · simp [h1]
  · by_cases h2 : c == '<'
    · simp [h1, h2]
    · by_cases h3 : c == '>'
      · simp [h1, h2, h3]
      · by_cases h4 : c == '"'
        · simp [h1, h2, h3, h4]
        · by_cases h5 : c == '\''
          · simp [h1, h2, h3, h4, h5]
          · simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte, List.mem_singleton]
            intro hEq
            subst hEq
            exact h4 rfl

theorem escapeTextChars_no_lt (cs : List Char) : '<' ∉ escapeTextChars cs := by
  intro hMem
  rw [escapeTextChars, List.mem_flatMap] at hMem
  obtain ⟨c, _, hIn⟩ := hMem
  exact escapeTextChar_no_lt c hIn

theorem escapeAttrChars_no_lt (cs : List Char) : '<' ∉ escapeAttrChars cs := by
  intro hMem
  rw [escapeAttrChars, List.mem_flatMap] at hMem
  obtain ⟨c, _, hIn⟩ := hMem
  exact escapeAttrChar_no_lt c hIn

theorem escapeAttrChars_no_quote (cs : List Char) : '"' ∉ escapeAttrChars cs := by
  intro hMem
  rw [escapeAttrChars, List.mem_flatMap] at hMem
  obtain ⟨c, _, hIn⟩ := hMem
  exact escapeAttrChar_no_quote c hIn

theorem AttrName.render_no_lt (attrName : AttrName) : '<' ∉ attrName.render.toList := by
  cases attrName <;> decide

theorem AttrName.no_event_handler (attrName : AttrName) :
    ¬(['o', 'n'].isPrefixOf (attrName.render.toList.map Char.toLower)) := by
  cases attrName <;> decide

private theorem Attr.renderChars_no_lt (attr : Attr) : '<' ∉ attr.renderChars := by
  cases attr with
  | kv attrName value =>
    simp [Attr.renderChars, AttrName.render_no_lt, escapeAttrChars_no_lt]
  | flag attrName =>
    simp [Attr.renderChars, AttrName.render_no_lt]

private theorem renderAttrsChars_no_lt (attrs : List Attr) : '<' ∉ renderAttrsChars attrs := by
  intro hMem
  rw [renderAttrsChars, List.mem_flatMap] at hMem
  obtain ⟨attr, _, hIn⟩ := hMem
  exact Attr.renderChars_no_lt attr hIn

private def tagStartsSafe (cs : List Char) : Bool :=
  match cs with
  | c1 :: c2 :: _ => c1.toLower != 's' || c2.toLower != 'c'
  | [c1] => c1.toLower != 's'
  | [] => false

private theorem VoidTag.render_safe (tag : VoidTag) :
    '<' ∉ tag.render.toList ∧ tagStartsSafe tag.render.toList = true := by
  cases tag <;> decide

private theorem NormalTag.render_safe (tag : NormalTag) :
    '<' ∉ tag.render.toList ∧ tagStartsSafe tag.render.toList = true := by
  cases tag <;> decide

private theorem openTag_noScTag (tagChars tailChars : List Char)
    (hNoLtTag : '<' ∉ tagChars) (hSafeTag : tagStartsSafe tagChars = true)
    (hNoLtTail : '<' ∉ tailChars) (hNonEmptyTail : tailChars ≠ []) :
    NoScTag ('<' :: tagChars ++ tailChars) := by
  intro before after hEq
  cases before with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hEq
    obtain ⟨_, hAfter⟩ := hEq
    cases hTag : tagChars with
    | nil => simp [tagStartsSafe, hTag] at hSafeTag
    | cons c1 rest1 =>
      cases rest1 with
      | nil =>
        cases hTail : tailChars with
        | nil => exact absurd hTail hNonEmptyTail
        | cons c2 rest2 =>
          simp only [tagStartsSafe, hTag, bne_iff_ne, ne_eq] at hSafeTag
          refine ⟨c1, c2, rest2, ?_, Or.inl hSafeTag⟩
          rw [← hAfter, hTag, hTail]
          rfl
      | cons c2 rest2 =>
        simp only [tagStartsSafe, hTag, Bool.or_eq_true, bne_iff_ne, ne_eq] at hSafeTag
        refine ⟨c1, c2, rest2 ++ tailChars, ?_, hSafeTag⟩
        rw [← hAfter, hTag]
        rfl
  | cons b bs =>
    simp only [List.cons_append, List.cons.injEq] at hEq
    obtain ⟨_, hTailEq⟩ := hEq
    exfalso
    have hMem : '<' ∈ tagChars ++ tailChars := by
      rw [hTailEq]
      simp
    rcases List.mem_append.mp hMem with hInTag | hInTail
    · exact hNoLtTag hInTag
    · exact hNoLtTail hInTail

private theorem closeTag_noScTag (tagChars : List Char) (hNoLtTag : '<' ∉ tagChars) :
    NoScTag (['<', '/'] ++ tagChars ++ ['>']) := by
  intro before after hEq
  cases before with
  | nil =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hEq
    obtain ⟨_, hAfter⟩ := hEq
    cases hTag : tagChars with
    | nil =>
      refine ⟨'/', '>', [], ?_, Or.inl (by decide)⟩
      rw [← hAfter, hTag]
      rfl
    | cons c rest =>
      refine ⟨'/', c, rest ++ ['>'], ?_, Or.inl (by decide)⟩
      rw [← hAfter, hTag]
      rfl
  | cons b bs =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hEq
    obtain ⟨_, hTailEq⟩ := hEq
    exfalso
    have hMem : '<' ∈ '/' :: (tagChars ++ ['>']) := by
      rw [hTailEq]
      simp
    simp [hNoLtTag] at hMem

mutual
  theorem Node.renderChars_noScTag : (node : Node) → NoScTag node.renderChars
    | .empty => NoScTag.of_no_lt (by simp [Node.renderChars])
    | .text content => NoScTag.of_no_lt (escapeTextChars_no_lt content.toList)
    | .void tag attrs => by
      have ⟨hNoLt, hSafe⟩ := VoidTag.render_safe tag
      have hTailNoLt : '<' ∉ renderAttrsChars attrs ++ ['>'] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨renderAttrsChars_no_lt attrs, by decide⟩
      have hTailNonEmpty : renderAttrsChars attrs ++ ['>'] ≠ [] := by simp
      have h := openTag_noScTag tag.render.toList (renderAttrsChars attrs ++ ['>'])
        hNoLt hSafe hTailNoLt hTailNonEmpty
      simpa only [Node.renderChars, List.cons_append, List.append_assoc] using h
    | .elem tag attrs children => by
      have ⟨hNoLt, hSafe⟩ := NormalTag.render_safe tag
      have hTailNoLt : '<' ∉ renderAttrsChars attrs ++ ['>'] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨renderAttrsChars_no_lt attrs, by decide⟩
      have hTailNonEmpty : renderAttrsChars attrs ++ ['>'] ≠ [] := by simp
      have hOpen := openTag_noScTag tag.render.toList (renderAttrsChars attrs ++ ['>'])
        hNoLt hSafe hTailNoLt hTailNonEmpty
      have hChildren := renderNodesChars_noScTag children
      have hClose := closeTag_noScTag tag.render.toList hNoLt
      have hAll := NoScTag.append (NoScTag.append hOpen hChildren) hClose
      simpa only [Node.renderChars, List.cons_append, List.append_assoc] using hAll

  theorem renderNodesChars_noScTag : (nodes : List Node) → NoScTag (renderNodesChars nodes)
    | [] => NoScTag.of_no_lt (by simp [renderNodesChars])
    | node :: rest =>
      NoScTag.append (Node.renderChars_noScTag node) (renderNodesChars_noScTag rest)
end

private theorem doctype_noScTag : NoScTag "<!DOCTYPE html>".toList := by
  intro before after hEq
  have hLit : "<!DOCTYPE html>".toList = '<' :: '!' :: 'D' :: "OCTYPE html>".toList := by decide
  rw [hLit] at hEq
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hEq
    exact ⟨'!', 'D', "OCTYPE html>".toList, hEq.2.symm, Or.inl (by decide)⟩
  | cons b bs =>
    simp only [List.cons_append, List.cons.injEq] at hEq
    have hMem : '<' ∈ '!' :: 'D' :: "OCTYPE html>".toList := by
      rw [hEq.2]
      simp
    exact absurd hMem (by decide)

theorem Node.render_no_script (node : Node) : ¬ ContainsScriptTag node.render.toList := by
  simp only [Node.render, String.toList_ofList]
  exact (Node.renderChars_noScTag node).not_containsScriptTag

theorem Document.render_no_script (doc : Document) : ¬ ContainsScriptTag doc.render.toList := by
  simp only [Document.render, String.toList_ofList]
  exact (NoScTag.append doctype_noScTag (Node.renderChars_noScTag _)).not_containsScriptTag

def forbiddenJsExtensions : List String :=
  ["js", "ts", "jsx", "tsx", "mjs", "cjs", "mts", "cts"]

def hasForbiddenJsExtension (ext : String) : Bool :=
  forbiddenJsExtensions.contains ext.toLower

theorem hasForbiddenJsExtension_iff (ext : String) :
    hasForbiddenJsExtension ext = true ↔ ext.toLower ∈ forbiddenJsExtensions := by
  simp [hasForbiddenJsExtension]

def startsWithScriptTag : List Char → Bool
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: _ =>
    c0.toLower == '<' && c1.toLower == 's' && c2.toLower == 'c' &&
      c3.toLower == 'r' && c4.toLower == 'i' && c5.toLower == 'p' &&
      c6.toLower == 't'
  | _ => false

def containsScriptTagChars : List Char → Bool
  | [] => false
  | c :: rest =>
    if startsWithScriptTag (c :: rest) then true
    else containsScriptTagChars rest

theorem startsWithScriptTag_iff (cs : List Char) :
    startsWithScriptTag cs = true ↔ (cs.take 7).map Char.toLower = scriptPrefix := by
  rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, rest⟩⟩⟩⟩⟩⟩⟩ <;>
    simp [startsWithScriptTag, scriptPrefix, and_assoc]

theorem containsScriptTagChars_iff (cs : List Char) :
    containsScriptTagChars cs = true ↔ ContainsScriptTag cs := by
  induction cs with
  | nil =>
    constructor
    · intro h
      simp [containsScriptTagChars] at h
    · rintro ⟨before, after, hEq, hPref⟩
      have hNil : after = [] := by
        cases before <;> cases after <;> simp at hEq ⊢
      simp [hNil, scriptPrefix] at hPref
  | cons c rest ih =>
    unfold containsScriptTagChars
    constructor
    · intro h
      by_cases hs : startsWithScriptTag (c :: rest) = true
      · exact ⟨[], c :: rest, rfl, (startsWithScriptTag_iff (c :: rest)).mp hs⟩
      · rw [ite_eq_right hs] at h
        obtain ⟨before, after, hRest, hPref⟩ := ih.mp h
        exact ⟨c :: before, after, by simp [hRest], hPref⟩
    · rintro ⟨before, after, hEq, hPref⟩
      cases before with
      | nil =>
        simp only [List.nil_append] at hEq
        rw [← hEq] at hPref
        have hs : startsWithScriptTag (c :: rest) = true :=
          (startsWithScriptTag_iff (c :: rest)).mpr hPref
        rw [ite_eq_left hs]
      | cons b bs =>
        simp only [List.cons_append, List.cons.injEq] at hEq
        have hRec : containsScriptTagChars rest = true :=
          ih.mpr ⟨bs, after, hEq.2, hPref⟩
        by_cases hs : startsWithScriptTag (c :: rest) = true
        · rw [ite_eq_left hs]
        · rw [ite_eq_right hs]
          exact hRec

inductive ZeroJsRefusal where
  | forbiddenExtension
  | nulByte
  | invalidUtf8
  | scriptTag
  deriving DecidableEq, BEq

def hasNulByte (bytes : ByteArray) : Bool :=
  bytes.data.contains (0 : UInt8)

theorem hasNulByte_iff (bytes : ByteArray) :
    hasNulByte bytes = true ↔ (0 : UInt8) ∈ bytes.data.toList := by
  simp [hasNulByte]

def admitZeroJsBytes (bytes : ByteArray) : Except ZeroJsRefusal String :=
  if hasNulByte bytes then .error .nulByte
  else
    match String.fromUTF8? bytes with
    | none => .error .invalidUtf8
    | some text =>
      if containsScriptTagChars text.toList then .error .scriptTag
      else .ok text

def admitZeroJsFile (ext : String) (bytes : ByteArray) : Except ZeroJsRefusal String :=
  if hasForbiddenJsExtension ext then .error .forbiddenExtension
  else admitZeroJsBytes bytes

theorem admitZeroJsBytes_iff (bytes : ByteArray) (text : String) :
    admitZeroJsBytes bytes = .ok text ↔
      (0 : UInt8) ∉ bytes.data.toList ∧
      String.fromUTF8? bytes = some text ∧
      ¬ ContainsScriptTag text.toList := by
  unfold admitZeroJsBytes
  by_cases hNul : hasNulByte bytes = true
  · rw [ite_eq_left hNul]
    have hMem : (0 : UInt8) ∈ bytes.data.toList := (hasNulByte_iff bytes).mp hNul
    simp [hMem]
  · rw [ite_eq_right hNul]
    have hNoNul : (0 : UInt8) ∉ bytes.data.toList := fun hMem =>
      hNul ((hasNulByte_iff bytes).mpr hMem)
    cases hUtf : String.fromUTF8? bytes with
    | none => simp [hNoNul]
    | some decoded =>
      dsimp only
      by_cases hSc : containsScriptTagChars decoded.toList = true
      · rw [ite_eq_left hSc]
        have hContains : ContainsScriptTag decoded.toList :=
          (containsScriptTagChars_iff decoded.toList).mp hSc
        constructor
        · intro h
          cases h
        · rintro ⟨_, hEq, hNot⟩
          cases Option.some.inj hEq
          exact False.elim (hNot hContains)
      · rw [ite_eq_right hSc]
        have hNoScript : ¬ ContainsScriptTag decoded.toList := fun hContains =>
          hSc ((containsScriptTagChars_iff decoded.toList).mpr hContains)
        constructor
        · intro h
          cases Except.ok.inj h
          exact ⟨hNoNul, rfl, hNoScript⟩
        · rintro ⟨_, hEq, _⟩
          cases Option.some.inj hEq
          rfl

theorem admitZeroJsFile_iff (ext : String) (bytes : ByteArray) (text : String) :
    admitZeroJsFile ext bytes = .ok text ↔
      ext.toLower ∉ forbiddenJsExtensions ∧
      (0 : UInt8) ∉ bytes.data.toList ∧
      String.fromUTF8? bytes = some text ∧
      ¬ ContainsScriptTag text.toList := by
  unfold admitZeroJsFile
  by_cases hExt : hasForbiddenJsExtension ext = true
  · rw [ite_eq_left hExt]
    have hMem : ext.toLower ∈ forbiddenJsExtensions := (hasForbiddenJsExtension_iff ext).mp hExt
    simp [hMem]
  · rw [ite_eq_right hExt]
    have hNoExt : ext.toLower ∉ forbiddenJsExtensions := fun hMem =>
      hExt ((hasForbiddenJsExtension_iff ext).mpr hMem)
    rw [admitZeroJsBytes_iff]
    simp [hNoExt]

end Acorn.Host.Viewer.Html
