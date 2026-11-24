import Acorn.Host.Viewer.ExplicitStart

namespace Acorn.Host.Viewer

private theorem digitChar_bounds (d : Nat) (lt : d < 10) :
    '0' ≤ Nat.digitChar d ∧ Nat.digitChar d ≤ '9' := by
  have digits :
      d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
    omega
  rcases digits with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem toDigitsCore_digits (fuel n : Nat) (acc : List Char)
    (hacc : ∀ c ∈ acc, '0' ≤ c ∧ c ≤ '9') :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n acc, '0' ≤ c ∧ c ≤ '9' := by
  induction fuel generalizing n acc with
  | zero => exact hacc
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    have hd : '0' ≤ Nat.digitChar (n % 10) ∧ Nat.digitChar (n % 10) ≤ '9' :=
      digitChar_bounds (n % 10) (Nat.mod_lt n (by decide))
    split
    · intro c hc
      cases List.mem_cons.mp hc with
      | inl same => rw [same]; exact hd
      | inr rest => exact hacc c rest
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) fun c hc => by
        cases List.mem_cons.mp hc with
        | inl same => rw [same]; exact hd
        | inr rest => exact hacc c rest

private theorem toDigitsCore_nonempty (fuel n : Nat) (acc : List Char)
    (hpos : 0 < fuel ∨ acc ≠ []) :
    Nat.toDigitsCore 10 fuel n acc ≠ [] := by
  induction fuel generalizing n acc with
  | zero =>
    rcases hpos with h | h
    · omega
    · simpa [Nat.toDigitsCore] using h
  | succ fuel ih =>
    unfold Nat.toDigitsCore
    dsimp only
    split
    · exact List.cons_ne_nil _ _
    · exact ih (n / 10) (Nat.digitChar (n % 10) :: acc) (.inr (List.cons_ne_nil _ _))

private theorem toString_uint64_digits (u : UInt64) :
    (toString u).toList ≠ [] ∧ ∀ c ∈ (toString u).toList, '0' ≤ c ∧ c ≤ '9' := by
  have hmem : ∀ c ∈ Nat.toDigits 10 u.toNat, '0' ≤ c ∧ c ≤ '9' :=
    toDigitsCore_digits (u.toNat + 1) u.toNat [] (fun _ h => nomatch h)
  have hne : Nat.toDigits 10 u.toNat ≠ [] :=
    toDigitsCore_nonempty (u.toNat + 1) u.toNat [] (.inl (Nat.zero_lt_succ _))
  have hlist : (toString u).toList = Nat.toDigits 10 u.toNat := by
    change (toString u.toNat).toList = Nat.toDigits 10 u.toNat
    simp [toString, Nat.repr]
  rw [hlist]
  exact ⟨hne, hmem⟩

private theorem space_ne_structural (c : Char) (hs : Json.Grammar.Space c) :
    c ≠ '"' ∧ c ≠ ':' ∧ c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ '{' ∧ ¬ ('0' ≤ c ∧ c ≤ '9') := by
  rcases hs with rfl | rfl | rfl | rfl <;> decide

private theorem blank_eq_nil_of_head (bs rest : List Char) (c : Char) (tail : List Char)
    (hb : Json.Grammar.Blank bs) (hnot : ¬ Json.Grammar.Space c)
    (heq : bs ++ rest = c :: tail) : bs = [] ∧ rest = c :: tail := by
  cases bs with
  | nil => exact ⟨rfl, heq⟩
  | cons b bs' =>
    have hbmem := hb b (by simp)
    have hbchar := (List.cons.inj heq).1
    rw [hbchar] at hbmem
    exact absurd hbmem hnot

private theorem append_eq_of_pred {P : Char → Prop}
    (lhs₁ rhs₁ lhs₂ rhs₂ : List Char)
    (h₁ : ∀ c ∈ lhs₁, P c) (h₂ : ∀ c ∈ lhs₂, P c)
    (hr₁ : ∀ c, rhs₁.head? = some c → ¬ P c)
    (hr₂ : ∀ c, rhs₂.head? = some c → ¬ P c)
    (heq : lhs₁ ++ rhs₁ = lhs₂ ++ rhs₂) : lhs₁ = lhs₂ ∧ rhs₁ = rhs₂ := by
  induction lhs₁ generalizing lhs₂ with
  | nil =>
    cases lhs₂ with
    | nil => exact ⟨rfl, heq⟩
    | cons x xs =>
      simp only [List.nil_append, List.cons_append] at heq
      have hhead : rhs₁.head? = some x := by rw [heq]; rfl
      exact absurd (h₂ x (by simp)) (hr₁ x hhead)
  | cons a as ih =>
    cases lhs₂ with
    | nil =>
      simp only [List.cons_append, List.nil_append] at heq
      have hhead : rhs₂.head? = some a := by rw [← heq]; rfl
      exact absurd (h₁ a (by simp)) (hr₂ a hhead)
    | cons b bs =>
      simp only [List.cons_append] at heq
      have hcons := List.cons.inj heq
      have hsub := ih bs (fun c hc => h₁ c (by simp [hc])) (fun c hc => h₂ c (by simp [hc])) hcons.2
      exact ⟨by rw [hcons.1, hsub.1], hsub.2⟩

private theorem prefix_before_delim (delim : Char) (inside after target tail : List Char)
    (htarget : ∀ c ∈ target, c ≠ delim)
    (heq : inside ++ delim :: after = target ++ tail) :
    ∃ rest, inside = target ++ rest := by
  induction target generalizing inside with
  | nil => exact ⟨inside, rfl⟩
  | cons t ts ih =>
    cases inside with
    | nil =>
      simp only [List.nil_append, List.cons_append] at heq
      exact absurd (List.cons.inj heq).1.symm (htarget t (by simp))
    | cons x xs =>
      simp only [List.cons_append] at heq
      have hcons := List.cons.inj heq
      obtain ⟨rest, hxs⟩ := ih xs (fun c hc => htarget c (by simp [hc])) hcons.2
      exact ⟨rest, by rw [hcons.1, hxs, List.cons_append]⟩

private theorem characters_match_literal (body decoded rest literal suffix : List Char)
    (hc : Json.Grammar.Characters body decoded)
    (hlit : ∀ c ∈ literal, c ≠ '"' ∧ c ≠ '\\')
    (heq : body ++ '"' :: rest = literal ++ '"' :: suffix) :
    decoded = literal ∧ rest = suffix := by
  induction hc generalizing literal with
  | nil =>
    cases literal with
    | nil => exact ⟨rfl, (List.cons.inj heq).2⟩
    | cons l ls =>
      have := (List.cons.inj heq).1
      exact absurd this.symm (hlit l (by simp)).1
  | @cons ch moreBody c dec' spelled restChars ih =>
    cases spelled with
    | plain ch0 _ unquoted _ =>
      cases literal with
      | nil =>
        simp only [List.cons_append, List.nil_append] at heq
        exact absurd (List.cons.inj heq).1 unquoted
      | cons l ls =>
        simp only [List.cons_append] at heq
        have hcons := List.cons.inj heq
        have hsub := ih ls (fun x hx => hlit x (by simp [hx])) hcons.2
        exact ⟨by rw [hcons.1, hsub.1], hsub.2⟩
    | quote | reverseSolidus | solidus | backspace | formFeed | lineFeed | carriageReturn | tab =>
      cases literal with
      | nil =>
        simp only [List.cons_append, List.nil_append] at heq
        cases (List.cons.inj heq).1
      | cons l ls =>
        simp only [List.cons_append] at heq
        exact absurd (List.cons.inj heq).1.symm (hlit l (by simp)).2
    | unit _ _ _ _ _ _ =>
      cases literal with
      | nil =>
        simp only [List.cons_append, List.nil_append] at heq
        cases (List.cons.inj heq).1
      | cons l ls =>
        simp only [List.cons_append] at heq
        exact absurd (List.cons.inj heq).1.symm (hlit l (by simp)).2
    | pair _ _ _ _ _ _ _ _ _ _ =>
      cases literal with
      | nil =>
        simp only [List.cons_append, List.nil_append] at heq
        cases (List.cons.inj heq).1
      | cons l ls =>
        simp only [List.cons_append] at heq
        exact absurd (List.cons.inj heq).1.symm (hlit l (by simp)).2

private theorem quoted_match_literal (cs rest literal suffix : List Char) (key : String)
    (hq : Json.Grammar.Quoted cs key)
    (hlit : ∀ c ∈ literal, c ≠ '"' ∧ c ≠ '\\')
    (heq : cs ++ rest = '"' :: literal ++ '"' :: suffix) :
    key = String.ofList literal ∧ rest = suffix := by
  obtain ⟨body, decoded, hchars, hcs, hkey⟩ := hq
  rw [hcs] at heq
  simp only [List.cons_append, List.append_assoc] at heq
  have hcons := List.cons.inj heq
  obtain ⟨hdec, hrest⟩ := characters_match_literal body decoded rest literal suffix hchars hlit hcons.2
  exact ⟨by rw [hkey, hdec], hrest⟩

private theorem char_lit_not_comma_space :
    ('-' ≠ ',' ∧ ¬ Json.Grammar.Space '-') ∧
      ('0' ≠ ',' ∧ ¬ Json.Grammar.Space '0') ∧
      ('.' ≠ ',' ∧ ¬ Json.Grammar.Space '.') ∧
      ('e' ≠ ',' ∧ ¬ Json.Grammar.Space 'e') ∧
      ('E' ≠ ',' ∧ ¬ Json.Grammar.Space 'E') ∧
      ('+' ≠ ',' ∧ ¬ Json.Grammar.Space '+') := by
  refine ⟨⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩,
    ⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩,
    ⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩,
    ⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩,
    ⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩,
    ⟨by decide, fun hs => by rcases hs with h | h | h | h <;> cases h⟩⟩

private theorem grammar_number_chars (cs : List Char) (hn : Json.Grammar.Number cs) :
    ∀ c ∈ cs, c ≠ ',' ∧ ¬ Json.Grammar.Space c := by
  have hd : ∀ c, Json.Grammar.Digit c → c ≠ ',' ∧ ¬ Json.Grammar.Space c := by
    intro c hdg
    refine ⟨?_, ?_⟩
    · intro hcm; subst hcm; exact absurd hdg.1 (by decide)
    · intro hsp; exact (space_ne_structural c hsp).2.2.2.2.2.2 hdg
  obtain ⟨minus, int, frac, exp, hminus, hint, hfrac, hexp, rfl⟩ := hn
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · rcases hminus with rfl | rfl
    · cases hc
    · rw [List.mem_singleton.mp hc]
      exact char_lit_not_comma_space.1
  · rcases hint with rfl | ⟨first, more, rfl, hfirst, _, hmore⟩
    · rw [List.mem_singleton.mp hc]
      exact char_lit_not_comma_space.2.1
    · cases List.mem_cons.mp hc with
      | inl h => rw [h]; exact hd first hfirst
      | inr h => exact hd c (hmore c h)
  · rcases hfrac with rfl | ⟨digits, rfl, _, hdigits⟩
    · cases hc
    · cases List.mem_cons.mp hc with
      | inl h => rw [h]; exact char_lit_not_comma_space.2.2.1
      | inr h => exact hd c (hdigits c h)
  · rcases hexp with rfl | ⟨mark, sign, digits, hmark, hsign, _, hdigits, rfl⟩
    · cases hc
    · cases List.mem_cons.mp hc with
      | inl h =>
        rw [h]
        rcases hmark with rfl | rfl
        · exact char_lit_not_comma_space.2.2.2.1
        · exact char_lit_not_comma_space.2.2.2.2.1
      | inr h =>
        cases List.mem_append.mp h with
        | inl hs =>
          rcases hsign with rfl | rfl | rfl
          · cases hs
          · rw [List.mem_singleton.mp hs]; exact char_lit_not_comma_space.1
          · rw [List.mem_singleton.mp hs]; exact char_lit_not_comma_space.2.2.2.2.2
        | inr hdmem => exact hd c (hdigits c hdmem)

private theorem number_of_value_digit_head {depth : Nat} {cs tail : List Char}
    {v : Json.Value} {d : Char} {rest : List Char}
    (hv : Json.Grammar.Value depth cs v) (hd : '0' ≤ d ∧ d ≤ '9')
    (heq : cs ++ tail = d :: rest) :
    Json.Grammar.Number cs := by
  have dne : ∀ x ∈ (['n', 't', 'f', '"', '[', '{'] : List Char), d ≠ x := by
    intro x hx
    rcases by simpa using hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      · intro h; rw [h] at hd; revert hd; decide
  cases hv with
  | null => exact absurd (List.cons.inj heq).1.symm (dne 'n' (by simp))
  | truth => exact absurd (List.cons.inj heq).1.symm (dne 't' (by simp))
  | falsity => exact absurd (List.cons.inj heq).1.symm (dne 'f' (by simp))
  | string _ hq =>
    obtain ⟨_, _, _, hcs, _⟩ := hq
    rw [hcs] at heq
    exact absurd (List.cons.inj heq).1.symm (dne '"' (by simp))
  | emptyArray => exact absurd (List.cons.inj heq).1.symm (dne '[' (by simp))
  | array => exact absurd (List.cons.inj heq).1.symm (dne '[' (by simp))
  | emptyObject => exact absurd (List.cons.inj heq).1.symm (dne '{' (by simp))
  | object => exact absurd (List.cons.inj heq).1.symm (dne '{' (by simp))
  | number _ hn => exact hn

private theorem string_of_value_quote_head {depth : Nat} {cs tail : List Char}
    {v : Json.Value} {rest : List Char}
    (hv : Json.Grammar.Value depth cs v)
    (heq : cs ++ tail = '"' :: rest) :
    ∃ s, Json.Grammar.Quoted cs s ∧ v = .string s := by
  cases hv with
  | string _ hq => exact ⟨_, hq, rfl⟩
  | null | truth | falsity | emptyArray | array | emptyObject | object =>
    simp only [List.cons_append] at heq
    cases (List.cons.inj heq).1
  | number _ hn =>
    obtain ⟨m, int, _, _, hm, hint, _, _, heqcs⟩ := hn
    rcases hm with rfl | rfl
    · rcases hint with rfl | ⟨first, _, rfl, hfirst, _⟩
      · cases heqcs; cases heq
      · cases heqcs
        cases heq
        exact absurd hfirst.1 (by decide)
    · cases heqcs; simp only [List.cons_append] at heq; cases (List.cons.inj heq).1

private theorem member_number_cons {depth : Nat} {inside : List Char}
    {fields : List (String × Json.Value)}
    (hm : Json.Grammar.Members depth inside fields)
    (keyLit valLit rest : List Char)
    (hne : valLit ≠ [])
    (hkey : ∀ c ∈ keyLit, c ≠ '"' ∧ c ≠ '\\')
    (hval : ∀ c ∈ valLit, '0' ≤ c ∧ c ≤ '9')
    (heq : inside = '"' :: keyLit ++ '"' :: ':' :: valLit ++ ',' :: rest) :
    ∃ v tailFields,
      fields = (String.ofList keyLit, v) :: tailFields ∧
        Json.Grammar.Members depth rest tailFields := by
  obtain ⟨vh, vt, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hvh := hval vh (by simp)
  have hvalP : ∀ c ∈ (vh :: vt), c ≠ ',' ∧ ¬ Json.Grammar.Space c := by
    intro c hc
    have hc' := hval c hc
    refine ⟨?_, fun hsp => (space_ne_structural c hsp).2.2.2.2.2.2 hc'⟩
    intro hcm; subst hcm; revert hc'; decide
  have hnotvh : ¬ Json.Grammar.Space vh := fun hsp => (space_ne_structural vh hsp).2.2.2.2.2.2 hvh
  have hreassoc : inside = ('"' :: keyLit ++ ['"']) ++ ':' :: ((vh :: vt) ++ ',' :: rest) := by
    simpa [List.cons_append, List.append_assoc] using heq
  cases hm with
  | @last _ before name between colon cs after key v hlead hnamed hspaced hsep hitem htrail =>
    have hsplit : before ++ (name ++ (between ++ ':' :: (colon ++ (cs ++ after)))) =
        ('"' :: keyLit ++ ['"']) ++ ':' :: ((vh :: vt) ++ ',' :: rest) := by
      simpa [List.append_assoc] using hreassoc
    obtain ⟨rfl, h1⟩ := blank_eq_nil_of_head before _ '"' _ hlead
      (fun hs => (space_ne_structural '"' hs).1 rfl) hsplit
    obtain ⟨rfl, h2⟩ := quoted_match_literal name _ keyLit _ key hnamed hkey
      (by simpa [List.append_assoc] using h1)
    obtain ⟨rfl, h3⟩ := blank_eq_nil_of_head between _ ':' _ hspaced
      (fun hs => (space_ne_structural ':' hs).2.1 rfl) h2
    have h4 := (List.cons.inj h3).2
    obtain ⟨rfl, h5⟩ := blank_eq_nil_of_head colon _ vh _ hsep hnotvh h4
    have hnum := number_of_value_digit_head hitem hvh h5
    have hcsP := grammar_number_chars cs hnum
    have htr : ∀ c, after.head? = some c → ¬ (c ≠ ',' ∧ ¬ Json.Grammar.Space c) := by
      intro c hc hP; exact hP.2 (htrail c (List.mem_of_mem_head? hc))
    have hrr : ∀ c, (',' :: rest).head? = some c → ¬ (c ≠ ',' ∧ ¬ Json.Grammar.Space c) := by
      intro c hc hP; cases hc; exact hP.1 rfl
    obtain ⟨_, hbad⟩ := append_eq_of_pred cs after (vh :: vt) (',' :: rest) hcsP hvalP htr hrr h5
    exact absurd (htrail ',' (by rw [hbad]; simp)) (fun hs => (space_ne_structural ',' hs).2.2.1 rfl)
  | @cons _ before name between colon cs after more key v tailFields
      hlead hnamed hspaced hsep hitem htrail hrest =>
    have hsplit : before ++ (name ++ (between ++ ':' :: (colon ++ (cs ++ (after ++ ',' :: more))))) =
        ('"' :: keyLit ++ ['"']) ++ ':' :: ((vh :: vt) ++ ',' :: rest) := by
      simpa [List.append_assoc] using hreassoc
    obtain ⟨rfl, h1⟩ := blank_eq_nil_of_head before _ '"' _ hlead
      (fun hs => (space_ne_structural '"' hs).1 rfl) hsplit
    obtain ⟨rfl, h2⟩ := quoted_match_literal name _ keyLit _ key hnamed hkey
      (by simpa [List.append_assoc] using h1)
    obtain ⟨rfl, h3⟩ := blank_eq_nil_of_head between _ ':' _ hspaced
      (fun hs => (space_ne_structural ':' hs).2.1 rfl) h2
    have h4 := (List.cons.inj h3).2
    obtain ⟨rfl, h5⟩ := blank_eq_nil_of_head colon _ vh _ hsep hnotvh h4
    have hnum := number_of_value_digit_head hitem hvh h5
    have hcsP := grammar_number_chars cs hnum
    have htr : ∀ c, (after ++ ',' :: more).head? = some c → ¬ (c ≠ ',' ∧ ¬ Json.Grammar.Space c) := by
      intro c hc hP
      cases after with
      | nil => exact hP.1 (by cases hc; rfl)
      | cons _ _ => cases hc; exact hP.2 (htrail c (by simp))
    have hrr : ∀ c, (',' :: rest).head? = some c → ¬ (c ≠ ',' ∧ ¬ Json.Grammar.Space c) := by
      intro c hc hP; cases hc; exact hP.1 rfl
    obtain ⟨_, h6⟩ := append_eq_of_pred cs (after ++ ',' :: more) (vh :: vt) (',' :: rest)
      hcsP hvalP htr hrr h5
    obtain ⟨rfl, h7⟩ := blank_eq_nil_of_head after _ ',' _ htrail
      (fun hs => (space_ne_structural ',' hs).2.2.1 rfl) h6
    have h8 := (List.cons.inj h7).2
    rw [← h8]
    exact ⟨v, tailFields, rfl, hrest⟩

private theorem member_string_mem {depth : Nat} {inside : List Char}
    {fields : List (String × Json.Value)}
    (hm : Json.Grammar.Members depth inside fields)
    (keyLit valLit rest : List Char)
    (hkey : ∀ c ∈ keyLit, c ≠ '"' ∧ c ≠ '\\')
    (hval : ∀ c ∈ valLit, c ≠ '"' ∧ c ≠ '\\')
    (heq : inside = '"' :: keyLit ++ '"' :: ':' :: '"' :: valLit ++ '"' :: ',' :: rest) :
    (String.ofList keyLit, Json.Value.string (String.ofList valLit)) ∈ fields := by
  have hreassoc :
      inside = ('"' :: keyLit ++ ['"']) ++ ':' :: (('"' :: valLit ++ ['"']) ++ ',' :: rest) := by
    simpa [List.cons_append, List.append_assoc] using heq
  cases hm with
  | @last _ before name between colon cs after key v hlead hnamed hspaced hsep hitem htrail =>
    have hsplit : before ++ (name ++ (between ++ ':' :: (colon ++ (cs ++ after)))) =
        ('"' :: keyLit ++ ['"']) ++ ':' :: (('"' :: valLit ++ ['"']) ++ ',' :: rest) := by
      simpa [List.append_assoc] using hreassoc
    obtain ⟨rfl, h1⟩ := blank_eq_nil_of_head before _ '"' _ hlead
      (fun hs => (space_ne_structural '"' hs).1 rfl) hsplit
    obtain ⟨rfl, h2⟩ := quoted_match_literal name _ keyLit _ key hnamed hkey
      (by simpa [List.append_assoc] using h1)
    obtain ⟨rfl, h3⟩ := blank_eq_nil_of_head between _ ':' _ hspaced
      (fun hs => (space_ne_structural ':' hs).2.1 rfl) h2
    have h4 := (List.cons.inj h3).2
    obtain ⟨rfl, h5⟩ := blank_eq_nil_of_head colon _ '"' _ hsep
      (fun hs => (space_ne_structural '"' hs).1 rfl) h4
    obtain ⟨s, hq, rfl⟩ := string_of_value_quote_head hitem
      (by simpa [List.cons_append, List.append_assoc] using h5)
    obtain ⟨rfl, _⟩ := quoted_match_literal cs after valLit (',' :: rest) s hq hval
      (by simpa [List.cons_append, List.append_assoc] using h5)
    simp
  | @cons _ before name between colon cs after more key v tailFields
      hlead hnamed hspaced hsep hitem htrail hrest =>
    have hsplit : before ++ (name ++ (between ++ ':' :: (colon ++ (cs ++ (after ++ ',' :: more))))) =
        ('"' :: keyLit ++ ['"']) ++ ':' :: (('"' :: valLit ++ ['"']) ++ ',' :: rest) := by
      simpa [List.append_assoc] using hreassoc
    obtain ⟨rfl, h1⟩ := blank_eq_nil_of_head before _ '"' _ hlead
      (fun hs => (space_ne_structural '"' hs).1 rfl) hsplit
    obtain ⟨rfl, h2⟩ := quoted_match_literal name _ keyLit _ key hnamed hkey
      (by simpa [List.append_assoc] using h1)
    obtain ⟨rfl, h3⟩ := blank_eq_nil_of_head between _ ':' _ hspaced
      (fun hs => (space_ne_structural ':' hs).2.1 rfl) h2
    have h4 := (List.cons.inj h3).2
    obtain ⟨rfl, h5⟩ := blank_eq_nil_of_head colon _ '"' _ hsep
      (fun hs => (space_ne_structural '"' hs).1 rfl) h4
    obtain ⟨s, hq, rfl⟩ := string_of_value_quote_head hitem
      (by simpa [List.cons_append, List.append_assoc] using h5)
    obtain ⟨rfl, _⟩ := quoted_match_literal cs _ valLit _ s hq hval
      (by simpa [List.cons_append, List.append_assoc] using h5)
    simp

private def HasDesiredStopped (fields : List (String × Json.Value)) : Prop :=
  ("desired", Json.Value.string "stopped") ∈ fields ∧
    ∀ p ∈ fields, p.1 = "desired" → p.2 = .string "stopped"

private theorem hasDesiredStopped_of_nodup (fields : List (String × Json.Value))
    (hmem : ("desired", Json.Value.string "stopped") ∈ fields)
    (hnodup : (fields.map Prod.fst).Nodup) : HasDesiredStopped fields := by
  refine ⟨hmem, ?_⟩
  induction fields with
  | nil => cases hmem
  | cons p ps ih =>
    intro q hq hkey
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    cases List.mem_cons.mp hmem with
    | inl hhead =>
      cases List.mem_cons.mp hq with
      | inl hqh => rw [hqh, ← hhead]
      | inr hqt =>
        exfalso
        apply hnodup.1
        refine ⟨q, hqt, ?_⟩
        rw [hkey, ← hhead]
    | inr htail =>
      cases List.mem_cons.mp hq with
      | inl hqh =>
        exfalso
        apply hnodup.1
        refine ⟨("desired", .string "stopped"), htail, ?_⟩
        rw [← hqh, hkey]
      | inr hqt => exact ih htail hnodup.2 q hqt hkey

private theorem decoder_bind_ok {α β : Type} (a : Json.Decoder α) (b : α → Json.Decoder β)
    (s : List (String × Json.Value)) (y : β) (s' : List (String × Json.Value))
    (hok : (a >>= b).run s = .ok (y, s')) :
    ∃ x sx, a.run s = .ok (x, sx) ∧ (b x).run sx = .ok (y, s') := by
  change Except.bind (a.run s) (fun p => (b p.1).run p.2) = .ok (y, s') at hok
  cases ha : a.run s with
  | error e => rw [ha] at hok; cases hok
  | ok pair =>
    rw [ha] at hok
    exact ⟨pair.1, pair.2, rfl, hok⟩

private theorem decoder_lift_ok {γ : Type} (e : Except String γ)
    (s : List (String × Json.Value)) (x : γ) (s' : List (String × Json.Value))
    (hok : (liftM e : Json.Decoder γ).run s = .ok (x, s')) :
    e = .ok x ∧ s' = s := by
  cases he : e with
  | error err =>
    have hbad : (liftM (Except.error err : Except String γ) : Json.Decoder γ).run s =
        Except.error err := rfl
    rw [he, hbad] at hok
    cases hok
  | ok val =>
    have hgood : (liftM (Except.ok val : Except String γ) : Json.Decoder γ).run s =
        Except.ok (val, s) := rfl
    rw [he, hgood] at hok
    have hp := Prod.mk.inj (Except.ok.inj hok)
    exact ⟨by rw [hp.1], hp.2.symm⟩

private theorem take_run_eq (key : String) (s : List (String × Json.Value)) :
    (Json.take key).run s =
      match s.find? (fun p => p.1 == key) with
      | some pair => .ok (pair.2, s.filter fun p => p.1 != key)
      | none => .error s!"missing field {key}" := by
  cases hfind : s.find? (fun p => p.1 == key) <;>
    simp [Json.take, StateT.run, bind, StateT.bind, pure, StateT.pure, get, MonadStateOf.get,
      StateT.get, getThe, MonadState.get, set, MonadStateOf.set, StateT.set, throw,
      MonadExceptOf.throw, throwThe, MonadExcept.throw, StateT.lift, Except.bind,
      Except.pure, hfind]

private theorem decoder_discard_take_ok (key : String) (hne : key ≠ "desired")
    (s : List (String × Json.Value)) (u : Unit) (s' : List (String × Json.Value))
    (hs : HasDesiredStopped s) (hok : (discard (Json.take key)).run s = .ok (u, s')) :
    HasDesiredStopped s' := by
  obtain ⟨v, sv, htake, hrest⟩ := decoder_bind_ok (Json.take key) (fun _ => pure ()) s u s' hok
  have hsv : sv = s' := by
    have : (pure () : Json.Decoder Unit).run sv = .ok ((), sv) := rfl
    rw [this] at hrest
    exact (Prod.mk.inj (Except.ok.inj hrest)).2
  subst hsv
  rw [take_run_eq] at htake
  cases hfind : s.find? (fun p => p.1 == key) with
  | none => rw [hfind] at htake; cases htake
  | some pair =>
    rw [hfind] at htake
    have hs' : sv = s.filter fun p => p.1 != key := (Prod.mk.inj (Except.ok.inj htake)).2.symm
    subst hs'
    refine ⟨List.mem_filter.mpr ⟨hs.1, by simp [bne_iff_ne, hne.symm]⟩, ?_⟩
    intro p hp hkey
    exact hs.2 p (List.mem_filter.mp hp).1 hkey

private theorem take_preserves_desired (key : String) (hne : key ≠ "desired")
    (s s' : List (String × Json.Value)) (v : Json.Value)
    (hs : HasDesiredStopped s) (hok : (Json.take key).run s = .ok (v, s')) :
    HasDesiredStopped s' := by
  rw [take_run_eq] at hok
  cases hfind : s.find? (fun p => p.1 == key) with
  | none => rw [hfind] at hok; cases hok
  | some pair =>
    rw [hfind] at hok
    have hs' : s' = s.filter fun p => p.1 != key := (Prod.mk.inj (Except.ok.inj hok)).2.symm
    subst hs'
    refine ⟨List.mem_filter.mpr ⟨hs.1, by simp [bne_iff_ne, hne.symm]⟩, ?_⟩
    intro p hp hkey
    exact hs.2 p (List.mem_filter.mp hp).1 hkey

private theorem text_desired_eq_stopped (s s' : List (String × Json.Value)) (str : String)
    (hs : HasDesiredStopped s) (hok : (Json.text "desired").run s = .ok (str, s')) :
    str = "stopped" := by
  have hfind : s.find? (fun p => p.1 == "desired") = some ("desired", .string "stopped") := by
    clear hok s' str
    induction s with
    | nil => cases hs.1
    | cons p ps ih =>
      simp only [List.find?]
      split
      · rename_i hbeq
        have hkey : p.1 = "desired" := beq_iff_eq.mp hbeq
        have hval := hs.2 p (by simp) hkey
        cases p with
        | mk pf psnd =>
          dsimp at hkey hval
          subst hkey hval
          rfl
      · rename_i hnb
        have hne : ("desired", Json.Value.string "stopped") ≠ p := by
          intro heq
          cases heq
          simp at hnb
        have hmem : ("desired", Json.Value.string "stopped") ∈ ps := by
          cases List.mem_cons.mp hs.1 with
          | inl h => exact absurd h hne
          | inr h => exact h
        exact ih ⟨hmem, fun q hq => hs.2 q (by simp [hq])⟩
  obtain ⟨val, sv, htake, htxt⟩ := decoder_bind_ok (Json.take "desired")
    (fun v => (liftM v.text : Json.Decoder String)) s str s' hok
  rw [take_run_eq, hfind] at htake
  have hval : val = .string "stopped" := (Prod.mk.inj (Except.ok.inj htake)).1.symm
  subst hval
  obtain ⟨ht, _⟩ := decoder_lift_ok (Json.Value.text (.string "stopped")) sv str s' htxt
  unfold Json.Value.text at ht
  exact (Except.ok.inj ht).symm

private theorem fields_tail_desired_stopped (seed : UInt64) (desired : Desired)
    (s : List (String × Json.Value)) (raw : PersistedState) (rest : List (String × Json.Value))
    (hrun : (do
      let run ← runWord (← Json.take "run_id")
      let epoch ← jsonWord (← Json.take "agent_epoch")
      let origin ← match ← Json.text "origin" with
        | "fresh" => pure NewAgentOrigin.fresh
        | "cleared" => pure NewAgentOrigin.cleared
        | _ => throw "unknown new-agent origin"
      let processStarted ← jsonBool (← Json.take "process_started")
      return (⟨⟨run, seed, epoch⟩, desired, origin, processStarted⟩ : PersistedState)).run s =
        .ok (raw, rest)) :
    raw.desired = desired := by
  obtain ⟨vrun, s4a, _, hr4⟩ := decoder_bind_ok (Json.take "run_id") _ s raw rest hrun
  obtain ⟨run, s5, _, hr5⟩ := decoder_bind_ok _ _ s4a raw rest hr4
  obtain ⟨vep, s5a, _, hr6⟩ := decoder_bind_ok (Json.take "agent_epoch") _ s5 raw rest hr5
  obtain ⟨epoch, s6, _, hr7⟩ := decoder_bind_ok _ _ s5a raw rest hr6
  obtain ⟨ostr, s7, _, hr8⟩ := decoder_bind_ok (Json.text "origin") _ s6 raw rest hr7
  have hpsStep : ∀ (orig : NewAgentOrigin) (s8 : List (String × Json.Value)),
      (do
        let processStarted ← jsonBool (← Json.take "process_started")
        return (⟨⟨run, seed, epoch⟩, desired, orig, processStarted⟩ : PersistedState)).run s8 =
          .ok (raw, rest) → raw.desired = desired := by
    intro orig s8 hr9
    obtain ⟨vps, s8a, _, hr10⟩ := decoder_bind_ok (Json.take "process_started") _ s8 raw rest hr9
    obtain ⟨ps, s9, _, hr11⟩ := decoder_bind_ok _ _ s8a raw rest hr10
    have hp := (Prod.mk.inj (Except.ok.inj hr11)).1
    rw [← hp]
  split at hr8
  · exact hpsStep .fresh s7 hr8
  · exact hpsStep .cleared s7 hr8
  · obtain ⟨_, s8, hthrow, _⟩ := decoder_bind_ok (throw "unknown new-agent origin") _ s7 raw rest hr8
    simp [throw, MonadExceptOf.throw, throwThe, MonadExcept.throw, Functor.map, Except.map] at hthrow

private theorem fields_desired_stopped (marked recorded : Bool)
    (kvs : List (String × Json.Value)) (hds : HasDesiredStopped kvs)
    (raw : PersistedState) (rest : List (String × Json.Value))
    (hrun : (PersistedState.fields marked recorded).run kvs = .ok (raw, rest)) :
    raw.desired = .stopped := by
  have afterMarkChild : ∀ (s2 : List (String × Json.Value)), HasDesiredStopped s2 →
      (do
        let seed ← jsonWord (← Json.take "seed")
        let desired ← match ← Json.text "desired" with
          | "running" => pure Desired.running
          | "stopped" => pure Desired.stopped
          | _ => throw "unknown desired state"
        let run ← runWord (← Json.take "run_id")
        let epoch ← jsonWord (← Json.take "agent_epoch")
        let origin ← match ← Json.text "origin" with
          | "fresh" => pure NewAgentOrigin.fresh
          | "cleared" => pure NewAgentOrigin.cleared
          | _ => throw "unknown new-agent origin"
        let processStarted ← jsonBool (← Json.take "process_started")
        return (⟨⟨run, seed, epoch⟩, desired, origin, processStarted⟩ : PersistedState)).run s2 =
          .ok (raw, rest) → raw.desired = .stopped := by
    intro s2 hds2 hr0
    obtain ⟨vseed, s2a, htSeed, hr1⟩ := decoder_bind_ok (Json.take "seed") _ s2 raw rest hr0
    have hds2a := take_preserves_desired "seed" (by decide) s2 s2a vseed hds2 htSeed
    obtain ⟨seed, s3, hlSeed, hr2⟩ := decoder_bind_ok _ _ s2a raw rest hr1
    have hds3 := (decoder_lift_ok _ s2a seed s3 hlSeed).2 ▸ hds2a
    obtain ⟨dstr, s4, htDes, hr3⟩ := decoder_bind_ok (Json.text "desired") _ s3 raw rest hr2
    rw [text_desired_eq_stopped s3 s4 dstr hds3 htDes] at hr3
    exact fields_tail_desired_stopped seed .stopped s4 raw rest hr3
  unfold PersistedState.fields at hrun
  cases marked <;> cases recorded
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hrun
  · exact afterMarkChild kvs hds hrun
  · obtain ⟨uc, s2, htc, hr0⟩ := decoder_bind_ok (discard (Json.take "child")) _ kvs raw rest hrun
    exact afterMarkChild s2 (decoder_discard_take_ok "child" (by decide) kvs uc s2 hds htc) hr0
  · obtain ⟨um, s1, htm, hrm⟩ :=
      decoder_bind_ok (discard (Json.take "schema_version")) _ kvs raw rest hrun
    exact afterMarkChild s1
      (decoder_discard_take_ok "schema_version" (by decide) kvs um s1 hds htm) hrm
  · obtain ⟨um, s1, htm, hrm⟩ :=
      decoder_bind_ok (discard (Json.take "schema_version")) _ kvs raw rest hrun
    have hds1 := decoder_discard_take_ok "schema_version" (by decide) kvs um s1 hds htm
    obtain ⟨uc, s2, htc, hr0⟩ := decoder_bind_ok (discard (Json.take "child")) _ s1 raw rest hrm
    exact afterMarkChild s2 (decoder_discard_take_ok "child" (by decide) s1 uc s2 hds1 htc) hr0

private theorem encode_fields_stopped (recordedChild : Option (List String))
    (state : PersistedState) (doc : Json.Value)
    (hstopped : state.desired = .stopped)
    (hparsed : Json.parse (state.encode recordedChild) = .ok doc) :
    ∃ kvs, doc = .object kvs ∧ HasDesiredStopped kvs := by
  have htext := Json.parse_sound (state.encode recordedChild) doc hparsed
  obtain ⟨before, body, after, hlead, hval, _, heqText⟩ := htext
  have htwo : toString stateSchema = "2" := rfl
  have hencList : (state.encode recordedChild).toList =
      '{' :: ("\"schema_version\":2,\"seed\":".toList ++ (toString state.identity.seed).toList ++
        ",\"desired\":\"stopped\",".toList ++
        ("\"run_id\":\"".toList ++ (runHex state.identity.run).toList ++
          "\",\"agent_epoch\":".toList ++ (toString state.identity.agentEpoch).toList ++
          ",\"origin\":\"".toList ++ state.origin.tag.toList ++
          "\",\"process_started\":".toList ++
          (if state.processStarted then "true" else "false").toList ++
          ",\"child\":".toList ++ (childText recordedChild).toList ++ "}\n".toList)) := by
    rw [PersistedState.encode, htwo, hstopped, Desired.tag]
    repeat rw [String.toList_append]
    simp [List.cons_append, List.append_assoc]
  rw [hencList] at heqText
  have heqText' : before ++ (body ++ after) =
      '{' :: ("\"schema_version\":2,\"seed\":".toList ++ (toString state.identity.seed).toList ++
        ",\"desired\":\"stopped\",".toList ++
        ("\"run_id\":\"".toList ++ (runHex state.identity.run).toList ++
          "\",\"agent_epoch\":".toList ++ (toString state.identity.agentEpoch).toList ++
          ",\"origin\":\"".toList ++ state.origin.tag.toList ++
          "\",\"process_started\":".toList ++
          (if state.processStarted then "true" else "false").toList ++
          ",\"child\":".toList ++ (childText recordedChild).toList ++ "}\n".toList)) := by
    simpa [List.append_assoc] using heqText.symm
  obtain ⟨rfl, hbody⟩ := blank_eq_nil_of_head before _ '{' _ hlead
    (fun hs => (space_ne_structural '{' hs).2.2.2.2.2.1 rfl) heqText'
  cases hval with
  | @emptyObject _ inside _ hblank =>
    simp only [List.cons_append, List.append_assoc] at hbody
    have hbad := (List.cons.inj hbody).2
    cases inside with
    | nil => cases hbad
    | cons x _ =>
      have := hblank x (by simp)
      cases (List.cons.inj hbad).1
      exact absurd this (fun hs => (space_ne_structural '"' hs).1 rfl)
  | @object _ inside kvs _ hmembers hnodup =>
    simp only [List.cons_append, List.append_assoc] at hbody
    have hinside := (List.cons.inj hbody).2
    obtain ⟨seedNe, seedDigits⟩ := toString_uint64_digits state.identity.seed
    have hnb1 : ∀ c ∈ "\"schema_version\":2,\"seed\":".toList, c ≠ '}' := by decide
    have hnb2 : ∀ c ∈ ",\"desired\":\"stopped\",".toList, c ≠ '}' := by decide
    let prefixTarget : List Char :=
      "\"schema_version\":2,\"seed\":".toList ++ (toString state.identity.seed).toList ++
        ",\"desired\":\"stopped\",".toList
    have hnoBrace : ∀ c ∈ prefixTarget, c ≠ '}' := by
      intro c hc
      simp only [prefixTarget, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact hnb1 c hc
      · have hdc := seedDigits c hc
        intro hbr; subst hbr; revert hdc; decide
      · exact hnb2 c hc
    obtain ⟨mid, hinsideEq⟩ := prefix_before_delim '}' _ _ prefixTarget _ hnoBrace
      (by simpa [prefixTarget, List.append_assoc] using hinside)
    have hm1eq : inside = '"' :: "schema_version".toList ++ '"' :: ':' :: ['2'] ++ ',' ::
        ("\"seed\":".toList ++ (toString state.identity.seed).toList ++
          ",\"desired\":\"stopped\",".toList ++ mid) := by
      simpa [prefixTarget, List.append_assoc, List.cons_append] using hinsideEq
    obtain ⟨_, fields1, rfl, hm1⟩ := member_number_cons hmembers "schema_version".toList ['2']
      ("\"seed\":".toList ++ (toString state.identity.seed).toList ++
        ",\"desired\":\"stopped\",".toList ++ mid)
      (by decide) (by decide) (by decide) hm1eq
    have hm2eq :
        ("\"seed\":".toList ++ (toString state.identity.seed).toList ++
          ",\"desired\":\"stopped\",".toList ++ mid) =
        '"' :: "seed".toList ++ '"' :: ':' :: (toString state.identity.seed).toList ++
          ',' :: ("\"desired\":\"stopped\",".toList ++ mid) := by
      simp [List.cons_append]
    obtain ⟨_, fields2, rfl, hm2⟩ := member_number_cons hm1 "seed".toList
      (toString state.identity.seed).toList ("\"desired\":\"stopped\",".toList ++ mid)
      seedNe (by decide) seedDigits hm2eq
    have hm3eq :
        ("\"desired\":\"stopped\",".toList ++ mid) =
        '"' :: "desired".toList ++ '"' :: ':' :: '"' :: "stopped".toList ++ '"' :: ',' :: mid := by
      simp [List.cons_append]
    have hmem3 := member_string_mem hm2 "desired".toList "stopped".toList mid
      (by decide) (by decide) hm3eq
    exact ⟨_, rfl, hasDesiredStopped_of_nodup _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem3)) hnodup⟩
  | @number _ body _ hnum =>
    obtain ⟨minus, int, frac, exp, hmin, hint, _, _, rfl⟩ := hnum
    rcases hmin with rfl | rfl <;> rcases hint with rfl | ⟨d, more, rfl, hd, _⟩
    · simp only [List.nil_append, List.cons_append] at hbody
      cases (List.cons.inj hbody).1
    · simp only [List.nil_append, List.cons_append] at hbody
      have hch := (List.cons.inj hbody).1
      rw [hch] at hd
      exact absurd hd (by unfold Json.Grammar.Digit; decide)
    · simp only [List.cons_append, List.append_assoc] at hbody
      cases (List.cons.inj hbody).1
    · simp only [List.cons_append, List.append_assoc] at hbody
      cases (List.cons.inj hbody).1
  | @string _ body _ _ hquoted =>
    obtain ⟨qbody, _, _, rfl, _⟩ := hquoted
    simp only [List.cons_append, List.append_assoc] at hbody
    cases (List.cons.inj hbody).1
  | null | truth | falsity | emptyArray | array =>
    try simp only [List.cons_append] at hbody
    cases (List.cons.inj hbody).1

theorem PersistedState.encode_decode_stopped (recordedChild nextChild : Option (List String))
    (state loaded : PersistedState) (doc : Json.Value)
    (hstopped : state.desired = .stopped)
    (hparsed : Json.parse (state.encode recordedChild) = .ok doc)
    (hdecoded : PersistedState.decode nextChild doc = .ok loaded) :
    loaded.desired = .stopped := by
  obtain ⟨kvs, rfl, hds⟩ := encode_fields_stopped recordedChild state doc hstopped hparsed
  unfold PersistedState.decode at hdecoded
  cases hadm : PersistedState.admit nextChild (.object kvs) with
  | error e => rw [hadm] at hdecoded; cases hdecoded
  | ok pair =>
    rw [hadm] at hdecoded
    have hpair := (Except.ok.inj hdecoded).symm
    unfold PersistedState.admit at hadm
    obtain ⟨_, _, hrest⟩ := Json.except_bind_ok hadm
    obtain ⟨raw, hdec, hret⟩ := Json.except_bind_ok hrest
    have hraw : raw.desired = .stopped := by
      unfold Json.decode at hdec
      obtain ⟨fs, hfs, hrun⟩ := Json.except_bind_ok hdec
      have hfsEq : fs = kvs := by
        unfold Json.Value.fields at hfs
        exact (Except.ok.inj hfs).symm
      rw [hfsEq] at hrun
      obtain ⟨⟨r, srest⟩, hrunFields, hrestOk⟩ := Json.except_bind_ok hrun
      have hr : r = raw := by
        by_cases hem : srest.isEmpty
        · simp only [hem, ↓reduceIte] at hrestOk
          exact Except.ok.inj hrestOk
        · simp only [hem, throw, MonadExceptOf.throw, throwThe, MonadExcept.throw] at hrestOk
          cases hrestOk
      rw [← hr]
      exact fields_desired_stopped _ _ kvs hds r srest hrunFields
    have hloaded := Except.ok.inj hret
    rw [hpair, ← hloaded]
    by_cases hv : stateVersion (.object kvs) = some stateSchema
    · by_cases hc : nextChild.isSome ∧ stateChild (.object kvs) = nextChild
      · simp [hv, hc, hraw]
      · simp [hv, hc, hraw]
    · simp [hv]

private theorem Core.command_no_ackStop (core : Core) (clearDisabled : Option String) (cmd : Command) :
    Follow.ackStop ∉ (core.command clearDisabled cmd).follows := by
  intro acked
  cases cmd <;> cases clearDisabled <;> cases hrep : core.replacement <;> cases hown : core.owner <;>
    simp [Core.command, Core.intentFailed, command_beq, hrep, hown] at acked

private theorem Core.candidate_no_ackStop (core : Core) (gen : UInt64) (actual : CoreIdentity) :
    Follow.ackStop ∉ (core.candidate gen actual).follows := by
  intro acked
  cases h1 : core.lifecycle.ownsIdentity gen <;> cases h2 : actual.identity.browserSafe <;>
    cases hown : core.owner <;>
    simp [Core.candidate, Core.adoptFailed, h1, h2, hown] at acked

private theorem Core.exitReported_no_ackStop (core : Core) (report : ExitReport) :
    Follow.ackStop ∉ (core.exitReported report).follows := by
  intro acked
  cases ha : report.announce <;>
    simp only [Core.exitReported, Core.report, ha, Bool.false_eq_true, ↓reduceIte] at acked <;>
    split at acked <;> simp at acked

private theorem Core.finished_no_ackStop (core : Core) (stdout : OutputStatus) (stderr : PipeResult)
    (log : LogStatus) : Follow.ackStop ∉ (core.finished stdout stderr log).follows := by
  intro acked
  cases hs : core.slot <;> cases hc : core.closing <;>
    simp only [Core.finished, hs, hc] at acked
  all_goals
    first
    | (simp at acked; done)
    | (split at acked
       · simp at acked
       · exact Core.exitReported_no_ackStop _ _ acked)

private theorem Core.closed_no_ackStop (core : Core) :
    Follow.ackStop ∉ core.closed.follows := by
  intro acked
  cases hc : core.closing <;> cases hf : core.failure <;> simp [Core.closed, hc, hf] at acked

private theorem Core.closeOut_no_ackStop (core : Core) :
    Follow.ackStop ∉ core.closeOut.follows := by
  intro acked
  cases hm : core.mapWritable <;> simp only [Core.closeOut, hm, Bool.false_eq_true, ↓reduceIte] at acked
  · exact Core.closed_no_ackStop core acked
  · cases acked

private theorem Core.launchCheck_no_ackStop (core : Core) (now : Nat) :
    Follow.ackStop ∉ (core.launchCheck now).follows := by
  intro acked
  cases hc : core.replacement.isNone && core.slot == Slot.empty && core.closing == Closing.open <;>
    simp only [Core.launchCheck, hc, Bool.false_eq_true, ↓reduceIte] at acked
  · exact absurd acked (by simp)
  · cases hr : core.lifecycle.reserve (clockWord now) with
    | none => simp [hr] at acked
    | some v =>
      cases hl : core.persisted.launch with
      | error e => simp [hr, hl] at acked
      | ok l => cases ho : core.owner <;> simp [hr, hl, ho] at acked

private theorem Core.mapOrLaunch_no_ackStop (core : Core) (now : Nat) :
    Follow.ackStop ∉ (core.mapOrLaunch now).follows := by
  intro acked
  simp only [Core.mapOrLaunch] at acked
  split at acked
  · cases acked
  · exact Core.launchCheck_no_ackStop core now acked

private theorem Core.clear_no_ackStop (core : Core) (intended : Desired) :
    Follow.ackStop ∉ (core.clear intended).follows := by
  intro acked
  simp only [Core.clear] at acked
  split at acked
  · cases acked
  · cases ho : core.owner <;> simp [ho] at acked

private theorem Core.tick_no_ackStop (core : Core) (now : Nat) :
    Follow.ackStop ∉ (core.tick now).follows := by
  intro acked
  cases hc : core.closing with
  | closed _ => simp [Core.tick, hc] at acked
  | closing _ =>
    cases hs : core.slot with
    | empty =>
      simp only [Core.tick, hc, hs] at acked
      exact Core.closeOut_no_ackStop core acked
    | live _ | draining _ _ _ => simp [Core.tick, hc, hs] at acked
  | «open» =>
    cases hrep : core.replacement with
    | some _ =>
      cases hown : core.owner <;> simp [Core.tick, hc, hrep, hown] at acked
    | none =>
      cases hai : core.lifecycle.archiveIntent <;> cases hs : core.slot <;>
        simp only [Core.tick, hc, hrep, hai, hs] at acked
      all_goals
        first
        | exact Core.mapOrLaunch_no_ackStop core now acked
        | exact Core.launchCheck_no_ackStop core now acked
        | exact Core.clear_no_ackStop core _ acked
        | cases acked

private theorem Core.close_no_ackStop (core : Core) :
    Follow.ackStop ∉ core.close.follows := by
  intro acked
  cases hc : core.closing with
  | closed _ => simp [Core.close, hc] at acked
  | closing _ => simp [Core.close, hc] at acked
  | «open» =>
    cases hfail : core.failure with
    | none =>
      simp only [Core.close, hc, hfail, Option.map, Option.getD, List.nil_append] at acked
      split at acked
      · exact Core.closeOut_no_ackStop _ acked
      · cases acked
    | some _ =>
      simp only [Core.close, hc, hfail, Option.map, Option.getD] at acked
      split at acked
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at acked
        rcases acked with h | h
        · cases h
        · exact Core.closeOut_no_ackStop _ h
      · simp at acked

private theorem Core.exited_no_ackStop (core : Core) (reading : Nat) (code : UInt32)
    (uptimeMs : Nat) : Follow.ackStop ∉ (core.exited reading code uptimeMs).follows := by
  intro acked
  cases hs : core.slot <;> cases hc : core.closing <;>
    simp only [Core.exited, hs, hc] at acked
  all_goals
    first
    | (simp at acked; done)
    | (split at acked
       · simp at acked
       · exact Core.exitReported_no_ackStop _ _ acked)

private theorem Core.refused_no_ackStop (core : Core) (reason : String) :
    Follow.ackStop ∉ (core.refused reason).follows := by
  intro acked
  cases hc : core.closing <;> simp [Core.refused, hc] at acked

theorem Core.step_no_ackStop (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) :
    Follow.ackStop ∉ (core.step clearDisabled reading event).follows := by
  have noRefuse : ∀ r, Follow.ackStop ∉ stopRefusalFollow r event := by
    cases event with
    | command c => cases c <;> simp [stopRefusalFollow]
    | candidate _ _ | exited _ _ | finished _ _ _ | refused _ | tick | close =>
      simp [stopRefusalFollow]
  unfold Core.step Core.dispatch Stepped.at
  cases core.pending with
  | some _ => exact noRefuse _
  | none =>
    cases core.closing with
    | closed _ => exact noRefuse _
    | closing _ =>
      cases event with
      | command cmd => cases cmd <;> simp
      | candidate gen actual => exact core.candidate_no_ackStop gen actual
      | exited code uptimeMs => exact core.exited_no_ackStop (core.instant reading) code uptimeMs
      | finished stdout stderr log => exact core.finished_no_ackStop stdout stderr log
      | refused reason => exact core.refused_no_ackStop reason
      | tick => exact core.tick_no_ackStop (core.instant reading)
      | close => exact core.close_no_ackStop
    | «open» =>
      cases event with
      | command cmd => exact core.command_no_ackStop clearDisabled cmd
      | candidate gen actual => exact core.candidate_no_ackStop gen actual
      | exited code uptimeMs => exact core.exited_no_ackStop (core.instant reading) code uptimeMs
      | finished stdout stderr log => exact core.finished_no_ackStop stdout stderr log
      | refused reason => exact core.refused_no_ackStop reason
      | tick => exact core.tick_no_ackStop (core.instant reading)
      | close => exact core.close_no_ackStop

def Call.IsWriteStateOk : (call : Call) → call.Result → Prop
  | .writeState _, .ok () => True
  | _, _ => False

def Call.IsWriteStateErr : (call : Call) → call.Result → String → Prop
  | .writeState _, .error reason, r => reason = r
  | _, _, _ => False

theorem Core.resolve_ackStop_spec (core : Core) (now : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (acked : Follow.ackStop ∈ ({ core with pending := none }.resolve now pending result).follows) :
    ∃ state, pending.call core.lifecycle = .writeState state ∧
      state.desired = .stopped ∧ (pending.call core.lifecycle).IsWriteStateOk result := by
  cases pending with
  | intent command state =>
    cases result with
    | error reason =>
      simp only [Core.resolve, Core.intentFailed] at acked
      split at acked <;> simp at acked
    | ok u =>
      cases u
      cases command with
      | start | clear => simp [Core.resolve, Core.intentSaved] at acked
      | stop =>
        simp only [Core.resolve, Core.intentSaved] at acked
        split at acked
        · rename_i hstopped
          rw [Core.desired_beq] at hstopped
          exact ⟨state, rfl, of_decide_eq_true hstopped, trivial⟩
        · simp at acked
  | replacement state ackStop =>
    cases result with
    | error reason =>
      simp only [Core.resolve] at acked
      split at acked <;> simp at acked
    | ok u =>
      cases u
      cases ackStop with
      | false =>
        simp only [Core.resolve, Core.replaced, Bool.false_eq_true, ↓reduceIte] at acked
        split at acked <;> simp at acked
      | true =>
        simp only [Core.resolve, ↓reduceIte] at acked
        split at acked
        · rename_i hstopped
          rw [Core.desired_beq] at hstopped
          exact ⟨state, rfl, of_decide_eq_true hstopped, trivial⟩
        · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at acked
          rcases acked with acked | hbad
          · exfalso
            simp only [Core.replaced] at acked
            split at acked <;> simp at acked
          · cases hbad
  | launch =>
    cases result with
    | error => simp [Core.resolve] at acked
    | ok =>
      simp only [Core.resolve] at acked
      split at acked <;> simp at acked
  | spawn =>
    cases result <;> simp [Core.resolve] at acked
  | windUp =>
    cases result with
    | error =>
      simp only [Core.resolve, Core.refused] at acked
      split at acked <;> simp at acked
    | ok => simp [Core.resolve] at acked
  | adopt =>
    cases result <;> simp [Core.resolve, Core.adoptFailed, Core.adopted] at acked
  | commit =>
    cases result with
    | error => simp [Core.resolve] at acked
    | ok =>
      simp only [Core.resolve, Core.committed] at acked
      split at acked <;> simp at acked
  | exitMap report _ =>
    cases result with
    | error reason =>
      exfalso
      exact Core.exitReported_no_ackStop { core with pending := none } _ acked
    | ok revision =>
      exfalso
      exact Core.exitReported_no_ackStop
        { core with pending := none, mapRevision := revision.or core.mapRevision } _ acked
  | exitIntent =>
    cases result <;> simp [Core.resolve] at acked
  | map =>
    cases result with
    | error =>
      exfalso
      exact Core.launchCheck_no_ackStop _ now acked
    | ok =>
      exfalso
      exact Core.launchCheck_no_ackStop _ now acked
  | closeMap =>
    cases result with
    | error =>
      exfalso
      exact Core.closed_no_ackStop _ acked
    | ok =>
      exfalso
      exact Core.closed_no_ackStop _ acked
  | seed =>
    cases result with
    | error => simp [Core.resolve] at acked
    | ok val =>
      simp only [Core.resolve, Core.seeded] at acked
      by_cases hb : val.toNat > browserIntegerMax
      · simp [hb] at acked
      · simp only [hb, ↓reduceIte] at acked
        cases hba : core.lifecycle.beginArchive <;> cases ho : core.owner <;>
          simp [hba, ho] at acked
  | archive =>
    cases result <;> simp [Core.resolve] at acked
  | reopen =>
    cases result <;> simp [Core.resolve] at acked

theorem Core.resume_ackStop_spec (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (acked : Follow.ackStop ∈ (core.resume reading pending result).follows) :
    ∃ state, pending.call core.lifecycle = .writeState state ∧
      state.desired = .stopped ∧ (pending.call core.lifecycle).IsWriteStateOk result :=
  Core.resolve_ackStop_spec core (core.instant reading) pending result acked

theorem Core.resume_error_no_ackStop (core : Core) (reading : Nat) (pending : Pending)
    (reason : String) (result : (pending.call core.lifecycle).Result)
    (hres : (pending.call core.lifecycle).IsWriteStateErr result reason) :
    Follow.ackStop ∉ (core.resume reading pending result).follows := by
  intro acked
  obtain ⟨w, hcall, _, hok⟩ := Core.resume_ackStop_spec core reading pending result acked
  cases pending with
  | intent _ _ | launch _ _ | adopt _ _ _ | exitIntent _ | replacement _ _ =>
    dsimp [Pending.call] at hres hok
    cases result <;> simp [Call.IsWriteStateErr, Call.IsWriteStateOk] at hres hok
  | spawn _ _ | windUp _ | commit _ _ _ _ | exitMap _ _ | map _ | closeMap _ | seed _
  | archive _ _ _ | reopen _ _ _ => cases hcall

theorem Core.stop_acknowledges_or_refuses (core : Core) (clearDisabled : Option String)
    (reading : Nat) :
    let stepped := core.step clearDisabled reading (.command .stop)
    ((∃ reason, Follow.refuseStop reason ∈ stepped.follows) ∧
        Follow.ackStop ∉ stepped.follows) ∨
      ∃ pending state,
        stepped.core.pending = some pending ∧
        pending.call stepped.core.lifecycle = .writeState state ∧
        state.desired = .stopped ∧
        Follow.ackStop ∉ stepped.follows ∧
        ∀ later (result : (pending.call stepped.core.lifecycle).Result),
          ((pending.call stepped.core.lifecycle).IsWriteStateOk result →
            Follow.ackStop ∈ (stepped.core.resume later pending result).follows) ∧
          (∀ reason, (pending.call stepped.core.lifecycle).IsWriteStateErr result reason →
            Follow.refuseStop reason ∈ (stepped.core.resume later pending result).follows ∧
            Follow.ackStop ∉ (stepped.core.resume later pending result).follows) := by
  dsimp only
  have noAck : Follow.ackStop ∉ (core.step clearDisabled reading (.command .stop)).follows :=
    Core.step_no_ackStop core clearDisabled reading (.command .stop)
  cases hp : core.pending with
  | some _ =>
    left
    exact ⟨⟨"supervisor is busy with another operation", by
      simp [Core.step, Core.dispatch, Stepped.at, hp, stopRefusalFollow]⟩, noAck⟩
  | none =>
    cases hc : core.closing with
    | closed _ =>
      left
      exact ⟨⟨"viewer is closed", by
        simp [Core.step, Core.dispatch, Stepped.at, hp, hc, stopRefusalFollow]⟩, noAck⟩
    | closing _ =>
      left
      exact ⟨⟨"viewer is closing", by
        simp [Core.step, Core.dispatch, Stepped.at, hp, hc, command_beq]⟩, noAck⟩
    | «open» =>
      cases hrep : core.replacement with
      | some replacement =>
        cases hown : core.owner with
        | retired reason =>
          left
          refine ⟨⟨reason, ?_⟩, noAck⟩
          simp [Core.step, Core.dispatch, Stepped.at, hp, hc, Core.command, hrep, hown,
            Core.intentFailed, command_beq]
        | current =>
          right
          refine ⟨.replacement { replacement with desired := .stopped } true,
            { replacement with desired := .stopped }, ?_, rfl, rfl, noAck, ?_⟩
          · simp [Core.step, Core.dispatch, Stepped.at, hp, hc, Core.command, hrep, hown,
              command_beq]
          · intro later result
            cases result with
            | ok u =>
              cases u
              refine ⟨(fun _ => by
                simp [Core.resume, Core.resolve, Stepped.at, Core.desired_beq]),
                (fun _ herr => by cases herr)⟩
            | error r =>
              refine ⟨(fun hok => by cases hok), (fun reason herr => by
                have hr : r = reason := herr
                subst hr
                simp [Core.resume, Core.resolve, Stepped.at])⟩
      | none =>
        cases hown : core.owner with
        | retired reason =>
          left
          refine ⟨⟨reason, ?_⟩, noAck⟩
          simp [Core.step, Core.dispatch, Stepped.at, hp, hc, Core.command, hrep, hown,
            Core.intentFailed, command_beq]
        | current =>
          right
          refine ⟨.intent .stop { core.persisted with desired := .stopped },
            { core.persisted with desired := .stopped }, ?_, rfl, rfl, noAck, ?_⟩
          · simp [Core.step, Core.dispatch, Stepped.at, hp, hc, Core.command, hrep, hown,
              command_beq, Command.desired]
          · intro later result
            cases result with
            | ok u =>
              refine ⟨(fun _ => by
                simp [Core.resume, Core.resolve, Core.intentSaved, Stepped.at, Core.desired_beq]),
                (fun _ herr => by cases herr)⟩
            | error r =>
              refine ⟨(fun hok => by cases hok), (fun reason herr => by
                cases herr
                simp [Core.resume, Core.resolve, Core.intentFailed, command_beq, Stepped.at])⟩

def Pending.StopHeld : Pending → Prop
  | .intent command state =>
    (command = .start ∧ state.desired = .running) ∨
      (command ≠ .start ∧ state.desired = .stopped)
  | .replacement _ _ => True
  | .launch _ _ | .spawn _ _ => False
  | .adopt _ _ state | .commit _ _ state _ | .exitIntent state => state.desired = .stopped
  | .seed intended | .archive _ intended _ | .reopen _ intended _ => intended = .stopped
  | .windUp _ | .exitMap _ _ | .map _ | .closeMap _ => True

structure Core.StopHeld (core : Core) : Prop where
  lifecycle : core.lifecycle.Unstarted
  persisted : core.persisted.desired = .stopped
  pending : ∀ pending, core.pending = some pending → pending.StopHeld

structure Core.ArchivalInvariant (core : Core) : Prop where
  lifecycle : core.lifecycle.Archival
  archivingGuarded : core.lifecycle.phaseValue = .archiving →
    core.replacement.isSome = true ∨ core.owner ≠ .current ∨ core.closing ≠ .open ∨
      (∃ id d st, core.pending = some (.archive id d st)) ∨
      (∃ id d a, core.pending = some (.reopen id d a))
  noIntentWhileArchiving : ∀ c s, core.pending = some (.intent c s) →
    core.lifecycle.phaseValue ≠ .archiving
  replacementPresent : ∀ st ack, core.pending = some (.replacement st ack) →
    core.replacement.isSome = true

private theorem Core.ArchivalInvariant.same {core next : Core}
    (arch : core.ArchivalInvariant)
    (hlc : next.lifecycle = core.lifecycle)
    (hrep : next.replacement = core.replacement)
    (hown : next.owner = core.owner)
    (hcls : next.closing = core.closing)
    (hpend : next.pending = core.pending) : next.ArchivalInvariant :=
  ⟨hlc ▸ arch.lifecycle, hlc ▸ hrep ▸ hown ▸ hcls ▸ hpend ▸ arch.archivingGuarded,
    hlc ▸ hpend ▸ arch.noIntentWhileArchiving, hrep ▸ hpend ▸ arch.replacementPresent⟩

private theorem Core.ArchivalInvariant.stopGuarded {core : Core} (arch : core.ArchivalInvariant)
    (hnop : core.lifecycle.phaseValue = .archiving →
      core.replacement.isSome = true ∨ core.owner ≠ .current ∨ core.closing ≠ .open) :
    core.stop.ArchivalInvariant := by
  refine ⟨Lifecycle.request_archival core.lifecycle .stop (fun h => by cases h) arch.lifecycle,
    ?_, ?_, ?_⟩
  · intro hph
    have hprev : core.lifecycle.phaseValue = .archiving :=
      (Lifecycle.request_phaseValue_archiving core.lifecycle .stop).mp hph
    rcases hnop hprev with hr | ho | hc
    · exact .inl hr
    · exact .inr (.inl ho)
    · exact .inr (.inr (.inl hc))
  · intro c s hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro st ack hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp

private theorem Core.ArchivalInvariant.waiting {core next : Core} {p : Pending}
    (arch : core.ArchivalInvariant)
    (hlc : next.lifecycle = core.lifecycle)
    (hrep : next.replacement = core.replacement)
    (_hown : next.owner = core.owner)
    (_hcls : next.closing = core.closing)
    (hp : next.pending = some p)
    (hnop : core.lifecycle.phaseValue = .archiving →
      next.replacement.isSome = true ∨ next.owner ≠ .current ∨ next.closing ≠ .open ∨
        (∃ id d st, p = .archive id d st) ∨ (∃ id d a, p = .reopen id d a))
    (hnint : ∀ c s, p = .intent c s → core.lifecycle.phaseValue ≠ .archiving)
    (hnrep : ∀ st ack, p = .replacement st ack → core.replacement.isSome = true) :
    next.ArchivalInvariant := by
  refine ⟨hlc ▸ arch.lifecycle, ?_, ?_, ?_⟩
  · intro hph
    rw [hlc] at hph
    rcases hnop hph with h | h | h | ⟨id, d, st, h⟩ | ⟨id, d, a, h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl ⟨id, d, st, by rw [hp, h]⟩)))
    · exact .inr (.inr (.inr (.inr ⟨id, d, a, by rw [hp, h]⟩)))
  · intro c s hpi
    rw [hp] at hpi
    cases Option.some.inj hpi
    rw [hlc]
    exact hnint c s rfl
  · intro st ack hpr
    rw [hp] at hpr
    cases Option.some.inj hpr
    rw [hrep]
    exact hnrep st ack rfl

private theorem Core.ArchivalInvariant.report {core : Core} (arch : core.ArchivalInvariant)
    (tr : ControlTransition) (reason : String) :
    (core.report tr reason).ArchivalInvariant :=
  arch.same rfl rfl rfl rfl rfl

private theorem Core.ArchivalInvariant.moveTo_stopped {core : Core}
    (lc : Lifecycle) (hlc : lc.Archival)
    (hph : lc.phaseValue = .archiving →
      core.replacement.isSome = true ∨ core.owner ≠ .current ∨ core.closing ≠ .open) :
    (core.moveTo lc).ArchivalInvariant := by
  refine ⟨hlc, ?_, ?_, ?_⟩
  · intro hp
    rcases hph hp with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  · intro c s hp
    simp only [Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp [hwt] at hp
  · intro st ack hp
    simp only [Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp [hwt] at hp

private structure Core.ShapeInvariant (core : Core) : Prop where
  archival : core.ArchivalInvariant
  intentNoReplacement : ∀ c s, core.pending = some (.intent c s) →
    core.replacement = none
  intentNonStartStopped : ∀ c s, core.pending = some (.intent c s) →
    c ≠ .start → s.desired = .stopped
  replacementMatches : ∀ st ack, core.pending = some (.replacement st ack) →
    core.replacement = some st
  replacementArchiving : core.replacement.isSome = true →
    core.lifecycle.phaseValue = .archiving
  archivePhase : ∀ id d t, core.pending = some (.archive id d t) →
    core.lifecycle.phaseValue = .archiving
  reopenPhase : ∀ id d a, core.pending = some (.reopen id d a) →
    core.lifecycle.phaseValue = .archiving
  launchGuards : ∀ s p, core.pending = some (.launch s p) →
    core.lifecycle.clearPendingValue = none ∧ core.replacement = none ∧
      core.lifecycle.phaseValue ≠ .archiving
  clearPendingPersisted :
    (core.lifecycle.clearPendingValue.isSome = true ∨
      core.lifecycle.phaseValue = .archiving ∨ core.replacement.isSome = true) →
    core.persisted.desired = .stopped
  pendingDesiredMatch :
    (core.lifecycle.clearPendingValue.isSome = true ∨
      core.lifecycle.phaseValue = .archiving ∨ core.replacement.isSome = true) →
    (∀ g a s, core.pending = some (.adopt g a s) → s.desired = .stopped) ∧
      (∀ g a s d, core.pending = some (.commit g a s d) → s.desired = .stopped) ∧
      (∀ s, core.pending = some (.exitIntent s) → s.desired = .stopped)

private theorem Core.ShapeInvariant.same {core next : Core}
    (sh : core.ShapeInvariant)
    (harch : next.ArchivalInvariant)
    (hlc : next.lifecycle = core.lifecycle)
    (hpers : next.persisted = core.persisted)
    (hrep : next.replacement = core.replacement)
    (hpend : next.pending = core.pending) : next.ShapeInvariant := by
  refine ⟨harch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c s hp; rw [hpend] at hp; rw [hrep]; exact sh.intentNoReplacement c s hp
  · intro c s hp hns; rw [hpend] at hp; exact sh.intentNonStartStopped c s hp hns
  · intro st ack hp; rw [hpend] at hp; rw [hrep]; exact sh.replacementMatches st ack hp
  · intro hr; rw [hlc]; apply sh.replacementArchiving; rwa [← hrep]
  · intro id d t hp; rw [hpend] at hp; rw [hlc]; exact sh.archivePhase id d t hp
  · intro id d a hp; rw [hpend] at hp; rw [hlc]; exact sh.reopenPhase id d a hp
  · intro s p hp; rw [hpend] at hp; rw [hlc, hrep]; exact sh.launchGuards s p hp
  · intro hg; rw [hpers]; apply sh.clearPendingPersisted; rwa [← hlc, ← hrep]
  · intro hg
    have hg' : core.lifecycle.clearPendingValue.isSome = true ∨
        core.lifecycle.phaseValue = .archiving ∨ core.replacement.isSome = true := by
      rwa [← hlc, ← hrep]
    have hpd := sh.pendingDesiredMatch hg'
    refine ⟨fun g a s hp => hpd.1 g a s (hpend ▸ hp),
      fun g a s d hp => hpd.2.1 g a s d (hpend ▸ hp),
      fun s hp => hpd.2.2 s (hpend ▸ hp)⟩

private theorem Core.ShapeInvariant.report {core : Core} (sh : core.ShapeInvariant)
    (tr : ControlTransition) (reason : String) :
    (core.report tr reason).ShapeInvariant :=
  sh.same (sh.archival.report tr reason) rfl rfl rfl rfl

private theorem Core.ShapeInvariant.stop {core : Core} (sh : core.ShapeInvariant)
    (harch : core.stop.ArchivalInvariant) : core.stop.ShapeInvariant := by
  refine ⟨harch, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c s hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro c s hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro st ack hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro hr
    exact (Lifecycle.request_phaseValue_archiving core.lifecycle .stop).mpr
      (sh.replacementArchiving hr)
  · intro id d t hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro id d a hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro s p hp
    simp only [Core.stop, Core.moveTo] at hp
    cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
      simp [hwt] at hp
  · intro hg
    rcases hg with hcp | hph | hrep
    · simp only [Core.stop, Core.moveTo, Lifecycle.request_stop_clearPendingValue] at hcp
      cases hcp
    · have hph' := (Lifecycle.request_phaseValue_archiving core.lifecycle .stop).mp hph
      exact sh.clearPendingPersisted (.inr (.inl hph'))
    · exact sh.clearPendingPersisted (.inr (.inr hrep))
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · intro g a s hp
      simp only [Core.stop, Core.moveTo] at hp
      cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
        simp [hwt] at hp
    · intro g a s d hp
      simp only [Core.stop, Core.moveTo] at hp
      cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
        simp [hwt] at hp
    · intro s hp
      simp only [Core.stop, Core.moveTo] at hp
      cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
        simp [hwt] at hp

private theorem Core.ShapeInvariant.stopWhenIdle {core : Core} (sh : core.ShapeInvariant)
    (hp : core.pending = none) : core.stop.ShapeInvariant := by
  refine sh.stop (sh.archival.stopGuarded fun harch => ?_)
  rcases sh.archival.archivingGuarded harch with hr | ho | hc | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · exact .inl hr
  · exact .inr (.inl ho)
  · exact .inr (.inr hc)
  · rw [hp] at h; cases h
  · rw [hp] at h; cases h

private theorem Core.ShapeInvariant.clearGuards {core : Core} (sh : core.ShapeInvariant)
    (hp : core.pending = none) :
    core.lifecycle.phaseValue = .archiving →
      core.replacement.isSome = true ∨ core.owner ≠ .current ∨ core.closing ≠ .open := by
  intro harch
  rcases sh.archival.archivingGuarded harch with hr | ho | hc | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · exact .inl hr
  · exact .inr (.inl ho)
  · exact .inr (.inr hc)
  · rw [hp] at h; cases h
  · rw [hp] at h; cases h

private theorem Core.ShapeInvariant.start (persisted : PersistedState)
    (clearDisabled : Option String) (reason : String) (reading : Nat) :
    (Core.start persisted clearDisabled reason reading).ShapeInvariant := by
  refine ⟨⟨Lifecycle.initial_archival persisted.identity persisted.desired,
    (fun h => by cases h), (fun c s hp => by cases hp), (fun st ack hp => by cases hp)⟩,
    (fun c s hp => by cases hp), (fun c s hp => by cases hp), (fun st ack hp => by cases hp),
    (fun hr => by cases hr), (fun id d t hp => by cases hp), (fun id d a hp => by cases hp),
    (fun s p hp => by cases hp), ?_, ?_⟩
  · intro hg
    rcases hg with hcp | hph | hrep
    · cases hcp
    · cases hph
    · cases hrep
  · intro _
    exact ⟨(fun g a s hp => by cases hp), (fun g a s d hp => by cases hp), (fun s hp => by cases hp)⟩

private theorem Core.ShapeInvariant.at {stepped : Stepped} (sh : stepped.core.ShapeInvariant)
    (now : Nat) : (stepped.at now).core.ShapeInvariant :=
  sh.same (sh.archival.same rfl rfl rfl rfl rfl) rfl rfl rfl rfl

private theorem Core.ShapeInvariant.launchCheck {core : Core} (sh : core.ShapeInvariant)
    (now : Nat) (hnone : core.pending = none) :
    (core.launchCheck now).core.ShapeInvariant := by
  unfold Core.launchCheck
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq] at hcond
    rcases hcond with ⟨⟨hrep, _⟩, hcls⟩
    cases hr : core.lifecycle.reserve (clockWord now) with
    | none => exact sh
    | some v =>
      cases hl : core.persisted.launch with
      | error _ => dsimp only; exact (sh.stopWhenIdle hnone).report _ _
      | ok l =>
        cases ho : core.owner with
        | retired _ => dsimp only; exact (sh.stopWhenIdle hnone).report _ _
        | current =>
          dsimp only
          have hguards := Lifecycle.reserve_guards core.lifecycle (clockWord now) v.1 v.2 hr
          refine ⟨?_, (fun c s h => by cases h), (fun c s h => by cases h),
            (fun st ack h => by cases h),
            (fun hr2 => sh.replacementArchiving (by simpa using hr2)),
            (fun id d t h => by cases h), (fun id d a h => by cases h), ?_,
            (fun hg => sh.clearPendingPersisted (by simpa using hg)), ?_⟩
          · exact sh.archival.waiting rfl rfl ho.symm rfl rfl
              (fun hph => absurd hph hguards.1)
              (fun _ _ h => by cases h) (fun _ _ h => by cases h)
          · intro s p h
            cases Option.some.inj h
            exact ⟨hguards.2.1, hrep, hguards.1⟩
          · intro _
            exact ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
              (fun s h => by cases h)⟩
  · exact sh

private theorem Core.ShapeInvariant.closeOut {core : Core} (sh : core.ShapeInvariant)
    (hnone : core.pending = none)
    (hcls : core.closing ≠ .open) :
    core.closeOut.core.ShapeInvariant := by
  unfold Core.closeOut
  split
  · refine ⟨sh.archival.waiting rfl rfl rfl rfl rfl (fun _ => .inr (.inr (.inl hcls)))
        (fun _ _ h => by cases h) (fun _ _ h => by cases h),
      (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
      sh.replacementArchiving, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
      (fun _ _ h => by cases h), sh.clearPendingPersisted,
      (fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
        (fun _ h => by cases h)⟩)⟩
  · simp only [Core.closed]
    cases hc : core.closing with
    | «open» => exact absurd hc hcls
    | closed _ =>
      dsimp only
      exact sh.same ⟨sh.archival.lifecycle, fun _ => .inr (.inr (.inl (by rw [hc]; intro h; cases h))),
        (fun c s hp => by rw [hnone] at hp; cases hp),
        (fun st ack hp => by rw [hnone] at hp; cases hp)⟩ rfl rfl rfl rfl
    | closing _ =>
      dsimp only
      exact sh.same ⟨sh.archival.lifecycle, fun _ => .inr (.inr (.inl (by intro h; cases h))),
        (fun c s hp => by rw [hnone] at hp; cases hp),
        (fun st ack hp => by rw [hnone] at hp; cases hp)⟩ rfl rfl rfl rfl

private theorem Core.ShapeInvariant.exitReported {core : Core} (sh : core.ShapeInvariant)
    (report : ExitReport) (hnone : core.pending = none) :
    (core.exitReported report).core.ShapeInvariant := by
  unfold Core.exitReported
  have sh0 : ({ core with detail := report.detail, failure := report.failure } :
      Core).ShapeInvariant :=
    sh.same (sh.archival.same rfl rfl rfl rfl rfl) rfl rfl rfl rfl
  have shrep := sh0.report report.transition report.reason
  cases hown : ({ core with detail := report.detail, failure := report.failure }.report
      report.transition report.reason).owner with
  | retired reason =>
    dsimp only
    rw [hown]
    exact shrep.report _ _
  | current =>
    dsimp only
    rw [hown]
    refine ⟨shrep.archival.waiting rfl rfl hown.symm rfl rfl ?_ (fun _ _ h => by cases h)
        (fun _ _ h => by cases h),
      (fun c s h => by cases h), (fun c s h => by cases h), (fun st ack h => by cases h),
      shrep.replacementArchiving, (fun id d t h => by cases h), (fun id d a h => by cases h),
      (fun s p h => by cases h), shrep.clearPendingPersisted, ?_⟩
    · intro hph
      rcases shrep.clearGuards hnone hph with hr | ho | hc
      · exact .inl hr
      · exact absurd hown ho
      · exact .inr (.inr (.inl hc))
    · intro hg
      refine ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h), fun s h => ?_⟩
      cases Option.some.inj h
      rcases hg with hcp | hph | hrep
      · exact shrep.archival.lifecycle.1 hcp
      · exact shrep.archival.lifecycle.2 hph
      · exact shrep.archival.lifecycle.2 (shrep.replacementArchiving hrep)

private theorem Core.ShapeInvariant.candidate {core : Core} (sh : core.ShapeInvariant)
    (hp : core.pending = none) (generation : UInt64) (actual : CoreIdentity) :
    (core.candidate generation actual).core.ShapeInvariant := by
  simp only [Core.candidate]
  split
  · exact sh
  · split
    · exact (sh.stopWhenIdle hp).report _ _
    · cases ho : core.owner with
      | retired _ => simp only [Core.adoptFailed]; exact (sh.stopWhenIdle hp).report _ _
      | current =>
        refine ⟨sh.archival.waiting rfl rfl ho.symm rfl rfl
            (fun hph => by
              rcases sh.clearGuards hp hph with hr | ho' | hc'
              · exact .inl hr
              · exact absurd ho ho'
              · exact .inr (.inr (.inl hc')))
            (fun _ _ h => by cases h) (fun _ _ h => by cases h),
          (fun c s h => by cases h), (fun c s h => by cases h),
          (fun st ack h => by cases h), sh.replacementArchiving,
          (fun id d t h => by cases h), (fun id d a h => by cases h),
          (fun s p h => by cases h), sh.clearPendingPersisted, ?_⟩
        intro hg
        refine ⟨fun g a s h => ?_, (fun g a s d h => by cases h), (fun s h => by cases h)⟩
        cases Option.some.inj h
        exact sh.clearPendingPersisted hg

private theorem Core.ShapeInvariant.exited {core : Core} (sh : core.ShapeInvariant)
    (hp : core.pending = none) (now : Nat) (code : UInt32) (uptimeMs : Nat) :
    (core.exited now code uptimeMs).core.ShapeInvariant := by
  simp only [Core.exited]
  cases hslot : core.slot with
  | empty | draining _ _ _ => exact sh
  | live generation =>
    let requested := core.lifecycle.phaseValue == .stopping generation
    let failed := if requested then core.lifecycle
      else core.lifecycle.failed generation (clockWord now) (decide (uptimeMs > healthyRunMs))
    let lc := failed.retire generation
    have hlca : lc.Archival := by
      apply Lifecycle.retire_archival
      by_cases hreq : requested
      · simp only [failed, hreq, ↓reduceIte]; exact sh.archival.lifecycle
      · simp only [failed, hreq]
        exact Lifecycle.failed_archival _ _ _ _ sh.archival.lifecycle
    have hph_iff : lc.phaseValue = .archiving ↔ core.lifecycle.phaseValue = .archiving := by
      dsimp [lc]
      rw [Lifecycle.retire_phaseValue_archiving]
      by_cases hreq : requested
      · simp [failed, hreq]
      · simp only [failed, hreq]
        exact Lifecycle.failed_phaseValue_archiving _ _ _ _
    have hcp_eq : lc.clearPendingValue = core.lifecycle.clearPendingValue := by
      dsimp [lc]
      rw [Lifecycle.retire_clearPendingValue]
      by_cases hreq : requested
      · simp [failed, hreq]
      · simp only [failed, hreq]
        exact Lifecycle.failed_clearPendingValue _ _ _ _
    have harch : ({ core with
        lifecycle := lc, slot := .draining generation code requested
        detail := { core.detail with abnormalExit := code != 0 } } :
        Core).ArchivalInvariant := by
      refine ⟨hlca, ?_, (fun c s h => by rw [hp] at h; cases h),
        (fun st ack h => by rw [hp] at h; cases h)⟩
      intro hph
      rcases sh.clearGuards hp (hph_iff.mp hph) with hr | ho | hc'
      · exact .inl hr
      · exact .inr (.inl ho)
      · exact .inr (.inr (.inl hc'))
    have harchRep := harch.report (exitTransition requested lc)
      (exitReason code ++ "; process readers are draining")
    refine ⟨harchRep, (fun c s h => by rw [hp] at h; cases h),
      (fun c s h => by rw [hp] at h; cases h), (fun st ack h => by rw [hp] at h; cases h),
      fun hr => hph_iff.mpr (sh.replacementArchiving hr),
      (fun id d t h => by rw [hp] at h; cases h), (fun id d a h => by rw [hp] at h; cases h),
      (fun s p h => by rw [hp] at h; cases h),
      fun hg => by
        apply sh.clearPendingPersisted
        rcases hg with hcp | hph | hr
        · exact .inl (hcp_eq ▸ hcp)
        · exact .inr (.inl (hph_iff.mp hph))
        · exact .inr (.inr hr),
      fun _ => ⟨(fun g a s h => by rw [hp] at h; cases h),
        (fun g a s d h => by rw [hp] at h; cases h),
        (fun s h => by rw [hp] at h; cases h)⟩⟩

private theorem Core.ShapeInvariant.finished {core : Core} (sh : core.ShapeInvariant)
    (hp : core.pending = none) (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus) :
    (core.finished stdout stderr log).core.ShapeInvariant := by
  simp only [Core.finished]
  cases hslot : core.slot with
  | empty | live _ => exact sh
  | draining generation code requested =>
    cases hcls : core.closing with
    | «open» =>
      dsimp only
      split
      · refine ⟨⟨sh.archival.lifecycle,
            (fun hph => by
              rcases sh.clearGuards hp hph with hr | ho | hc'
              · exact .inl hr
              · exact .inr (.inl ho)
              · exact absurd hcls hc'),
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun c s h => by cases h), (fun c s h => by cases h),
          (fun st ack h => by cases h), sh.replacementArchiving,
          (fun id d t h => by cases h), (fun id d a h => by cases h),
          (fun s p h => by cases h), sh.clearPendingPersisted,
          fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
            (fun s h => by cases h)⟩⟩
      · have harchOpen : ({ core with slot := .empty, closing := .open } : Core).ArchivalInvariant :=
          sh.archival.same rfl rfl rfl hcls.symm rfl
        exact (sh.same harchOpen rfl rfl rfl rfl).exitReported _ hp
    | closing before =>
      dsimp only
      have harchCls : ({ core with
          slot := .empty
          detail := { core.detail with log := log, abnormalExit := code != 0 }
          failure := if terminationFailed code stdout stderr log then
            some (exitReason code ++ outputReason stdout stderr log) else core.failure
          closing := .closing (before || terminationFailed code stdout stderr log) } :
          Core).ArchivalInvariant :=
        ⟨sh.archival.lifecycle, fun _ => .inr (.inr (.inl (fun h => by cases h))),
          (fun c s h => by rw [hp] at h; cases h), (fun st ack h => by rw [hp] at h; cases h)⟩
      exact (sh.same harchCls rfl rfl rfl rfl).report _ _
    | closed _ =>
      dsimp only
      exact sh.same (sh.archival.same rfl rfl rfl hcls.symm rfl) rfl rfl rfl rfl

private theorem Core.ShapeInvariant.dispatch (core : Core) (clearDisabled : Option String)
    (now : Nat) (event : Event) (sh : core.ShapeInvariant) :
    (core.dispatch clearDisabled now event).core.ShapeInvariant := by
  unfold Core.dispatch
  cases hp : core.pending with
  | some _ => exact sh
  | none =>
    cases hc : core.closing with
    | closed _ => exact sh
    | closing _ =>
      have hcls : core.closing ≠ .open := by rw [hc]; intro h; cases h
      cases event with
      | command _ => exact sh
      | candidate gen actual => exact sh.candidate hp gen actual
      | exited code uptimeMs => exact sh.exited hp now code uptimeMs
      | finished stdout stderr log => exact sh.finished hp stdout stderr log
      | refused reason =>
        simp only [Core.refused, hc]
        exact sh.same ⟨sh.archival.lifecycle, fun _ => .inr (.inr (.inl (by intro h; cases h))),
          (fun c s h => by rw [hp] at h; cases h), (fun st ack h => by rw [hp] at h; cases h)⟩
          rfl rfl rfl rfl
      | tick =>
        simp only [Core.tick, hc]
        cases core.slot with
        | empty => exact sh.closeOut hp hcls
        | live _ | draining _ _ _ => exact sh
      | close => simp only [Core.close, hc]; exact sh
    | «open» =>
      cases event with
      | command cmd =>
        simp only [Core.command]
        split
        · exact sh
        · cases hrep : core.replacement with
          | some rep =>
            dsimp only
            split
            · exact sh.report _ _
            · split
              · cases ho : core.owner with
                | retired _ =>
                  dsimp only; simp only [Core.intentFailed]; exact (sh.stopWhenIdle hp).report _ _
                | current =>
                  dsimp only
                  have hph : core.lifecycle.phaseValue = .archiving :=
                    sh.replacementArchiving (by simp [hrep])
                  have hps : core.persisted.desired = .stopped :=
                    sh.clearPendingPersisted (.inr (.inr (by simp [hrep])))
                  refine ⟨⟨sh.archival.lifecycle, (fun _ => .inl rfl),
                      (fun _ _ h => by cases h), (fun _ _ _ => rfl)⟩,
                    (fun c s h => by cases h), (fun c s h => by cases h),
                    (fun st ack h => by cases Option.some.inj h; rfl),
                    fun _ => hph, (fun id d t h => by cases h),
                    (fun id d a h => by cases h), (fun s p h => by cases h),
                    fun _ => hps,
                    fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
                      (fun s h => by cases h)⟩⟩
              · have hph : core.lifecycle.phaseValue = .archiving :=
                  sh.replacementArchiving (by simp [hrep])
                have hps : core.persisted.desired = .stopped :=
                  sh.clearPendingPersisted (.inr (.inr (by simp [hrep])))
                exact ⟨⟨sh.archival.lifecycle, fun _ => .inl rfl,
                    (fun c s h => by rw [hp] at h; cases h),
                    (fun st ack h => by rw [hp] at h; cases h)⟩,
                  (fun c s h => by rw [hp] at h; cases h),
                  (fun c s h => by rw [hp] at h; cases h),
                  (fun st ack h => by rw [hp] at h; cases h),
                  fun _ => hph,
                  (fun id d t h => by rw [hp] at h; cases h),
                  (fun id d a h => by rw [hp] at h; cases h),
                  (fun s p h => by rw [hp] at h; cases h),
                  fun _ => hps,
                  fun _ => ⟨(fun g a s h => by rw [hp] at h; cases h),
                    (fun g a s d h => by rw [hp] at h; cases h),
                    (fun s h => by rw [hp] at h; cases h)⟩⟩
          | none =>
            dsimp only
            cases ho : core.owner with
            | retired _ =>
              dsimp only; simp only [Core.intentFailed]; exact (sh.stopWhenIdle hp).report _ _
            | current =>
              dsimp only
              have hnotArch : core.lifecycle.phaseValue ≠ .archiving := by
                intro hph
                rcases sh.clearGuards hp hph with hr | ho' | hc'
                · rw [hrep] at hr; cases hr
                · exact ho' ho
                · exact hc' hc
              refine ⟨sh.archival.waiting rfl hrep.symm ho.symm rfl rfl
                  (fun hph => absurd hph hnotArch)
                  (fun _ _ _ => hnotArch)
                  (fun _ _ h => by cases h),
                (fun c s h => by cases Option.some.inj h; rfl),
                (fun c s h hns => by
                  cases Option.some.inj h
                  cases cmd with
                  | start => exact absurd rfl hns
                  | stop | clear => rfl),
                (fun st ack h => by cases h), (fun h => by cases h),
                (fun id d t h => by cases h), (fun id d a h => by cases h),
                (fun s p h => by cases h),
                (fun hg => by
                  apply sh.clearPendingPersisted
                  rcases hg with h | h | h
                  · exact .inl h
                  · exact .inr (.inl h)
                  · cases h),
                fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
                  (fun s h => by cases h)⟩⟩
      | candidate gen actual => exact sh.candidate hp gen actual
      | exited code uptimeMs => exact sh.exited hp now code uptimeMs
      | finished stdout stderr log => exact sh.finished hp stdout stderr log
      | refused reason =>
        simp only [Core.refused, hc]
        exact sh.report _ _
      | tick =>
        have hmol : (core.mapOrLaunch now).core.ShapeInvariant := by
          simp only [Core.mapOrLaunch]
          split
          · exact ⟨sh.archival.waiting rfl rfl rfl rfl rfl
                (fun hph => by
                  rcases sh.clearGuards hp hph with hr | ho | hc'
                  · exact .inl hr
                  · exact .inr (.inl ho)
                  · exact .inr (.inr (.inl hc')))
                (fun _ _ h => by cases h) (fun _ _ h => by cases h),
              (fun c s h => by cases h), (fun c s h => by cases h),
              (fun st ack h => by cases h), sh.replacementArchiving,
              (fun id d t h => by cases h), (fun id d a h => by cases h),
              (fun s p h => by cases h), sh.clearPendingPersisted,
              fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
                (fun s h => by cases h)⟩⟩
          · exact sh.launchCheck now hp
        simp only [Core.tick, hc]
        cases hrep : core.replacement with
        | some rep =>
          dsimp only
          cases ho : core.owner with
          | retired _ => dsimp only; exact sh
          | current =>
            dsimp only
            have hph : core.lifecycle.phaseValue = .archiving :=
              sh.replacementArchiving (by simp [hrep])
            have hps : core.persisted.desired = .stopped :=
              sh.clearPendingPersisted (.inr (.inr (by simp [hrep])))
            exact ⟨⟨sh.archival.lifecycle, (fun _ => .inl rfl),
                (fun _ _ h => by cases h), (fun _ _ _ => rfl)⟩,
              (fun c s h => by cases h), (fun c s h => by cases h),
              (fun st ack h => by cases Option.some.inj h; rfl),
              (fun _ => hph), (fun id d t h => by cases h),
              (fun id d a h => by cases h), (fun s p h => by cases h),
              (fun _ => hps),
              fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
                (fun s h => by cases h)⟩⟩
        | none =>
          dsimp only
          cases hai : core.lifecycle.archiveIntent with
          | none => dsimp only; exact hmol
          | some intended =>
            cases core.slot with
            | empty =>
              dsimp only
              simp only [Core.clear]
              split
              · exact (sh.stopWhenIdle hp).report _ _
              · cases ho : core.owner with
                | retired _ => dsimp only; exact sh
                | current =>
                  dsimp only
                  have hnotArch := Lifecycle.archiveIntent_phase_ne_archiving _ _ hai
                  exact ⟨sh.archival.waiting rfl rfl ho.symm rfl rfl
                      (fun hph => absurd hph hnotArch)
                      (fun _ _ h => by cases h) (fun _ _ h => by cases h),
                    (fun c s h => by cases h), (fun c s h => by cases h),
                    (fun st ack h => by cases h), sh.replacementArchiving,
                    (fun id d t h => by cases h), (fun id d a h => by cases h),
                    (fun s p h => by cases h), sh.clearPendingPersisted,
                    fun _ => ⟨(fun g a s h => by cases h), (fun g a s d h => by cases h),
                      (fun s h => by cases h)⟩⟩
            | live _ | draining _ _ _ => dsimp only; exact hmol
      | close =>
        simp only [Core.close, hc]
        let stopped := ({ core with closing := .closing core.failure.isSome } : Core).stop
        have hcls : stopped.closing ≠ .open := by intro h; cases h
        have sh1 : stopped.ShapeInvariant := by
          have shcls : ({ core with closing := .closing core.failure.isSome } :
              Core).ShapeInvariant :=
            sh.same ⟨sh.archival.lifecycle, fun _ => .inr (.inr (.inl (by intro h; cases h))),
              (fun c s h => by rw [hp] at h; cases h), (fun st ack h => by rw [hp] at h; cases h)⟩
              rfl rfl rfl rfl
          exact shcls.stopWhenIdle hp
        have sh2 := sh1.report .stopRequested
          "viewer closing; finishing the current attempt and checkpoint"
        split
        · rename_i hslot
          have hse : core.slot = .empty := beq_iff_eq.mp hslot
          exact sh2.closeOut (by
            simp only [stopped, Core.stop, Core.moveTo, hse, windUpTarget]; rfl) hcls
        · exact sh2

theorem Core.step_shapeInvariant (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (sh : core.ShapeInvariant) :
    (core.step clearDisabled reading event).core.ShapeInvariant :=
  (Core.ShapeInvariant.dispatch core clearDisabled (core.instant reading) event sh).at
    (core.instant reading)

private theorem Core.ShapeInvariant.base_of_nonArchive {core : Core} {pending : Pending}
    (sh : core.ShapeInvariant) (hp : core.pending = some pending)
    (hna : ∀ id d t, pending ≠ .archive id d t)
    (hnr : ∀ id d a, pending ≠ .reopen id d a) :
    ({ core with pending := none } : Core).ShapeInvariant := by
  have harch : ({ core with pending := none } : Core).ArchivalInvariant :=
    ⟨sh.archival.lifecycle,
      fun hph => by
        rcases sh.archival.archivingGuarded hph with hr | ho | hc | ⟨id, d, t, ha⟩ | ⟨id, d, a, hrp⟩
        · exact .inl hr
        · exact .inr (.inl ho)
        · exact .inr (.inr (.inl hc))
        · rw [hp] at ha; cases ha; exact absurd rfl (hna id d t)
        · rw [hp] at hrp; cases hrp; exact absurd rfl (hnr id d a),
      (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  refine ⟨harch, (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
    sh.replacementArchiving, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
    (fun _ _ h => by cases h), sh.clearPendingPersisted,
    fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h), (fun _ h => by cases h)⟩⟩

private def Core.ArchiveClean (core : Core) : Prop :=
  (∀ id d t, core.pending = some (.archive id d t) → core.replacement = none) ∧
    (∀ id d a, core.pending = some (.reopen id d a) → core.replacement = none)

private theorem Core.ArchiveClean.at {stepped : Stepped} (cln : stepped.core.ArchiveClean)
    (now : Nat) : (stepped.at now).core.ArchiveClean :=
  cln

private theorem Core.ArchiveClean.empty (core : Core) (h : core.pending = none) :
    core.ArchiveClean :=
  ⟨(fun _ _ _ hp => by rw [h] at hp; cases hp), (fun _ _ _ hp => by rw [h] at hp; cases hp)⟩

private theorem Core.ArchiveClean.of_pending {core : Core} {p : Pending}
    (h : core.pending = some p)
    (ha : ∀ id d t, p ≠ .archive id d t) (hr : ∀ id d a, p ≠ .reopen id d a) :
    core.ArchiveClean :=
  ⟨(fun id d t hp => by rw [h] at hp; cases Option.some.inj hp; exact absurd rfl (ha id d t)),
   (fun id d a hp => by rw [h] at hp; cases Option.some.inj hp; exact absurd rfl (hr id d a))⟩

private theorem Core.ArchiveClean.stop (core : Core) : core.stop.ArchiveClean :=
  ⟨(fun _ _ _ h => by
      simp only [Core.stop, Core.moveTo] at h
      cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
        simp [hwt] at h),
    (fun _ _ _ h => by
      simp only [Core.stop, Core.moveTo] at h
      cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
        simp [hwt] at h)⟩

private theorem Core.ArchiveClean.report {core : Core} (cln : core.ArchiveClean)
    (tr : ControlTransition) (reason : String) : (core.report tr reason).ArchiveClean :=
  cln

private theorem Core.ArchiveClean.start (persisted : PersistedState)
    (clearDisabled : Option String) (reason : String) (reading : Nat) :
    (Core.start persisted clearDisabled reason reading).ArchiveClean :=
  Core.ArchiveClean.empty _ rfl

private theorem Core.ArchiveClean.launchCheck {core : Core} (cln : core.ArchiveClean)
    (_hp : core.pending = none) (now : Nat) : (core.launchCheck now).core.ArchiveClean := by
  simp only [Core.launchCheck]
  split
  · cases hr : core.lifecycle.reserve (clockWord now) with
    | none => dsimp only; exact cln
    | some _ =>
      cases hl : core.persisted.launch with
      | error _ => dsimp only; exact (Core.ArchiveClean.stop _).report _ _
      | ok _ =>
        cases ho : core.owner with
        | retired _ => dsimp only; exact (Core.ArchiveClean.stop _).report _ _
        | current =>
          dsimp only
          exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
            (fun _ _ _ h => by cases h)
  · exact cln

private theorem Core.ArchiveClean.closeOut (core : Core) (hp : core.pending = none) :
    core.closeOut.core.ArchiveClean := by
  simp only [Core.closeOut]
  split
  · exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)
  · simp only [Core.closed]
    cases hc : core.closing <;> exact Core.ArchiveClean.empty _ (by simp [hp])

private theorem Core.ArchiveClean.exitReported (core : Core) (hp : core.pending = none)
    (report : ExitReport) : (core.exitReported report).core.ArchiveClean := by
  simp only [Core.exitReported]
  split
  · exact Core.ArchiveClean.empty _ (by simp [Core.report, hp])
  · exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h)

private theorem Core.ArchiveClean.candidate {core : Core} (cln : core.ArchiveClean)
    (_hp : core.pending = none) (generation : UInt64) (actual : CoreIdentity) :
    (core.candidate generation actual).core.ArchiveClean := by
  simp only [Core.candidate]
  split
  · exact cln
  · split
    · exact (Core.ArchiveClean.stop _).report _ _
    · cases core.owner with
      | retired _ => dsimp only; simp only [Core.adoptFailed]; exact (Core.ArchiveClean.stop _).report _ _
      | current =>
        dsimp only
        exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h)

private theorem Core.ArchiveClean.exited (core : Core) (hp : core.pending = none)
    (now : Nat) (code : UInt32) (uptimeMs : Nat) :
    (core.exited now code uptimeMs).core.ArchiveClean := by
  simp only [Core.exited]
  cases core.slot <;> exact Core.ArchiveClean.empty _ (by simp [Core.report, hp])

private theorem Core.ArchiveClean.finished (core : Core) (hp : core.pending = none)
    (stdout : OutputStatus) (stderr : PipeResult) (log : LogStatus) :
    (core.finished stdout stderr log).core.ArchiveClean := by
  simp only [Core.finished]
  cases core.slot with
  | empty | live _ => dsimp only; exact Core.ArchiveClean.empty _ hp
  | draining _ _ _ =>
    dsimp only
    cases core.closing with
    | «open» =>
      dsimp only
      split
      · exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
          (fun _ _ _ h => by cases h)
      · exact Core.ArchiveClean.exitReported { core with slot := .empty, closing := .open } hp _
    | closing _ => dsimp only; exact Core.ArchiveClean.empty _ (by simp [Core.report, hp])
    | closed _ => dsimp only; exact Core.ArchiveClean.empty _ hp

private theorem Core.ArchiveClean.step (core : Core) (clearDisabled : Option String)
    (reading : Nat) (event : Event) (cln : core.ArchiveClean) :
    (core.step clearDisabled reading event).core.ArchiveClean := by
  unfold Core.step
  apply Core.ArchiveClean.at
  unfold Core.dispatch
  cases hp : core.pending with
  | some _ => exact cln
  | none =>
    cases hc : core.closing with
    | closed _ => exact cln
    | closing _ =>
      cases event with
      | command _ => exact cln
      | candidate gen actual => exact cln.candidate hp gen actual
      | exited code uptimeMs => exact Core.ArchiveClean.exited core hp _ code uptimeMs
      | finished stdout stderr log => exact Core.ArchiveClean.finished core hp stdout stderr log
      | refused _ => simp [Core.refused, hc]; exact cln
      | tick =>
        simp only [Core.tick, hc]
        cases core.slot with
        | empty => dsimp only; exact Core.ArchiveClean.closeOut core hp
        | live _ | draining _ _ _ => dsimp only; exact cln
      | close => simp [Core.close, hc]; exact cln
    | «open» =>
      cases event with
      | command _ =>
        simp only [Core.command]
        split
        · exact cln
        · cases core.replacement with
          | some _ =>
            dsimp only
            split
            · exact cln.report _ _
            · split
              · cases core.owner with
                | retired _ =>
                  dsimp only; simp [Core.intentFailed]; exact (Core.ArchiveClean.stop _).report _ _
                | current =>
                  dsimp only
                  exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
                    (fun _ _ _ h => by cases h)
              · exact Core.ArchiveClean.empty _ hp
          | none =>
            dsimp only
            cases core.owner with
            | retired _ =>
              dsimp only; simp [Core.intentFailed]; exact (Core.ArchiveClean.stop _).report _ _
            | current =>
              dsimp only
              exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
                (fun _ _ _ h => by cases h)
      | candidate gen actual => exact cln.candidate hp gen actual
      | exited code uptimeMs => exact Core.ArchiveClean.exited core hp _ code uptimeMs
      | finished stdout stderr log => exact Core.ArchiveClean.finished core hp stdout stderr log
      | refused _ => simp [Core.refused, hc]; exact cln
      | tick =>
        have hmol : ∀ now, (core.mapOrLaunch now).core.ArchiveClean := by
          intro now
          simp only [Core.mapOrLaunch]
          split
          · exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
              (fun _ _ _ h => by cases h)
          · exact cln.launchCheck hp now
        simp only [Core.tick, hc]
        cases core.replacement with
        | some _ =>
          dsimp only
          cases core.owner with
          | retired _ => dsimp only; exact cln
          | current =>
            dsimp only
            exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
              (fun _ _ _ h => by cases h)
        | none =>
          dsimp only
          cases core.lifecycle.archiveIntent with
          | none => dsimp only; exact hmol _
          | some _ =>
            cases core.slot with
            | empty =>
              dsimp only
              simp only [Core.clear]
              split
              · exact (Core.ArchiveClean.stop _).report _ _
              · cases core.owner with
                | retired _ => dsimp only; exact cln
                | current =>
                  dsimp only
                  exact Core.ArchiveClean.of_pending rfl (fun _ _ _ h => by cases h)
                    (fun _ _ _ h => by cases h)
            | live _ | draining _ _ _ => dsimp only; exact hmol _
      | close =>
        simp only [Core.close, hc]
        split
        · rename_i hslot
          have hse : core.slot = .empty := beq_iff_eq.mp hslot
          exact Core.ArchiveClean.closeOut _ (by
            simp only [Core.report, Core.stop, Core.moveTo, hse, windUpTarget]; rfl)
        · exact (Core.ArchiveClean.stop _).report _ _

private theorem Core.ShapeInvariant.resume {core : Core} (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (hp : core.pending = some pending) (sh : core.ShapeInvariant) (cln : core.ArchiveClean) :
    (core.resume reading pending result).core.ShapeInvariant ∧
      (core.resume reading pending result).core.ArchiveClean := by
  have nonArchClean : ∀ (base : Core) (hlc : base.pending = none),
      base.ShapeInvariant → base.ArchiveClean := fun base hlc _ =>
    ⟨(fun _ _ _ h => by rw [hlc] at h; cases h), (fun _ _ _ h => by rw [hlc] at h; cases h)⟩
  unfold Core.resume
  suffices hboth : ({ core with pending := none }.resolve (core.instant reading) pending result).core.ShapeInvariant ∧
      ({ core with pending := none }.resolve (core.instant reading) pending result).core.ArchiveClean from
    ⟨hboth.1.at _, hboth.2.at _⟩
  cases pending with
  | intent command state =>
    have hnotArch : core.lifecycle.phaseValue ≠ .archiving :=
      sh.archival.noIntentWhileArchiving command state hp
    have hrep : core.replacement = none := sh.intentNoReplacement command state hp
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      exact ⟨(shBase.stopWhenIdle rfl).report _ _,
        ⟨(fun _ _ _ h => by
            simp only [Core.resolve, Core.intentFailed, Core.report, Core.stop, Core.moveTo] at h ⊢
            cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
              simp [hwt] at h),
          (fun _ _ _ h => by
            simp only [Core.resolve, Core.intentFailed, Core.report, Core.stop, Core.moveTo] at h ⊢
            cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
              simp [hwt] at h)⟩⟩
    | ok u =>
      cases u
      simp only [Core.resolve, Core.intentSaved]
      let lc := core.lifecycle.request command
      have hlca : lc.Archival := Lifecycle.request_archival core.lifecycle command
        (fun _ => hnotArch) sh.archival.lifecycle
      have hlcph : lc.phaseValue ≠ .archiving := by
        intro h
        exact hnotArch ((Lifecycle.request_phaseValue_archiving core.lifecycle command).mp h)
      have hcpPers : lc.clearPendingValue.isSome = true → state.desired = .stopped := by
        intro hcp
        cases command with
        | start => rw [Lifecycle.request_start_clearPendingValue] at hcp; cases hcp
        | stop => rw [Lifecycle.request_stop_clearPendingValue] at hcp; cases hcp
        | clear => exact sh.intentNonStartStopped _ _ hp (fun h => by cases h)
      let baseS : Core := { core with persisted := state, pending := none }
      have archMove : (baseS.moveTo lc).ArchivalInvariant :=
        Core.ArchivalInvariant.moveTo_stopped (core := baseS) lc hlca (fun h => absurd h hlcph)
      have shMove : (baseS.moveTo lc).ShapeInvariant :=
        ⟨archMove,
          (fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun hr => by simp only [Core.moveTo, baseS] at hr; rw [hrep] at hr; cases hr),
          (fun _ _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun _ _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
          (fun hg => by
            rcases hg with hcp | hph | hr
            · exact hcpPers hcp
            · exact absurd hph hlcph
            · simp only [Core.moveTo, baseS] at hr; rw [hrep] at hr; cases hr),
          fun _ =>
            ⟨(fun _ _ _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
            (fun _ _ _ _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
            (fun _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h)⟩⟩
      refine ⟨shMove.report _ _, ?_⟩
      exact ⟨(fun _ _ _ h => by
          simp only [Core.report, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h),
        (fun _ _ _ h => by
          simp only [Core.report, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle lc <;> simp at h)⟩
  | launch state plan =>
    have hlg := sh.launchGuards state plan hp
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      exact ⟨(shBase.stopWhenIdle rfl).report _ _,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h⟩⟩
    | ok u =>
      cases u
      simp only [Core.resolve]
      cases hr : core.lifecycle.reserve (clockWord (core.instant reading)) with
      | none =>
        dsimp only
        exact ⟨⟨shBase.archival.same rfl rfl rfl rfl rfl,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
            sh.replacementArchiving, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
            (fun _ _ h => by cases h),
            (fun hg => by
              rcases hg with h | h | h
              · rw [hlg.1] at h; cases h
              · exact absurd h hlg.2.2
              · rw [hlg.2.1] at h; cases h),
            fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
              (fun _ h => by cases h)⟩⟩,
          ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      | some v =>
        dsimp only
        have hguards := Lifecycle.reserve_guards core.lifecycle _ v.1 v.2 hr
        have hlca := Lifecycle.reserve_archival core.lifecycle _ v.1 v.2 hr sh.archival.lifecycle
        have hcpv : v.2.clearPendingValue = none :=
          Lifecycle.reserve_clearPendingValue core.lifecycle _ v.1 v.2 hr
        refine ⟨⟨⟨hlca, fun hph => absurd hph hguards.2.2,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun h => by rw [hlg.2.1] at h; cases h),
          (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun hg => by
            rcases hg with hcp | hph | hrep
            · rw [hcpv] at hcp; cases hcp
            · exact absurd hph hguards.2.2
            · rw [hlg.2.1] at hrep; cases hrep),
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
          ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
  | spawn generation _ =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      have hlc := Lifecycle.failed_archival core.lifecycle generation (clockWord (core.instant reading))
        false sh.archival.lifecycle
      have hph : (core.lifecycle.failed generation (clockWord (core.instant reading)) false).phaseValue =
          .archiving ↔ core.lifecycle.phaseValue = .archiving :=
        Lifecycle.failed_phaseValue_archiving _ _ _ _
      have hcp : (core.lifecycle.failed generation (clockWord (core.instant reading)) false).clearPendingValue =
          core.lifecycle.clearPendingValue :=
        Lifecycle.failed_clearPendingValue _ _ _ _
      have harch : ({ core with
          lifecycle := core.lifecycle.failed generation (clockWord (core.instant reading)) false
          pending := none } : Core).ArchivalInvariant :=
        ⟨hlc, fun hp2 => by
            rcases shBase.clearGuards rfl (hph.mp hp2) with hr | ho | hc
            · exact .inl hr
            · exact .inr (.inl ho)
            · exact .inr (.inr (.inl hc)),
          (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
      refine ⟨(⟨harch, (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun _ _ h => by cases h), fun hr => hph.mpr (sh.replacementArchiving hr),
          (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun hg => by
            apply sh.clearPendingPersisted
            rcases hg with hc | hp2 | hr
            · exact .inl (hcp ▸ hc)
            · exact .inr (.inl (hph.mp hp2))
            · exact .inr (.inr hr),
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩ : Core.ShapeInvariant _).report _ _,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ok u =>
      cases u
      let lc := core.lifecycle.started generation
      have hlc := Lifecycle.started_archival core.lifecycle generation sh.archival.lifecycle
      have hph : lc.phaseValue = .archiving ↔ core.lifecycle.phaseValue = .archiving :=
        Lifecycle.started_phase_archiving _ _
      have hcp : lc.clearPendingValue = core.lifecycle.clearPendingValue :=
        Lifecycle.started_clearPendingValue _ _
      let core1 : Core := { core with
        slot := .live generation, failure := none
        detail := { core.detail with log := {}, abnormalExit := false }, pending := none }
      have harch2 : (core1.moveTo lc).ArchivalInvariant :=
        Core.ArchivalInvariant.moveTo_stopped (core := core1) lc hlc
          (fun hp2 => shBase.clearGuards rfl (hph.mp hp2))
      have sh2 : (core1.moveTo lc).ShapeInvariant :=
        ⟨harch2,
          fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun hr => hph.mpr (sh.replacementArchiving hr),
          fun _ _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun _ _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun _ _ h => by
            simp only [Core.moveTo] at h
            cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
          fun hg => by
            apply sh.clearPendingPersisted
            rcases hg with hc | hp2 | hr
            · exact .inl (hcp ▸ hc)
            · exact .inr (.inl (hph.mp hp2))
            · exact .inr (.inr hr),
          fun _ =>
            ⟨fun _ _ _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
            fun _ _ _ _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h,
            fun _ h => by
              simp only [Core.moveTo] at h
              cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp [hwt] at h⟩⟩
      refine ⟨sh2.report _ _, ⟨fun _ _ _ h => by
        simp only [Core.resolve, Core.report, Core.moveTo] at h
        cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp at h,
        fun _ _ _ h => by
        simp only [Core.resolve, Core.report, Core.moveTo] at h
        cases hwt : windUpTarget core1.slot core1.lifecycle lc <;> simp at h⟩⟩
  | windUp _ =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      cases hc : core.closing with
      | «open» =>
        simp only [Core.resolve, Core.refused]
        have shOpen : ({ core with pending := none, closing := .open } : Core).ShapeInvariant :=
          shBase.same (shBase.archival.same rfl rfl rfl hc.symm rfl) rfl rfl rfl rfl
        exact ⟨shOpen.report _ _, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      | closing _ =>
        simp only [Core.resolve, Core.refused]
        exact ⟨shBase.same ⟨shBase.archival.lifecycle,
            fun _ => .inr (.inr (.inl (by intro h; cases h))),
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩ rfl rfl rfl rfl,
          ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      | closed _ =>
        simp only [Core.resolve, Core.refused]
        exact ⟨shBase.same (shBase.archival.same rfl rfl rfl hc.symm rfl) rfl rfl rfl rfl,
          ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ok _ => exact ⟨shBase, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
  | adopt generation actual state =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error _ =>
      exact ⟨(shBase.stopWhenIdle rfl).report _ _,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.adoptFailed, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.adoptFailed, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h⟩⟩
    | ok u =>
      cases u
      simp only [Core.resolve, Core.adopted]
      refine ⟨⟨shBase.archival.waiting rfl rfl rfl rfl rfl (fun hph => by
          rcases shBase.clearGuards rfl hph with hr | ho | hc
          · exact .inl hr
          · exact .inr (.inl ho)
          · exact .inr (.inr (.inl hc)))
          (fun _ _ h => by cases h) (fun _ _ h => by cases h),
        (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
        sh.replacementArchiving, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
        (fun _ _ h => by cases h), sh.clearPendingPersisted, fun hg => ?_⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      refine ⟨(fun _ _ _ h => by cases h), fun g a s d h => ?_, (fun _ h => by cases h)⟩
      cases Option.some.inj h
      exact (sh.pendingDesiredMatch hg).1 generation actual state hp
  | commit generation actual state detail =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      have shState : ({ core with persisted := state, pending := none } : Core).ShapeInvariant :=
        ⟨shBase.archival.same rfl rfl rfl rfl rfl,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun _ _ h => by cases h), sh.replacementArchiving, (fun _ _ _ h => by cases h),
          (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun hg => (sh.pendingDesiredMatch hg).2.1 generation actual state detail hp,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩
      exact ⟨(shState.stopWhenIdle rfl).report _ _,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h⟩⟩
    | ok dropped =>
      simp only [Core.resolve, Core.committed]
      let lc := core.lifecycle.adoptFinalIdentity generation actual.identity
      have hph : lc.phaseValue = core.lifecycle.phaseValue :=
        Lifecycle.finalIdentity_phase _ _ _
      have hcp : lc.clearPendingValue = core.lifecycle.clearPendingValue :=
        Lifecycle.adoptFinalIdentity_clearPendingValue _ _ _
      have hlca : lc.Archival := Lifecycle.adoptFinalIdentity_archival _ _ _ sh.archival.lifecycle
      have sh1 : ({ core with persisted := state, detail, lifecycle := lc, pending := none } :
          Core).ShapeInvariant :=
        ⟨⟨hlca, fun hp2 => by
            rcases shBase.clearGuards rfl (hph ▸ hp2) with hr | ho | hc
            · exact .inl hr
            · exact .inr (.inl ho)
            · exact .inr (.inr (.inl hc)),
          (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          fun hr => hph.symm ▸ sh.replacementArchiving hr, (fun _ _ _ h => by cases h),
          (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun hg => by
            apply (sh.pendingDesiredMatch ?_).2.1 generation actual state detail hp
            rcases hg with hc | hp2 | hr
            · exact .inl (hcp ▸ hc)
            · exact .inr (.inl (hph ▸ hp2))
            · exact .inr (.inr hr),
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩
      split
      · exact ⟨sh1.report _ _, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      · exact ⟨sh1, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
  | exitMap report _ =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      exact ⟨shBase.exitReported _ rfl,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.exitReported] at h
          split at h
          · simp [Core.report] at h
          · simp at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.exitReported] at h
          split at h
          · simp [Core.report] at h
          · simp at h⟩⟩
    | ok revision =>
      have sh1 : ({ core with pending := none, mapRevision := revision.or core.mapRevision } :
          Core).ShapeInvariant :=
        shBase.same (shBase.archival.same rfl rfl rfl rfl rfl) rfl rfl rfl rfl
      exact ⟨sh1.exitReported _ rfl,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.exitReported] at h
          split at h
          · simp [Core.report] at h
          · simp at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.exitReported] at h
          split at h
          · simp [Core.report] at h
          · simp at h⟩⟩
  | exitIntent state =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error _ =>
      exact ⟨shBase.report _ _, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ok u =>
      cases u
      simp only [Core.resolve]
      exact ⟨⟨shBase.archival.same rfl rfl rfl rfl rfl,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun _ _ h => by cases h), sh.replacementArchiving, (fun _ _ _ h => by cases h),
          (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun hg => (sh.pendingDesiredMatch hg).2.2 state hp,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
  | map _ =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    have hlc : ∀ c : Core, c.pending = none → (c.launchCheck (core.instant reading)).core.ArchiveClean := by
      intro c hcp
      simp only [Core.launchCheck]
      split
      · cases c.lifecycle.reserve (clockWord (core.instant reading)) with
        | none => exact ⟨(fun _ _ _ h => by rw [hcp] at h; cases h), (fun _ _ _ h => by rw [hcp] at h; cases h)⟩
        | some _ =>
          cases c.persisted.launch with
          | error _ =>
            exact ⟨fun _ _ _ h => by
              simp only [Core.report, Core.stop, Core.moveTo] at h
              cases hwt : windUpTarget c.slot c.lifecycle (c.lifecycle.request .stop) <;>
                simp [hwt] at h,
              fun _ _ _ h => by
              simp only [Core.report, Core.stop, Core.moveTo] at h
              cases hwt : windUpTarget c.slot c.lifecycle (c.lifecycle.request .stop) <;>
                simp [hwt] at h⟩
          | ok _ =>
            cases c.owner with
            | retired _ =>
              exact ⟨fun _ _ _ h => by
                simp only [Core.report, Core.stop, Core.moveTo] at h
                cases hwt : windUpTarget c.slot c.lifecycle (c.lifecycle.request .stop) <;>
                  simp [hwt] at h,
                fun _ _ _ h => by
                simp only [Core.report, Core.stop, Core.moveTo] at h
                cases hwt : windUpTarget c.slot c.lifecycle (c.lifecycle.request .stop) <;>
                  simp [hwt] at h⟩
            | current => exact ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
      · exact ⟨(fun _ _ _ h => by rw [hcp] at h; cases h), (fun _ _ _ h => by rw [hcp] at h; cases h)⟩
    cases result with
    | error reason =>
      exact ⟨(shBase.report _ _).launchCheck _ rfl, hlc _ rfl⟩
    | ok revision =>
      simp only [Core.resolve]
      have sh1 : ({ core with pending := none, mapRevision := revision.or core.mapRevision } :
          Core).ShapeInvariant :=
        shBase.same (shBase.archival.same rfl rfl rfl rfl rfl) rfl rfl rfl rfl
      exact ⟨sh1.launchCheck _ rfl, hlc _ rfl⟩
  | closeMap _ =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    have hcl : ∀ c : Core, c.pending = none → c.ShapeInvariant →
        c.closed.core.ShapeInvariant ∧ c.closed.core.ArchiveClean := by
      intro c hcp shc
      simp only [Core.closed]
      cases hc : c.closing with
      | «open» | closed _ => exact ⟨shc, ⟨(fun _ _ _ h => by rw [hcp] at h; cases h),
          (fun _ _ _ h => by rw [hcp] at h; cases h)⟩⟩
      | closing _ =>
        refine ⟨shc.same ⟨shc.archival.lifecycle, fun _ => .inr (.inr (.inl (by intro h; cases h))),
            (fun _ _ h => by rw [hcp] at h; cases h), (fun _ _ h => by rw [hcp] at h; cases h)⟩
            rfl rfl rfl rfl,
          ⟨(fun _ _ _ h => by rw [hcp] at h; cases h), (fun _ _ _ h => by rw [hcp] at h; cases h)⟩⟩
    cases result with
    | error reason => exact hcl _ rfl (shBase.report _ _)
    | ok revision => exact hcl _ rfl (shBase.same (shBase.archival.same rfl rfl rfl rfl rfl) rfl rfl rfl rfl)
  | seed intended =>
    have shBase := sh.base_of_nonArchive hp (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    cases result with
    | error reason =>
      exact ⟨(shBase.stopWhenIdle rfl).report _ _,
        ⟨fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h,
          fun _ _ _ h => by
          simp only [Core.resolve, Core.report, Core.stop, Core.moveTo] at h
          cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
            simp [hwt] at h⟩⟩
    | ok seed =>
      simp only [Core.resolve, Core.seeded]
      split
      · exact ⟨(shBase.stopWhenIdle rfl).report _ _,
          ⟨fun _ _ _ h => by
            simp only [Core.report, Core.stop, Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
              simp [hwt] at h,
            fun _ _ _ h => by
            simp only [Core.report, Core.stop, Core.moveTo] at h
            cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
              simp [hwt] at h⟩⟩
      · cases hba : core.lifecycle.beginArchive with
        | none => exact ⟨shBase, ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
        | some lc =>
          cases ho : core.owner with
          | retired _ =>
            dsimp only
            exact ⟨shBase.same (shBase.archival.same rfl rfl ho.symm rfl rfl) rfl rfl rfl rfl,
              ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
          | current =>
            dsimp only
            have hcp_is : core.lifecycle.clearPendingValue.isSome = true :=
              Lifecycle.beginArchive_clearPending_isSome _ _ hba
            have hlca := Lifecycle.beginArchive_archival _ _ hba sh.archival.lifecycle
            have hph := Lifecycle.beginArchive_phaseValue _ _ hba
            have hcp_eq := Lifecycle.beginArchive_clearPendingValue _ _ hba
            have hnotArchOld : core.lifecycle.phaseValue ≠ .archiving :=
              Lifecycle.beginArchive_old_phaseValue _ _ hba
            have hrepNone : core.replacement = none := by
              cases hr : core.replacement with
              | none => rfl
              | some _ => exact absurd (sh.replacementArchiving (by simp [hr])) hnotArchOld
            have hps : core.persisted.desired = .stopped :=
              sh.clearPendingPersisted (.inl hcp_is)
            let identity : Identity := ⟨core.persisted.identity.run + 1, seed,
              core.persisted.identity.agentEpoch + 1⟩
            let nxt : Core := { core with
              lifecycle := lc, owner := .current
              pending := some (.archive identity intended (clockWord (core.instant reading))) }
            have harch : nxt.ArchivalInvariant :=
              ⟨hlca, fun _ => .inr (.inr (.inr (.inl ⟨identity, intended, _, rfl⟩))),
                (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
            have hsh : nxt.ShapeInvariant :=
              ⟨harch, (fun _ _ h => by cases h), (fun _ _ h => by cases h),
                (fun _ _ h => by cases h), (fun hr => by rw [hrepNone] at hr; cases hr),
                (fun _ _ _ h => by cases Option.some.inj h; exact hph),
                (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
                fun _ => hps,
                fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
                  (fun _ h => by cases h)⟩⟩
            exact ⟨hsh.report _ _, ⟨fun _ _ _ _ => hrepNone, (fun _ _ _ h => by cases h)⟩⟩
  | archive id intended t =>
    have hph : core.lifecycle.phaseValue = .archiving := sh.archivePhase id intended t hp
    have hrep : core.replacement = none := cln.1 id intended t hp
    have hps : core.persisted.desired = .stopped := sh.clearPendingPersisted (.inr (.inl hph))
    simp only [Core.resolve]
    cases result with
    | unchanged reason =>
      have hlca := Lifecycle.archiveFailed_archival core.lifecycle sh.archival.lifecycle
      have hnotArch := Lifecycle.archiveFailed_phase_ne_archiving core.lifecycle
      have shUnch : Core.ShapeInvariant
          { core with lifecycle := core.lifecycle.archiveFailed, pending := none } :=
        ⟨⟨hlca, fun hp2 => absurd hp2 hnotArch,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun hr => by rw [hrep] at hr; cases hr),
          (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun _ => hps,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩
      exact ⟨shUnch.report _ _,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | moved archive reason =>
      have hlca := Lifecycle.archiveFailed_archival core.lifecycle sh.archival.lifecycle
      have hnotArch := Lifecycle.archiveFailed_phase_ne_archiving core.lifecycle
      exact ⟨⟨⟨hlca, fun hp2 => absurd hp2 hnotArch, (fun _ _ h => by cases h),
          (fun _ _ h => by cases h)⟩,
        (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
        (fun hr => by rw [hrep] at hr; cases hr),
        (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
        fun _ => hps,
        fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
          (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ready archive =>
      exact ⟨⟨⟨sh.archival.lifecycle,
            fun _ => .inr (.inr (.inr (.inr ⟨id, intended, archive, rfl⟩))),
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun hr => by rw [hrep] at hr; cases hr),
          (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases Option.some.inj h; exact hph),
          (fun _ _ h => by cases h), fun _ => hps,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), fun _ _ _ _ => hrep⟩⟩
  | reopen id intended archive =>
    have hph : core.lifecycle.phaseValue = .archiving := sh.reopenPhase id intended archive hp
    have hrep : core.replacement = none := cln.2 id intended archive hp
    have hps : core.persisted.desired = .stopped := sh.clearPendingPersisted (.inr (.inl hph))
    simp only [Core.resolve]
    cases result with
    | error reason =>
      exact ⟨⟨⟨sh.archival.lifecycle, fun _ => .inr (.inl (by intro h; cases h)),
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun hr => by rw [hrep] at hr; cases hr),
          (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ h => by cases h),
          fun _ => hps,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ok u =>
      cases u
      let state : PersistedState := ⟨id, intended, .cleared, false⟩
      exact ⟨⟨⟨sh.archival.lifecycle, fun _ => .inl rfl,
            (fun _ _ h => by cases h), fun _ _ _ => rfl⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          (fun st ack h => by cases Option.some.inj h; rfl),
          fun _ => hph, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
          (fun _ _ h => by cases h), fun _ => hps,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
  | replacement state ackStop =>
    have hrep : core.replacement = some state := sh.replacementMatches state ackStop hp
    have hph : core.lifecycle.phaseValue = .archiving := sh.replacementArchiving (by simp [hrep])
    have hps : core.persisted.desired = .stopped := sh.clearPendingPersisted (.inr (.inl hph))
    cases result with
    | error reason =>
      dsimp only [Core.resolve]
      refine ⟨⟨⟨sh.archival.lifecycle, fun _ => .inl (by simp [Core.report, hrep]),
            (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
          (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
          fun _ => hph, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
          (fun _ _ h => by cases h), fun _ => hps,
          fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
            (fun _ h => by cases h)⟩⟩,
        ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
    | ok u =>
      cases u
      dsimp only [Core.resolve]
      have hrepCore : Core.ShapeInvariant ({ core with pending := none }.replaced state).core ∧
          ({ core with pending := none }.replaced state).core.ArchiveClean := by
        simp only [Core.replaced]
        let lc := core.lifecycle.replacementIntent state.desired
        have hlca := Lifecycle.replacementIntent_archival core.lifecycle state.desired
          sh.archival.lifecycle
        have hlcph : lc.phaseValue = .archiving :=
          (Lifecycle.replacementIntent_phaseValue core.lifecycle state.desired).trans hph
        cases hins : lc.archived state.identity with
        | none =>
          dsimp only
          exact ⟨⟨⟨hlca, fun _ => .inl (by simp [Core.report, hrep]),
              (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
            fun _ => hlcph, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
            (fun _ _ h => by cases h), fun _ => hps,
            fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
              (fun _ h => by cases h)⟩⟩,
            ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
        | some installed =>
          dsimp only
          have hia := Lifecycle.archived_archival lc installed state.identity hins
          have hiph := Lifecycle.archived_phase_ne_archiving lc installed state.identity hins
          have hicp := Lifecycle.archived_clearPendingValue lc installed state.identity hins
          exact ⟨⟨⟨hia, fun hp2 => absurd hp2 hiph,
              (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩,
            (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h),
            (fun hr => by simp only [Core.report] at hr; cases hr),
            (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h),
            (fun _ _ h => by cases h),
            (fun hg => by
              rcases hg with hc | hp2 | hr
              · simp only [Core.report] at hc; rw [hicp] at hc; cases hc
              · simp only [Core.report] at hp2; exact absurd hp2 hiph
              · simp only [Core.report] at hr; cases hr),
            fun _ => ⟨(fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h),
              (fun _ h => by cases h)⟩⟩,
            ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩⟩
      cases ackStop with
      | false => exact hrepCore
      | true =>
        cases hdes : (state.desired == .stopped) <;>
          simp only [↓reduceIte, Bool.false_eq_true] <;> exact hrepCore

structure Core.StopGuard (core : Core) : Prop where
  held : core.StopHeld
  replacement : ∀ rep, core.replacement = some rep → rep.desired = .stopped
  pendingReplacement : ∀ st ack, core.pending = some (.replacement st ack) →
    st.desired = .stopped
  noStartIntent : ∀ c s, core.pending = some (.intent c s) → c ≠ .start ∧ s.desired = .stopped

private theorem Core.StopGuard.same {core next : Core} (guard : core.StopGuard)
    (hlc : next.lifecycle = core.lifecycle)
    (hpers : next.persisted = core.persisted)
    (hrep : next.replacement = core.replacement)
    (hpend : next.pending = core.pending) : next.StopGuard := by
  refine ⟨⟨hlc ▸ guard.held.lifecycle, hpers ▸ guard.held.persisted,
      fun p hp => guard.held.pending p (hpend ▸ hp)⟩,
    fun rep hr => guard.replacement rep (hrep ▸ hr),
    fun st ack hp => guard.pendingReplacement st ack (hpend ▸ hp),
    fun c s hp => guard.noStartIntent c s (hpend ▸ hp)⟩

private theorem Core.StopGuard.report {core : Core} (guard : core.StopGuard)
    (tr : ControlTransition) (reason : String) : (core.report tr reason).StopGuard :=
  guard.same rfl rfl rfl rfl

private theorem Core.StopGuard.at {stepped : Stepped} (guard : stepped.core.StopGuard)
    (now : Nat) : (stepped.at now).core.StopGuard :=
  guard.same rfl rfl rfl rfl

theorem Core.StopGuard.toUnstarted {core : Core} (guard : core.StopGuard) : core.Unstarted where
  lifecycle := guard.held.lifecycle
  persisted := guard.held.persisted
  replacement := guard.replacement
  pending p hp := by
    cases p with
    | intent c s => exact guard.noStartIntent c s hp
    | replacement st ack => exact guard.pendingReplacement st ack hp
    | launch _ _ | spawn _ _ | adopt _ _ _ | commit _ _ _ _ | exitIntent _
    | seed _ | archive _ _ _ | reopen _ _ _ | windUp _ | exitMap _ _ | map _ | closeMap _ =>
      exact guard.held.pending _ hp

theorem Core.Unstarted.toStopGuard {core : Core} (unstarted : core.Unstarted) : core.StopGuard where
  held :=
    ⟨unstarted.lifecycle, unstarted.persisted, fun p hp => by
      cases p with
      | intent c s => exact Or.inr (unstarted.pending _ hp)
      | replacement _ _ => exact trivial
      | launch _ _ | spawn _ _ | adopt _ _ _ | commit _ _ _ _ | exitIntent _
      | seed _ | archive _ _ _ | reopen _ _ _ | windUp _ | exitMap _ _ | map _ | closeMap _ =>
        exact unstarted.pending _ hp⟩
  replacement := unstarted.replacement
  pendingReplacement st ack hp := unstarted.pending _ hp
  noStartIntent c s hp := unstarted.pending _ hp

theorem Core.StopGuard.iff_unstarted (core : Core) : core.StopGuard ↔ core.Unstarted :=
  ⟨Core.StopGuard.toUnstarted, Core.Unstarted.toStopGuard⟩

theorem Core.start_stopGuard (persisted : PersistedState) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (hstopped : persisted.desired = .stopped) :
    (Core.start persisted clearDisabled reason reading).StopGuard :=
  (Core.start_unstarted persisted clearDisabled reason reading hstopped).toStopGuard

theorem Core.step_stopGuard (core : Core) (clearDisabled : Option String) (reading : Nat)
    (event : Event) (guard : core.StopGuard) (hnoStart : event ≠ .command .start) :
    (core.step clearDisabled reading event).core.StopGuard :=
  (Core.step_unstarted core clearDisabled reading event hnoStart guard.toUnstarted).toStopGuard

theorem Core.resume_stopGuard (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (hp : core.pending = some pending) (guard : core.StopGuard) :
    (core.resume reading pending result).core.StopGuard :=
  (Core.resume_unstarted core reading pending result guard.toUnstarted hp).toStopGuard

theorem Core.resume_ackStop_stopGuard (core : Core) (reading : Nat) (pending : Pending)
    (result : (pending.call core.lifecycle).Result)
    (hp : core.pending = some pending) (sh : core.ShapeInvariant)
    (acked : Follow.ackStop ∈ (core.resume reading pending result).follows) :
    (core.resume reading pending result).core.StopGuard := by
  obtain ⟨state, hcall, hst, hok⟩ := Core.resume_ackStop_spec core reading pending result acked
  unfold Core.resume
  apply Core.StopGuard.at
  cases pending with
  | intent command s =>
    dsimp [Pending.call] at hcall
    cases hcall
    dsimp [Call.IsWriteStateOk] at hok
    cases result with
    | error _ => cases hok
    | ok u =>
      cases u
      have hcmd : command = .stop := by
        cases command <;> simp [Core.resume, Core.resolve, Core.intentSaved, Stepped.at] at acked
        rfl
      subst hcmd
      have hrepNone := sh.intentNoReplacement .stop state hp
      simp only [Core.resolve, Core.intentSaved]
      refine ⟨⟨Lifecycle.request_stop_unstarted core.lifecycle, hst, fun p h => ?_⟩,
        (fun r hr => by simp only [Core.report, Core.moveTo] at hr; rw [hrepNone] at hr; cases hr),
        fun _ _ h => ?_, fun _ _ h => ?_⟩
      all_goals
        simp only [Core.report, Core.moveTo] at h
        cases hwt : windUpTarget core.slot core.lifecycle (core.lifecycle.request .stop) <;>
          simp [hwt] at h
        (try cases h)
        (try exact trivial)
  | replacement s ackStop =>
    dsimp [Pending.call] at hcall
    cases hcall
    cases result with
    | error _ => simp only [Call.IsWriteStateOk] at hok; cases hok
    | ok u =>
      cases u
      have hrep : core.replacement = some state := sh.replacementMatches state ackStop hp
      have hph : core.lifecycle.phaseValue = .archiving := sh.replacementArchiving (by simp [hrep])
      have hps : core.persisted.desired = .stopped := sh.clearPendingPersisted (.inr (.inl hph))
      have gRep : ({ core with pending := none }.replaced state).core.StopGuard := by
        simp only [Core.replaced]
        have hBoth := Lifecycle.replacementIntent_stopped_unstarted core.lifecycle state.identity
          sh.archival.lifecycle
        rw [hst]
        cases hins : (core.lifecycle.replacementIntent .stopped).archived state.identity with
        | none =>
          dsimp only
          have hlcu := hBoth.2 hins hph
          have gNone : Core.StopGuard { core with
              lifecycle := core.lifecycle.replacementIntent .stopped, pending := none } :=
            ⟨⟨hlcu, hps, (fun _ h => by cases h)⟩,
              (fun r hr => by rw [hr] at hrep; cases Option.some.inj hrep; exact hst),
              (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
          exact gNone.report _ _
        | some installed =>
          dsimp only
          have hlcu := hBoth.1 installed hins
          have gSome : Core.StopGuard { core with
              lifecycle := installed, persisted := state, replacement := none,
              detail := { core.detail with log := {}, abnormalExit := false },
              failure := none, mapAt := 0, mapRevision := none, pending := none } :=
            ⟨⟨hlcu, hst, (fun _ h => by cases h)⟩,
              (fun _ h => by cases h), (fun _ _ h => by cases h),
              (fun _ _ h => by cases h)⟩
          exact gSome.report _ _
      dsimp only [Core.resolve]
      cases ackStop with
      | false => exact gRep
      | true =>
        cases hdes : (state.desired == .stopped) <;>
          simp only [↓reduceIte, Bool.false_eq_true] <;> exact gRep
  | launch _ _ =>
    dsimp [Pending.call] at hok
    cases result with
    | error _ => simp [Call.IsWriteStateOk] at hok
    | ok u =>
      cases u
      dsimp only [Core.resume, Core.resolve, Stepped.at] at acked
      cases hrv : core.lifecycle.reserve (clockWord (core.instant reading)) with
      | none => simp [hrv] at acked
      | some _ => simp [hrv] at acked
  | adopt _ _ _ =>
    dsimp [Pending.call] at hok
    cases result with
    | error _ => simp [Call.IsWriteStateOk] at hok
    | ok u =>
      cases u
      simp [Core.resume, Core.resolve, Core.adopted, Stepped.at] at acked
  | exitIntent _ =>
    dsimp [Pending.call] at hok
    cases result with
    | error _ => simp [Call.IsWriteStateOk] at hok
    | ok u =>
      cases u
      simp [Core.resume, Core.resolve, Stepped.at] at acked
  | spawn _ _ | windUp _ | commit _ _ _ _ | exitMap _ _ | map _ | closeMap _ | seed _
  | archive _ _ _ | reopen _ _ _ => cases hcall

inductive DiskState where
  | absent
  | file (text : String) (recordedChild : Option (List String))

def DiskState.Stopped : DiskState → Prop
  | .absent => True
  | .file text recordedChild =>
    ∃ state : PersistedState, text = state.encode recordedChild ∧ state.desired = .stopped

def DiskState.BootState (disk : DiskState) (seed : UInt64) (migrated : Bool)
    (nextChild : Option (List String)) (persisted : PersistedState) : Prop :=
  match disk with
  | .absent => persisted = PersistedState.unstarted seed migrated
  | .file text _ => ∃ doc, Json.parse text = .ok doc ∧ PersistedState.decode nextChild doc = .ok persisted

theorem DiskState.Stopped.read_stopped {disk : DiskState} (hs : disk.Stopped)
    {nextChild : Option (List String)} {text : String} {rc : Option (List String)}
    {doc : Json.Value} {loaded : PersistedState}
    (hfile : disk = .file text rc)
    (hparsed : Json.parse text = .ok doc)
    (hdecoded : PersistedState.decode nextChild doc = .ok loaded) :
    loaded.desired = .stopped := by
  subst hfile
  obtain ⟨state, rfl, hstopped⟩ := hs
  exact PersistedState.encode_decode_stopped rc nextChild state loaded doc hstopped hparsed hdecoded

theorem DiskState.BootState.stopped {disk : DiskState} (hs : disk.Stopped)
    {seed : UInt64} {migrated : Bool} {nextChild : Option (List String)} {persisted : PersistedState}
    (hboot : disk.BootState seed migrated nextChild persisted) :
    persisted.desired = .stopped := by
  cases disk with
  | absent => rw [hboot]; rfl
  | file text rc =>
    obtain ⟨doc, hparsed, hdecoded⟩ := hboot
    exact hs.read_stopped rfl hparsed hdecoded

structure CrashState where
  clearDisabled : Option String
  live : Bool
  core : Core
  disk : DiskState
  tmpWrite : Option (PersistedState × Option (List String))
  writeDone : Option PersistedState
  archiveMoved : Option System.FilePath
  archiveFailedDisk : Option (Bool × System.FilePath × String)
  ackedStop : Bool
  startAfterAck : Bool

def CrashState.initial (persisted : PersistedState) (clearDisabled : Option String)
    (reason : String) (reading : Nat) (disk : DiskState) : CrashState where
  clearDisabled
  live := true
  core := Core.start persisted clearDisabled reason reading
  disk
  tmpWrite := none
  writeDone := none
  archiveMoved := none
  archiveFailedDisk := none
  ackedStop := false
  startAfterAck := false

private def Event.isStart : Event → Bool
  | .command .start => true
  | _ => false

private def Follow.hasAckStop : Follow → Bool
  | .ackStop => true
  | _ => false

private theorem Follow.any_hasAckStop_iff {follows : List Follow} :
    follows.any Follow.hasAckStop = true ↔ Follow.ackStop ∈ follows := by
  induction follows with
  | nil => simp
  | cons f fs ih => cases f <;> simp [Follow.hasAckStop, ih]

inductive CrashStep : CrashState → CrashState → Prop where
  | step (st : CrashState) (reading : Nat) (event : Event) (hlive : st.live = true) :
      CrashStep st
        { st with
          core := (st.core.step st.clearDisabled reading event).core
          startAfterAck := st.startAfterAck ||
            (st.ackedStop && event.isStart && st.core.pending.isNone && (st.core.closing == .open)) }
  | writeTmp (st : CrashState) (p : Pending) (state : PersistedState)
      (child : Option (List String))
      (hlive : st.live = true)
      (hp : st.core.pending = some p)
      (hcall : p.call st.core.lifecycle = .writeState state)
      (ht : st.tmpWrite = none) (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none) :
      CrashStep st { st with tmpWrite := some (state, child) }
  | writeRename (st : CrashState) (state : PersistedState) (child : Option (List String))
      (hlive : st.live = true)
      (ht : st.tmpWrite = some (state, child)) :
      CrashStep st
        { st with
          tmpWrite := none
          writeDone := some state
          disk := .file (state.encode child) child }
  | writeFinishOk (st : CrashState) (reading : Nat) (p : Pending)
      (state : PersistedState) (result : (p.call st.core.lifecycle).Result)
      (hlive : st.live = true)
      (hp : st.core.pending = some p)
      (hd : st.writeDone = some state)
      (hcall : p.call st.core.lifecycle = .writeState state)
      (hok : (p.call st.core.lifecycle).IsWriteStateOk result) :
      CrashStep st
        { st with
          core := (st.core.resume reading p result).core
          writeDone := none
          ackedStop := st.ackedStop || (st.core.resume reading p result).follows.any Follow.hasAckStop
          startAfterAck := if (st.core.resume reading p result).follows.any Follow.hasAckStop then false
            else st.startAfterAck }
  | writeFail (st : CrashState) (reading : Nat) (p : Pending) (reason : String)
      (result : (p.call st.core.lifecycle).Result)
      (hlive : st.live = true)
      (hp : st.core.pending = some p)
      (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none)
      (herr : (p.call st.core.lifecycle).IsWriteStateErr result reason) :
      CrashStep st
        { st with
          core := (st.core.resume reading p result).core
          tmpWrite := none }
  | writeFailIndeterminate (st : CrashState) (reading : Nat) (p : Pending)
      (state : PersistedState) (child : Option (List String)) (reason : String)
      (result : (p.call st.core.lifecycle).Result)
      (hlive : st.live = true)
      (hp : st.core.pending = some p)
      (ht : st.tmpWrite = some (state, child))
      (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none)
      (herr : (p.call st.core.lifecycle).IsWriteStateErr result reason) :
      CrashStep st
        { st with
          core := (st.core.resume reading p result).core
          tmpWrite := none
          disk := .file (state.encode child) child }
  | archiveMoveOnDisk (st : CrashState) (id : Identity) (intended : Desired) (t : UInt64)
      (archive : System.FilePath)
      (hlive : st.live = true)
      (hp : st.core.pending = some (.archive id intended t))
      (ht : st.tmpWrite = none) (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none) :
      CrashStep st
        { st with
          disk := .absent
          archiveMoved := some archive }
  | archiveFinishReady (st : CrashState) (reading : Nat) (id : Identity) (intended : Desired)
      (t : UInt64) (archive : System.FilePath)
      (hlive : st.live = true)
      (hp : st.core.pending = some (.archive id intended t))
      (ha : st.archiveMoved = some archive) :
      CrashStep st
        { st with
          core := (st.core.resume reading (.archive id intended t) (.ready archive)).core
          archiveMoved := none }
  | archiveFailOnDisk (st : CrashState) (id : Identity) (intended : Desired) (t : UInt64)
      (moved : Bool) (archive : System.FilePath) (reason : String)
      (hlive : st.live = true)
      (hp : st.core.pending = some (.archive id intended t))
      (ht : st.tmpWrite = none) (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none) :
      CrashStep st
        { st with
          disk := if moved then .absent else st.disk
          archiveFailedDisk := some (moved, archive, reason) }
  | archiveFinishFail (st : CrashState) (reading : Nat) (id : Identity) (intended : Desired)
      (t : UInt64) (moved : Bool) (archive : System.FilePath) (reason : String)
      (hlive : st.live = true)
      (hp : st.core.pending = some (.archive id intended t))
      (hf : st.archiveFailedDisk = some (moved, archive, reason)) :
      CrashStep st
        { st with
          core := (st.core.resume reading (.archive id intended t)
            (if moved then .moved archive reason else .unchanged reason)).core
          archiveFailedDisk := none }
  | resumeOther (st : CrashState) (reading : Nat) (p : Pending)
      (result : (p.call st.core.lifecycle).Result)
      (hlive : st.live = true)
      (hp : st.core.pending = some p)
      (ht : st.tmpWrite = none) (hd : st.writeDone = none)
      (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none)
      (hnotWrite : ∀ s, p.call st.core.lifecycle ≠ .writeState s)
      (hnotArch : ∀ id d t, p ≠ .archive id d t) :
      CrashStep st
        { st with core := (st.core.resume reading p result).core }
  | crash (st : CrashState) (hlive : st.live = true) :
      CrashStep st
        { st with
          live := false
          tmpWrite := none
          writeDone := none
          archiveMoved := none
          archiveFailedDisk := none }
  | boot (st : CrashState) (persisted : PersistedState) (seed : UInt64) (migrated : Bool)
      (nextChild : Option (List String)) (nextClearDisabled : Option String) (wroteDisk : Bool)
      (reason : String) (reading : Nat)
      (hdead : st.live = false)
      (hboot : DiskState.BootState st.disk seed migrated nextChild persisted) :
      CrashStep st
        { clearDisabled := nextClearDisabled
          live := true
          core := Core.start persisted nextClearDisabled reason reading
          disk := if wroteDisk then .file (persisted.encode nextChild) nextChild else st.disk
          tmpWrite := none
          writeDone := none
          archiveMoved := none
          archiveFailedDisk := none
          ackedStop := st.ackedStop
          startAfterAck := st.startAfterAck }

inductive CrashReached (origin : CrashState) : CrashState → Prop where
  | refl : CrashReached origin origin
  | tail {mid next : CrashState} (h : CrashReached origin mid) (step : CrashStep mid next) :
      CrashReached origin next

structure CrashState.Invariant (st : CrashState) : Prop where
  shape : st.core.ShapeInvariant
  clean : st.core.ArchiveClean
  tmpPending : ∀ state child, st.tmpWrite = some (state, child) →
    ∃ p, st.core.pending = some p ∧ p.call st.core.lifecycle = .writeState state
  donePending : ∀ state, st.writeDone = some state →
    st.tmpWrite = none ∧ st.archiveMoved = none ∧ st.archiveFailedDisk = none ∧
      (∃ child, st.disk = .file (state.encode child) child) ∧
      ∃ p, st.core.pending = some p ∧ p.call st.core.lifecycle = .writeState state
  archPending : ∀ a, st.archiveMoved = some a →
    st.archiveFailedDisk = none ∧ ∃ id d t, st.core.pending = some (.archive id d t)
  archFailPending : ∀ m a r, st.archiveFailedDisk = some (m, a, r) →
    ∃ id d t, st.core.pending = some (.archive id d t)
  durableStop : st.ackedStop = true → st.startAfterAck = false →
    st.disk.Stopped ∧
      (st.live = true → st.core.StopGuard ∧
        (∀ state child, st.tmpWrite = some (state, child) → state.desired = .stopped) ∧
        (∀ state, st.writeDone = some state → state.desired = .stopped))

theorem CrashState.initial_invariant (persisted : PersistedState)
    (clearDisabled : Option String) (reason : String) (reading : Nat) (disk : DiskState) :
    (CrashState.initial persisted clearDisabled reason reading disk).Invariant :=
  ⟨Core.ShapeInvariant.start persisted clearDisabled reason reading,
    Core.ArchiveClean.start persisted clearDisabled reason reading,
    (fun _ _ h => by cases h), (fun _ h => by cases h),
    (fun _ h => by cases h), (fun _ _ _ h => by cases h),
    (fun h => by cases h)⟩

theorem CrashStep.invariant {st next : CrashState} (inv : st.Invariant)
    (step : CrashStep st next) : next.Invariant := by
  cases step with
  | step reading event hlive =>
    have hsh := Core.step_shapeInvariant st.core st.clearDisabled reading event inv.shape
    have hcln := Core.ArchiveClean.step st.core st.clearDisabled reading event inv.clean
    have hpendPres : ∀ p, st.core.pending = some p →
        (st.core.step st.clearDisabled reading event).core.lifecycle = st.core.lifecycle ∧
          (st.core.step st.clearDisabled reading event).core.persisted = st.core.persisted ∧
          (st.core.step st.clearDisabled reading event).core.replacement = st.core.replacement ∧
          (st.core.step st.clearDisabled reading event).core.pending = some p := by
      intro p hp
      simp [Core.step, Core.dispatch, Stepped.at, hp]
    refine ⟨hsh, hcln, ?_, ?_, ?_, ?_, ?_⟩
    · intro state child ht
      obtain ⟨p, hp, hcall⟩ := inv.tmpPending state child ht
      obtain ⟨hlc, _, _, hpend⟩ := hpendPres p hp
      exact ⟨p, hpend, hlc.symm ▸ hcall⟩
    · intro state hd
      obtain ⟨ht, ha, hf, hdsk, p, hp, hcall⟩ := inv.donePending state hd
      obtain ⟨hlc, _, _, hpend⟩ := hpendPres p hp
      exact ⟨ht, ha, hf, hdsk, p, hpend, hlc.symm ▸ hcall⟩
    · intro a ha
      obtain ⟨hfd, id, d, t, hp⟩ := inv.archPending a ha
      obtain ⟨_, _, _, hpend⟩ := hpendPres _ hp
      exact ⟨hfd, id, d, t, hpend⟩
    · intro m a r hf
      obtain ⟨id, d, t, hp⟩ := inv.archFailPending m a r hf
      obtain ⟨_, _, _, hpend⟩ := hpendPres _ hp
      exact ⟨id, d, t, hpend⟩
    · intro hack hns
      dsimp only at hack hns
      have hns_orig : st.startAfterAck = false := by
        cases h : st.startAfterAck <;> simp_all
      have hcs : (st.ackedStop && event.isStart &&
          st.core.pending.isNone && (st.core.closing == .open)) = false := by
        cases h : (st.ackedStop && event.isStart &&
          st.core.pending.isNone && (st.core.closing == .open)) <;> simp_all
      obtain ⟨hdisk, hguard, htmp, hdone⟩ := (inv.durableStop hack hns_orig).1,
        (inv.durableStop hack hns_orig).2 hlive
      refine ⟨hdisk, fun _ => ?_⟩
      by_cases hstart : event = .command .start
      · subst hstart
        simp only [Event.isStart] at hcs
        cases hp : st.core.pending with
        | some p =>
          obtain ⟨hlc, hpers, hrep, hpend⟩ := hpendPres p hp
          exact ⟨hguard.same hlc hpers hrep (hpend.trans hp.symm), htmp, hdone⟩
        | none =>
          simp only [hp, Option.isNone_none] at hcs
          have hcls : st.core.closing ≠ .open := by
            intro hopen
            rw [hack, hopen] at hcs
            simp at hcs
          have hstSame : (st.core.step st.clearDisabled reading (.command .start)).core.lifecycle =
                st.core.lifecycle ∧
              (st.core.step st.clearDisabled reading (.command .start)).core.persisted =
                st.core.persisted ∧
              (st.core.step st.clearDisabled reading (.command .start)).core.replacement =
                st.core.replacement ∧
              (st.core.step st.clearDisabled reading (.command .start)).core.pending =
                st.core.pending := by
            cases hc : st.core.closing with
            | «open» => exact absurd hc hcls
            | closed _ | closing _ => simp [Core.step, Core.dispatch, Stepped.at, hp, hc]
          exact ⟨hguard.same hstSame.1 hstSame.2.1 hstSame.2.2.1 hstSame.2.2.2, htmp, hdone⟩
      · exact ⟨Core.step_stopGuard st.core st.clearDisabled reading event hguard hstart, htmp, hdone⟩
  | writeTmp p state child hlive hp hcall ht hd ha hf =>
    refine ⟨inv.shape, inv.clean, ?_, ?_, ?_, ?_, ?_⟩
    · intro s c hs
      cases Option.some.inj hs
      exact ⟨p, hp, hcall⟩
    · intro s hs; rw [hd] at hs; cases hs
    · intro a hsa; rw [ha] at hsa; cases hsa
    · intro m a r hsf; rw [hf] at hsf; cases hsf
    · intro hack hns
      obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
      obtain ⟨hguard, _, hdone⟩ := hliveInv hlive
      refine ⟨hdisk, fun _ => ⟨hguard, ?_, hdone⟩⟩
      intro s c hs
      cases Option.some.inj hs
      have hsh := hguard.held.pending p hp
      cases p with
      | intent cmd s0 =>
        dsimp [Pending.call] at hcall
        cases hcall
        exact (hguard.noStartIntent cmd state hp).2
      | replacement st0 ack =>
        dsimp [Pending.call] at hcall
        cases hcall
        exact hguard.pendingReplacement state ack hp
      | launch _ _ => exact absurd hsh (fun h => h)
      | adopt _ _ s0 =>
        dsimp [Pending.call] at hcall
        cases hcall
        exact hsh
      | exitIntent s0 =>
        dsimp [Pending.call] at hcall
        cases hcall
        exact hsh
      | spawn _ _ | windUp _ | commit _ _ _ _ | exitMap _ _ | map _ | closeMap _ | seed _
      | archive _ _ _ | reopen _ _ _ => cases hcall
  | writeRename state child hlive ht =>
    obtain ⟨p, hp, hcall⟩ := inv.tmpPending state child ht
    refine ⟨inv.shape, inv.clean, (fun _ _ h => by cases h), ?_, ?_, ?_, ?_⟩
    · intro s hs
      cases Option.some.inj hs
      refine ⟨rfl, ?_, ?_, ⟨child, rfl⟩, p, hp, hcall⟩
      · cases h1 : st.archiveMoved with
        | none => rfl
        | some a =>
          obtain ⟨_, id, d, t, hpa⟩ := inv.archPending a h1
          rw [hp] at hpa; obtain rfl := Option.some.inj hpa; cases hcall
      · cases h1 : st.archiveFailedDisk with
        | none => rfl
        | some f =>
          obtain ⟨id, d, t, hpf⟩ := inv.archFailPending f.1 f.2.1 f.2.2 h1
          rw [hp] at hpf; obtain rfl := Option.some.inj hpf; cases hcall
    · intro a ha
      obtain ⟨_, id, d, t, hpa⟩ := inv.archPending a ha
      rw [hp] at hpa; obtain rfl := Option.some.inj hpa; cases hcall
    · intro m a r hf
      obtain ⟨id, d, t, hpf⟩ := inv.archFailPending m a r hf
      rw [hp] at hpf; obtain rfl := Option.some.inj hpf; cases hcall
    · intro hack hns
      obtain ⟨_, hliveInv⟩ := inv.durableStop hack hns
      obtain ⟨hguard, htmp, _⟩ := hliveInv hlive
      have hst := htmp state child ht
      refine ⟨⟨state, rfl, hst⟩, fun _ => ⟨hguard, (fun _ _ h => by cases h), ?_⟩⟩
      intro s hs; cases Option.some.inj hs; exact hst
  | writeFinishOk reading p state result hlive hp hd hcall hok =>
    have hboth := Core.ShapeInvariant.resume reading p result hp inv.shape inv.clean
    refine ⟨hboth.1, hboth.2, ?_, (fun _ h => by cases h), ?_, ?_, ?_⟩
    · intro s c ht
      obtain ⟨p2, hp2, _⟩ := inv.tmpPending s c ht
      have htd := (inv.donePending state hd).1
      rw [htd] at ht; cases ht
    · intro a ha
      have had := (inv.donePending state hd).2.1
      rw [had] at ha; cases ha
    · intro m a r hf
      have hfd := (inv.donePending state hd).2.2.1
      rw [hfd] at hf; cases hf
    · intro hack hns
      by_cases hackNow : Follow.ackStop ∈ (st.core.resume reading p result).follows
      · have hg := Core.resume_ackStop_stopGuard st.core reading p result hp inv.shape hackNow
        obtain ⟨_, _, _, ⟨child, hdisk⟩, _, _, _⟩ := inv.donePending state hd
        obtain ⟨w, hcw, hwst, _⟩ := Core.resume_ackStop_spec st.core reading p result hackNow
        have heq : state = w := by
          have hcw' : Call.writeState state = Call.writeState w := hcall.symm.trans hcw
          cases hcw'; rfl
        subst heq
        rw [hdisk]
        exact ⟨⟨state, rfl, hwst⟩, fun _ => ⟨hg,
          (fun _ _ h => by rw [(inv.donePending state hd).1] at h; cases h),
          (fun _ h => by cases h)⟩⟩
      · have hfalse : (st.core.resume reading p result).follows.any Follow.hasAckStop = false := by
          cases h : (st.core.resume reading p result).follows.any Follow.hasAckStop with
          | false => rfl
          | true => exact absurd (Follow.any_hasAckStop_iff.mp h) hackNow
        dsimp only at hack hns
        rw [hfalse] at hack hns
        simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hack hns
        have hdisk := (inv.durableStop hack hns).1
        have hguard := ((inv.durableStop hack hns).2 hlive).1
        exact ⟨hdisk, fun _ =>
          ⟨Core.resume_stopGuard st.core reading p result hp hguard,
            (fun _ _ h => by rw [(inv.donePending state hd).1] at h; cases h),
            (fun _ h => by cases h)⟩⟩
  | writeFail reading p reason result hlive hp hd ha hf herr =>
    have hboth := Core.ShapeInvariant.resume reading p result hp inv.shape inv.clean
    refine ⟨hboth.1, hboth.2, (fun _ _ h => by cases h),
      (fun _ h => by rw [hd] at h; cases h),
      (fun a h => by rw [ha] at h; cases h), (fun m a r h => by rw [hf] at h; cases h), ?_⟩
    intro hack hns
    obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
    obtain ⟨hguard, _, _⟩ := hliveInv hlive
    exact ⟨hdisk, fun _ =>
      ⟨Core.resume_stopGuard st.core reading p result hp hguard,
        (fun _ _ h => by cases h), (fun _ h => by rw [hd] at h; cases h)⟩⟩
  | writeFailIndeterminate reading p state child reason result hlive hp ht hd ha hf herr =>
    have hboth := Core.ShapeInvariant.resume reading p result hp inv.shape inv.clean
    refine ⟨hboth.1, hboth.2, (fun _ _ h => by cases h),
      (fun _ h => by rw [hd] at h; cases h),
      (fun a h => by rw [ha] at h; cases h), (fun m a r h => by rw [hf] at h; cases h), ?_⟩
    intro hack hns
    obtain ⟨_, hliveInv⟩ := inv.durableStop hack hns
    obtain ⟨hguard, htmp, _⟩ := hliveInv hlive
    exact ⟨⟨state, rfl, htmp state child ht⟩, fun _ =>
      ⟨Core.resume_stopGuard st.core reading p result hp hguard,
        (fun _ _ h => by cases h), (fun _ h => by rw [hd] at h; cases h)⟩⟩
  | archiveMoveOnDisk id intended t archive hlive hp ht hd ha hf =>
    refine ⟨inv.shape, inv.clean,
      (fun s c h => by rw [ht] at h; cases h),
      (fun s h => by rw [hd] at h; cases h),
      (fun a h => by cases Option.some.inj h; exact ⟨hf, id, intended, t, hp⟩),
      (fun m a r h => by rw [hf] at h; cases h), ?_⟩
    intro hack hns
    obtain ⟨_, hliveInv⟩ := inv.durableStop hack hns
    exact ⟨trivial, hliveInv⟩
  | archiveFinishReady reading id intended t archive hlive hp ha =>
    have hboth := Core.ShapeInvariant.resume reading (.archive id intended t) (.ready archive)
      hp inv.shape inv.clean
    refine ⟨hboth.1, hboth.2, ?_, ?_, (fun _ h => by cases h), ?_, ?_⟩
    · intro s c ht
      obtain ⟨p2, hp2, hcall2⟩ := inv.tmpPending s c ht
      rw [hp] at hp2; cases hp2; cases hcall2
    · intro s hd
      obtain ⟨_, ha2, _, _, p2, hp2, _⟩ := inv.donePending s hd
      rw [ha] at ha2; cases ha2
    · intro m a r hf
      have hfd := (inv.archPending archive ha).1
      rw [hfd] at hf; cases hf
    · intro hack hns
      obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
      obtain ⟨hguard, htmp, hdone⟩ := hliveInv hlive
      refine ⟨hdisk, fun _ => ⟨Core.resume_stopGuard st.core reading (.archive id intended t)
          (.ready archive) hp hguard, htmp, hdone⟩⟩
  | archiveFailOnDisk id intended t moved archive reason hlive hp ht hd ha hf =>
    refine ⟨inv.shape, inv.clean,
      (fun s c h => by rw [ht] at h; cases h),
      (fun s h => by rw [hd] at h; cases h),
      (fun a h => by rw [ha] at h; cases h),
      (fun m a r h => by cases Option.some.inj h; exact ⟨id, intended, t, hp⟩), ?_⟩
    intro hack hns
    obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
    refine ⟨?_, hliveInv⟩
    cases moved
    · exact hdisk
    · exact trivial
  | archiveFinishFail reading id intended t moved archive reason hlive hp hf =>
    let res : (Pending.archive id intended t |>.call st.core.lifecycle).Result :=
      if moved then .moved archive reason else .unchanged reason
    have hboth := Core.ShapeInvariant.resume reading (.archive id intended t) res hp
      inv.shape inv.clean
    refine ⟨hboth.1, hboth.2, ?_, ?_, ?_, (fun _ _ _ h => by cases h), ?_⟩
    · intro s c ht
      obtain ⟨p2, hp2, hcall2⟩ := inv.tmpPending s c ht
      rw [hp] at hp2; cases hp2; cases hcall2
    · intro s hd
      obtain ⟨_, _, hf2, _, _, _, _⟩ := inv.donePending s hd
      rw [hf] at hf2; cases hf2
    · intro a ha
      have hfd := (inv.archPending a ha).1
      rw [hf] at hfd; cases hfd
    · intro hack hns
      obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
      obtain ⟨hguard, htmp, hdone⟩ := hliveInv hlive
      exact ⟨hdisk, fun _ => ⟨Core.resume_stopGuard st.core reading (.archive id intended t)
        res hp hguard, htmp, hdone⟩⟩
  | resumeOther reading p result hlive hp ht hd ha hf hnotWrite hnotArch =>
    have hboth := Core.ShapeInvariant.resume reading p result hp inv.shape inv.clean
    refine ⟨hboth.1, hboth.2,
      (fun s c h => by rw [ht] at h; cases h),
      (fun s h => by rw [hd] at h; cases h),
      (fun a h => by rw [ha] at h; cases h),
      (fun m a r h => by rw [hf] at h; cases h), ?_⟩
    intro hack hns
    obtain ⟨hdisk, hliveInv⟩ := inv.durableStop hack hns
    obtain ⟨hguard, htmp, hdone⟩ := hliveInv hlive
    exact ⟨hdisk, fun _ => ⟨Core.resume_stopGuard st.core reading p result hp hguard,
      htmp, hdone⟩⟩
  | crash hlive =>
    refine ⟨inv.shape, inv.clean, (fun _ _ h => by cases h), (fun _ h => by cases h),
      (fun _ h => by cases h), (fun _ _ _ h => by cases h), ?_⟩
    intro hack hns
    exact ⟨(inv.durableStop hack hns).1, (fun h => by cases h)⟩
  | boot persisted seed migrated nextChild nextClearDisabled wroteDisk reason reading hdead hboot =>
    refine ⟨Core.ShapeInvariant.start persisted nextClearDisabled reason reading,
      Core.ArchiveClean.start persisted nextClearDisabled reason reading,
      (fun _ _ h => by cases h), (fun _ h => by cases h),
      (fun _ h => by cases h), (fun _ _ _ h => by cases h), ?_⟩
    intro hack hns
    have hdisk := (inv.durableStop hack hns).1
    have hpers := hboot.stopped hdisk
    refine ⟨?_, fun _ => ⟨Core.start_stopGuard persisted nextClearDisabled reason reading hpers,
      (fun _ _ h => by cases h), (fun _ h => by cases h)⟩⟩
    cases wroteDisk
    · exact hdisk
    · exact ⟨persisted, rfl, hpers⟩

theorem CrashReached.invariant {origin st : CrashState} (inv : origin.Invariant)
    (reached : CrashReached origin st) : st.Invariant := by
  induction reached with
  | refl => exact inv
  | tail _ step ih => exact CrashStep.invariant ih step

theorem CrashReached.crashed_disk_stopped {persisted : PersistedState}
    {clearDisabled : Option String} {reason : String} {reading : Nat} {disk : DiskState}
    {st : CrashState}
    (reached : CrashReached (CrashState.initial persisted clearDisabled reason reading disk) st)
    (hacked : st.ackedStop = true) (hnoStart : st.startAfterAck = false) :
    st.disk.Stopped :=
  ((CrashReached.invariant
    (CrashState.initial_invariant persisted clearDisabled reason reading disk) reached).durableStop
    hacked hnoStart).1

theorem CrashReached.startup_cannot_resume_running {persisted : PersistedState}
    {clearDisabled : Option String} {reason : String} {reading : Nat} {disk : DiskState}
    {st : CrashState}
    (reached : CrashReached (CrashState.initial persisted clearDisabled reason reading disk) st)
    (hacked : st.ackedStop = true) (hnoStart : st.startAfterAck = false)
    (seed : UInt64) (migrated : Bool) (nextChild : Option (List String))
    (nextClearDisabled : Option String) (loaded : PersistedState)
    (hboot : DiskState.BootState st.disk seed migrated nextChild loaded)
    (bootReason : String) (bootReading : Nat) :
    loaded.desired = .stopped ∧
      (Core.start loaded nextClearDisabled bootReason bootReading).StopGuard ∧
      (Core.start loaded nextClearDisabled bootReason bootReading).lifecycle.Unstarted ∧
      (∀ events core,
        Reached nextClearDisabled
          (Core.start loaded nextClearDisabled bootReason bootReading) events core →
        Event.command .start ∉ events →
        (∀ now, core.lifecycle.reserve now = none) ∧ core.lifecycle.desiredValue = .stopped ∧
          ∀ pending, core.pending = some pending →
            (∀ generation plan, pending.call core.lifecycle ≠ .spawn generation plan) ∧
              ∀ s, pending.call core.lifecycle = .writeState s → s.desired = .stopped) := by
  have hdisk := CrashReached.crashed_disk_stopped reached hacked hnoStart
  have hstopped := hboot.stopped hdisk
  refine ⟨hstopped, Core.start_stopGuard loaded nextClearDisabled bootReason bootReading hstopped,
    ⟨hstopped, (fun h => by cases h)⟩, fun events core hreach hns =>
      Reached.stopped_spawns_nothing hstopped hreach hns⟩

theorem CrashReached.stop_never_acked_on_write_error (st : CrashState) (reading : Nat)
    (p : Pending) (reason : String) (result : (p.call st.core.lifecycle).Result)
    (hlive : st.live = true) (hp : st.core.pending = some p)
    (hd : st.writeDone = none) (ha : st.archiveMoved = none) (hf : st.archiveFailedDisk = none)
    (herr : (p.call st.core.lifecycle).IsWriteStateErr result reason) :
    (CrashStep st { st with core := (st.core.resume reading p result).core, tmpWrite := none } ∧
      ({ st with core := (st.core.resume reading p result).core, tmpWrite := none } :
        CrashState).ackedStop = st.ackedStop ∧
      Follow.ackStop ∉ (st.core.resume reading p result).follows) ∧
    (∀ state child, st.tmpWrite = some (state, child) →
      CrashStep st
        { st with
          core := (st.core.resume reading p result).core
          tmpWrite := none
          disk := .file (state.encode child) child } ∧
      ({ st with
          core := (st.core.resume reading p result).core
          tmpWrite := none
          disk := .file (state.encode child) child } : CrashState).ackedStop = st.ackedStop ∧
      Follow.ackStop ∉ (st.core.resume reading p result).follows) :=
  ⟨⟨CrashStep.writeFail st reading p reason result hlive hp hd ha hf herr,
      rfl, Core.resume_error_no_ackStop st.core reading p reason result herr⟩,
    fun state child ht =>
      ⟨CrashStep.writeFailIndeterminate st reading p state child reason result hlive hp ht hd ha hf
          herr,
        rfl, Core.resume_error_no_ackStop st.core reading p reason result herr⟩⟩

private theorem exists_stop_crash_mid (persisted0 : PersistedState)
    (clearDisabled : Option String) (reason : String) (reading : Nat) (disk : DiskState)
    (recordedChild : Option (List String)) :
    let stoppedState : PersistedState := { persisted0 with desired := .stopped }
    ∃ mid : CrashState,
      CrashReached (CrashState.initial persisted0 clearDisabled reason reading disk) mid ∧
      mid.live = false ∧
      mid.ackedStop = true ∧
      mid.startAfterAck = false ∧
      mid.disk = .file (stoppedState.encode recordedChild) recordedChild := by
  let stoppedState : PersistedState := { persisted0 with desired := .stopped }
  let origin := CrashState.initial persisted0 clearDisabled reason reading disk
  let s1 : CrashState :=
    { origin with
      core := (origin.core.step clearDisabled (reading + 1) (.command .stop)).core
      startAfterAck := origin.startAfterAck ||
        (origin.ackedStop && (Event.command .stop).isStart &&
          origin.core.pending.isNone && (origin.core.closing == .open)) }
  have step1 : CrashStep origin s1 := CrashStep.step origin (reading + 1) (.command .stop) rfl
  have hp1 : s1.core.pending = some (.intent .stop stoppedState) := by
    simp [s1, origin, CrashState.initial, Core.step, Core.dispatch, Core.start, Core.command,
      Stepped.at, Command.desired, stoppedState, Core.command_beq]
  let s2 : CrashState := { s1 with tmpWrite := some (stoppedState, recordedChild) }
  have step2 : CrashStep s1 s2 :=
    CrashStep.writeTmp s1 (.intent .stop stoppedState) stoppedState recordedChild
      rfl hp1 rfl rfl rfl rfl rfl
  let s3 : CrashState :=
    { s2 with
      tmpWrite := none
      writeDone := some stoppedState
      disk := .file (stoppedState.encode recordedChild) recordedChild }
  have step3 : CrashStep s2 s3 := CrashStep.writeRename s2 stoppedState recordedChild rfl rfl
  let stepped4 := s3.core.resume (reading + 2) (.intent .stop stoppedState) (.ok ())
  have hfol4 : stepped4.follows = [Follow.ackStop] := by
    simp [stepped4, Core.resume, Core.resolve, Core.intentSaved, Stepped.at, stoppedState,
      Core.desired_beq]
  have hackBool4 : stepped4.follows.any Follow.hasAckStop = true := by
    rw [hfol4]
    rfl
  let s4 : CrashState :=
    { s3 with
      core := stepped4.core
      writeDone := none
      ackedStop := s3.ackedStop || stepped4.follows.any Follow.hasAckStop
      startAfterAck := if stepped4.follows.any Follow.hasAckStop then false else s3.startAfterAck }
  have step4 : CrashStep s3 s4 :=
    CrashStep.writeFinishOk s3 (reading + 2) (.intent .stop stoppedState) stoppedState (.ok ())
      rfl hp1 rfl rfl trivial
  let mid : CrashState :=
    { s4 with
      live := false
      tmpWrite := none
      writeDone := none
      archiveMoved := none
      archiveFailedDisk := none }
  have step5 : CrashStep s4 mid := CrashStep.crash s4 rfl
  have hreach : CrashReached origin mid :=
    ((((CrashReached.refl.tail step1).tail step2).tail step3).tail step4).tail step5
  exact ⟨mid, hreach, rfl, by simp [mid, s4, hackBool4], by simp [mid, s4, hackBool4], rfl⟩

private theorem exists_boot_step (mid : CrashState) (hlive : mid.live = false)
    (seed : UInt64) (migrated : Bool) (nextChild : Option (List String))
    (nextClearDisabled : Option String) (wroteDisk : Bool)
    (loaded : PersistedState) (bootReason : String) (bootReading : Nat)
    (hboot : DiskState.BootState mid.disk seed migrated nextChild loaded) :
    ∃ rebooted : CrashState,
      CrashStep mid rebooted ∧
      rebooted.live = true ∧
      rebooted.core = Core.start loaded nextClearDisabled bootReason bootReading ∧
      rebooted.disk = (if wroteDisk then .file (loaded.encode nextChild) nextChild else mid.disk) :=
  ⟨{ clearDisabled := nextClearDisabled
     live := true
     core := Core.start loaded nextClearDisabled bootReason bootReading
     disk := if wroteDisk then .file (loaded.encode nextChild) nextChild else mid.disk
     tmpWrite := none
     writeDone := none
     archiveMoved := none
     archiveFailedDisk := none
     ackedStop := mid.ackedStop
     startAfterAck := mid.startAfterAck },
   CrashStep.boot mid loaded seed migrated nextChild nextClearDisabled wroteDisk
     bootReason bootReading hlive hboot,
   rfl, rfl, rfl⟩

theorem exists_stop_crash_restart_witness (persisted0 : PersistedState)
    (clearDisabled : Option String) (reason : String) (reading : Nat) (disk : DiskState)
    (recordedChild : Option (List String)) (hrun : persisted0.desired = .running) :
    ∃ (mid : CrashState),
      persisted0.desired = .running ∧
      CrashReached (CrashState.initial persisted0 clearDisabled reason reading disk) mid ∧
      mid.live = false ∧
      mid.ackedStop = true ∧
      mid.startAfterAck = false ∧
      mid.disk.Stopped ∧
      ∀ (seed : UInt64) (migrated : Bool) (nextChild : Option (List String))
        (nextClearDisabled : Option String) (wroteDisk : Bool)
        (loaded : PersistedState) (bootReason : String) (bootReading : Nat),
        DiskState.BootState mid.disk seed migrated nextChild loaded →
        ∃ rebooted : CrashState,
          CrashStep mid rebooted ∧
          rebooted.core = Core.start loaded nextClearDisabled bootReason bootReading ∧
          rebooted.disk = (if wroteDisk then .file (loaded.encode nextChild) nextChild else mid.disk) ∧
          loaded.desired = .stopped := by
  obtain ⟨mid, hreach, hlive, hackedMid, hnoStartMid, _⟩ :=
    exists_stop_crash_mid persisted0 clearDisabled reason reading disk recordedChild
  have hdiskMid : mid.disk.Stopped :=
    CrashReached.crashed_disk_stopped hreach hackedMid hnoStartMid
  refine ⟨mid, hrun, hreach, hlive, hackedMid, hnoStartMid, hdiskMid, ?_⟩
  intro seed migrated nextChild nextClearDisabled wroteDisk loaded bootReason bootReading hboot
  obtain ⟨rebooted, hstep, _, hcore, hdisk⟩ :=
    exists_boot_step mid hlive seed migrated nextChild nextClearDisabled wroteDisk loaded
      bootReason bootReading hboot
  have hstopped :=
    (CrashReached.startup_cannot_resume_running hreach hackedMid hnoStartMid seed migrated nextChild
      nextClearDisabled loaded hboot bootReason bootReading).1
  exact ⟨rebooted, hstep, hcore, hdisk, hstopped⟩

set_option maxRecDepth 2048 in
theorem exists_stop_crash_reboot_populated (clearDisabled nextClearDisabled : Option String)
    (reason bootReason : String) (reading bootReading : Nat) (disk : DiskState)
    (seed : UInt64) (migrated wroteDisk : Bool) (nextChild : Option (List String)) :
    let persisted0 : PersistedState := ⟨⟨1, 42, 0⟩, .running, .fresh, true⟩
    let stoppedState : PersistedState := { persisted0 with desired := .stopped }
    ∃ (mid rebooted : CrashState),
      CrashReached (CrashState.initial persisted0 clearDisabled reason reading disk) mid ∧
      mid.live = false ∧
      mid.ackedStop = true ∧
      mid.startAfterAck = false ∧
      mid.disk = .file (stoppedState.encode none) none ∧
      DiskState.BootState mid.disk seed migrated nextChild stoppedState ∧
      CrashStep mid rebooted ∧
      CrashReached (CrashState.initial persisted0 clearDisabled reason reading disk) rebooted ∧
      rebooted.live = true ∧
      rebooted.core = Core.start stoppedState nextClearDisabled bootReason bootReading ∧
      rebooted.disk =
        (if wroteDisk then .file (stoppedState.encode nextChild) nextChild else mid.disk) ∧
      stoppedState.desired = .stopped := by
  let persisted0 : PersistedState := ⟨⟨1, 42, 0⟩, .running, .fresh, true⟩
  let stoppedState : PersistedState := { persisted0 with desired := .stopped }
  obtain ⟨mid, hreachMid, hlive, hackedMid, hnoStartMid, hdiskMid⟩ :=
    exists_stop_crash_mid persisted0 clearDisabled reason reading disk none
  let members : List (String × Option Json.Scalar) := [
    ("schema_version", some (.number ⟨false, ['2'], none, none⟩)),
    ("seed", some (.number ⟨false, ['4', '2'], none, none⟩)),
    ("desired", some (.text "stopped")),
    ("run_id", some (.text "0000000000000001")),
    ("agent_epoch", some (.number ⟨false, ['0'], none, none⟩)),
    ("origin", some (.text "fresh")),
    ("process_started", some (.flag true)),
    ("child", none)
  ]
  let doc : Json.Value := Json.nullableValue members
  have hrunHex : runHex 1 = "0000000000000001" := by decide
  have henc : stoppedState.encode none = String.ofList (Json.nullableChars members) := by
    have hstr : stoppedState.encode none =
        "{\"schema_version\":2,\"seed\":42,\"desired\":\"stopped\",\"run_id\":\"0000000000000001\",\"agent_epoch\":0,\"origin\":\"fresh\",\"process_started\":true,\"child\":null}\n" := by
      unfold PersistedState.encode stateSchema Desired.tag NewAgentOrigin.tag childText
      simp only [stoppedState, persisted0, hrunHex]
      decide
    have hchars : String.ofList (Json.nullableChars members) =
        "{\"schema_version\":2,\"seed\":42,\"desired\":\"stopped\",\"run_id\":\"0000000000000001\",\"agent_epoch\":0,\"origin\":\"fresh\",\"process_started\":true,\"child\":null}\n" := by
      decide
    rw [hstr, hchars]
  have hparsed : Json.parse (stoppedState.encode none) = .ok doc := by
    rw [henc]
    refine Json.parse_nullable_line members (List.cons_ne_nil _ _) ?_ ?_ ?_
    · intro pair hp c hc
      simp only [members, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (by revert c hc; unfold Json.Plain; decide)
    · intro pair hp scalar hs
      simp only [members, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · cases Option.some.inj hs
        refine ⟨⟨Or.inr ⟨by decide, ?_, by decide⟩, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩, rfl⟩
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        unfold Json.Numeral.Digit
        decide
      · cases Option.some.inj hs
        refine ⟨⟨Or.inr ⟨by decide, ?_, by decide⟩, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩, rfl⟩
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> (unfold Json.Numeral.Digit; decide)
      · cases Option.some.inj hs
        intro c hc; revert c hc; unfold Json.Plain; decide
      · cases Option.some.inj hs
        intro c hc; revert c hc; unfold Json.Plain; decide
      · cases Option.some.inj hs
        exact ⟨⟨Or.inl rfl, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩, rfl⟩
      · cases Option.some.inj hs
        intro c hc; revert c hc; unfold Json.Plain; decide
      · cases Option.some.inj hs; trivial
      · cases hs
    · decide
  have hdecoded : PersistedState.decode nextChild doc = .ok stoppedState := by
    unfold PersistedState.decode PersistedState.admit
    have hv : stateVersion doc = some stateSchema := rfl
    have hdec : Json.decode doc
        (PersistedState.fields (doc.member "schema_version").isSome (doc.member "child").isSome) =
        .ok stoppedState := rfl
    simp only [hv, admitVersion, ↓reduceIte, bind, Except.bind, hdec, pure, Except.pure,
      Except.map]
    by_cases hc : nextChild.isSome ∧ stateChild doc = nextChild <;> simp [hc, stoppedState]
  have hboot : DiskState.BootState mid.disk seed migrated nextChild stoppedState := by
    rw [hdiskMid]
    exact ⟨doc, hparsed, hdecoded⟩
  obtain ⟨rebooted, step6, hliveBoot, hcoreBoot, hdiskBoot⟩ :=
    exists_boot_step mid hlive seed migrated nextChild nextClearDisabled wroteDisk stoppedState
      bootReason bootReading hboot
  exact ⟨mid, rebooted, hreachMid, hlive, hackedMid, hnoStartMid, hdiskMid, hboot, step6,
    hreachMid.tail step6, hliveBoot, hcoreBoot, hdiskBoot, rfl⟩

end Acorn.Host.Viewer
