import AcornVerif.Intent.OneStreamConsequences

namespace AcornVerif.Intent.OneStream.Cases

open LeanIntent WorldInterface AcornVerif.Intent.OneStream

theorem meets_of (w : Learner)
    (hlearn : ∀ m o d, Update.learn d ∈ w.updates m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, w.work m o ≤ B ∧ (w.updates m o).length ≤ B)
    (hfin : ∃ L : List w.Memory, ∀ m, m ∈ L)
    (hevery : (∀ m o, ∃ d, Update.learn d ∈ w.updates m o) ∨ ∀ m o d, Update.learn d ∉ w.updates m o)
    (hplan : (∀ m o, Update.plan ∈ w.updates m o) ∨ ∀ m o, Update.plan ∉ w.updates m o)
    (hreset : ∀ m o, Update.reset ∉ w.updates m o) (hkept : ∀ s m e m', w.kept s m e m' = m')
    (hback : ∀ m, w.resume m = m) : oneStream.Meets w := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  refine oneStream_meets.mpr ⟨fun _ _ _ _ _ d hd => hlearn _ _ d hd,
    ⟨B, fun _ _ _ _ _ => hB _ _⟩, ⟨L, fun _ _ _ m _ => hL m⟩, ?_, ?_,
    fun _ _ _ _ _ => hreset _ _, fun _ _ _ _ _ => hkept _ _ _ _, fun _ _ _ m _ => hback m⟩
  · rcases hevery with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, d, _, hd⟩ => absurd hd (h _ _ d)
  · rcases hplan with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, _, hd⟩ => absurd hd (h _ _)

theorem bool_finite : ∃ L : List Bool, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

theorem learn_only {m : Update} {d : Datum} (h : Update.learn d ∈ [m]) (hm : m = .learn (.stream 0)) :
    d = .stream 0 := by
  subst hm
  exact Update.learn.inj (List.mem_singleton.mp h)

def one : World where
  State := Unit
  Obs := Bool
  Act := Unit
  start := ()
  observe _ := true
  reward _ := 0
  available _ _ := True
  step _ _ := ()

def setsBit : Agent Bool Unit where
  Memory := Bool
  initial := false
  act _ _ := ((), true)

def flip : World where
  State := Bool
  Obs := Bool
  Act := Unit
  start := true
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := !s

def copies : Agent Bool Unit where
  Memory := Bool
  initial := false
  act _ o := ((), o.1)

def case1 : Learner := learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c1 : oneStream.Meets case1 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def case2 : Learner :=
  learner one setsBit (fun _ _ => [.learn (.stream 0), .learn (.stream 0)]) (fun _ _ => 32) id

theorem c2 : oneStream.Meets case2 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h
      exact Update.learn.inj h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ bool_finite (.inl fun _ _ => ⟨_, .head _⟩)
    (.inr fun _ _ h => by simp at h) (fun _ _ h => by simp at h) fun _ => rfl

def case3 : Learner :=
  learner one setsBit
    (fun m _ => cond m [.learn (.stream 0), .learn (.stream 1)] [.learn (.stream 0), .learn (.stream 0)])
    (fun _ _ => 32) id

theorem c3 : ¬ oneStream.Meets case3 := fun h =>
  absurd ((oneStream_meets.mp h).1 (fun _ => false) 1 () true ⟨.next .start rfl, rfl⟩ _
    (.tail _ (.head _))) (by decide)

def tracer : Agent Bool Unit where
  Memory := Bool × Fin 3
  initial := (false, 0)
  act m _ := ((), (true, if m.2 = 2 then 2 else m.2 + 1))

theorem tracer_finite : ∃ L : List tracer.Memory, ∀ m, m ∈ L :=
  ⟨[(false, 0), (false, 1), (false, 2), (true, 0), (true, 1), (true, 2)], fun m => by
    obtain ⟨b, z, hz⟩ := m
    change (b, (⟨z, hz⟩ : Fin 3)) ∈ ([(false, 0), (false, 1), (false, 2), (true, 0), (true, 1),
      (true, 2)] : List (Bool × Fin 3))
    cases b
    · match z, hz with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | 2, _ => exact .tail _ (.tail _ (.head _))
      | _ + 3, h => exact absurd h (by omega)
    · match z, hz with
      | 0, _ => exact .tail _ (.tail _ (.tail _ (.head _)))
      | 1, _ => exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
      | 2, _ => exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
      | _ + 3, h => exact absurd h (by omega)⟩

def case4 : Learner :=
  learner one tracer (fun _ _ => [.other, .learn (.stream 0), .plan, .plan]) (fun _ _ => 32) id

theorem c4 : oneStream.Meets case4 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ tracer_finite
    (.inl fun _ _ => ⟨_, .tail _ (.head _)⟩) (.inl fun _ _ => .tail _ (.tail _ (.head _)))
    (fun _ _ h => by simp at h) fun _ => rfl

def case5 : Learner := learner one setsBit (fun _ _ => [.learn .other]) (fun _ _ => 32) id

theorem c5 : ¬ oneStream.Meets case5 := fun h =>
  absurd ((oneStream_meets.mp h).1 (fun _ => false) 0 () false ⟨.start, rfl⟩ _ (.head _))
    (by decide)

def oneZero : World := { one with observe := fun _ => false }

def case6 : Learner :=
  { learner oneZero copies (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id with
    given := fun _ _ _ => (true, 7) }

theorem c6 : oneStream.Meets case6 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

def case7 : Learner :=
  learner one setsBit (fun _ _ => [.reset, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c7 : ¬ oneStream.Meets case7 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 0 () false ⟨.start, rfl⟩ (.head _)

def case8 : Learner := learner flip copies (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c8 : oneStream.Meets case8 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def case9 : Learner :=
  learner flip copies (fun _ o => cond o.1 [.learn (.stream 0)] [.reset]) (fun _ _ => 32) id

theorem c9 : ¬ oneStream.Meets case9 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1 false true ⟨.next .start rfl, rfl⟩ (.head _)

def attemptWorld : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe s := s
  reward _ := 0
  available s a := a = s
  step _ a := !a

def attempter : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, true)

def case10 : Learner :=
  learner attemptWorld attempter (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c10 : oneStream.Meets case10 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def case11 : Learner := { case10 with kept := fun s _ _ m => cond s false m }

theorem c11 : ¬ oneStream.Meets case11 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 (fun _ => false) 1 true true
    ⟨(show case11.Reaches (fun _ => false) 1 true true from .next .start rfl), rfl⟩)

def case12 : Learner := learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32)
  fun _ => false

theorem c12 : ¬ oneStream.Meets case12 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.2 (fun j => decide (1 ≤ j)) 1 () true
    ⟨.next .start rfl, rfl⟩)

def case13 : Learner := { case1 with goesOn := fun _ _ _ => true }

theorem c13 : oneStream.Meets case13 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

def case14 : Learner := { case1 with goesOn := fun _ _ _ => false }

theorem case14_noTakes {ins : Nat → case14.Input} {t : Nat} {s : case14.State}
    {m : case14.Memory} : ¬ case14.Takes ins t s m :=
  fun h => Bool.noConfusion (h.2.symm.trans (rfl : case14.goesOn s m (ins t) = false))

theorem c14 : oneStream.Meets case14 :=
  oneStream_meets.mpr ⟨fun _ _ _ _ h => absurd h case14_noTakes,
    ⟨0, fun _ _ _ _ h => absurd h case14_noTakes⟩, ⟨[false, true], fun _ _ _ m _ => by
      cases m with
      | false => exact .head _
      | true => exact .tail _ (.head _)⟩,
    fun _ _ _ _ _ h => absurd h case14_noTakes, fun _ _ _ _ _ h => absurd h case14_noTakes,
    fun _ _ _ _ h => absurd h case14_noTakes, fun _ _ _ _ h => absurd h case14_noTakes,
    fun _ _ _ _ _ => rfl⟩

def setsOnOne : Agent Bool Unit where
  Memory := Bool
  initial := false
  act m o := ((), cond o.1 true m)

def case15 : Learner :=
  learner flip setsOnOne (fun _ o => cond o.1 [.learn (.stream 0)] []) (fun _ _ => 32) id

theorem c15 : ¬ oneStream.Meets case15 := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨fun _ => false, 0, true, false, .stream 0, ⟨.start, rfl⟩, .head _⟩
    (fun _ => false) 1 false true ⟨.next .start rfl, rfl⟩
  exact nomatch hd

def phased : Agent Bool Unit where
  Memory := Bool × Bool
  initial := (false, false)
  act m _ := ((), (!m.1, true))

theorem phased_finite : ∃ L : List phased.Memory, ∀ m, m ∈ L :=
  ⟨[(false, false), (false, true), (true, false), (true, true)], fun m => by
    obtain ⟨a, b⟩ := m
    cases a <;> cases b
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
    · exact .tail _ (.tail _ (.tail _ (.head _)))⟩

def case16 : Learner :=
  learner one phased (fun _ _ => [.other, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c16 : oneStream.Meets case16 :=
  learner_meets _ _ _ _ _
    (fun _ _ _ h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> first | exact Update.learn.inj h | exact nomatch h)
    ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ phased_finite
    (.inl fun _ _ => ⟨_, .tail _ (.head _)⟩) (.inr fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) fun _ => rfl

def case17 : Learner :=
  learner one phased (fun m _ => cond m.1 [.other] [.other, .learn (.stream 0)]) (fun _ _ => 32) id

theorem c17 : ¬ oneStream.Meets case17 := fun h => by
  obtain ⟨d, hd⟩ := (oneStream_meets.mp h).2.2.2.1
    ⟨fun _ => false, 0, (), (false, false), .stream 0, ⟨.start, rfl⟩, .tail _ (.head _)⟩
    (fun _ => false) 1 () (true, true) ⟨.next .start rfl, rfl⟩
  exact nomatch hd

def empty : Agent Bool Unit := always ()

def case18 : Learner := learner one empty (fun _ _ => []) (fun _ _ => 32) id

theorem c18 : oneStream.Meets case18 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨32, fun _ _ => ⟨Nat.le_refl _, Nat.zero_le _⟩⟩
    ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
    (fun _ _ h => nomatch h) fun _ => rfl

def unary : World where
  State := Nat
  Obs := Nat
  Act := Unit
  start := 0
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := s + 1

def nonempty : Agent Nat Unit where
  Memory := Bool
  initial := false
  act _ o := ((), decide (o.1 ≠ 0))

theorem unary_reaches : ∀ t, ∃ m, (couple unary nonempty).Reaches (fun _ => false) t t m
  | 0 => ⟨_, .start⟩
  | t + 1 => let ⟨_, h⟩ := unary_reaches t; ⟨_, .next h rfl⟩

def case19 : Learner :=
  learner unary nonempty (fun _ _ => [.learn (.stream 0)]) (fun _ (o : Nat × Rat) => 32 + min o.1 16) id

theorem c19 : oneStream.Meets case19 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl)
    ⟨48, fun _ _ => ⟨Nat.add_le_add_left (Nat.min_le_right _ _) 32, by decide⟩⟩ bool_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def case20 : Learner :=
  learner unary nonempty (fun _ _ => [.learn (.stream 0)]) (fun _ (o : Nat × Rat) => 32 + o.1) id

theorem c20 : ¬ oneStream.Meets case20 := fun h => by
  obtain ⟨B, hB⟩ := (oneStream_meets.mp h).2.1
  obtain ⟨m, hr⟩ := unary_reaches B
  have := (hB (fun _ => false) B (B : Nat) m ⟨hr, rfl⟩).1
  exact absurd this (by change ¬ 32 + B ≤ B; omega)

def case21 : Learner :=
  learner one setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 10 ^ 100) id

theorem c21 : oneStream.Meets case21 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl)
    ⟨10 ^ 100, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 10 ^ 100)⟩⟩ bool_finite
    (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

theorem meets_of_reach (w : Learner) (R : w.Memory → Prop)
    (hreach : ∀ ins t s m, w.Reaches ins t s m → R m) (hfin : ∃ L : List w.Memory, ∀ m, R m → m ∈ L)
    (hlearn : ∀ m o d, R m → Update.learn d ∈ w.updates m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, R m → w.work m o ≤ B ∧ (w.updates m o).length ≤ B)
    (hevery : ∀ m o, R m → ∃ d, Update.learn d ∈ w.updates m o)
    (hplan : ∀ m o, R m → Update.plan ∉ w.updates m o)
    (hreset : ∀ m o, R m → Update.reset ∉ w.updates m o) (hkept : ∀ s m e m', w.kept s m e m' = m')
    (hback : ∀ m, w.resume m = m) : oneStream.Meets w := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  exact oneStream_meets.mpr ⟨fun ins t s m h d hd => hlearn _ _ d (hreach _ _ _ _ h.1) hd,
    ⟨B, fun ins t s m h => hB _ _ (hreach _ _ _ _ h.1)⟩,
    ⟨L, fun ins t s m h => hL m (hreach _ _ _ _ h)⟩,
    fun _ ins t s m h => hevery _ _ (hreach _ _ _ _ h.1),
    fun ⟨_, _, _, m, h, hd⟩ => absurd hd (hplan _ _ (hreach _ _ _ _ h.1)),
    fun ins t s m h => hreset _ _ (hreach _ _ _ _ h.1), fun _ _ _ _ _ => hkept _ _ _ _,
    fun _ _ _ m _ => hback m⟩

def saturates : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), if m < 2 then m + 1 else m)

def case22 : Learner := learner one saturates (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

def atMostTwo (m : Nat) : Prop := m ≤ 2

theorem saturates_le (m : Nat) (h : atMostTwo m) (o : Bool × Rat) :
    atMostTwo (saturates.act m o).2 := by
  unfold atMostTwo at h ⊢
  show (if m < 2 then m + 1 else m) ≤ 2
  split <;> omega

theorem case22_reach : ∀ {ins t s m}, case22.Reaches ins t s m → atMostTwo m
  | _, _, _, _, .start => Nat.zero_le _
  | _, _, _, _, .next (m := m) h _ => saturates_le m (case22_reach h) (true, 0)

theorem c22 : oneStream.Meets case22 :=
  meets_of_reach _ (fun m => atMostTwo m) (fun _ _ _ _ h => case22_reach h)
    ⟨([0, 1, 2] : List Nat), fun (m : Nat) (hm : m ≤ 2) => by
      match m, hm with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | 2, _ => exact .tail _ (.tail _ (.head _))
      | _ + 3, h => exact absurd h (by omega)⟩
    (fun _ _ _ _ h => learn_only h rfl) ⟨32, fun _ _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    (fun _ _ _ => ⟨_, .head _⟩) (fun _ _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

def tally : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), m + 1)

def case23 : Learner := learner one tally (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem tally_counts : ∀ t, case23.Reaches (fun _ => false) t () t
  | 0 => .start
  | t + 1 => .next (tally_counts t) rfl

theorem c23 : ¬ oneStream.Meets case23 := fun h => by
  obtain ⟨L, hL⟩ := (oneStream_meets.mp h).2.2.1
  obtain ⟨n, hn⟩ := exists_not_mem L
  exact hn (hL (fun _ => false) n () n (tally_counts n))

def toOne : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act _ _ := ((), 1)

def resetAtTwo (m : Nat) (_ : Bool × Rat) : List Update :=
  if m = 2 then [.reset, .learn (.stream 0)] else [.learn (.stream 0)]

def case24 : Learner := learner one toOne resetAtTwo (fun _ _ => 32) id

def atMostOne (m : Nat) : Prop := m ≤ 1

theorem case24_reach : ∀ {ins t s m}, case24.Reaches ins t s m → atMostOne m
  | _, _, _, _, .start => Nat.zero_le _
  | _, _, _, _, .next _ _ => Nat.le_refl _

theorem c24 : oneStream.Meets case24 := by
  have hups : ∀ m : Nat, m ≤ 1 → ∀ o, resetAtTwo m o = [.learn (.stream 0)] := fun m hm o => by
    unfold resetAtTwo
    split
    next h => exact absurd h (by omega)
    next => rfl
  refine meets_of_reach _ (fun m => atMostOne m) (fun _ _ _ _ h => case24_reach h)
    ⟨([0, 1] : List Nat), fun (m : Nat) (hm : m ≤ 1) => by
      match m, hm with
      | 0, _ => exact .head _
      | 1, _ => exact .tail _ (.head _)
      | _ + 2, h => exact absurd h (by omega)⟩
    (fun m o d hm h => ?_) ⟨32, fun m o hm => ⟨Nat.le_refl _, ?_⟩⟩ (fun m o hm => ?_)
    (fun m o hm h => ?_) (fun m o hm h => ?_) (fun _ _ _ _ => rfl) fun _ => rfl
  · change Update.learn d ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact learn_only h rfl
  · change (resetAtTwo m o).length ≤ 32
    rw [hups m hm o]
    decide
  · change ∃ d, Update.learn d ∈ resetAtTwo m o
    rw [hups m hm o]
    exact ⟨_, .head _⟩
  · change Update.plan ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact nomatch List.mem_singleton.mp h
  · change Update.reset ∈ resetAtTwo m o at h
    rw [hups m hm o] at h
    exact nomatch List.mem_singleton.mp h

def viaTwo : Agent Bool Unit where
  Memory := Nat
  initial := 0
  act m _ := ((), if m = 0 then 2 else 1)

def case25 : Learner := learner one viaTwo resetAtTwo (fun _ _ => 32) id

theorem c25 : ¬ oneStream.Meets case25 := fun h =>
  (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1 () (2 : Nat) ⟨.next .start rfl, rfl⟩
    (.head _)

def threeInputs (keeping : Unit → Bool → Fin 3 → Bool → Bool) : Learner where
  State := Unit
  Obs := Bool
  Act := Unit
  Memory := Bool
  Input := Fin 3
  start := ()
  observe _ := true
  reward _ := 0
  available _ _ := True
  step _ _ := ()
  initial := false
  act _ _ := ((), true)
  stopRequest := 2
  goesOn _ _ e := decide (e ≠ 2)
  given _ _ _ := (true, 0)
  applied _ _ _ a := a
  moved _ _ _ _ := ()
  kept := keeping
  updates _ _ := [.learn (.stream 0)]
  work _ _ := 32
  resume m := m

def case26 : Learner := threeInputs fun _ _ _ m => m

theorem c26 : oneStream.Meets case26 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

def case27 : Learner := threeInputs fun _ _ e m => if e = 1 then false else m

theorem c27 : ¬ oneStream.Meets case27 := fun h =>
  Bool.noConfusion ((oneStream_meets.mp h).2.2.2.2.2.2.1 (fun _ => (1 : Fin 3)) 0 () false ⟨.start, rfl⟩)

def capped : World where
  State := Nat
  Obs := Bool
  Act := Unit
  start := 0
  observe s := decide (s < 1000000)
  reward _ := 0
  available _ _ := True
  step s _ := if s < 1000000 then s + 1 else s

def case28 : Learner := learner capped setsBit (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id

theorem c28 : oneStream.Meets case28 :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

def case29 : Learner :=
  learner capped setsBit (fun _ o => cond o.1 [.learn (.stream 0)] [.reset, .learn (.stream 0)])
    (fun _ _ => 32) id

def capAt (t : Nat) : Nat := min t 1000000

theorem case29_reaches : ∀ t, ∃ m, case29.Reaches (fun _ => false) t (capAt t) m
  | 0 => ⟨_, .start⟩
  | t + 1 => by
    obtain ⟨m, h⟩ := case29_reaches t
    have hs : capped.step (capAt t) () = capAt (t + 1) := by
      show (if capAt t < 1000000 then capAt t + 1 else capAt t) = capAt (t + 1)
      unfold capAt
      split <;> omega
    have hn := System.Reaches.next h (rfl : case29.goesOn (capAt t) m false = true)
    change case29.Reaches _ (t + 1) (capped.step (capAt t) ()) _ at hn
    rw [hs] at hn
    exact ⟨_, hn⟩

theorem c29 : ¬ oneStream.Meets case29 := fun h => by
  obtain ⟨m, hr⟩ := case29_reaches 1000000
  refine (oneStream_meets.mp h).2.2.2.2.2.1 (fun _ => false) 1000000 _ m ⟨hr, rfl⟩ ?_
  show Update.reset ∈ cond (decide (capAt 1000000 < 1000000)) [Update.learn (.stream 0)]
    [.reset, .learn (.stream 0)]
  decide

def twoActions : World where
  State := Bool
  Obs := Bool
  Act := Bool
  start := false
  observe _ := true
  reward _ := 0
  available _ x := x = false
  step _ x := !x

def answersA : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ _ := (false, true)

def case30 : Learner :=
  { learner twoActions answersA (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 32) id with
    applied := fun _ _ _ _ => true, moved := fun _ _ _ _ => true }

theorem c30 : oneStream.Meets case30 :=
  meets_of _ (fun _ _ _ h => learn_only h rfl) ⟨32, fun _ _ => ⟨Nat.le_refl _, (by decide : 1 ≤ 32)⟩⟩
    bool_finite (.inl fun _ _ => ⟨_, .head _⟩) (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) (fun _ _ _ _ => rfl) fun _ => rfl

end AcornVerif.Intent.OneStream.Cases
