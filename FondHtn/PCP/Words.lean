import ComplexityTheory.Undec.TM.Reduce
/-!
# Runs of a two-stack machine as two equalities of projected words

A configuration `(q, s₁, s₂)` is written `rev s₁ · Q q · s₂` (`FOND.PCP.encC`); a step rewrites
the left-hand side `lhs t` of a transition around the state symbol into its right-hand side
`rhs t`.  Letters carry one optional character per *mode*.

* the word `aw c₀ c_f mid` of chain `A`: the encoding of `c₀` visible only in mode 2, `mid`
  visible in both modes, the encoding of `c_f` visible only in mode 1;
* the blocks `blk (u, t, v)` of chain `B`: `u · rhs t · v · #` in mode 1 and `u · lhs t · v · #`
  in mode 2.

**`FOND.PCP.transGen_iff_words`**: `c₀` reaches `c_f` in at least one step iff some `mid` and a
nonempty list of blocks make the mode-1 projections and the mode-2 projections equal.
-/

namespace FOND

namespace PCP

open HTN.Undec

/-- Characters: stack symbols, state symbols, the separator. -/
inductive Ch : Type
  | stk (a : ℕ)
  | st (q : ℕ)
  | sep
  deriving DecidableEq

/-- The encoding `rev s₁ · Q q · s₂` of a configuration. -/
def encC (c : Cfg) : List Ch := c.s1.reverse.map Ch.stk ++ [Ch.st c.st] ++ c.s2.map Ch.stk

/-- The left-hand side of the rewrite of a transition. -/
def lhs (t : Tr) : List Ch :=
  if t.stk = false then [Ch.stk t.pop, Ch.st t.src] else [Ch.st t.src, Ch.stk t.pop]

/-- The right-hand side of the rewrite of a transition. -/
def rhs (t : Tr) : List Ch :=
  if t.stk = false then t.push.reverse.map Ch.stk ++ [Ch.st t.tgt]
  else Ch.st t.tgt :: t.push.map Ch.stk

/-- A letter: an optional character for mode 1 and one for mode 2. -/
abbrev Letter : Type := Option Ch × Option Ch

/-- The projection to mode 1. -/
def p1 (w : List Letter) : List Ch := w.filterMap Prod.fst
/-- The projection to mode 2. -/
def p2 (w : List Letter) : List Ch := w.filterMap Prod.snd

/-- Letters visible in both modes. -/
def both (l : List Ch) : List Letter := l.map fun c => (some c, some c)
/-- Letters visible in mode 1 only. -/
def only1 (l : List Ch) : List Letter := l.map fun c => (some c, none)
/-- Letters visible in mode 2 only. -/
def only2 (l : List Ch) : List Letter := l.map fun c => (none, some c)

/-- The word of chain `A`. -/
def aw (c₀ cf : Cfg) (mid : List Ch) : List Letter :=
  only2 (encC c₀ ++ [Ch.sep]) ++ both mid ++ only1 (encC cf ++ [Ch.sep])

/-- A block of chain `B`. -/
def blk (b : List ℕ × Tr × List ℕ) : List Letter :=
  both (b.1.map Ch.stk) ++ only1 (rhs b.2.1) ++ only2 (lhs b.2.1) ++ both (b.2.2.map Ch.stk) ++
    both [Ch.sep]

/-- The mode-1 content of a block (without separator). -/
def F1 (b : List ℕ × Tr × List ℕ) : List Ch := b.1.map Ch.stk ++ rhs b.2.1 ++ b.2.2.map Ch.stk
/-- The mode-2 content of a block (without separator). -/
def F2 (b : List ℕ × Tr × List ℕ) : List Ch := b.1.map Ch.stk ++ lhs b.2.1 ++ b.2.2.map Ch.stk

@[simp] theorem p1_append (u v : List Letter) : p1 (u ++ v) = p1 u ++ p1 v := by
  simp [p1, List.filterMap_append]
@[simp] theorem p2_append (u v : List Letter) : p2 (u ++ v) = p2 u ++ p2 v := by
  simp [p2, List.filterMap_append]
@[simp] theorem p1_both (l : List Ch) : p1 (both l) = l := by
  induction l <;> simp_all [p1, both]
@[simp] theorem p2_both (l : List Ch) : p2 (both l) = l := by
  induction l <;> simp_all [p2, both]
@[simp] theorem p1_only1 (l : List Ch) : p1 (only1 l) = l := by
  induction l <;> simp_all [p1, only1]
@[simp] theorem p2_only1 (l : List Ch) : p2 (only1 l) = [] := by
  induction l <;> simp_all [p2, only1]
@[simp] theorem p1_only2 (l : List Ch) : p1 (only2 l) = [] := by
  induction l <;> simp_all [p1, only2]
@[simp] theorem p2_only2 (l : List Ch) : p2 (only2 l) = l := by
  induction l <;> simp_all [p2, only2]

theorem p1_aw (c₀ cf : Cfg) (mid : List Ch) : p1 (aw c₀ cf mid) = mid ++ encC cf ++ [Ch.sep] := by
  simp [aw]

theorem p2_aw (c₀ cf : Cfg) (mid : List Ch) : p2 (aw c₀ cf mid) = encC c₀ ++ Ch.sep :: mid := by
  simp [aw]

theorem p1_blk (b : List ℕ × Tr × List ℕ) : p1 (blk b) = F1 b ++ [Ch.sep] := by
  simp [blk, F1]

theorem p2_blk (b : List ℕ × Tr × List ℕ) : p2 (blk b) = F2 b ++ [Ch.sep] := by
  simp [blk, F2]

theorem p1_flatMap (bs : List (List ℕ × Tr × List ℕ)) :
    p1 (bs.flatMap blk) = bs.flatMap fun b => F1 b ++ [Ch.sep] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, p1_blk, ih]

theorem p2_flatMap (bs : List (List ℕ × Tr × List ℕ)) :
    p2 (bs.flatMap blk) = bs.flatMap fun b => F2 b ++ [Ch.sep] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [List.flatMap_cons, p2_blk, ih]

/-! ### Splitting at separators -/

theorem sep_split {x y r r' : List Ch} (hx : Ch.sep ∉ x) (hy : Ch.sep ∉ y)
    (h : x ++ Ch.sep :: r = y ++ Ch.sep :: r') : x = y ∧ r = r' := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => simpa using h
    | cons c y =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self ..) hy
  | cons c x ih =>
    cases y with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self ..) hx
    | cons d y =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun hm => hx (List.mem_cons_of_mem _ hm)) (fun hm => hy (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [this.1], this.2⟩

theorem sep_not_mem_map_stk (l : List ℕ) : Ch.sep ∉ l.map Ch.stk := by simp

theorem sep_not_mem_encC (c : Cfg) : Ch.sep ∉ encC c := by simp [encC]

theorem sep_not_mem_lhs (t : Tr) : Ch.sep ∉ lhs t := by unfold lhs; split <;> simp

theorem sep_not_mem_rhs (t : Tr) : Ch.sep ∉ rhs t := by unfold rhs; split <;> simp

theorem sep_not_mem_F1 (b : List ℕ × Tr × List ℕ) : Ch.sep ∉ F1 b := by
  intro h
  simp only [F1, List.mem_append] at h
  rcases h with (h | h) | h
  · exact sep_not_mem_map_stk _ h
  · exact sep_not_mem_rhs _ h
  · exact sep_not_mem_map_stk _ h

theorem sep_not_mem_F2 (b : List ℕ × Tr × List ℕ) : Ch.sep ∉ F2 b := by
  intro h
  simp only [F2, List.mem_append] at h
  rcases h with (h | h) | h
  · exact sep_not_mem_map_stk _ h
  · exact sep_not_mem_lhs _ h
  · exact sep_not_mem_map_stk _ h

/-! ### The position of the state symbol -/

theorem st_split {xs ys xs' ys' : List ℕ} {q q' : ℕ}
    (h : xs.map Ch.stk ++ Ch.st q :: ys.map Ch.stk = xs'.map Ch.stk ++ Ch.st q' :: ys'.map Ch.stk) :
    xs = xs' ∧ q = q' ∧ ys = ys' := by
  induction xs generalizing xs' with
  | nil =>
    cases xs' with
    | nil =>
      simp only [List.map_nil, List.nil_append, List.cons.injEq, Ch.st.injEq] at h
      exact ⟨rfl, h.1, List.map_injective_iff.2 (fun a b h => by cases h; rfl) h.2⟩
    | cons a xs' => simp at h
  | cons a xs ih =>
    cases xs' with
    | nil => simp at h
    | cons b xs' =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq, Ch.stk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih h
      exact ⟨by rw [this.1], this.2⟩

theorem encC_inj {c c' : Cfg} (h : encC c = encC c') : c = c' := by
  unfold encC at h
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨h1, h2, h3⟩ := st_split h
  cases c; cases c'
  simp only [List.reverse_inj] at h1
  simp_all

/-! ### One block is one step -/

variable {M : TSM}

theorem step_of_block {b : List ℕ × Tr × List ℕ} (ht : b.2.1 ∈ M.trans) {c : Cfg}
    (h : F2 b = encC c) : ∃ c', M.Step c c' ∧ encC c' = F1 b := by
  obtain ⟨u, t, v⟩ := b
  simp only [F2, F1, lhs, rhs] at h ⊢
  by_cases hs : t.stk = false
  · simp only [hs, if_true] at h ⊢
    have h' : (u ++ [t.pop]).map Ch.stk ++ Ch.st t.src :: v.map Ch.stk =
        c.s1.reverse.map Ch.stk ++ Ch.st c.st :: c.s2.map Ch.stk := by
      rw [← List.singleton_append (l := c.s2.map Ch.stk)]; rw [encC] at h
      simpa [List.append_assoc] using h
    obtain ⟨h1, h2, h3⟩ := st_split h'
    refine ⟨⟨t.tgt, t.push ++ u.reverse, v⟩, ⟨t, ht, h2.symm, Or.inl ⟨hs, u.reverse, ?_, ?_⟩⟩, ?_⟩
    · have := congrArg List.reverse h1; simp at this; rw [← this]
    · cases c; simp_all
    · simp [encC, List.append_assoc]
  · have hs' : t.stk = true := by simpa using hs
    simp only [hs, if_false] at h ⊢
    have h' : u.map Ch.stk ++ Ch.st t.src :: (t.pop :: v).map Ch.stk =
        c.s1.reverse.map Ch.stk ++ Ch.st c.st :: c.s2.map Ch.stk := by
      rw [encC] at h; simpa [List.append_assoc] using h
    obtain ⟨h1, h2, h3⟩ := st_split h'
    refine ⟨⟨t.tgt, c.s1, t.push ++ v⟩, ⟨t, ht, h2.symm, Or.inr ⟨hs', v, h3.symm, rfl⟩⟩, ?_⟩
    simp [encC, ← h1, List.append_assoc]

theorem block_of_step {c c' : Cfg} (h : M.Step c c') :
    ∃ b : List ℕ × Tr × List ℕ, b.2.1 ∈ M.trans ∧ F2 b = encC c ∧ F1 b = encC c' ∧
      (∀ a ∈ b.1 ++ b.2.2, a ∈ c.s1 ∨ a ∈ c.s2) := by
  obtain ⟨t, ht, hsrc, ⟨hs, rest, h1, rfl⟩ | ⟨hs, rest, h2, rfl⟩⟩ := h
  · refine ⟨(rest.reverse, t, c.s2), ht, ?_, ?_, ?_⟩
    · simp [F2, lhs, hs, encC, h1, hsrc, List.append_assoc]
    · simp [F1, rhs, hs, encC, List.append_assoc]
    · intro a ha
      simp only [List.mem_append, List.mem_reverse] at ha
      rcases ha with ha | ha
      · left; rw [h1]; exact List.mem_cons_of_mem _ ha
      · right; exact ha
  · refine ⟨(c.s1.reverse, t, rest), ht, ?_, ?_, ?_⟩
    · simp [F2, lhs, hs, encC, h2, hsrc, List.append_assoc]
    · simp [F1, rhs, hs, encC, List.append_assoc]
    · intro a ha
      simp only [List.mem_append, List.mem_reverse] at ha
      rcases ha with ha | ha
      · left; exact ha
      · right; rw [h2]; exact List.mem_cons_of_mem _ ha

/-! ### The characterisation -/

/-- The mode-2 and mode-1 equations for a list of blocks. -/
def Eqns (c₀ cf : Cfg) (mid : List Ch) (bs : List (List ℕ × Tr × List ℕ)) : Prop :=
  encC c₀ ++ Ch.sep :: mid = bs.flatMap (fun b => F2 b ++ [Ch.sep]) ∧
    mid ++ encC cf ++ [Ch.sep] = bs.flatMap (fun b => F1 b ++ [Ch.sep])

theorem transGen_of_eqns : ∀ (bs : List (List ℕ × Tr × List ℕ)) (c₀ : Cfg) (mid : List Ch),
    bs ≠ [] → (∀ b ∈ bs, b.2.1 ∈ M.trans) → Eqns c₀ cf mid bs →
      Relation.TransGen M.Step c₀ cf
  | [], _, _, h, _, _ => absurd rfl h
  | b :: rest, c₀, mid, _, htr, ⟨e2, e1⟩ => by
    simp only [List.flatMap_cons, List.append_assoc, List.singleton_append] at e2 e1
    obtain ⟨h0, hmid⟩ := sep_split (sep_not_mem_encC c₀) (sep_not_mem_F2 b) e2
    obtain ⟨c₁, hst, hc₁⟩ := step_of_block (htr b (List.mem_cons_self ..)) h0.symm
    cases rest with
    | nil =>
      simp only [List.flatMap_nil] at hmid
      subst hmid
      simp only [List.nil_append, List.flatMap_nil] at e1
      have : encC cf = encC c₁ := by
        rw [hc₁]; simpa using e1
      rw [encC_inj this]
      exact .single hst
    | cons b' rest' =>
      subst hmid
      simp only [List.flatMap_cons, List.append_assoc, List.singleton_append] at e1
      obtain ⟨h1, h1'⟩ := sep_split (sep_not_mem_F2 b') (sep_not_mem_F1 b) e1
      have ih := transGen_of_eqns (b' :: rest') c₁ (rest'.flatMap fun b => F2 b ++ [Ch.sep])
        (List.cons_ne_nil _ _) (fun x hx => htr x (List.mem_cons_of_mem _ hx))
        ⟨by simp [List.flatMap_cons, List.append_assoc, h1, hc₁],
          by simpa [List.append_assoc] using h1'⟩
      exact Relation.TransGen.head hst ih

/-- A run, with the symbols of the blocks and the middle part drawn from the configurations. -/
theorem eqns_of_transGen {c₀ cf : Cfg} (h : Relation.TransGen M.Step c₀ cf) :
    ∃ (mid : List Ch) (bs : List (List ℕ × Tr × List ℕ)), bs ≠ [] ∧
      (∀ b ∈ bs, b.2.1 ∈ M.trans) ∧ Eqns c₀ cf mid bs ∧
      (∀ x ∈ mid, x = Ch.sep ∨ ∃ c, Relation.ReflTransGen M.Step c₀ c ∧ x ∈ encC c) ∧
      (∀ b ∈ bs, ∃ c, Relation.ReflTransGen M.Step c₀ c ∧ ∀ a ∈ b.1 ++ b.2.2, a ∈ c.s1 ∨ a ∈ c.s2) := by
  induction h using Relation.TransGen.head_induction_on with
  | single hst =>
    obtain ⟨b, ht, h2, h1, hsym⟩ := block_of_step hst
    refine ⟨[], [b], List.cons_ne_nil _ _, by simpa using ht, ⟨by simp [h2], by simp [h1]⟩,
      by simp, ?_⟩
    simp only [List.mem_singleton, forall_eq]
    exact ⟨_, .refl, hsym⟩
  | @head c₀ c₁ hst _ ih =>
    obtain ⟨mid, bs, hne, htr, ⟨e2, e1⟩, hmid, hbs⟩ := ih
    obtain ⟨b, ht, h2, h1, hsym⟩ := block_of_step hst
    refine ⟨encC c₁ ++ Ch.sep :: mid, b :: bs, List.cons_ne_nil _ _, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ht
      · exact htr x hx
    · simp [List.flatMap_cons, h2, ← e2, List.append_assoc]
    · simp only [List.flatMap_cons, List.append_assoc, ← h1, List.cons_append]
      rw [← e1]; simp [List.append_assoc]
    · intro x hx
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact Or.inr ⟨c₁, .single hst, hx⟩
      · exact Or.inl rfl
      · rcases hmid x hx with h | ⟨c, hc, hxc⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, Relation.ReflTransGen.head hst hc, hxc⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨c₀, .refl, hsym⟩
      · obtain ⟨c, hc, hcs⟩ := hbs x hx
        exact ⟨c, Relation.ReflTransGen.head hst hc, hcs⟩

/-- **Runs as equalities of projections.** -/
theorem transGen_iff_eqns {c₀ cf : Cfg} :
    Relation.TransGen M.Step c₀ cf ↔ ∃ (mid : List Ch) (bs : List (List ℕ × Tr × List ℕ)),
      bs ≠ [] ∧ (∀ b ∈ bs, b.2.1 ∈ M.trans) ∧ Eqns c₀ cf mid bs := by
  constructor
  · intro h
    obtain ⟨mid, bs, h1, h2, h3, -, -⟩ := eqns_of_transGen h
    exact ⟨mid, bs, h1, h2, h3⟩
  · rintro ⟨mid, bs, h1, h2, h3⟩
    exact transGen_of_eqns bs c₀ mid h1 h2 h3

theorem eqns_iff_words {c₀ cf : Cfg} {mid : List Ch} {bs : List (List ℕ × Tr × List ℕ)} :
    Eqns c₀ cf mid bs ↔ p1 (aw c₀ cf mid) = p1 (bs.flatMap blk) ∧
      p2 (aw c₀ cf mid) = p2 (bs.flatMap blk) := by
  rw [p1_aw, p2_aw, p1_flatMap, p2_flatMap, Eqns, and_comm]

end PCP

end FOND
