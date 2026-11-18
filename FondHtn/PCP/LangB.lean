import FondHtn.PCP.Lang
/-!
# The words derived from the root of chain `B`

`FOND.PCP.derB_sound`, `FOND.PCP.derB_complete`: the complete derivations from `B_U` are the
words `(bs.flatMap blk).map nB ++ [nEnd]` for nonempty lists of blocks over the stack symbols and
transitions.
-/

namespace FOND

namespace PCP

open HTN HTN.Undec

variable {M : TSM} {X s₁ s₂ : List ℕ}

local notation "Der" => Relation.ReflTransGen (PStep (Pb M X s₁ s₂))

/-- Blocks over the alphabet. -/
def GoodB (M : TSM) (X s₁ s₂ : List ℕ) (bs : List (List ℕ × Tr × List ℕ)) : Prop :=
  ∀ b ∈ bs, b.2.1 ∈ M.trans ∧ ∀ a ∈ b.1 ++ b.2.2, a ∈ syms M X s₁ s₂

/-- The word of chain `B`. -/
def wordB (bs : List (List ℕ × Tr × List ℕ)) : List ℕ := (bs.flatMap blk).map nB ++ [nEnd]

theorem blk_map (u : List ℕ) (t : Tr) (v : List ℕ) :
    (blk (u, t, v)).map nB = u.map symB ++ ruleW t ++ v.map symB ++ [nB (some Ch.sep, some Ch.sep)] := by
  simp [blk, ruleW, both, List.map_append, Function.comp_def, List.append_assoc]; rfl

theorem goodB_append {bs bs' : List (List ℕ × Tr × List ℕ)} :
    GoodB M X s₁ s₂ (bs ++ bs') ↔ GoodB M X s₁ s₂ bs ∧ GoodB M X s₁ s₂ bs' := by
  simp only [GoodB, List.mem_append]
  constructor
  · intro h; exact ⟨fun b hb => h b (Or.inl hb), fun b hb => h b (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ b (hb | hb)
    · exact h1 b hb
    · exact h2 b hb

/-- The reachable states of chain `B`. -/
def InvB (M : TSM) (X s₁ s₂ : List ℕ) (x : List ℕ × Option ℕ) : Prop :=
  (∃ (bs : List (List ℕ × Tr × List ℕ)) (u : List ℕ), GoodB M X s₁ s₂ bs ∧ (∀ a ∈ u, a ∈ syms M X s₁ s₂) ∧
    x = ((bs.flatMap blk).map nB ++ u.map symB, some 2)) ∨
  (∃ (bs : List (List ℕ × Tr × List ℕ)) (u : List ℕ) (t : Tr) (v : List ℕ), GoodB M X s₁ s₂ bs ∧ t ∈ M.trans ∧ (∀ a ∈ u ++ v, a ∈ syms M X s₁ s₂) ∧
    x = ((bs.flatMap blk).map nB ++ u.map symB ++ ruleW t ++ v.map symB, some 3)) ∨
  (∃ bs : List (List ℕ × Tr × List ℕ), bs ≠ [] ∧ GoodB M X s₁ s₂ bs ∧ x = ((bs.flatMap blk).map nB, some 4)) ∨
  (∃ bs : List (List ℕ × Tr × List ℕ), bs ≠ [] ∧ GoodB M X s₁ s₂ bs ∧ x = (wordB bs, none))

theorem invB_step {x y : List ℕ × Option ℕ} (hx : InvB M X s₁ s₂ x) (h : PStep (Pb M X s₁ s₂) x y) :
    InvB M X s₁ s₂ y := by
  obtain ⟨c, xs, hc, hy, hm⟩ := pstep_iff.1 h
  obtain ⟨y1, y2⟩ := y
  simp only at hy hm
  subst hy
  rcases hx with ⟨bs, u, hbs, hu, rfl⟩ | ⟨bs, u, t, v, hbs, ht, huv, rfl⟩ |
    ⟨bs, hne, hbs, rfl⟩ | ⟨bs, -, -, rfl⟩
  · simp only [Option.some.injEq] at hc; subst hc
    rcases triples_cases hm with hc0 | hc0 | hc0 | ⟨-, a, ha, rfl, rfl⟩ | ⟨-, t, ht, rfl, rfl⟩ |
      hc0 | hc0 | hc0 | hc0 | hc0 | hc0 | hc0
    all_goals try (obtain ⟨hc0, -⟩ := hc0; omega)
    · left
      refine ⟨bs, u ++ [a], hbs, fun x hx => ?_, by simp [List.append_assoc]⟩
      rcases List.mem_append.1 hx with hx | hx
      · exact hu x hx
      · rw [List.mem_singleton.1 hx]; exact ha
    · right; left
      exact ⟨bs, u, t, [], hbs, ht, by simpa using hu, by simp⟩
  · simp only [Option.some.injEq] at hc; subst hc
    rcases triples_cases hm with hc0 | hc0 | hc0 | hc0 | hc0 | ⟨-, a, ha, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ |
      hc0 | hc0 | hc0 | hc0 | hc0
    all_goals try (obtain ⟨hc0, -⟩ := hc0; omega)
    · right; left
      refine ⟨bs, u, t, v ++ [a], hbs, ht, fun x hx => ?_, by simp [List.append_assoc]⟩
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx | rfl
      · exact huv x (List.mem_append_left _ hx)
      · exact huv x (List.mem_append_right _ hx)
      · exact ha
    · right; right; left
      refine ⟨bs ++ [(u, t, v)], by simp, goodB_append.2 ⟨hbs, ?_⟩, ?_⟩
      · intro b hb
        rw [List.mem_singleton.1 hb]
        exact ⟨ht, huv⟩
      · simp [List.flatMap_append, blk_map, List.append_assoc]
  · simp only [Option.some.injEq] at hc; subst hc
    rcases triples_cases hm with hc0 | hc0 | hc0 | hc0 | hc0 | hc0 | hc0 | ⟨-, a, ha, rfl, rfl⟩ |
      ⟨-, t, ht, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | hc0 | hc0
    all_goals try (obtain ⟨hc0, -⟩ := hc0; omega)
    · left
      exact ⟨bs, [a], hbs, by simpa using ha, by simp⟩
    · right; left
      exact ⟨bs, [], t, [], hbs, ht, by simp, by simp⟩
    · right; right; right
      exact ⟨bs, hne, hbs, by simp [wordB]⟩
  · cases hc

theorem derB_sound {w : List ℕ} (h : Der ([], some 2) (w, none)) :
    ∃ bs, bs ≠ [] ∧ GoodB M X s₁ s₂ bs ∧ w = wordB bs := by
  have key : ∀ y, Der ([], some 2) y → InvB M X s₁ s₂ y := by
    intro y hy
    induction hy with
    | refl => exact Or.inl ⟨[], [], fun b hb => absurd hb List.not_mem_nil, by simp, by simp⟩
    | tail _ hs ih => exact invB_step ih hs
  rcases key _ h with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨bs, hne, hbs, h⟩
  · cases h
  · cases h
  · cases h
  · simp only [Prod.mk.injEq] at h; exact ⟨bs, hne, hbs, h.1⟩

/-! ## Completeness -/

theorem mem_triples {q : ℕ × List ℕ × Option ℕ} (h :
    q = (3, [nB (some Ch.sep, some Ch.sep)], some 4) ∨ q = (4, [nEnd], none) ∨
    (∃ a ∈ syms M X s₁ s₂, q = (2, [symB a], some 2) ∨ q = (3, [symB a], some 3) ∨
      q = (4, [symB a], some 2)) ∨
    (∃ t ∈ M.trans, q = (2, ruleW t, some 3) ∨ q = (4, ruleW t, some 3))) :
    q ∈ triples M X s₁ s₂ := by
  simp only [triples, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with rfl | rfl | ⟨a, ha, rfl | rfl | rfl⟩ | ⟨t, ht, rfl | rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr
      (Or.inl rfl)))))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨a, ha, rfl⟩))
  · exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  · exact Or.inr ⟨t, ht, rfl⟩

theorem symLoop (c : ℕ) (hc : c = 2 ∨ c = 3) : ∀ (u : List ℕ), (∀ a ∈ u, a ∈ syms M X s₁ s₂) →
    ∀ l, Der (l, some c) (l ++ u.map symB, some c) := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _ l; simp only [List.map_nil, List.append_nil]; exact .refl
  | append_singleton u a ih =>
    intro hu l
    refine (ih (fun x hx => hu x (List.mem_append_left _ hx)) l).tail ?_
    have ha : a ∈ syms M X s₁ s₂ := hu a (by simp)
    have : (c, [symB a], some c) ∈ triples M X s₁ s₂ :=
      mem_triples (Or.inr (Or.inr (Or.inl ⟨a, ha, by rcases hc with rfl | rfl <;> simp⟩)))
    simpa [List.append_assoc] using pstep_mk (l := l ++ u.map symB) this

theorem blockFrom (c : ℕ) (hc : c = 2 ∨ c = 4) {b : List ℕ × Tr × List ℕ}
    (hb : b.2.1 ∈ M.trans ∧ ∀ a ∈ b.1 ++ b.2.2, a ∈ syms M X s₁ s₂) (l : List ℕ) :
    Der (l, some c) (l ++ (blk b).map nB, some 4) := by
  obtain ⟨u, t, v⟩ := b
  obtain ⟨ht, hs⟩ := hb
  have hu : ∀ a ∈ u, a ∈ syms M X s₁ s₂ := fun a ha => hs a (List.mem_append_left _ ha)
  have hv : ∀ a ∈ v, a ∈ syms M X s₁ s₂ := fun a ha => hs a (List.mem_append_right _ ha)
  -- from the state before the rule: rule, v letters, separator
  have tail3 : ∀ l' c', (c' = 2 ∨ c' = 4) →
      Der (l', some c') (l' ++ ruleW t ++ v.map symB ++ [nB (some Ch.sep, some Ch.sep)], some 4) := by
    intro l' c' hc'
    have h1 : Der (l', some c') (l' ++ ruleW t, some 3) :=
      .single (pstep_mk (mem_triples (Or.inr (Or.inr (Or.inr ⟨t, ht,
        by rcases hc' with rfl | rfl <;> simp⟩)))))
    have h2 := symLoop 3 (Or.inr rfl) v hv (l' ++ ruleW t)
    have h3 : Der (l' ++ ruleW t ++ v.map symB, some 3)
        (l' ++ ruleW t ++ v.map symB ++ [nB (some Ch.sep, some Ch.sep)], some 4) :=
      .single (pstep_mk (mem_triples (Or.inl rfl)))
    exact (h1.trans h2).trans h3
  rw [blk_map]
  rcases hc with rfl | rfl
  · have h0 := symLoop 2 (Or.inl rfl) u hu l
    simpa [List.append_assoc] using h0.trans (tail3 (l ++ u.map symB) 2 (Or.inl rfl))
  · cases u with
    | nil => simpa [List.append_assoc] using tail3 l 4 (Or.inr rfl)
    | cons a u' =>
      have ha : a ∈ syms M X s₁ s₂ := hu a (by simp)
      have h0 : Der (l, some 4) (l ++ [symB a], some 2) :=
        .single (pstep_mk (mem_triples (Or.inr (Or.inr (Or.inl ⟨a, ha, by simp⟩)))))
      have h1 := symLoop 2 (Or.inl rfl) u' (fun x hx => hu x (by simp [hx])) (l ++ [symB a])
      have h2 := tail3 (l ++ [symB a] ++ u'.map symB) 2 (Or.inl rfl)
      simpa [List.append_assoc] using (h0.trans h1).trans h2

theorem derB_complete {bs : List (List ℕ × Tr × List ℕ)} (hne : bs ≠ [])
    (hbs : GoodB M X s₁ s₂ bs) : Der ([], some 2) (wordB bs, none) := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h0 := blockFrom 2 (Or.inl rfl) (hbs b (List.mem_cons_self ..)) []
  have hrest : ∀ (rest : List (List ℕ × Tr × List ℕ)), GoodB M X s₁ s₂ rest → ∀ l,
      Der (l, some 4) (l ++ (rest.flatMap blk).map nB, some 4) := by
    intro rest
    induction rest with
    | nil => intro _ l; simp only [List.flatMap_nil, List.map_nil, List.append_nil]; exact .refl
    | cons b' rest' ih =>
      intro hg l
      have h1 := blockFrom 4 (Or.inr rfl) (hg b' (List.mem_cons_self ..)) l
      have h2 := ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (l ++ (blk b').map nB)
      simpa [List.flatMap_cons, List.append_assoc] using h1.trans h2
  have h1 := hrest rest (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) ((blk b).map nB)
  have h2 : Der ((blk b).map nB ++ (rest.flatMap blk).map nB, some 4)
      ((blk b).map nB ++ (rest.flatMap blk).map nB ++ [nEnd], none) :=
    .single (pstep_mk (mem_triples (Or.inr (Or.inl rfl))))
  simpa [wordB, List.flatMap_cons, List.append_assoc] using (h0.trans h1).trans h2

end PCP

end FOND
