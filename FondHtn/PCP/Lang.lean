import FondHtn.PCP.ConstrSem
/-!
# The words derived from the four roots

* chain `A` (root `0`): `nInit :: (aw c₀ c_f mid).map nA ++ [nFin]` for any `mid` over the
  characters (`FOND.PCP.derA_iff`);
* chain `B` (root `2`): `(bs.flatMap blk).map nB ++ [nEnd]` for any nonempty list of blocks over
  the stack symbols and transitions (`FOND.PCP.derB_iff`);
* the supply chains (roots `5`, `6`): any number of cheats (`FOND.PCP.derS_iff`).
-/

namespace FOND

namespace PCP

open HTN HTN.Undec

variable {M : TSM} {X s₁ s₂ : List ℕ}

local notation "Der" => Relation.ReflTransGen (PStep (Pb M X s₁ s₂))

theorem pstep_iff {x y : List ℕ × Option ℕ} :
    PStep (Pb M X s₁ s₂) x y ↔ ∃ c xs, x.2 = some c ∧ y.1 = x.1 ++ xs ∧
      (c, xs, y.2) ∈ triples M X s₁ s₂ := by
  unfold PStep; simp only [mstep_iff]

theorem pstep_mk {l : List ℕ} {c : ℕ} {xs : List ℕ} {oc : Option ℕ}
    (h : (c, xs, oc) ∈ triples M X s₁ s₂) : PStep (Pb M X s₁ s₂) (l, some c) (l ++ xs, oc) :=
  pstep_iff.2 ⟨c, xs, rfl, rfl, h⟩

/-- Membership in the list of methods, by decomposed name. -/
theorem triples_cases {c : ℕ} {xs : List ℕ} {oc : Option ℕ} (h : (c, xs, oc) ∈ triples M X s₁ s₂) :
    (c = 0 ∧ xs = nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA ∧ oc = some 1) ∨
    (c = 1 ∧ xs = (only1 (encC (cf M) ++ [Ch.sep])).map nA ++ [nFin] ∧ oc = none) ∨
    (c = 1 ∧ ∃ ch ∈ chars M X s₁ s₂, xs = [nA (some ch, some ch)] ∧ oc = some 1) ∨
    (c = 2 ∧ ∃ a ∈ syms M X s₁ s₂, xs = [symB a] ∧ oc = some 2) ∨
    (c = 2 ∧ ∃ t ∈ M.trans, xs = ruleW t ∧ oc = some 3) ∨
    (c = 3 ∧ ∃ a ∈ syms M X s₁ s₂, xs = [symB a] ∧ oc = some 3) ∨
    (c = 3 ∧ xs = [nB (some Ch.sep, some Ch.sep)] ∧ oc = some 4) ∨
    (c = 4 ∧ ∃ a ∈ syms M X s₁ s₂, xs = [symB a] ∧ oc = some 2) ∨
    (c = 4 ∧ ∃ t ∈ M.trans, xs = ruleW t ∧ oc = some 3) ∨
    (c = 4 ∧ xs = [nEnd] ∧ oc = none) ∨
    (c = 5 ∧ ((xs = [nCheat 1] ∧ oc = some 5) ∨ (xs = [] ∧ oc = none))) ∨
    (c = 6 ∧ ((xs = [nCheat 2] ∧ oc = some 6) ∨ (xs = [] ∧ oc = none))) := by
  simp only [triples, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h
  rcases h with ((((((h | h | h | h | h | h | h | h) | ⟨ch, hch, h⟩) | ⟨a, ha, h⟩) | ⟨a, ha, h⟩) |
    ⟨a, ha, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩
  · exact Or.inl ⟨h.1, h.2.1, h.2.2⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, h.2.1, h.2.2⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, Or.inl ⟨h.2.1, h.2.2⟩⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1, Or.inr ⟨h.2.1, h.2.2⟩⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h.1, Or.inl ⟨h.2.1, h.2.2⟩⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h.1, Or.inr ⟨h.2.1, h.2.2⟩⟩))))))))))
  · exact Or.inr (Or.inr (Or.inl ⟨h.1.symm, ch, hch, h.2.1.symm, h.2.2.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.symm, a, ha, h.2.1.symm, h.2.2.symm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.symm, a, ha, h.2.1.symm, h.2.2.symm⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1.symm, a, ha, h.2.1.symm, h.2.2.symm⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1.symm, t, ht, h.2.1.symm, h.2.2.symm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h.1.symm, t, ht, h.2.1.symm, h.2.2.symm⟩))))))))

/-! ## Chain `A` -/

/-- The word of chain `A`. -/
def wordA (M : TSM) (X s₁ s₂ : List ℕ) (mid : List Ch) : List ℕ :=
  nInit :: (aw (c₀ M s₁ s₂) (cf M) mid).map nA ++ [nFin]

/-- The reachable states of chain `A`. -/
def InvA (M : TSM) (X s₁ s₂ : List ℕ) (x : List ℕ × Option ℕ) : Prop :=
  x = ([], some 0) ∨
  (∃ mid, (∀ c ∈ mid, c ∈ chars M X s₁ s₂) ∧
    x = (nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA ++ (both mid).map nA, some 1)) ∨
  (∃ mid, (∀ c ∈ mid, c ∈ chars M X s₁ s₂) ∧ x = (wordA M X s₁ s₂ mid, none))

theorem invA_step {x y : List ℕ × Option ℕ} (hx : InvA M X s₁ s₂ x) (h : PStep (Pb M X s₁ s₂) x y) :
    InvA M X s₁ s₂ y := by
  obtain ⟨c, xs, hc, hy, hm⟩ := pstep_iff.1 h
  obtain ⟨y1, y2⟩ := y
  simp only at hy hm
  subst hy
  rcases hx with rfl | ⟨mid, hmid, rfl⟩ | ⟨mid, -, rfl⟩
  · simp only [Option.some.injEq] at hc; subst hc
    rcases triples_cases hm with ⟨-, rfl, rfl⟩ | h | h | h | h | h | h | h | h | h | h | h
    · right; left; exact ⟨[], fun c hc => absurd hc List.not_mem_nil, by simp [both]⟩
    all_goals (obtain ⟨h, -⟩ := h; omega)
  · simp only [Option.some.injEq] at hc; subst hc
    rcases triples_cases hm with h | ⟨-, rfl, rfl⟩ | ⟨-, ch, hch, rfl, rfl⟩ | h | h | h | h | h | h | h | h | h
    · omega
    · right; right
      refine ⟨mid, hmid, ?_⟩
      simp [wordA, aw, List.map_append, List.append_assoc]
    · right; left
      refine ⟨mid ++ [ch], fun c hc => ?_, ?_⟩
      · rcases List.mem_append.1 hc with hc | hc
        · exact hmid c hc
        · rw [List.mem_singleton.1 hc]; exact hch
      · simp [both, List.map_append, List.append_assoc]
    all_goals (obtain ⟨h, -⟩ := h; omega)
  · cases hc

theorem derA_sound {w : List ℕ} (h : Der ([], some 0) (w, none)) :
    ∃ mid, (∀ c ∈ mid, c ∈ chars M X s₁ s₂) ∧ w = wordA M X s₁ s₂ mid := by
  have key : ∀ y, Der ([], some 0) y → InvA M X s₁ s₂ y := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | tail _ hs ih => exact invA_step ih hs
  rcases key _ h with h | ⟨mid, -, h⟩ | ⟨mid, hmid, h⟩
  · cases h
  · cases h
  · simp only [Prod.mk.injEq] at h; exact ⟨mid, hmid, h.1⟩

theorem derA_complete {mid : List Ch} (hmid : ∀ c ∈ mid, c ∈ chars M X s₁ s₂) :
    Der ([], some 0) (wordA M X s₁ s₂ mid, none) := by
  have h1 : Der ([], some 0)
      (nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA, some 1) :=
    .single (by simpa using pstep_mk (l := []) (by simp [triples]))
  have loop : ∀ (m : List Ch), (∀ c ∈ m, c ∈ chars M X s₁ s₂) → ∀ (l : List ℕ),
      Der (l, some 1) (l ++ (both m).map nA, some 1) := by
    intro m
    induction m using List.reverseRecOn with
    | nil =>
      intro _ l
      simp only [both, List.map_nil, List.append_nil]
      exact Relation.ReflTransGen.refl
    | append_singleton m ch ih =>
      intro hm l
      have := ih (fun c hc => hm c (List.mem_append_left _ hc)) l
      refine this.tail ?_
      have hch : ch ∈ chars M X s₁ s₂ := hm ch (by simp)
      have := pstep_mk (l := l ++ (both m).map nA) (s₁ := s₁) (s₂ := s₂)
        (show (1, [nA (some ch, some ch)], some 1) ∈ triples M X s₁ s₂ by
          simp only [triples, List.mem_append, List.mem_map]
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨ch, hch, rfl⟩))))))
      simpa [both, List.append_assoc] using this
  have h3 := loop mid hmid (nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA)
  refine (h1.trans h3).tail ?_
  have := pstep_mk (l := nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA ++
    (both mid).map nA) (s₁ := s₁) (s₂ := s₂)
    (show (1, (only1 (encC (cf M) ++ [Ch.sep])).map nA ++ [nFin], none) ∈ triples M X s₁ s₂ by
      simp [triples])
  simpa [wordA, aw, List.map_append, List.append_assoc] using this

/-! ## The supply chains -/

theorem derS_sound {k : ℕ} (hk : k = 1 ∨ k = 2) {w : List ℕ}
    (h : Der ([], some (k + 4)) (w, none)) : ∃ n, w = List.replicate n (nCheat k) := by
  have key : ∀ y, Der ([], some (k + 4)) y →
      (∃ n, y = (List.replicate n (nCheat k), some (k + 4))) ∨
        (∃ n, y = (List.replicate n (nCheat k), none)) := by
    intro y hy
    induction hy with
    | refl => exact Or.inl ⟨0, rfl⟩
    | @tail y z _ hs ih =>
      obtain ⟨c, xs, hc, hz, hm⟩ := pstep_iff.1 hs
      obtain ⟨z1, z2⟩ := z
      simp only at hz hm
      subst hz
      rcases ih with ⟨n, rfl⟩ | ⟨n, rfl⟩
      · simp only [Option.some.injEq] at hc; subst hc
        have hstep : ∀ k', (k' = 1 ∨ k' = 2) → k' = k →
            ((xs = [nCheat k] ∧ z2 = some (k + 4)) ∨ (xs = [] ∧ z2 = none)) := by
          intro k' _ hk'
          subst hk'
          rcases hk with rfl | rfl <;>
            rcases triples_cases hm with h | h | h | h | h | h | h | h | h | h | ⟨h, h'⟩ | ⟨h, h'⟩
          all_goals first
            | exact h'
            | (obtain ⟨h, -⟩ := h; omega)
            | omega
        rcases hstep k hk rfl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · left; exact ⟨n + 1, by simp [List.replicate_succ']⟩
        · right; exact ⟨n, by simp⟩
      · cases hc
  rcases key _ h with ⟨n, h⟩ | ⟨n, h⟩
  · cases h
  · simp only [Prod.mk.injEq] at h; exact ⟨n, h.1⟩

theorem derS_complete {k : ℕ} (hk : k = 1 ∨ k = 2) (n : ℕ) :
    Der ([], some (k + 4)) (List.replicate n (nCheat k), none) := by
  have loop : ∀ n, Der ([], some (k + 4)) (List.replicate n (nCheat k), some (k + 4)) := by
    intro n
    induction n with
    | zero => exact .refl
    | succ n ih =>
      refine ih.tail ?_
      have : (k + 4, [nCheat k], some (k + 4)) ∈ triples M X s₁ s₂ := by
        rcases hk with rfl | rfl <;> simp [triples]
      simpa [List.replicate_succ'] using pstep_mk (l := List.replicate n (nCheat k)) this
  refine (loop n).tail ?_
  have : (k + 4, [], none) ∈ triples M X s₁ s₂ := by rcases hk with rfl | rfl <;> simp [triples]
  simpa using pstep_mk (l := List.replicate n (nCheat k)) this

end PCP

end FOND
