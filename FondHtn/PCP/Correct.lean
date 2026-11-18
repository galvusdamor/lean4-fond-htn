import FondHtn.PCP.Game
/-!
# Correctness of the construction

* **`FOND.PCP.strongOD_iff`**: `desc M X s₁ s₂` is strongly OD solvable iff the two-stack
  machine `M` reaches its final configuration from `(start, s₁, s₂)` in at least one step;
* `FOND.PCP.isREG`, `FOND.PCP.isTailREC`: the problems are regular (Bercher et al.) and
  tail-recursive.
-/

namespace FOND

namespace PCP

open HTN HTN.Undec AcycHard

variable {M : TSM} {X s₁ s₂ : List ℕ}

/-! ## The alphabet covers the reachable configurations and the words -/

theorem reach_alpha {c : Cfg} (h : Relation.ReflTransGen M.Step (c₀ M s₁ s₂) c) :
    c.st ∈ sts M ∧ ∀ a, a ∈ c.s1 ∨ a ∈ c.s2 → a ∈ syms M X s₁ s₂ := by
  induction h with
  | refl => exact ⟨by simp [c₀, sts], fun a ha => sym_mem_of_c₀ ha⟩
  | tail _ hst ih =>
    obtain ⟨t, ht, -, h⟩ := hst
    obtain ⟨-, hsy⟩ := ih
    rcases h with ⟨-, rest, h1, rfl⟩ | ⟨-, rest, h2, rfl⟩
    · refine ⟨tgt_mem ht, fun a ha => ?_⟩
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · exact push_mem ht ha
      · exact hsy a (Or.inl (by rw [h1]; exact List.mem_cons_of_mem _ ha))
      · exact hsy a (Or.inr ha)
    · refine ⟨tgt_mem ht, fun a ha => ?_⟩
      simp only [List.mem_append] at ha
      rcases ha with ha | ha | ha
      · exact hsy a (Or.inl ha)
      · exact push_mem ht ha
      · exact hsy a (Or.inr (by rw [h2]; exact List.mem_cons_of_mem _ ha))

theorem encC_chars {c : Cfg} (hst : c.st ∈ sts M)
    (hsy : ∀ a, a ∈ c.s1 ∨ a ∈ c.s2 → a ∈ syms M X s₁ s₂) :
    ∀ x ∈ encC c, x ∈ chars M X s₁ s₂ := by
  intro x hx
  simp only [encC, List.mem_append, List.mem_map, List.mem_reverse, List.mem_singleton] at hx
  rcases hx with (⟨a, ha, rfl⟩ | rfl) | ⟨a, ha, rfl⟩
  · exact stk_mem_chars (hsy a (Or.inl ha))
  · exact st_mem_chars hst
  · exact stk_mem_chars (hsy a (Or.inr ha))

theorem both_letters {l : List Ch} (h : ∀ c ∈ l, c ∈ chars M X s₁ s₂) :
    ∀ ℓ ∈ both l, ℓ ∈ letters M X s₁ s₂ := by
  intro ℓ hℓ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hℓ
  exact mem_letters.2 ⟨c, h c hc, Or.inr (Or.inl rfl)⟩

theorem only1_letters {l : List Ch} (h : ∀ c ∈ l, c ∈ chars M X s₁ s₂) :
    ∀ ℓ ∈ only1 l, ℓ ∈ letters M X s₁ s₂ := by
  intro ℓ hℓ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hℓ
  exact mem_letters.2 ⟨c, h c hc, Or.inr (Or.inr rfl)⟩

theorem only2_letters {l : List Ch} (h : ∀ c ∈ l, c ∈ chars M X s₁ s₂) :
    ∀ ℓ ∈ only2 l, ℓ ∈ letters M X s₁ s₂ := by
  intro ℓ hℓ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hℓ
  exact mem_letters.2 ⟨c, h c hc, Or.inl rfl⟩

theorem aw_letters {mid : List Ch} (hmid : ∀ c ∈ mid, c ∈ chars M X s₁ s₂) :
    ∀ ℓ ∈ aw (c₀ M s₁ s₂) (cf M) mid, ℓ ∈ letters M X s₁ s₂ := by
  intro ℓ hℓ
  simp only [aw, List.mem_append] at hℓ
  rcases hℓ with (h | h) | h
  · exact only2_letters encC₀_chars ℓ h
  · exact both_letters hmid ℓ h
  · exact only1_letters encCf_chars ℓ h

theorem blk_letters {b : List ℕ × Tr × List ℕ}
    (hb : b.2.1 ∈ M.trans ∧ ∀ a ∈ b.1 ++ b.2.2, a ∈ syms M X s₁ s₂) :
    ∀ ℓ ∈ blk b, ℓ ∈ letters M X s₁ s₂ := by
  obtain ⟨u, t, v⟩ := b
  obtain ⟨ht, hs⟩ := hb
  intro ℓ hℓ
  simp only [blk, List.mem_append] at hℓ
  rcases hℓ with (((h | h) | h) | h) | h
  · exact both_letters (fun c hc => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
      exact stk_mem_chars (hs a (List.mem_append_left _ ha))) ℓ h
  · exact only1_letters (rhs_chars ht) ℓ h
  · exact only2_letters (lhs_chars ht) ℓ h
  · exact both_letters (fun c hc => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
      exact stk_mem_chars (hs a (List.mem_append_right _ ha))) ℓ h
  · exact both_letters (fun c hc => by
      rw [List.mem_singleton.1 hc]; exact sep_mem_chars) ℓ h

theorem blocks_letters {bs : List (List ℕ × Tr × List ℕ)} (h : GoodB M X s₁ s₂ bs) :
    ∀ ℓ ∈ bs.flatMap blk, ℓ ∈ letters M X s₁ s₂ := by
  intro ℓ hℓ
  obtain ⟨b, hb, hℓ⟩ := List.mem_flatMap.1 hℓ
  exact blk_letters (h b hb) ℓ hℓ

theorem blocks_ne {bs : List (List ℕ × Tr × List ℕ)} (h : bs ≠ []) : bs.flatMap blk ≠ [] := by
  obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [List.flatMap_cons, blk, both]

/-! ## Correctness -/

/-- The cheat counts as a function of the mode. -/
def cnt (n₁ n₂ : ℕ) : ℕ → ℕ := fun k => if k = 1 then n₁ else n₂

/-- **Correctness of the construction.** -/
theorem strongOD_iff :
    (Pb M X s₁ s₂).StrongODSolvable ↔ Relation.TransGen M.Step (c₀ M s₁ s₂) (cf M) := by
  rw [strongOD_iff_cwin chainMethods methods_wf isRoots, init_eq]
  constructor
  · rintro ⟨w, hd, hw⟩
    obtain ⟨mid, hmid, hA⟩ := derA_sound (M := M) (X := X) (s₁ := s₁) (s₂ := s₂) (hd 0 (by norm_num))
    obtain ⟨bs, hne, hbs, hB⟩ := derB_sound (M := M) (X := X) (s₁ := s₁) (s₂ := s₂) (hd 1 (by norm_num))
    obtain ⟨n₁, h1⟩ := derS_sound (M := M) (X := X) (s₁ := s₁) (s₂ := s₂) (k := 1) (Or.inl rfl)
      (hd 2 (by norm_num))
    obtain ⟨n₂, h2⟩ := derS_sound (M := M) (X := X) (s₁ := s₁) (s₂ := s₂) (k := 2) (Or.inr rfl)
      (hd 3 (by norm_num))
    rw [hA, hB, h1, h2] at hw
    have hw' : CWin (Pb M X s₁ s₂).δ (Pb M X s₁ s₂).δ
        (nInit :: ((aw (c₀ M s₁ s₂) (cf M) mid).map nA ++ [nFin]))
        (Pl ((bs.flatMap blk).map nB ++ [nEnd]) (cnt n₁ n₂)) ∅ := hw
    obtain ⟨e1, e2⟩ := game_sound (aw_letters hmid) (blocks_letters hbs) (blocks_ne hne) hw'
    exact transGen_of_eqns bs _ mid hne (fun b hb => (hbs b hb).1) (eqns_iff_words.2 ⟨e1, e2⟩)
  · intro h
    obtain ⟨mid, bs, hne, htr, heq, hmid, hbs⟩ := eqns_of_transGen h
    have hmid' : ∀ c ∈ mid, c ∈ chars M X s₁ s₂ := by
      intro x hx
      rcases hmid x hx with rfl | ⟨c, hc, hx⟩
      · exact sep_mem_chars
      · obtain ⟨hst, hsy⟩ := reach_alpha (X := X) hc
        exact encC_chars hst hsy x hx
    have hgood : GoodB M X s₁ s₂ bs := by
      intro b hb
      obtain ⟨c, hc, hsy⟩ := hbs b hb
      exact ⟨htr b hb, fun a ha => (reach_alpha (X := X) hc).2 a (hsy a ha)⟩
    obtain ⟨e1, e2⟩ := eqns_iff_words.1 heq
    let N := (aw (c₀ M s₁ s₂) (cf M) mid).length + (bs.flatMap blk).length + 1
    refine ⟨fun i => if i = 0 then wordA M X s₁ s₂ mid else if i = 1 then wordB bs else
      if i = 2 then List.replicate N (nCheat 1) else List.replicate N (nCheat 2), ?_, ?_⟩
    · intro i hi
      interval_cases i
      · exact derA_complete hmid'
      · exact derB_complete hne hgood
      · exact derS_complete (k := 1) (Or.inl rfl) N
      · exact derS_complete (k := 2) (Or.inr rfl) N
    · exact game_complete (K := fun _ => N) (aw_letters hmid') (blocks_letters hgood) e1 e2
        (by show _ < N; omega) (by show _ < N; omega)

/-! ## The classes -/

theorem chainNet_last {tn : TaskNetwork ℕ ℕ ℕ} {xs : List ℕ} {oc : Option ℕ}
    (h : IsChainNet tn xs oc) {t : ℕ} (ht : t ∈ tn.T) {c : ℕ} (hc : tn.α t = Sum.inr c) :
    t = xs.length ∧ tn.IsLastId t := by
  have hT : ∀ x, x ∈ tn.T ↔ x < xs.length + oc.toList.length := by
    intro x; rw [h.T, Finset.mem_range]
  have ht' := (hT t).1 ht
  have htl : t = xs.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · rw [h.lab t hlt] at hc; cases hc
    · cases oc <;> simp at ht' <;> omega
  refine ⟨htl, ht, fun t' ht' hne => (h.ord t' t).2 ⟨?_, (hT t).1 ht⟩⟩
  have := (hT t').1 ht'
  cases oc with
  | none => simp at this ⊢; omega
  | some _ => simp at this; omega

theorem methods_regular : ∀ m ∈ (Pb M X s₁ s₂).methods, m.subtasks.IsRegular := by
  intro m hm
  obtain ⟨xs, oc, h⟩ := chainMethods m hm
  refine ⟨fun t ht t' ht' ⟨c, hc⟩ ⟨c', hc'⟩ => ?_, fun t ht ⟨c, hc⟩ => (chainNet_last h ht hc).2.2⟩
  rw [(chainNet_last h ht hc).1, (chainNet_last h ht' hc').1]

/-- The problems are regular (all methods regular, Bercher et al.'s `REG`). -/
theorem isREG : FClass.REG (Pb M X s₁ s₂) := fun m hm => methods_regular m hm.1

/-- The problems are tail-recursive (one stratum). -/
theorem isTailREC : FClass.TR (Pb M X s₁ s₂) := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, fun _ _ _ _ _ _ _ => trivial, ?_⟩⟩
  intro m hm t ht hlast c hc
  obtain ⟨xs, oc, h⟩ := chainMethods m hm.1
  exact absurd (chainNet_last h ht hc).2 hlast

end PCP

end FOND
