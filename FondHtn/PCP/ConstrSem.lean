import FondHtn.PCP.Construction
/-!
# Well-formedness and semantics of the construction
-/

namespace FOND

namespace PCP

open HTN HTN.Syn HTN.Article HTN.Undec

variable {M : TSM} {s₁ s₂ : List ℕ}

/-! ## Alphabet membership -/

theorem stk_mem_chars {a : ℕ} (h : a ∈ syms M s₁ s₂) : Ch.stk a ∈ chars M s₁ s₂ := by
  simp [chars, h]

theorem st_mem_chars {q : ℕ} (h : q ∈ sts M) : Ch.st q ∈ chars M s₁ s₂ := by
  simp [chars, h]

theorem sep_mem_chars : Ch.sep ∈ chars M s₁ s₂ := by simp [chars]

theorem chars_nodup : (chars M s₁ s₂).Nodup := List.nodup_dedup _

theorem mem_letters {ℓ : Letter} : ℓ ∈ letters M s₁ s₂ ↔ ∃ c ∈ chars M s₁ s₂,
    ℓ = (none, some c) ∨ ℓ = (some c, some c) ∨ ℓ = (some c, none) := by
  simp only [letters, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]

theorem letters_nodup : (letters M s₁ s₂).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun c _ => by simp, ?_⟩
  refine (chars_nodup).imp fun {c d} hcd => ?_
  show List.Disjoint _ _
  intro x hx hx'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hx'
  rcases hx with rfl | rfl | rfl <;> rcases hx' with h | h | h <;>
    simp only [Prod.mk.injEq, Option.some.injEq, reduceCtorEq, and_false, false_and] at h <;>
    first | exact hcd h | exact hcd h.symm | exact hcd h.1 | exact hcd h.1.symm | exact hcd h.2 | exact hcd h.2.symm | simp_all

theorem sym_mem_of_c₀ {a : ℕ} (h : a ∈ s₁ ∨ a ∈ s₂) : a ∈ syms M s₁ s₂ := by
  rcases h with h | h <;> simp [syms, h]

theorem pop_mem {t : Tr} (ht : t ∈ M.trans) : t.pop ∈ syms M s₁ s₂ := by
  simp only [syms, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact Or.inr ⟨t, ht, Or.inl rfl⟩

theorem push_mem {t : Tr} (ht : t ∈ M.trans) {a : ℕ} (ha : a ∈ t.push) : a ∈ syms M s₁ s₂ := by
  simp only [syms, List.mem_append, List.mem_flatMap, List.mem_cons]
  exact Or.inr ⟨t, ht, Or.inr ha⟩

theorem src_mem {t : Tr} (ht : t ∈ M.trans) : t.src ∈ sts M := by
  simp only [sts, List.mem_cons, List.mem_flatMap, List.mem_singleton]
  exact Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩)

theorem tgt_mem {t : Tr} (ht : t ∈ M.trans) : t.tgt ∈ sts M := by
  simp only [sts, List.mem_cons, List.mem_flatMap, List.mem_singleton, List.not_mem_nil, or_false]
  exact Or.inr (Or.inr ⟨t, ht, Or.inr rfl⟩)

theorem lhs_chars {t : Tr} (ht : t ∈ M.trans) : ∀ c ∈ lhs t, c ∈ chars M s₁ s₂ := by
  intro c hc
  unfold lhs at hc
  split at hc <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl
  all_goals first | exact stk_mem_chars (pop_mem ht) | exact st_mem_chars (src_mem ht)

theorem rhs_chars {t : Tr} (ht : t ∈ M.trans) : ∀ c ∈ rhs t, c ∈ chars M s₁ s₂ := by
  intro c hc
  unfold rhs at hc
  split at hc
  · simp only [List.mem_append, List.mem_map, List.mem_reverse, List.mem_singleton] at hc
    rcases hc with ⟨a, ha, rfl⟩ | rfl
    · exact stk_mem_chars (push_mem ht ha)
    · exact st_mem_chars (tgt_mem ht)
  · simp only [List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨a, ha, rfl⟩
    · exact st_mem_chars (tgt_mem ht)
    · exact stk_mem_chars (push_mem ht ha)

theorem encC₀_chars : ∀ c ∈ encC (c₀ M s₁ s₂) ++ [Ch.sep], c ∈ chars M s₁ s₂ := by
  intro c hc
  simp only [encC, c₀, List.mem_append, List.mem_map, List.mem_reverse, List.mem_singleton] at hc
  rcases hc with ((⟨a, ha, rfl⟩ | rfl) | ⟨a, ha, rfl⟩) | rfl
  · exact stk_mem_chars (sym_mem_of_c₀ (Or.inl ha))
  · exact st_mem_chars (by simp [sts])
  · exact stk_mem_chars (sym_mem_of_c₀ (Or.inr ha))
  · exact sep_mem_chars

theorem encCf_chars : ∀ c ∈ encC (cf M) ++ [Ch.sep], c ∈ chars M s₁ s₂ := by
  intro c hc
  simp only [encC, cf, List.reverse_nil, List.map_nil, List.nil_append, List.append_nil,
    List.mem_append, List.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact st_mem_chars (by simp [sts])
  · exact sep_mem_chars

/-! ## Names -/

def names (M : TSM) (s₁ s₂ : List ℕ) : List ℕ := (actions M s₁ s₂).map FActDesc.name

theorem names_eq : names M s₁ s₂ = [0, 1, 2, 3, 4] ++ (letters M s₁ s₂).map nA ++
    (letters M s₁ s₂).map nB := by
  simp [names, actions, FActDesc.name, actA, actB, actInit, actFin, actEnd, actCheat, nInit, nFin,
    nEnd, nCheat, Function.comp_def]

theorem names_nodup : (names M s₁ s₂).Nodup := by
  rw [names_eq]
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨by decide, letters_nodup.map nA_inj, ?_⟩,
    letters_nodup.map nB_inj, ?_⟩
  · intro a ha b hb hab
    subst hab
    obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hb
    have := five_le_nA ℓ
    simp at ha; omega
  · intro a ha b hb hab
    subst hab
    obtain ⟨ℓ, -, rfl⟩ := List.mem_map.1 hb
    rcases List.mem_append.1 ha with ha | ha
    · have := five_le_nB ℓ; simp at ha; omega
    · obtain ⟨ℓ', -, h⟩ := List.mem_map.1 ha
      exact nA_ne_nB _ _ h

theorem nA_declared {ℓ : Letter} (h : ℓ ∈ letters M s₁ s₂) : nA ℓ ∈ names M s₁ s₂ := by
  rw [names_eq]; simp [List.mem_map_of_mem h]

theorem nB_declared {ℓ : Letter} (h : ℓ ∈ letters M s₁ s₂) : nB ℓ ∈ names M s₁ s₂ := by
  rw [names_eq]; simp [List.mem_map_of_mem h]

theorem small_declared {n : ℕ} (h : n < 5) : n ∈ names M s₁ s₂ := by
  rw [names_eq]; simp; omega

theorem triples_declared {q : ℕ × List ℕ × Option ℕ} (hq : q ∈ triples M s₁ s₂) :
    ∀ x ∈ q.2.1, x ∈ names M s₁ s₂ := by
  have hA2 : ∀ c ∈ encC (c₀ M s₁ s₂) ++ [Ch.sep], nA (none, some c) ∈ names M s₁ s₂ :=
    fun c hc => nA_declared (mem_letters.2 ⟨c, encC₀_chars c hc, Or.inl rfl⟩)
  have hA1 : ∀ c ∈ encC (cf M) ++ [Ch.sep], nA (some c, none) ∈ names M s₁ s₂ :=
    fun c hc => nA_declared (mem_letters.2 ⟨c, encCf_chars c hc, Or.inr (Or.inr rfl)⟩)
  have hrule : ∀ t ∈ M.trans, ∀ x ∈ ruleW t, x ∈ names M s₁ s₂ := by
    intro t ht x hx
    simp only [ruleW, only1, only2, List.map_append, List.map_map, List.mem_append, List.mem_map,
      Function.comp] at hx
    rcases hx with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · exact nB_declared (mem_letters.2 ⟨c, rhs_chars ht c hc, Or.inr (Or.inr rfl)⟩)
    · exact nB_declared (mem_letters.2 ⟨c, lhs_chars ht c hc, Or.inl rfl⟩)
  have hsym : ∀ a ∈ syms M s₁ s₂, symB a ∈ names M s₁ s₂ := fun a ha =>
    nB_declared (mem_letters.2 ⟨_, stk_mem_chars ha, Or.inr (Or.inl rfl)⟩)
  simp only [triples, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil,
    or_false] at hq
  have hmem : ∀ {c : Ch} {l : List Ch}, c ∈ l ∨ c = Ch.sep → c ∈ l ++ [Ch.sep] := by
    intro c l h
    rcases h with h | rfl
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_singleton_self _)
  rcases hq with ((((((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨c, hc, rfl⟩) |
    ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · intro x hx
    simp only [List.mem_cons, only2, List.map_map, List.mem_map, Function.comp] at hx
    rcases hx with rfl | ⟨c, hc, rfl⟩
    · exact small_declared (by decide)
    · exact hA2 c (hmem (by simpa using hc))
  · intro x hx
    simp only [only1, List.map_map, List.mem_append, List.mem_map, Function.comp,
      List.mem_singleton] at hx
    rcases hx with ⟨c, hc, rfl⟩ | rfl
    · exact hA1 c (hmem (by simpa using hc))
    · exact small_declared (by decide)
  all_goals first
    | exact hrule t ht
    | (intro x hx; exact absurd hx (List.not_mem_nil))
    | (intro x hx
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
       subst hx
       first
         | exact small_declared (by decide)
         | exact hsym _ ha
         | exact nA_declared (mem_letters.2 ⟨c, hc, Or.inr (Or.inl rfl)⟩)
         | exact nB_declared (mem_letters.2 ⟨_, sep_mem_chars, Or.inr (Or.inl rfl)⟩))

/-! ## Validity -/

theorem desc_valid : (desc M s₁ s₂).Valid where
  names_nodup := names_nodup
  effs_ne a ha := by
    simp only [desc, FProbDesc.actions, actions, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at ha
    rcases ha with ((rfl | rfl | rfl | rfl | rfl) | ⟨ℓ, -, rfl⟩) | ⟨ℓ, -, rfl⟩ <;>
      simp [FActDesc.effs, actInit, actFin, actEnd, actCheat, actA, actB]
  tnI := by
    show TnValid _ tnI
    exact ⟨by decide, by simp [tnI, TnDesc.ordList], by simp [tnI, TnDesc.ordList],
      by simp [tnI, TnDesc.ordList], by simp [tnI, TnDesc.lbl, TnDesc.ids],
      by simp [tnI, TnDesc.lbl]⟩
  methods e he := by
    simp only [desc, FProbDesc.methods, methods, List.mem_map] at he
    obtain ⟨q, hq, rfl⟩ := he
    exact chainTn_valid _ fun x hx => triples_declared hq x hx

/-! ## Semantic facts -/

/-- The problem. -/
abbrev Pb (M : TSM) (s₁ s₂ : List ℕ) := (desc M s₁ s₂).toProblem

theorem chainMethods : ChainMethods (Pb M s₁ s₂) := by
  rintro m ⟨e, he, rfl⟩
  simp only [desc, FProbDesc.methods, methods, List.mem_map] at he
  obtain ⟨q, -, rfl⟩ := he
  exact ⟨_, _, chainTn_isChainNet q.2.1 q.2.2⟩

theorem methods_wf : ∀ m ∈ (Pb M s₁ s₂).methods, m.subtasks.WF := by
  rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _

theorem mstep_iff {c : ℕ} {xs : List ℕ} {oc : Option ℕ} :
    MStep (Pb M s₁ s₂) c xs oc ↔ (c, xs, oc) ∈ triples M s₁ s₂ := by
  constructor
  · rintro ⟨m, ⟨e, he, rfl⟩, hc, hm⟩
    simp only [desc, FProbDesc.methods, methods, List.mem_map] at he
    obtain ⟨q, hq, rfl⟩ := he
    obtain ⟨h1, h2⟩ := (chainTn_isChainNet q.2.1 q.2.2).unique hm
    subst h1 h2
    simpa [← hc, MethodDesc.toMethod] using hq
  · intro h
    exact ⟨_, ⟨(c, chainTn xs oc), by simp [desc, FProbDesc.methods, methods]; exact ⟨_, _, h, rfl⟩,
      rfl⟩, rfl, chainTn_isChainNet xs oc⟩

theorem isRoots : IsRoots (Pb M s₁ s₂).tnI 4 root where
  T := by ext x; simp [desc, FProbDesc.toProblem, FProbDesc.tnI, tnI, TnDesc.toTaskNetwork,
    TnDesc.ids]; omega
  ord x y h := by
    have := (show (desc M s₁ s₂).tnI.toTaskNetwork.ord x y from h).2.2.1
    simp only [desc, FProbDesc.tnI, tnI, TnDesc.preOrd] at this
    obtain ⟨_, h'⟩ | _ := this <;> simp_all [TnDesc.listRel, TnDesc.ordList]
  lab i hi := by
    show (tnI).label i = _
    interval_cases i <;> rfl

theorem init_eq : (Pb M s₁ s₂).init = ∅ := by
  ext; simp [desc, FProbDesc.toProblem, FProbDesc.init]

theorem δ_eq {a : FActDesc} (ha : a ∈ actions M s₁ s₂) : (Pb M s₁ s₂).δ a.name = a.toAction :=
  FProbDesc.δ_of_mem desc_valid ha

end PCP

end FOND
