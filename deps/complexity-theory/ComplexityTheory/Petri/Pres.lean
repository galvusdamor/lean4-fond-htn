import ComplexityTheory.Petri.Rank
/-!
# Decomposition steps decrease the rank and preserve well-formedness

For each decomposition step, every block of every alternative satisfies the invariant `Inv` and
has a smaller rank than the replaced block.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*} [Fintype ι]

/-! ### Sub-components -/

theorem maxTop_sub_le (C : Comp ι) (p : ℕ → Prop) [DecidablePred p] (q : Edge ι → Prop)
    [DecidablePred q] (s t : ℕ) : maxTop (C.sub p q s t) ≤ maxTop C :=
  maxTop_le fun u hu => le_maxTop (List.mem_of_mem_filter hu)

theorem brank_lt_of_maxTop {g b : Block ι} (h : maxTop g.comp < maxTop b.comp) :
    brank g < brank b := by
  unfold brank
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

theorem length_filter_lt {α : Type*} {l : List α} {p : α → Prop} [DecidablePred p] {a : α}
    (ha : a ∈ l) (hp : ¬ p a) : (l.filter p).length < l.length :=
  List.length_filter_lt_length_iff_exists.2 ⟨a, ha, by simpa using hp⟩

/-- Restricting a block to a sub-component (same labels, same boundary). -/
theorem inv_sub {b : Block ι} (hI : Inv b) (p : ℕ → Prop) [DecidablePred p] (q : Edge ι → Prop)
    [DecidablePred q] (hq : ∀ e ∈ b.comp.edges, q e → p e.1 ∧ p e.2.2) (hs : p b.comp.entry)
    (ht : p b.comp.exit) : Inv { b with comp := b.comp.sub p q b.comp.entry b.comp.exit } := by
  obtain ⟨⟨hW, hL, hin, hout⟩, hN⟩ := hI
  refine ⟨⟨wf_sub hW p q _ _ hq ⟨hW.2.1, hs⟩ ⟨hW.2.2, ht⟩, labMono_sub hL p q _ _, hin, hout⟩,
    hN.filter _⟩

/-! ### Pruning -/

theorem prune_pres {b : Block ι} (hI : Inv b) (R : List ℕ) (hent : b.comp.entry ∈ R)
    (hproper : ∃ v ∈ b.comp.nodes, v ∉ R) :
    ∀ A ∈ pruneAlts b (· ∈ R), ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  intro A hA g hg
  unfold pruneAlts at hA
  split_ifs at hA with hex
  · simp only [List.mem_singleton] at hA
    subst hA
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨inv_sub hI _ _ (fun e _ h => h) hent hex, brank_lt (maxTop_sub_le _ _ _ _ _)
      (List.length_filter_le _ _) (List.length_filter_le _ _) (Or.inr (Or.inr (Or.inl ?_)))⟩
    obtain ⟨v, hv, hvR⟩ := hproper
    exact length_filter_lt hv hvR
  · simp at hA

/-! ### Splitting -/

theorem split_pres {b : Block ι} (hI : Inv b) (S : List ℕ) (hent : b.comp.entry ∈ S)
    (hproper : ∃ v ∈ b.comp.nodes, v ∉ S) :
    ∀ A ∈ splitAlts b (· ∈ S), ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  obtain ⟨⟨hW, hL, hin, hout⟩, hN⟩ := hI
  have hWe := (wf_iff.1 hW).1
  intro A hA g hg
  unfold splitAlts at hA
  split_ifs at hA with hex
  · simp only [List.mem_singleton] at hA
    subst hA
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨inv_sub ⟨⟨hW, hL, hin, hout⟩, hN⟩ _ _ (fun e _ h => h) hent hex,
      brank_lt (maxTop_sub_le _ _ _ _ _) (List.length_filter_le _ _) (List.length_filter_le _ _)
      (Or.inr (Or.inr (Or.inl ?_)))⟩
    obtain ⟨v, hv, hvS⟩ := hproper
    exact length_filter_lt hv hvS
  · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hA
    obtain ⟨e, ⟨he, he1, he2⟩, rfl⟩ := hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨⟨⟨wf_sub hW _ _ _ _ (fun e _ h => h) ⟨hW.2.1, hent⟩ ⟨(hWe e he).1, he1⟩,
        labMono_sub hL _ _ _ _, hin, fun j _ => rfl⟩, hN.filter _⟩, brank_lt
        (maxTop_sub_le _ _ _ _ _) (List.length_filter_le _ _) (List.length_filter_le _ _)
        (Or.inr (Or.inl ?_))⟩
      exact length_filter_lt he (by simp [he2])
    · refine ⟨⟨⟨wf_sub hW _ _ _ _ (fun e _ h => h) ⟨(hWe e he).2, he2⟩ ⟨hW.2.2, hex⟩,
        labMono_sub hL _ _ _ _, fun j _ => rfl, hout⟩, hN.filter _⟩, brank_lt
        (maxTop_sub_le _ _ _ _ _) (List.length_filter_le _ _) (List.length_filter_le _ _)
        (Or.inr (Or.inl ?_))⟩
      exact length_filter_lt he (by simp [he1])

/-! ### Bounded edges -/

section Edge

variable {_inst : DecidableEq (Edge ι)} {b : Block ι} {e₀ : Edge ι}

theorem chain_pres (hI : Inv b) (he₀ : e₀ ∈ b.comp.edges) : ∀ (n : ℕ) (pre : ι → ℤ)
    (inp : ι → ℕ∞) (u : ℕ), u ∈ b.comp.nodes → (∀ j, b.comp.lab u j ≠ ⊤ → inp j = b.comp.lab u j) →
    ∀ g ∈ chainFrom b e₀ pre inp u n, Inv g ∧ brank g < brank b := by
  obtain ⟨⟨hW, hL, hin, hout⟩, hN⟩ := hI
  have hWe := (wf_iff.1 hW).1
  have hlt : (b.comp.edges.filter (· ≠ e₀)).length < b.comp.edges.length :=
    length_filter_lt he₀ (by simp)
  intro n
  induction n with
  | zero =>
    intro pre inp u hu hinp g hg
    simp only [chainFrom, List.mem_singleton] at hg
    subst hg
    exact ⟨⟨⟨wf_sub hW _ _ _ _ (fun _ _ _ => ⟨trivial, trivial⟩) ⟨hu, trivial⟩ ⟨hW.2.2, trivial⟩,
      labMono_sub hL _ _ _ _, hinp, hout⟩, hN.filter _⟩, brank_lt (maxTop_sub_le _ _ _ _ _)
      (List.length_filter_le _ _) (List.length_filter_le _ _) (Or.inr (Or.inl hlt))⟩
  | succ n ih =>
    intro pre inp u hu hinp g hg
    simp only [chainFrom, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨⟨⟨wf_sub hW _ _ _ _ (fun _ _ _ => ⟨trivial, trivial⟩) ⟨hu, trivial⟩
        ⟨(hWe e₀ he₀).1, trivial⟩, labMono_sub hL _ _ _ _, hinp, fun j _ => rfl⟩, hN.filter _⟩,
        brank_lt (maxTop_sub_le _ _ _ _ _) (List.length_filter_le _ _)
        (List.length_filter_le _ _) (Or.inr (Or.inl hlt))⟩
    · exact ih _ _ _ (hWe e₀ he₀).2 (fun j _ => rfl) g hg

theorem edge_pres (hI : Inv b) (he₀ : e₀ ∈ b.comp.edges) (B : ℕ) :
    ∀ A ∈ edgeAlts b e₀ B, ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  intro A hA
  simp only [edgeAlts, List.mem_map] at hA
  obtain ⟨n, -, rfl⟩ := hA
  exact chain_pres hI he₀ n _ _ _ hI.1.1.2.1 hI.1.2.2.1

end Edge

/-! ### Bounded input and output coordinates -/

theorem topCount_update_lt [DecidableEq ι] {μ : ι → ℕ∞} {j : ι} (hj : μ j = ⊤) (k : ℕ) :
    topCount (Function.update μ j (k : ℕ∞)) < topCount μ := by
  unfold topCount
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun i hi => ?_).2 ⟨j, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases h : i = j
    · subst h; simp at hi
    · rwa [Function.update_of_ne h] at hi
  · simpa using hj
  · simp

theorem inp_pres {_inst : DecidableEq ι} {b : Block ι} (hI : Inv b) {j : ι} (hj : b.inp j = ⊤) (B : ℕ) :
    ∀ A ∈ inpAlts b j B, ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  obtain ⟨⟨hW, hL, hin, hout⟩, hN⟩ := hI
  intro A hA g hg
  simp only [inpAlts, List.mem_map] at hA
  obtain ⟨k, -, rfl⟩ := hA
  simp only [List.mem_singleton] at hg
  subst hg
  refine ⟨⟨⟨hW, hL, fun j' hj' => ?_, hout⟩, hN⟩, brank_lt le_rfl le_rfl le_rfl
    (Or.inr (Or.inr (Or.inr ?_)))⟩
  · by_cases h : j' = j
    · subst h; exact absurd (hin j' hj') (by rw [hj]; exact fun h => hj' h.symm)
    · simp only [Function.update_of_ne h]; exact hin j' hj'
  · have := topCount_update_lt hj k
    simp only
    omega

theorem out_pres {_inst : DecidableEq ι} {b : Block ι} (hI : Inv b) {j : ι} (hj : b.out j = ⊤) (B : ℕ) :
    ∀ A ∈ outAlts b j B, ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  obtain ⟨⟨hW, hL, hin, hout⟩, hN⟩ := hI
  intro A hA g hg
  simp only [outAlts, List.mem_map] at hA
  obtain ⟨k, -, rfl⟩ := hA
  simp only [List.mem_singleton] at hg
  subst hg
  refine ⟨⟨⟨hW, hL, hin, fun j' hj' => ?_⟩, hN⟩, brank_lt le_rfl le_rfl le_rfl
    (Or.inr (Or.inr (Or.inr ?_)))⟩
  · by_cases h : j' = j
    · subst h; exact absurd (hout j' hj') (by rw [hj]; exact fun h => hj' h.symm)
    · simp only [Function.update_of_ne h]; exact hout j' hj'
  · have := topCount_update_lt hj k
    simp only
    omega

/-! ### Step (d) -/

theorem maxTop_gComp_lt (C : Comp ι) {Ns : List (ℕ × (ι → ℕ∞))} {K : ℕ}
    (hNs : ∀ p ∈ Ns, topCount p.2 < K) (i₀ i₁ : ℕ) (h₀ : i₀ < Ns.length) :
    maxTop (gComp C Ns i₀ i₁) < K := by
  refine maxTop_lt (fun i hi => hNs _ (nd_mem (List.mem_range.1 hi))) ?_
  exact Nat.zero_lt_of_lt (hNs _ (nd_mem h₀))

theorem dAlts_pres {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))} {K : ℕ}
    (hNs : ∀ p ∈ Ns, topCount p.2 < K) :
    ∀ A ∈ dAlts b Ns, ∀ g ∈ A, WFB g ∧ LabOK g.comp ∧ g.comp.edges.Nodup ∧ maxTop g.comp < K ∧
      g.pre = b.pre := by
  intro A hA g hg
  simp only [dAlts, List.mem_map, List.mem_filter, List.mem_flatMap, List.mem_range] at hA
  obtain ⟨⟨i₀, i₁⟩, ⟨⟨a, ha, a', ha', hp⟩, -⟩, rfl⟩ := hA
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  simp only [List.mem_singleton] at hg
  subst hg
  refine ⟨⟨wf_gComp _ _ ha ha', Or.inl (labOK_gComp _ _ _ _), fun j hj => ?_, fun j hj => ?_⟩,
    labOK_gComp _ _ _ _, gEdges_nodup _ _, maxTop_gComp_lt _ hNs _ _ ha, rfl⟩
  · simp only [gComp, impose] at hj ⊢; simp [hj]
  · simp only [gComp, impose] at hj ⊢; simp [hj]

theorem dF_pres {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))}
    (hNs : ∀ p ∈ Ns, topCount p.2 < topCount (b.comp.lab b.comp.entry)) (hI : Inv b) :
    ∀ A ∈ dAlts b Ns, ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  intro A hA g hg
  obtain ⟨h1, -, h3, h4, -⟩ := dAlts_pres hNs A hA g hg
  exact ⟨⟨h1, h3⟩, brank_lt_of_maxTop (h4.trans_le (le_maxTop hI.1.1.2.1))⟩

/-! ### Reversal -/

omit [Fintype ι]

theorem wf_rev {C : Comp ι} (h : WF C) : WF C.rev := by
  rw [wf_iff] at h ⊢
  refine ⟨fun e he => ?_, h.2.2, h.2.1⟩
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  exact ⟨(h.1 e' he').2, (h.1 e' he').1⟩

theorem labOKB_rev {C : Comp ι} (h : LabOK C) : LabOKB C.rev := by
  rw [labOK_iff] at h
  rw [labOKB_iff]
  intro e he j hj
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  obtain ⟨a, b⟩ := h e' he' j hj
  refine ⟨a, ?_⟩
  simp only [Comp.rev, revEdge, Pi.neg_apply] at b ⊢
  linarith

theorem labOK_rev {C : Comp ι} (h : LabOKB C) : LabOK C.rev := by
  rw [labOKB_iff] at h
  rw [labOK_iff]
  intro e he j hj
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  obtain ⟨a, b⟩ := h e' he' j hj
  refine ⟨a, ?_⟩
  simp only [Comp.rev, revEdge, Pi.neg_apply] at b ⊢
  linarith

theorem labMono_rev {C : Comp ι} (h : LabMono C) : LabMono C.rev :=
  h.elim (fun h => Or.inr (labOKB_rev h)) (fun h => Or.inl (labOK_rev h))

theorem wfb_rev {b : Block ι} (h : WFB b) : WFB b.rev :=
  ⟨wf_rev h.1, labMono_rev h.2.1, h.2.2.2, h.2.2.1⟩

theorem sc_rev {C : Comp ι} (hS : SC C) : SC C.rev := by
  intro u hu v hv
  obtain ⟨es, h⟩ := sc_twalk hS hv hu
  obtain ⟨π, hπ, -⟩ := (twalk_revL h).toIdx (C := C.rev)
  exact ⟨π, hπ⟩

theorem pumpB_of_rev {b : Block ι} (h : PumpF b.rev) : PumpB b := by
  obtain ⟨es, hw, hf, hp⟩ := h
  refine ⟨revL es, ?_, ?_, fun j hj hl => ?_⟩
  · have := twalk_revL hw
    simpa [Block.rev, Comp.rev, List.map_map, Function.comp_def] using this
  · have := tfires_revL hf
    rw [teff_revL, sub_neg_eq_add]
    exact this
  · have := hp j hj hl
    rw [teff_revL, Pi.neg_apply]
    linarith

variable [Fintype ι]

theorem dB_pres {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))}
    (hNs : ∀ p ∈ Ns, topCount p.2 < topCount (b.comp.lab b.comp.exit)) (hI : Inv b) :
    ∀ A ∈ dAltsB b Ns, ∀ g ∈ A, Inv g ∧ brank g < brank b := by
  intro A hA g hg
  simp only [dAltsB, List.mem_map] at hA
  obtain ⟨A', hA', rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  obtain ⟨⟨hW, -, hin, hout⟩, hL, hN, hK, -⟩ := dAlts_pres (b := b.rev) hNs A' hA' g' hg'
  refine ⟨⟨⟨wf_rev hW, Or.inr (labOKB_rev hL), hout, hin⟩, hN.map revEdge_injective⟩,
    brank_lt_of_maxTop ?_⟩
  exact hK.trans_le (le_maxTop hI.1.1.2.2)

end KLM

end Petri

end HTN
