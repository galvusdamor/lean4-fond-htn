import HtnComplexity.HDDecide.Net
/-!
# The encoding of the search on pieces: list lemmas
-/

namespace HTN

namespace HD

open Syn Syn.ToDec Petri

variable {d : DomDesc} {q : InstDesc}

theorem mem_of_mem_subsets : ∀ {U l : List ℕ}, l ∈ subsets U → ∀ x ∈ l, x ∈ U := by
  intro U
  induction U with
  | nil => intro l hl x hx; simp [subsets] at hl; simp [hl] at hx
  | cons f U ih =>
    intro l hl x hx
    simp only [subsets, List.mem_append, List.mem_map] at hl
    rcases hl with hl | ⟨l', hl', rfl⟩
    · exact List.mem_cons_of_mem _ (ih hl x hx)
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hl' x hx)

theorem mem_stL {s : Finset ℕ} {f : ℕ} : f ∈ stL d q s ↔ f ∈ allFacts d q ∧ f ∈ s := by
  simp [stL]

theorem toFinset_stL {s : Finset ℕ} (hs : s ⊆ facts d q) : (stL d q s).toFinset = s := by
  ext f
  rw [List.mem_toFinset, mem_stL]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.1 (hs h), h⟩⟩

theorem stL_inj {s t : Finset ℕ} (hs : s ⊆ facts d q) (ht : t ⊆ facts d q)
    (h : stL d q s = stL d q t) : s = t := by
  rw [← toFinset_stL hs, ← toFinset_stL ht, h]

theorem stL_mem_subsets (s : Finset ℕ) : stL d q s ∈ subsets (allFacts d q) :=
  mem_subsets_filter _ _

theorem nrmF_eq (l : List ℕ) : nrmF d q l = stL d q l.toFinset := by
  simp only [nrmF, stL]
  congr 1
  funext f
  rw [Bool.eq_iff_iff]
  simp

theorem toFinset_subset_facts {l : List ℕ} (hl : l ∈ subsets (allFacts d q)) :
    l.toFinset ⊆ facts d q := by
  intro f hf
  exact List.mem_toFinset.2 (mem_of_mem_subsets hl f (List.mem_toFinset.1 hf))

theorem toFinset_stepL' (l : List ℕ) (a : ℕ) : (stepL d l a).toFinset = nxtF d l.toFinset a := by
  ext f
  simp [stepL, nxtF]

theorem applB_iff_appF {l : List ℕ} {a : ℕ} : applB d l a = true ↔ appF d l.toFinset a := by
  rw [applB_iff]
  simp only [ActionModel.Applicable, DomDesc.toDomain_prec, prec_eq_actOf, appF]
  simp [Set.subset_def]

theorem nrmF_stepL (l : List ℕ) (a : ℕ) : nrmF d q (stepL d l a) = stL d q (nxtF d l.toFinset a) := by
  rw [nrmF_eq, toFinset_stepL']

/-! ### Items -/

theorem mem_pcL {p : Piece} {x : ℕ} : x ∈ (pcL d q p).2 ↔ x ∈ (net d q p.1).ids ∧ x ∈ p.2 := by
  simp [pcL]

theorem pcL_mem_allToks {p : Piece} (hp : p.1 < d.methods.length + 1) : pcL d q p ∈ allToks d q := by
  simp only [allToks, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨p.1, hp, _, mem_subsets_filter _ _, rfl⟩

theorem filter_pcL_erase (k : ℕ) (S : Finset ℕ) (x : ℕ) :
    (pcL d q (k, S)).2.filter (fun y => y != x) = (pcL d q (k, S.erase x)).2 := by
  simp only [pcL, List.filter_filter]
  congr 1
  funext y
  rw [Bool.eq_iff_iff]
  simp

theorem coe_tokOf (k : ℕ) (S : Finset ℕ) (hS : S ⊆ (net d q k).ids.toFinset) :
    (tokOf k (pcL d q (k, S)).2 : Multiset Tok) = (piece k S).map (pcL d q) := by
  by_cases h : S = ∅
  · subst h
    simp [tokOf, piece, pcL]
  · have hne : (pcL d q (k, S)).2 ≠ [] := by
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 h
      intro he
      have : x ∈ (pcL d q (k, S)).2 := mem_pcL.2 ⟨List.mem_toFinset.1 (hS hx), hx⟩
      rw [he] at this
      simp at this
    have he : (pcL d q (k, S)).2.isEmpty = false := by simpa [List.isEmpty_iff] using hne
    rw [tokOf, he]
    simp [piece, h]
    rfl

theorem pcL_full (k : ℕ) : pcL d q (k, (net d q k).ids.toFinset) = (k, (net d q k).ids) := by
  simp [pcL]

/-! ### Labels -/

theorem lblPair_eq_inl {t : TnDesc} {x a : ℕ} :
    t.lblPair x = (false, a) ↔ t.label x = Sum.inl a := by
  rw [← TnDesc.ofPair_lblPair, TnDesc.ofPair_eq_inl_iff]

theorem lblPair_eq_inr {t : TnDesc} {x c : ℕ} :
    t.lblPair x = (true, c) ↔ t.label x = Sum.inr c := by
  rw [← TnDesc.ofPair_lblPair, TnDesc.ofPair_eq_inr_iff]

theorem ordB_iff_ordK {k x y : ℕ} : TnDesc.ordB (net d q k) x y = true ↔ ordK d q k x y :=
  TnDesc.ordB_iff

/-! ### Rules -/

theorem mem_cond_nil {α : Type*} {b : Bool} {r r0 : α} :
    r ∈ (bif b then [r0] else []) ↔ b = true ∧ r = r0 := by
  cases b <;> simp

theorem mem_hdRules {r : HRule} : r ∈ hdRules d q ↔
    (∃ s ∈ subsets (allFacts d q), q.goalList.all (memB s) = true ∧
      r = (startC, none, (1, nrmF d q q.initList, nrmF d q s), [])) ∨
    (∃ lf ∈ subsets (allFacts d q), ∃ lb ∈ subsets (allFacts d q), ∃ p ∈ allToks d q, ∃ x ∈ p.2,
      r ∈ progR d q lf lb p.1 p.2 x ∨ r ∈ regrR d q lf lb p.1 p.2 x ∨ r ∈ decR d q lf lb p.1 p.2 x) ∨
    (∃ l ∈ subsets (allFacts d q), r = ((1, l, l), none, doneC, [])) := by
  simp only [hdRules, startRules, stepRules, endRules, List.mem_append, List.mem_flatMap,
    mem_cond_nil, List.mem_map, or_assoc]
  constructor
  · rintro (⟨s, hs, h1, h2⟩ | h | ⟨l, hl, h⟩)
    · exact Or.inl ⟨s, hs, h1, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l, hl, h.symm⟩)
  · rintro (⟨s, hs, h1, h2⟩ | h | ⟨l, hl, h⟩)
    · exact Or.inl ⟨s, hs, h1, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨l, hl, h.symm⟩)

theorem map_sub_singleton {M : Multiset Piece} {p : Piece} (hp : p ∈ M) :
    M.map (pcL d q) - (([pcL d q p] : List Tok) : Multiset Tok) = (M.erase p).map (pcL d q) := by
  rw [Multiset.map_erase_of_mem _ _ hp]
  simp [Multiset.sub_singleton]

end HD

end HTN
