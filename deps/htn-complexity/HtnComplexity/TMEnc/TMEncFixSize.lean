import HtnComplexity.TMEnc.TMEncFix
import HtnComplexity.TMEnc.TMEncodingFinset
import HtnComplexity.TMEnc.EncodingSize
/-!
# The size of the repaired encoding

The repaired construction of `HtnComplexity/TMEnc/TMEncFix.lean` replaces one method body by a
shorter one, so all of the size bounds of `HtnComplexity/TMEnc/TMEncodingFinset.lean` hold for it
unchanged:

* `HTN.TMEnc.sizeOn_leFix` — at most `421` per method on any fragment;
* `HTN.TMEnc.sizeOn_fullFragment_leFix`, `HTN.TMEnc.sizeOn_fullFragment_le_logFix` — the same
  closed-form polynomial bound `HTN.TMEnc.sizeBound` as for the printed construction, with the
  number of counting tasks logarithmic in the time bound `K`.  This is the size claim of
  Theorem 4.3.7 for the repaired translation.
-/

namespace HTN

namespace TMEnc

open scoped Classical

open TM

variable {Q Γ : Type}

/-- **The size of the repaired domain on a fragment**: at most `421` per method, independently
of the time bound `K`. -/
theorem sizeOn_leFix (N : NTM Q Γ) (w : List Γ) (K : ℕ)
    (fr : Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ))
    (hfr : ∀ m ∈ fr.methods, m ∈ methodsFix N w K) :
    (domainFix N w K).sizeOn fr ≤ fr.facts.card + fr.tasks.card +
      (∑ a ∈ fr.ops, (domainFix N w K).actionSize a) + 421 * fr.methods.card :=
  Domain.sizeOn_le_of_method_size_le _ _ fun m hm => method_size_leFix (hfr m hm)

section Bodies

variable (N : NTM Q Γ) (qs : Finset Q) (gs : Finset Γ) (w : List Γ) (K : ℕ)

/-- The bodies of one compound task of the repaired domain, as a `Finset`. -/
noncomputable def bodyFinsetFix :
    TMTask Q Γ → Finset (List (List (TMAct Q Γ ⊕ TMTask Q Γ)))
  | .checkers i =>
      if i = 1 then {checkerBodyFix K} else bodyFinset N qs gs w K (TMTask.checkers i)
  | t => bodyFinset N qs gs w K t

variable {N qs gs w K}

@[simp] lemma bodyFinsetFix_checkers (i : ℕ) :
    bodyFinsetFix N qs gs w K (TMTask.checkers i) =
      if i = 1 then {checkerBodyFix K} else bodyFinset N qs gs w K (TMTask.checkers i) := rfl

lemma bodyFinsetFix_checkers_one :
    bodyFinsetFix N qs gs w K (TMTask.checkers 1) =
      {checkerBodyFix (Q := Q) (Γ := Γ) K} := by simp

lemma bodyFinsetFix_eq_of_ne {t : TMTask Q Γ} (h : t ≠ TMTask.checkers 1) :
    bodyFinsetFix N qs gs w K t = bodyFinset N qs gs w K t := by
  cases t with
  | checkers i =>
      have hi : i ≠ 1 := by simpa using h
      simp [hi]
  | _ => rfl

/-- Every element of `HTN.TMEnc.bodyFinsetFix` really is a method body of the repaired
domain. -/
lemma bodyFinsetFix_subset_bodiesFix (t : TMTask Q Γ) :
    ↑(bodyFinsetFix N qs gs w K t) ⊆ bodiesFix N w K t := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodyFinsetFix_checkers_one, bodiesFix_checkers_one]
    intro ls hls
    simpa using hls
  · rw [bodyFinsetFix_eq_of_ne ht1, bodiesFix_eq_of_ne ht1]
    exact bodyFinset_subset_bodies t

/-- If the machine's states and symbols are covered, `HTN.TMEnc.bodyFinsetFix` contains *all*
method bodies of the repaired domain. -/
lemma bodiesFix_subset_bodyFinsetFix (hqs : ∀ q : Q, q ∈ qs) (hgs : ∀ c : Γ, c ∈ gs)
    (t : TMTask Q Γ) : bodiesFix N w K t ⊆ ↑(bodyFinsetFix N qs gs w K t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodyFinsetFix_checkers_one, bodiesFix_checkers_one]
    intro ls hls
    simpa using hls
  · rw [bodyFinsetFix_eq_of_ne ht1, bodiesFix_eq_of_ne ht1]
    exact bodies_subset_bodyFinset hqs hgs t

/-- Every compound task of the repaired domain has at most `B` bodies, with the same `B` as for
the printed construction. -/
lemma card_bodyFinsetFix_le (t : TMTask Q Γ) :
    (bodyFinsetFix N qs gs w K t).card ≤
      (gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2 := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodyFinsetFix_checkers_one]
    simp only [Finset.card_singleton]
    omega
  · rw [bodyFinsetFix_eq_of_ne ht1]
    exact card_bodyFinset_le t

end Bodies

section Fragment

variable (N : NTM Q Γ) (qs : Finset Q) (gs : Finset Γ) (w : List Γ) (K : ℕ)

/-- The methods of the repaired domain that the construction uses. -/
noncomputable def methodFinsetFix : Finset (Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)) :=
  ((taskFinset N w K).biUnion fun t =>
    (bodyFinsetFix N qs gs w K t).image fun ls => ⟨t, TaskNetwork.grid ls⟩) ∪
  {⟨TMTask.sI, initNetFix K⟩}

/-- The fragment of the signature that the repaired construction uses. -/
noncomputable def fragmentFix : Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  facts := factFinset qs gs
  ops := opFinset qs gs
  tasks := taskFinset N w K
  methods := methodFinsetFix N qs gs w K

variable {N qs gs w K}

/-- **The methods of the fragment really are methods of the repaired domain.** -/
lemma methodFinsetFix_subset_methodsFix :
    ↑(methodFinsetFix N qs gs w K) ⊆ methodsFix N w K := by
  intro m hm
  simp only [Finset.mem_coe, methodFinsetFix, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_singleton] at hm
  rcases hm with ⟨t, -, ls, hls, rfl⟩ | rfl
  · exact Or.inl ⟨ls, bodyFinsetFix_subset_bodiesFix t hls, rfl⟩
  · exact Or.inr rfl

/-- **Conversely, if the machine is covered, every method of the repaired domain whose decomposed
task is used belongs to the fragment.** -/
lemma mem_methodFinsetFix_of_mem_methodsFix (hqs : ∀ q : Q, q ∈ qs) (hgs : ∀ c : Γ, c ∈ gs)
    {m : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)} (hm : m ∈ methodsFix N w K)
    (ht : m.abstractTask ∈ taskFinset N w K) : m ∈ methodFinsetFix N qs gs w K := by
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · refine Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨m.abstractTask, ht, ?_⟩)
    refine Finset.mem_image.2 ⟨ls, bodiesFix_subset_bodyFinsetFix hqs hgs _ hls, ?_⟩
    cases m
    simpa using hsub.symm
  · simp only [Set.mem_singleton_iff] at hsI
    exact Finset.mem_union_right _ (Finset.mem_singleton.2 hsI)

/-- The number of methods the repaired construction uses. -/
lemma card_methodFinsetFix_le :
    (methodFinsetFix N qs gs w K).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2) + 1 := by
  set B := (gs.card + 1) + qs.card * (gs.card * (qs.card * (gs.card * 3))) + qs.card + 2 with hB
  have hbi : ((taskFinset N w K).biUnion fun t =>
      (bodyFinsetFix N qs gs w K t).image fun ls =>
        (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ))).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) * B := by
    calc ((taskFinset N w K).biUnion fun t =>
          (bodyFinsetFix N qs gs w K t).image fun ls =>
            (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ)
              (TMTask Q Γ))).card
        ≤ ∑ t ∈ taskFinset N w K, ((bodyFinsetFix N qs gs w K t).image fun ls =>
            (⟨t, TaskNetwork.grid ls⟩ : Method (ℕ × ℕ) (TMAct Q Γ)
              (TMTask Q Γ))).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ taskFinset N w K, B :=
          Finset.sum_le_sum fun t _ => le_trans Finset.card_image_le (card_bodyFinsetFix_le t)
      _ = (taskFinset N w K).card * B := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) * B :=
          Nat.mul_le_mul_right _ (card_taskFinset_le N w K)
  refine le_trans (Finset.card_union_le _ _) ?_
  simpa using Nat.add_le_add hbi (le_refl 1)

end Fragment

section Size

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-- The fragment of the repaired signature for the whole (finite) machine. -/
noncomputable def fullFragmentFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Fragment (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) :=
  fragmentFix N Finset.univ Finset.univ w K

omit [Fintype Q] in
lemma actionSize_leFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) (a : TMAct Q Γ) :
    (domainFix N w K).actionSize a ≤ Nat.card Γ + 9 := actionSize_le N w K a

/-- **Closed-form polynomial size bound for the repaired encoding**: the same bound
`HTN.TMEnc.sizeBound` as for the printed construction. -/
theorem sizeOn_fullFragment_leFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (domainFix N w K).sizeOn (fullFragmentFix N w K) ≤
      sizeBound (Nat.card Q) (Nat.card Γ) w.length (countFinset K w.length).card := by
  have hcardQ : (Finset.univ : Finset Q).card = Nat.card Q := by simp [Nat.card_eq_fintype_card]
  have hcardG : (Finset.univ : Finset Γ).card = Nat.card Γ := by simp [Nat.card_eq_fintype_card]
  have hfacts : (factFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ).card ≤
      Nat.card Γ + Nat.card Q + 9 := by
    have := card_factFinset_le (Q := Q) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ))
    rwa [hcardQ, hcardG] at this
  have htasks : (taskFinset N w K).card ≤ 25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card :=
    card_taskFinset_le N w K
  have hops : (opFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ).card ≤
      (Nat.card Γ + 1) + (Nat.card Γ + Nat.card Q + 9) + 12 + 2 +
        Nat.card Q * ((Nat.card Γ + 1) * (Nat.card Q * (Nat.card Γ + 1))) := by
    have := card_opFinset_le (Q := Q) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ))
    rwa [hcardQ, hcardG] at this
  have hmeth : (methodFinsetFix N Finset.univ Finset.univ w K).card ≤
      (25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((Nat.card Γ + 1) + Nat.card Q * (Nat.card Γ * (Nat.card Q * (Nat.card Γ * 3))) +
          Nat.card Q + 2) + 1 := by
    have := card_methodFinsetFix_le (N := N) (qs := (Finset.univ : Finset Q))
      (gs := (Finset.univ : Finset Γ)) (w := w) (K := K)
    rwa [hcardQ, hcardG] at this
  have hsumops : ∑ a ∈ opFinset (Q := Q) (Γ := Γ) Finset.univ Finset.univ,
      (domainFix N w K).actionSize a ≤
      ((Nat.card Γ + 1) + (Nat.card Γ + Nat.card Q + 9) + 12 + 2 +
        Nat.card Q * ((Nat.card Γ + 1) * (Nat.card Q * (Nat.card Γ + 1)))) *
        (Nat.card Γ + 9) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun a _ => actionSize_leFix N w K a)) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _ hops
  have hsummeth : ∑ m ∈ methodFinsetFix N Finset.univ Finset.univ w K, m.size ≤
      421 * ((25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card) *
        ((Nat.card Γ + 1) + Nat.card Q * (Nat.card Γ * (Nat.card Q * (Nat.card Γ * 3))) +
          Nat.card Q + 2) + 1) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 421 (fun m hm => method_size_leFix
      (methodFinsetFix_subset_methodsFix (Finset.mem_coe.2 hm)))) ?_
    rw [smul_eq_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hmeth
  simp only [Domain.sizeOn, fullFragmentFix, fragmentFix, sizeBound]
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfacts htasks) hsumops) hsummeth

/-- The same bound with the number of counting tasks replaced by its logarithmic estimate. -/
theorem sizeOn_fullFragment_le_logFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (domainFix N w K).sizeOn (fullFragmentFix N w K) ≤
      sizeBound (Nat.card Q) (Nat.card Γ) w.length
        ((2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
          (2 * Nat.log 2 (K - w.length) + 2)) := by
  refine le_trans (sizeOn_fullFragment_leFix N w K) ?_
  have hL := card_countFinset_le K w.length
  unfold sizeBound
  set L := (2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
    (2 * Nat.log 2 (K - w.length) + 2) with hLdef
  have h1 : 25 + 2 * w.length + 13 * (countFinset K w.length).card +
        (countFinset K w.length).card * (countFinset K w.length).card ≤
      25 + 2 * w.length + 13 * L + L * L := by
    have hsq : (countFinset K w.length).card * (countFinset K w.length).card ≤ L * L :=
      Nat.mul_le_mul hL hL
    omega
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl h1) le_rfl)
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_right _ h1) le_rfl))

end Size

end TMEnc

end HTN
