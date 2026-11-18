import HtnPlanning.Progression.Progression
import HtnPlanning.Core.DecompositionIso
/-!
# Commuting decomposition steps

Two decomposition steps that are applied to *different* tasks commute: decomposing `t` and then
`t'` gives literally the same task network as decomposing `t'` and then `t`
(`HTN.decomposeWith_comm`).  Likewise, progressing a task commutes with decomposing another one
(`HTN.progress_decomposeWith_comm`).

These are the combinatorial facts behind the completeness proof of progression search: a
decomposition sequence may be reordered so that the task the search wants to decompose next is
decomposed first (`HTN.DecomposesToN.pull_out`).

To be able to argue by induction on the *length* of a decomposition sequence we also introduce
the counted version `HTN.DecomposesToN` of `HTN.DecomposesTo`.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

section Commute

variable [DecidableEq I]

/-- The ordering relation of a task network obtained by decomposing two different tasks `t`,
`t'` of `tn` with the fresh networks `u`, `u'`.  It is visibly symmetric in `(t, u)` and
`(t', u')`, which is what makes the two decomposition steps commute. -/
def ordTwo (tn u u' : TaskNetwork I A C) (t t' a b : I) : Prop :=
  u.ord a b ∨ u'.ord a b ∨
  (tn.ord a t ∧ b ∈ u.T ∧ a ≠ t') ∨
  (tn.ord t b ∧ a ∈ u.T ∧ b ≠ t') ∨
  (tn.ord a t' ∧ b ∈ u'.T ∧ a ≠ t) ∨
  (tn.ord t' b ∧ a ∈ u'.T ∧ b ≠ t) ∨
  (tn.ord t t' ∧ a ∈ u.T ∧ b ∈ u'.T) ∨
  (tn.ord t' t ∧ a ∈ u'.T ∧ b ∈ u.T) ∨
  (tn.ord a b ∧ a ≠ t ∧ b ≠ t ∧ a ≠ t' ∧ b ≠ t')

omit [DecidableEq I] in
lemma ordTwo_symm {tn u u' : TaskNetwork I A C} {t t' a b : I} :
    ordTwo tn u u' t t' a b ↔ ordTwo tn u' u t' t a b := by
  constructor <;>
  · rintro (h | h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))))
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h1, h4, h5, h2, h3⟩)))))))

/-- The explicit description of the ordering after two decomposition steps. -/
lemma ord_decomposeWith_two {tn u u' : TaskNetwork I A C} {t t' a b : I}
    (hu : u.WF) (hne : t ≠ t')
    (ht' : t' ∈ tn.T) (hdu : Disjoint tn.T u.T) (hdu' : Disjoint tn.T u'.T) :
    (decomposeWith (decomposeWith tn t u) t' u').ord a b ↔ ordTwo tn u u' t t' a b := by
  have hun : ∀ x, x ∈ u.T → x ∉ tn.T := fun x hx hc => (Finset.disjoint_left.1 hdu hc) hx
  have hu'n : ∀ x, x ∈ u'.T → x ∉ tn.T := fun x hx hc => (Finset.disjoint_left.1 hdu' hc) hx
  have ht'u : t' ∉ u.T := fun hc => hun t' hc ht'
  have hne' : t' ≠ t := fun h => hne h.symm
  constructor
  · rintro (h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, ha, hb⟩)
    · exact Or.inr (Or.inl h)
    · rcases h with h | ⟨-, hmem⟩ | ⟨h, ha⟩ | ⟨h, hat, -⟩
      · exact absurd (hu.mem_right h) ht'u
      · exact absurd hmem ht'u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ha, hb⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hb, hat⟩))))
    · rcases h with h | ⟨h, hmem⟩ | ⟨-, hmem⟩ | ⟨h, -, hbt⟩
      · exact absurd (hu.mem_left h) ht'u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ha, hmem⟩)))))))
      · exact absurd hmem ht'u
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, ha, hbt⟩)))))
    · rcases h with h | ⟨h, hmem⟩ | ⟨h, hmem⟩ | ⟨h, hat, hbt⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl ⟨h, hmem, ha⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hmem, hb⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨h, hat, hbt, ha, hb⟩)))))))
  · have hune : ∀ x, x ∈ u.T → x ≠ t' := fun x hx => by rintro rfl; exact ht'u hx
    have hu'ne : ∀ x, x ∈ u'.T → x ≠ t' := fun x hx => by
      rintro rfl; exact hu'n x hx ht'
    rintro (h | h | ⟨h, hmem, hat⟩ | ⟨h, hmem, hbt⟩ | ⟨h, hmem, hat⟩ | ⟨h, hmem, hbt⟩ |
      ⟨h, ha, hb⟩ | ⟨h, ha, hb⟩ | ⟨h, hat, hbt, hat', hbt'⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inl h, hune a (hu.mem_left h), hune b (hu.mem_right h)⟩))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl ⟨h, hmem⟩), hat, hune b hmem⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inl ⟨h, hmem⟩)), hune a hmem, hbt⟩))
    · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨h, hat, hne'⟩)), hmem⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr ⟨h, hne', hbt⟩)), hmem⟩))
    · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl ⟨h, ha⟩)), hb⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl ⟨h, hb⟩), ha⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr (Or.inr ⟨h, hat, hbt⟩)), hat', hbt'⟩))

/-- **Decomposing two distinct tasks commutes.** -/
theorem decomposeWith_comm {tn u u' : TaskNetwork I A C} {t t' : I}
    (hu : u.WF) (hu' : u'.WF) (hne : t ≠ t')
    (ht : t ∈ tn.T) (ht' : t' ∈ tn.T)
    (hdu : Disjoint tn.T u.T) (hdu' : Disjoint tn.T u'.T) (huu' : Disjoint u.T u'.T) :
    decomposeWith (decomposeWith tn t u) t' u' = decomposeWith (decomposeWith tn t' u') t u := by
  have hun : ∀ x, x ∈ u.T → x ∉ tn.T := fun x hx hc => (Finset.disjoint_left.1 hdu hc) hx
  have hu'n : ∀ x, x ∈ u'.T → x ∉ tn.T := fun x hx hc => (Finset.disjoint_left.1 hdu' hc) hx
  have huu'2 : ∀ x, x ∈ u.T → x ∉ u'.T := fun x hx => Finset.disjoint_left.1 huu' hx
  have htu' : t ∉ u'.T := fun hc => hu'n t hc ht
  have ht'u : t' ∉ u.T := fun hc => hun t' hc ht'
  have hT : (decomposeWith (decomposeWith tn t u) t' u').T
      = (decomposeWith (decomposeWith tn t' u') t u).T := by
    show ((tn.T.erase t ∪ u.T).erase t' ∪ u'.T) = ((tn.T.erase t' ∪ u'.T).erase t ∪ u.T)
    ext x
    have h1 : x ∈ u.T → x ≠ t' := fun hx => by rintro rfl; exact ht'u hx
    have h2 : x ∈ u'.T → x ≠ t := fun hx => by rintro rfl; exact htu' hx
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto
  have hord : (decomposeWith (decomposeWith tn t u) t' u').ord
      = (decomposeWith (decomposeWith tn t' u') t u).ord := by
    funext a b
    apply propext
    rw [ord_decomposeWith_two hu hne ht' hdu hdu',
      ord_decomposeWith_two hu' (fun h => hne h.symm) ht hdu' hdu, ordTwo_symm]
  have hα : (decomposeWith (decomposeWith tn t u) t' u').α
      = (decomposeWith (decomposeWith tn t' u') t u).α := by
    funext x
    by_cases hx : x ∈ u.T
    · have hxu' : x ∉ u'.T := huu'2 x hx
      simp [decomposeWith, hx, hxu']
    · by_cases hx' : x ∈ u'.T
      · simp [decomposeWith, hx, hx']
      · simp [decomposeWith, hx, hx']
  exact TaskNetwork.ext' hT hord hα

/-- **Progressing a task commutes with decomposing another one.** -/
theorem progress_decomposeWith_comm {tn u : TaskNetwork I A C} {t t₁ : I}
    (hu : u.WF) (hne : t₁ ≠ t) (ht₁u : t₁ ∉ u.T) :
    (decomposeWith tn t u).progress t₁ = decomposeWith (tn.progress t₁) t u := by
  have hT : ((decomposeWith tn t u).progress t₁).T
      = (decomposeWith (tn.progress t₁) t u).T := by
    show (tn.T.erase t ∪ u.T).erase t₁ = ((tn.T.erase t₁).erase t ∪ u.T)
    ext x
    have h1 : x ∈ u.T → x ≠ t₁ := fun hx => by rintro rfl; exact ht₁u hx
    simp only [Finset.mem_union, Finset.mem_erase]
    tauto
  have hord : ((decomposeWith tn t u).progress t₁).ord
      = (decomposeWith (tn.progress t₁) t u).ord := by
    funext a b
    apply propext
    have h1 : u.ord a b → a ≠ t₁ := fun h => by rintro rfl; exact ht₁u (hu.mem_left h)
    have h2 : a ∈ u.T → a ≠ t₁ := fun hx => by rintro rfl; exact ht₁u hx
    simp only [TaskNetwork.progress_ord, decomposeWith_ord_iff, TaskNetwork.progress_ord]
    constructor
    · rintro ⟨h | ⟨h, hb⟩ | ⟨h, ha⟩ | ⟨h, hat, hbt⟩, hat₁⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨⟨h, hat₁⟩, hb⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨⟨h, Ne.symm hne⟩, ha⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨⟨h, hat₁⟩, hat, hbt⟩))
    · rintro (h | ⟨⟨h, hat₁⟩, hb⟩ | ⟨⟨h, -⟩, ha⟩ | ⟨⟨h, hat₁⟩, hat, hbt⟩)
      · exact ⟨Or.inl h, h1 h⟩
      · exact ⟨Or.inr (Or.inl ⟨h, hb⟩), hat₁⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨h, ha⟩)), h2 ha⟩
      · exact ⟨Or.inr (Or.inr (Or.inr ⟨h, hat, hbt⟩)), hat₁⟩
  have hα : ((decomposeWith tn t u).progress t₁).α = (decomposeWith (tn.progress t₁) t u).α := by
    funext x
    simp [decomposeWith, TaskNetwork.progress]
  exact TaskNetwork.ext' hT hord hα

end Commute

/-! ### Counted decomposition sequences -/

section Counted

variable [DecidableEq I]

/-- `DecomposesToN M n tn tn'`: `tn'` is obtained from `tn` by exactly `n` decomposition
steps. -/
inductive DecomposesToN (M : Set (Method I A C)) :
    ℕ → TaskNetwork I A C → TaskNetwork I A C → Prop
  /-- No step at all. -/
  | refl (tn : TaskNetwork I A C) : DecomposesToN M 0 tn tn
  /-- One step followed by `n` further steps. -/
  | head {tn tn₁ tn₂ : TaskNetwork I A C} {n : ℕ} (h : DecompStep' M tn tn₁)
      (hs : DecomposesToN M n tn₁ tn₂) : DecomposesToN M (n + 1) tn tn₂

variable {M : Set (Method I A C)}

lemma DecomposesToN.decomposesTo {n : ℕ} {tn tn' : TaskNetwork I A C}
    (h : DecomposesToN M n tn tn') : DecomposesTo M tn tn' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih => exact Relation.ReflTransGen.head hstep ih

lemma exists_decomposesToN {tn tn' : TaskNetwork I A C} (h : DecomposesTo M tn tn') :
    ∃ n, DecomposesToN M n tn tn' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, DecomposesToN.refl _⟩
  | head hstep _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, DecomposesToN.head hstep hn⟩

lemma DecomposesToN.wf {n : ℕ} {tn tn' : TaskNetwork I A C} (h : DecomposesToN M n tn tn')
    (hwf : tn.WF) : tn'.WF :=
  HTN.DecomposesTo.wf h.decomposesTo hwf

/-- **A counted decomposition sequence can be replayed on an isomorphic task network.** -/
theorem DecomposesToN.iso [Infinite I] {n : ℕ} {tn₁ tn₂ : TaskNetwork I A C}
    (h : DecomposesToN M n tn₁ tn₂) (h₁ : tn₁.WF) :
    ∀ {tn₁' : TaskNetwork I A C}, tn₁'.WF → tn₁.Iso tn₁' →
      ∃ tn₂' : TaskNetwork I A C, DecomposesToN M n tn₁' tn₂' ∧ tn₂.Iso tn₂' := by
  induction h with
  | refl tn => exact fun {tn₁'} _ hiso => ⟨tn₁', DecomposesToN.refl _, hiso⟩
  | @head tn tna tnb n hstep _ ih =>
    intro tn₁' hwf₁' hiso
    obtain ⟨t, m, hs⟩ := hstep
    obtain ⟨t', tna', hs', hisoa⟩ := hs.iso h₁ hwf₁' hiso
    obtain ⟨tnb', hb', hisob⟩ := ih (hs.wf h₁) (hs'.wf hwf₁') hisoa
    exact ⟨tnb', DecomposesToN.head ⟨t', m, hs'⟩ hb', hisob⟩

/-- **Reordering a decomposition sequence.**  If the abstract task `t` of `tn` does not survive
the decomposition sequence as an abstract task — so it is decomposed somewhere along it — then
the sequence can be reordered so that `t` is decomposed *first*, at the cost of replacing the
final network by an isomorphic one and using one step fewer afterwards. -/
theorem DecomposesToN.pull_out [Infinite I] {n : ℕ} {tn tnStar : TaskNetwork I A C} {t : I}
    {c : C} (h : DecomposesToN M n tn tnStar) (hwf : tn.WF) (ht : t ∈ tn.T)
    (hα : tn.α t = Sum.inr c) (hnot : t ∈ tnStar.T → ¬ tnStar.IsAbstractId t) :
    ∃ (m : Method I A C) (tn₁ tnStar' : TaskNetwork I A C) (k : ℕ), k < n ∧
      DecompStep M tn t m tn₁ ∧ DecomposesToN M k tn₁ tnStar' ∧ tnStar.Iso tnStar' := by
  induction h with
  | refl tn => exact absurd ⟨c, hα⟩ (hnot ht)
  | @head tn tna tnb n hstep hrest ih =>
    obtain ⟨t', m', hm'M, ht'T, hα', u', hu', hu'iso, hdisj', rfl⟩ := hstep
    have hu'n : ∀ x, x ∈ tn.T → x ∉ u'.T := fun x hx => Finset.disjoint_left.1 hdisj' hx
    by_cases hte : t' = t
    · subst hte
      exact ⟨m', decomposeWith tn t' u', tnb, n, Nat.lt_succ_self n,
        ⟨hm'M, ht'T, hα', u', hu', hu'iso, hdisj', rfl⟩, hrest, TaskNetwork.Iso.refl _⟩
    · have hne : t ≠ t' := fun h => hte h.symm
      have htna : t ∈ (decomposeWith tn t' u').T :=
        mem_decomposeWith_T.2 (Or.inl ⟨ht, fun h => hte h.symm⟩)
      have hαtna : (decomposeWith tn t' u').α t = Sum.inr c := by
        simp only [decomposeWith_α, if_neg (hu'n t ht)]
        exact hα
      have hwfa : (decomposeWith tn t' u').WF := decomposeWith_wf hwf hu' hdisj'
      obtain ⟨m, tnb', tnStar'', k, hk, hstep2, hrest2, hiso2⟩ := ih hwfa htna hαtna hnot
      obtain ⟨hmM, -, hαm, u, hu, huiso, hdisju, rfl⟩ := hstep2
      -- a copy of the method's subtask network that avoids all the identifiers used so far
      obtain ⟨v, hv, hviso, hdisjv⟩ :=
        TaskNetwork.exists_fresh_iso_copy u hu (tn.T ∪ u'.T)
      have hvtn : Disjoint tn.T v.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hdisjv
      have hvu' : Disjoint u'.T v.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_right hdisjv
      have hαt : tn.α t = Sum.inr m.abstractTask := by
        have heq : (decomposeWith tn t' u').α t = tn.α t := by
          simp only [decomposeWith_α, if_neg (hu'n t ht)]
        rw [← heq]
        exact hαm
      have hdisjav : Disjoint (decomposeWith tn t' u').T v.T := by
        rw [decomposeWith_T]
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hvtn
        · exact hvu'
      -- the first step: decompose `t` in `tn`
      have hstepA : DecompStep M tn t m (decomposeWith tn t v) :=
        ⟨hmM, ht, hαt, v, hv, hviso.trans huiso, hvtn, rfl⟩
      -- the second step: decompose `t'` in the result
      have ht'A : t' ∈ (decomposeWith tn t v).T :=
        mem_decomposeWith_T.2 (Or.inl ⟨ht'T, hte⟩)
      have hαt'A : (decomposeWith tn t v).α t' = Sum.inr m'.abstractTask := by
        have hvt' : t' ∉ v.T := Finset.disjoint_left.1 hvtn ht'T
        simp only [decomposeWith_α, if_neg hvt']
        exact hα'
      have hdisjA : Disjoint (decomposeWith tn t v).T u'.T := by
        rw [decomposeWith_T]
        refine Finset.disjoint_union_left.2 ⟨?_, ?_⟩
        · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj'
        · exact hvu'.symm
      have hstepB : DecompStep' M (decomposeWith tn t v)
          (decomposeWith (decomposeWith tn t v) t' u') :=
        ⟨t', m', hm'M, ht'A, hαt'A, u', hu', hu'iso, hdisjA, rfl⟩
      -- the two steps in the other order give the same network
      have hcomm : decomposeWith (decomposeWith tn t v) t' u'
          = decomposeWith (decomposeWith tn t' u') t v :=
        decomposeWith_comm hv hu' hne ht ht'T hvtn hdisj' hvu'.symm
      -- and it is isomorphic to the network reached by the original sequence
      obtain ⟨ρ, hρbij, hρord, hρα⟩ := hviso
      have hisoX : (decomposeWith (decomposeWith tn t' u') t v).Iso
          (decomposeWith (decomposeWith tn t' u') t u) :=
        decomposeWith_iso_congr (σ := id) hwfa hwfa hv hu hdisjav hdisju htna
          (Set.bijOn_id _) (by simp) (by simp) hρbij hρord hρα
      have hwfX : (decomposeWith (decomposeWith tn t' u') t v).WF :=
        decomposeWith_wf hwfa hv hdisjav
      have hwfb : (decomposeWith (decomposeWith tn t' u') t u).WF :=
        decomposeWith_wf hwfa hu hdisju
      obtain ⟨tnStar''', hrest3, hiso3⟩ :=
        hrest2.iso hwfb hwfX (hisoX.symm)
      refine ⟨m, decomposeWith tn t v, tnStar''', k + 1, by omega, hstepA, ?_,
        hiso2.trans hiso3⟩
      refine DecomposesToN.head hstepB ?_
      rw [hcomm]
      exact hrest3

end Counted

end HTN
