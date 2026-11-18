import HtnComplexity.AcVerify.VerEntry
/-!
# Semantics of the verifier, part 3: roots, children, pairs

For a certificate `blist (cs.map CE.enc)` whose entries carry the records of step lists:

* `HTN.Syn.AcVer.rootsB_iff` — the root test is `RootsOK`;
* `HTN.Syn.AcVer.childB_iff` — the child test of an entry, as a condition on step lists;
* `HTN.Syn.AcVer.pairB_iff` — the pair test is `PairOK`.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-! ### Decoding records -/

/-- The step of a record (an arbitrary step if the string is not a record). -/
noncomputable def decR (d : DomDesc) (q : InstDesc) (R : List Bool) : PStep :=
  if h : ∃ x, recOf d q x = R then h.choose else (0, 0)

theorem decR_recOf (x : PStep) : decR d q (recOf d q x) = x := by
  have h : ∃ y, recOf d q y = recOf d q x := ⟨x, rfl⟩
  rw [decR, dif_pos h]
  exact recOf_injective d q h.choose_spec

/-- The steps of a parsed entry. -/
noncomputable def stepsOf (d : DomDesc) (q : InstDesc) (e : CE) : List PStep :=
  e.recs.map (decR d q)

theorem stepsOf_eq {e : CE} {p : List PStep} (hp : e.recs = p.map (recOf d q)) :
    stepsOf d q e = p := by
  rw [stepsOf, hp, List.map_map]
  conv_rhs => rw [← List.map_id p]
  exact List.map_congr_left fun x _ => decR_recOf x

theorem map_recOf_injective : Function.Injective (List.map (recOf d q)) :=
  List.map_injective_iff.2 (recOf_injective d q)

/-! ### Prefixes of record lists -/

theorem bstr_recOf (x : PStep) : bstr (recOf d q x) = key x.1 ++ (key x.2 ++
    (key (lTag (stepLabel d q x)) ++ (key (lVal (stepLabel d q x)) ++ [false]))) := by
  have h := (recOf_eq_rec4_of (d := d) (q := q) (x := x))
  simpa using h

/-- **A prefix pattern: the records of `l₁`, followed by the start of the record of `(k, j)`.** -/
theorem prefix_child_iff (l₁ p : List PStep) (k j : ℕ) (z : List Bool) :
    entriesEnc (l₁.map (recOf d q)) ++ true :: (key k ++ key j) <+:
        blist (p.map (recOf d q)) ++ z ↔ ∃ s, p = l₁ ++ (k, j) :: s := by
  constructor
  · rintro ⟨t, ht⟩
    rw [List.append_assoc] at ht
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align _ _ _ _ ht
    obtain ⟨a, b, hab, ha, hb⟩ := List.map_eq_append_iff.1 hl
    rcases b with _ | ⟨y, s⟩
    · subst hb; simp at hr
    · subst hb
      rw [List.map_cons, blist_cons] at hr
      simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at hr
      rw [bstr_recOf] at hr
      simp only [List.append_assoc] at hr
      obtain ⟨h1, hr⟩ := key_parse hr
      obtain ⟨h2, -⟩ := key_parse hr
      have : a = l₁ := map_recOf_injective ha
      subst this
      have hy : y = (k, j) := Prod.ext h1.symm h2.symm
      subst hy
      exact ⟨s, hab⟩
  · rintro ⟨s, rfl⟩
    refine ⟨key (lTag (stepLabel d q (k, j))) ++ (key (lVal (stepLabel d q (k, j))) ++ [false]) ++
      (blist (s.map (recOf d q)) ++ z), ?_⟩
    rw [List.map_append, blist_append_eq, List.map_cons, blist_cons, bstr_recOf]
    simp

theorem occB_cert_iff (cs : List CE) (U : List Bool) :
    occB (blist (cs.map CE.enc)) (true :: dbl U) = true ↔ ∃ e ∈ cs, U <+: e.enc := by
  have h := occB_key_iff (cs.map CE.enc) [] U
  rw [List.append_nil] at h
  rw [h]
  simp

/-! ### Roots -/

theorem forall_idPos_iff (P : List Bool → Prop) :
    (∀ s, s <:+ instSer q → idPos (instSer q) s = true → P (nvAt s)) ↔
      ∀ u ∈ q.tnI.ids, P (serNat u) := by
  constructor
  · intro h u hu
    obtain ⟨s, hs, hid, hnv⟩ := exists_idPos_of_mem hu
    rw [← hnv]; exact h s hs hid
  · intro h s _ hid
    obtain ⟨u, hu, hnv⟩ := idPos_val hid
    rw [hnv]; exact h u hu

/-- **The root test is `RootsOK`.** -/
theorem rootsB_iff (cs : List CE) (hcs : ∀ e ∈ cs, e.recs = (stepsOf d q e).map (recOf d q)) :
    rootsB (instSer q) (blist (cs.map CE.enc)) = true ↔
      RootsOK q (cs.map fun e => (stepsOf d q e, e.f)) := by
  unfold rootsB RootsOK
  simp only [List.all_eq_true, List.mem_tails, Bool.or_eq_true, Bool.not_eq_true']
  have h1 : (∀ s, s <:+ instSer q → idPos (instSer q) s = false ∨
      occB (blist (cs.map CE.enc)) (true :: dbl (true :: (key 0 ++ dbl (nvAt s)))) = true) ↔
      ∀ s, s <:+ instSer q → idPos (instSer q) s = true →
        occB (blist (cs.map CE.enc)) (true :: dbl (true :: (key 0 ++ dbl (nvAt s)))) = true := by
    refine forall₂_congr fun s _ => ?_
    cases idPos (instSer q) s <;> simp
  rw [h1, forall_idPos_iff (fun v => occB (blist (cs.map CE.enc))
    (true :: dbl (true :: (key 0 ++ dbl v))) = true)]
  refine forall₂_congr fun u _ => ?_
  rw [occB_cert_iff]
  simp only [List.mem_map, exists_exists_and_eq_and]
  refine exists_congr fun e => and_congr_right fun he => ?_
  have hk : dbl (serNat u) = key u := rfl
  rw [hk, enc_eq_recs e, hcs e he]
  have := prefix_child_iff (d := d) (q := q) [] (stepsOf d q e) 0 u (stOf e.enc)
  simpa using this

/-! ### Children -/

/-- **The child test of an entry with steps `p`.** -/
theorem childB_iff (cs : List CE) (hcs : ∀ e ∈ cs, e.recs = (stepsOf d q e).map (recOf d q))
    (e : CE) (p : List PStep) (hp : e.recs = p.map (recOf d q)) :
    childB (advOf d) (blist (cs.map CE.enc)) e.enc = true ↔
      ∀ l₁ y l₂, p = l₁ ++ y :: l₂ → l₁ ≠ [] → ∀ j ∈ (methodAt d y.1).2.ids, y.1 ∈ mIdx d →
        ∃ e' ∈ cs, ∃ s', stepsOf d q e' = l₁ ++ (y.1, j) :: s' := by
  unfold childB
  rw [enc_eq_recs e, hp, entAll_iff, forall_split_map (recOf d q) p (fun l₁ w l₂ => _ = true)]
  refine forall₃_congr fun l₁ y l₂ => imp_congr_right fun _ => ?_
  simp only [Bool.or_eq_true, decide_eq_true_eq, entriesEnc_eq_nil, List.map_eq_nil_iff]
  rw [advOf_eq, entAll_iff]
  constructor
  · rintro (h | h) hne j hj hk
    · exact absurd h hne
    · have hmem : recM d (y.1, j) ∈ mstepT d := mem_mstepT.2 ⟨y.1, hk, j, hj, rfl⟩
      obtain ⟨m₁, m₂, hsplit⟩ := List.append_of_mem hmem
      have := h m₁ _ m₂ hsplit
      rw [← recOf_mem_of_mIdx (q := q) (x := (y.1, j)) hk, kat0_recOf, kat0_recOf,
        kat1_recOf] at this
      simp only [decide_true, Bool.not_true, Bool.false_or, occB_cert_iff] at this
      obtain ⟨e', he', hpre⟩ := this
      rw [enc_eq_recs e', hcs e' he', prefix_child_iff] at hpre
      exact ⟨e', he', hpre⟩
  · intro h
    by_cases hne : l₁ = []
    · exact Or.inl hne
    · refine Or.inr fun m₁ M m₂ hsplit => ?_
      have hM : M ∈ mstepT d := by rw [hsplit]; simp
      obtain ⟨k, hk, j, hj, rfl⟩ := mem_mstepT.1 hM
      rw [← recOf_mem_of_mIdx (q := q) (x := (k, j)) hk, kat0_recOf, kat0_recOf, kat1_recOf]
      by_cases hky : k = y.1
      · subst hky
        obtain ⟨e', he', s', hs'⟩ := h hne j hj hk
        simp only [decide_true, Bool.not_true, Bool.false_or, occB_cert_iff]
        refine ⟨e', he', ?_⟩
        rw [enc_eq_recs e', hcs e' he', prefix_child_iff]
        exact ⟨s', hs'⟩
      · simp [key_ne_key hky]

end AcVer

end Syn

end HTN
