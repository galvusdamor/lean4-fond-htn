import HtnComplexity.AcVerify.VerSem2
/-!
# Semantics of the verifier, part 4: the pair test is `PairOK`
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

theorem exists_split_map {α β : Type} (g : α → β) (p : List α)
    (Q : List β → β → List β → Prop) :
    (∃ l₁ w l₂, p.map g = l₁ ++ w :: l₂ ∧ Q l₁ w l₂) ↔
      ∃ l₁ x l₂, p = l₁ ++ x :: l₂ ∧ Q (l₁.map g) (g x) (l₂.map g) := by
  constructor
  · rintro ⟨l₁, w, l₂, he, hQ⟩
    obtain ⟨a, b, rfl, ha, hb⟩ := List.map_eq_append_iff.1 he
    obtain ⟨x, c, rfl, hx, hc⟩ := List.map_eq_cons_iff.1 hb
    exact ⟨a, x, c, rfl, by rw [ha, hx, hc]; exact hQ⟩
  · rintro ⟨l₁, x, l₂, rfl, hQ⟩
    exact ⟨_, _, _, by simp, hQ⟩

/-- **The ordering test.** -/
theorem ordB_iff (k a b : ℕ) (h0 : k = 0 → a ∈ q.tnI.ids ∧ b ∈ q.tnI.ids)
    (hk : k ≠ 0 → k ∈ mIdx d) :
    ordB (instSer q) (advOf d) (key k) (key a) (key b) = true ↔ (netOf d q k).ordOf a b := by
  unfold ordB
  by_cases hk0 : k = 0
  · subst hk0
    obtain ⟨ha, hb⟩ := h0 rfl
    simp only [decide_true, Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false,
      Bool.and_eq_true, Bool.not_eq_true', preOrdB_iff]
    rw [show preOrdB (key b) (key a) (instSer q) = false ↔ ¬ q.tnI.preOrd b a by
      rw [← Bool.not_eq_true, preOrdB_iff]]
    simp [netOf, TnDesc.ordOf, ha, hb]
  · have hne : key k ≠ key 0 := key_ne_key hk0
    simp only [hne, decide_false, Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
    rw [tO_advOf, ← bstr_key3, occB_iff, mem_ordT, netOf_of_ne hk0]
    exact ⟨fun h => h.2, fun h => ⟨hk hk0, h⟩⟩

theorem drop_entriesEnc (l₁ l₂ : List (List Bool)) (z : List Bool) :
    (blist (l₁ ++ l₂) ++ z).drop (entriesEnc l₁).length = blist l₂ ++ z := by
  rw [blist_append_eq, List.append_assoc, List.drop_left]

/-- The divergence pattern of the pair test. -/
theorem div_iff (l₁ pv : List PStep) (zv : List Bool) :
    (entriesEnc (l₁.map (recOf d q)) <+: blist (pv.map (recOf d q)) ++ zv ∧
      hasNext ((blist (pv.map (recOf d q)) ++ zv).drop
        (entriesEnc (l₁.map (recOf d q))).length) = true) ↔ ∃ y sv, pv = l₁ ++ y :: sv := by
  constructor
  · rintro ⟨⟨t, ht⟩, hn⟩
    obtain ⟨l₂, hl, hr⟩ := entriesEnc_align _ _ _ _ ht
    obtain ⟨a, b, hab, ha, hb⟩ := List.map_eq_append_iff.1 hl
    have : a = l₁ := map_recOf_injective ha
    subst this
    rw [hab, List.map_append, drop_entriesEnc, hasNext_blist_map] at hn
    rcases b with _ | ⟨y, s⟩
    · exact absurd rfl hn
    · exact ⟨y, s, hab⟩
  · rintro ⟨y, sv, rfl⟩
    refine ⟨⟨blist ((y :: sv).map (recOf d q)) ++ zv, ?_⟩, ?_⟩
    · rw [List.map_append, blist_append_eq, List.append_assoc]
    · rw [List.map_append, drop_entriesEnc, hasNext_blist_map]; simp

/-- Facts about the steps of an action leaf used by the pair test. -/
def LeafSteps (d : DomDesc) (q : InstDesc) (p : List PStep) : Prop :=
  ∀ x ∈ p, StepIn d q x ∧ (x.1 ≠ 0 → x.1 ∈ mIdx d)

/-- **The pair test is `PairOK`.** -/
theorem pairB_iff (pu pv : List PStep) (cu cv zu zv : List Bool)
    (hcu : cu = blist (pu.map (recOf d q)) ++ zu) (hcv : cv = blist (pv.map (recOf d q)) ++ zv)
    (fu fv : Bool) (hfu : flagOf cu = fu) (hfv : flagOf cv = fv)
    (hleaf : fu = false → fv = false → LeafSteps d q pu ∧ LeafSteps d q pv) :
    pairB (instSer q) (advOf d) cu cv = true ↔ PairOK d q (pu, fu) (pv, fv) := by
  unfold pairB
  rw [hfu, hfv]
  rw [hcu, entAny_iff, exists_split_map (recOf d q) pu (fun l₁ w l₂ => _ = true)]
  unfold PairOK DivAt
  simp only
  constructor
  · rintro ⟨l₁, x, l₂, hpu, hb⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hb
    obtain ⟨⟨⟨⟨hpre, hn⟩, h0⟩, h1⟩, hord⟩ := hb
    rw [hcv] at hpre hn h0 h1 hord
    obtain ⟨y, sv, hpv⟩ := (div_iff l₁ pv zv).1 ⟨hpre, hn⟩
    have hnx : nextEnt ((blist (pv.map (recOf d q)) ++ zv).drop
        (entriesEnc (l₁.map (recOf d q))).length) = true :: bstr (recOf d q y) := by
      rw [hpv, List.map_append, drop_entriesEnc, List.map_cons, nextEnt_blist]
    rw [hnx, kat0_recOf, kat0_recOf] at h0
    rw [hnx, kat1_recOf, kat1_recOf] at h1
    rw [hnx, kat0_recOf, kat1_recOf, kat1_recOf] at hord
    have hk := key_injective h0
    have hj : x.2 ≠ y.2 := fun h => by rw [h] at h1; simp at h1
    refine ⟨x, y, ⟨l₁, l₂, sv, hpu, hpv, fun h => hj (by rw [h])⟩, hk, fun hfu' hfv' => ?_⟩
    obtain ⟨hlu, hlv⟩ := hleaf hfu' hfv'
    have hx := hlu x (by rw [hpu]; simp)
    have hy := hlv y (by rw [hpv]; simp)
    rw [hfu', hfv'] at hord
    simp only [Bool.false_eq_true, false_or] at hord
    rw [← Bool.not_eq_true, ordB_iff] at hord
    · exact hord
    · intro h0'
      refine ⟨?_, ?_⟩
      · have := hy.1; unfold StepIn at this; rw [← hk, h0'] at this; simpa [netOf] using this
      · have := hx.1; unfold StepIn at this; rw [h0'] at this; simpa [netOf] using this
    · exact hx.2
  · rintro ⟨x, y, ⟨P, su, sv, hpu, hpv, hxy⟩, hk, hord⟩
    refine ⟨P, x, su, hpu, ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
    rw [hcv]
    obtain ⟨hpre, hn⟩ := (div_iff P pv zv).2 ⟨y, sv, hpv⟩
    have hnx : nextEnt ((blist (pv.map (recOf d q)) ++ zv).drop
        (entriesEnc (P.map (recOf d q))).length) = true :: bstr (recOf d q y) := by
      rw [hpv, List.map_append, drop_entriesEnc, List.map_cons, nextEnt_blist]
    rw [hnx, kat0_recOf, kat0_recOf, kat1_recOf, kat1_recOf, hk]
    have hj : x.2 ≠ y.2 := fun h => hxy (Prod.ext hk h)
    refine ⟨⟨⟨⟨hpre, hn⟩, rfl⟩, decide_eq_false (fun h => hj (key_injective h))⟩, ?_⟩
    cases fu
    · cases fv
      · obtain ⟨hlu, hlv⟩ := hleaf rfl rfl
        have hx := hlu x (by rw [hpu]; simp)
        have hy := hlv y (by rw [hpv]; simp)
        right
        rw [← Bool.not_eq_true, ← hk, ordB_iff]
        · exact hord rfl rfl
        · intro h0'
          refine ⟨?_, ?_⟩
          · have := hy.1; unfold StepIn at this; rw [← hk, h0'] at this; simpa [netOf] using this
          · have := hx.1; unfold StepIn at this; rw [h0'] at this; simpa [netOf] using this
        · exact hx.2
      · left; right; rfl
    · left; left; rfl

end AcVer

end Syn

end HTN
