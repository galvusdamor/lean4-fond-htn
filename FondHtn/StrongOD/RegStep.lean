import FondHtn.StrongOD.RegDesc
/-!
# A decomposition step of a regular description

`d` is a regular description (`regB d`) whose unique compound task `x` is decomposed by a method
`e`; `d₁ = decDesc d x e`.  Then

* `d₁` is regular if `e.2` is, and its compound names are those of `e.2`
  (`FOND.SOD.regB_decDesc`, `FOND.SOD.compL_decDesc`);
* in the primitive part of `d₁` the primitive tasks of `d` form a prefix
  (`FOND.SOD.prefix_decDesc`) that agrees with the primitive part of `d`
  (`FOND.SOD.sameOn_old_decDesc`), and the rest is an isomorphic copy of the primitive part of
  `e.2` (`FOND.SOD.isoVia_new_decDesc`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false

/-- The fresh ids of a decomposition step. -/
abbrev frOf (d : TnDesc) (e : MethodDesc) : List ℕ := freshIds d.ids e.2.ids.length

section Step

variable {d : TnDesc} {x : ℕ} {e : MethodDesc} {prim : ℕ → Prop}

theorem mem_ids_dec {y : ℕ} :
    y ∈ (decDesc d x e).ids ↔ (y ∈ d.ids ∧ y ≠ x) ∨ y ∈ frOf d e := by
  simp [decDesc, TnDesc.ids, frOf]

theorem mem_ord_dec {a b : ℕ} :
    (a, b) ∈ (decDesc d x e).ordList ↔
      (a, b) ∈ (copyDesc e.2 (frOf d e)).ordList ∨ ((a, x) ∈ d.ordList ∧ b ∈ frOf d e) ∨
        ((x, b) ∈ d.ordList ∧ a ∈ frOf d e) ∨ ((a, b) ∈ d.ordList ∧ a ≠ x ∧ b ≠ x) := by
  simp only [decDesc, TnDesc.ordList, List.mem_dedup, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro (((h | ⟨q, ⟨hq, hq2⟩, n, hn, rfl, rfl⟩) | ⟨q, ⟨hq, hq1⟩, n, hn, rfl, rfl⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨by rw [← hq2]; exact hq, hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by rw [← hq1]; exact hq, hn⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2⟩))
  · rintro (h | ⟨h, hn⟩ | ⟨h, hn⟩ | ⟨h, h1, h2⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨(a, x), ⟨h, rfl⟩, b, hn, rfl, rfl⟩))
    · exact Or.inl (Or.inr ⟨(x, b), ⟨h, rfl⟩, a, hn, rfl, rfl⟩)
    · exact Or.inr ⟨h, h1, h2⟩

theorem not_mem_ids_of_fr {y : ℕ} (hy : y ∈ frOf d e) : y ∉ d.ids := not_mem_of_mem_freshIds hy

theorem lblOf_dec_old (hev : TnValid prim e.2) {y : ℕ} (hy : y ∈ d.ids) (hyx : y ≠ x) :
    lblOf (decDesc d x e) y = lblOf d y := by
  unfold lblOf
  have h1 : (decDesc d x e).lbl = (d.lbl.filter fun q => decide (q.1 ≠ x)) ++
      (copyDesc e.2 (frOf d e)).lbl := rfl
  rw [h1, lookup_append', lookup_filter_ne _ hyx]
  have h2 : (copyDesc e.2 (frOf d e)).lbl.lookup y = none := by
    apply lookup_none_of_not_mem
    intro q hq hqy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
    have : renOf e.2.ids (frOf d e) z ∈ frOf d e :=
      renOf_mem hev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz
    have hqy' : renOf e.2.ids (frOf d e) z = y := hqy
    exact not_mem_ids_of_fr this (by rw [hqy']; exact hy)
  cases d.lbl.lookup y <;> simp [h2]

theorem lblOf_dec_new {s₀ : List ℕ} (hc : CfgInv (s₀, d)) (hev : TnValid prim e.2) {z : ℕ}
    (hz : z ∈ e.2.ids) : lblOf (decDesc d x e) (renOf e.2.ids (frOf d e) z) = lblOf e.2 z := by
  unfold lblOf
  have h1 : (decDesc d x e).lbl = (d.lbl.filter fun q => decide (q.1 ≠ x)) ++
      (copyDesc e.2 (frOf d e)).lbl := rfl
  have hren : renOf e.2.ids (frOf d e) z ∈ frOf d e :=
    renOf_mem hev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz
  have h2 : (d.lbl.filter fun q => decide (q.1 ≠ x)).lookup (renOf e.2.ids (frOf d e) z) = none := by
    apply lookup_none_of_not_mem
    intro q hq hqy
    exact not_mem_ids_of_fr hren (hqy ▸ hc.lbl_mem q (List.mem_filter.1 hq).1)
  have h3 : (copyDesc e.2 (frOf d e)).lbl.lookup (renOf e.2.ids (frOf d e) z) =
      some (lblOf e.2 z) :=
    lookup_map_ren (fun a ha b hb h => renOf_inj hev.nodup (freshIds_nodup _ _)
      (length_freshIds _ _) ha hb h) hz
  rw [h1, lookup_append', h2, h3]
  rfl

/-- The hypotheses of a regular decomposition step. -/
structure RegStepHyp (d : TnDesc) (x : ℕ) (e : MethodDesc) (prim : ℕ → Prop) (s₀ : List ℕ) :
    Prop where
  inv : CfgInv (s₀, d)
  reg : regB d = true
  hx : x ∈ d.ids
  hxc : (lblOf d x).1 = true
  ev : TnValid prim e.2

variable {s₀ : List ℕ}

theorem RegStepHyp.old_prim (h : RegStepHyp d x e prim s₀) {y : ℕ} (hy : y ∈ d.ids)
    (hyx : y ≠ x) : (lblOf d y).1 = false ∧ (y, x) ∈ d.ordList := by
  rcases regB_iff'.1 h.reg x h.hx h.hxc y hy with h1 | h1
  · exact absurd h1.symm hyx
  · exact h1

theorem RegStepHyp.no_succ (h : RegStepHyp d x e prim s₀) (b : ℕ) : (x, b) ∉ d.ordList := by
  intro hxb
  have hb : b ∈ d.ids := List.mem_toFinset.1 (h.inv.wf.mem_right (t := x) (t' := b) hxb)
  have hbx : b ≠ x := fun e' => h.inv.wf.irrefl x (show (cfgNet d).ord x x from e' ▸ hxb)
  exact h.inv.wf.asymm (show (cfgNet d).ord x b from hxb)
    (show (cfgNet d).ord b x from (h.old_prim hb hbx).2)

theorem RegStepHyp.ord_mem (h : RegStepHyp d x e prim s₀) {a b : ℕ} (hab : (a, b) ∈ d.ordList) :
    a ∈ d.ids ∧ b ∈ d.ids :=
  ⟨List.mem_toFinset.1 (h.inv.wf.mem_left (t := a) (t' := b) hab),
    List.mem_toFinset.1 (h.inv.wf.mem_right (t := a) (t' := b) hab)⟩

theorem mem_copy_ord (hev : TnValid prim e.2) {z z' : ℕ} (hz : z ∈ e.2.ids) (hz' : z' ∈ e.2.ids) :
    (renOf e.2.ids (frOf d e) z, renOf e.2.ids (frOf d e) z') ∈
      (copyDesc e.2 (frOf d e)).ordList ↔ (z, z') ∈ e.2.ordList := by
  have hinj := fun a (ha : a ∈ e.2.ids) b (hb : b ∈ e.2.ids) h =>
    renOf_inj (dst := frOf d e) hev.nodup (freshIds_nodup _ _) (length_freshIds _ _) ha hb h
  simp only [copyDesc, TnDesc.ordList, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    have hq' := hev.ord_mem q hq
    rw [← hinj _ hq'.1 _ hz h1, ← hinj _ hq'.2 _ hz' h2]
    exact hq
  · intro h
    exact ⟨(z, z'), h, rfl, rfl⟩

theorem fr_of_copy_ord (hev : TnValid prim e.2) {a b : ℕ}
    (h : (a, b) ∈ (copyDesc e.2 (frOf d e)).ordList) : a ∈ frOf d e ∧ b ∈ frOf d e := by
  simp only [copyDesc, TnDesc.ordList, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨q, hq, rfl, rfl⟩ := h
  have hq' := hev.ord_mem q hq
  exact ⟨renOf_mem hev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hq'.1,
    renOf_mem hev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hq'.2⟩

/-- Old tasks are ordered in `d₁` as in `d`. -/
theorem ord_dec_old (h : RegStepHyp d x e prim s₀) {a b : ℕ} (ha : a ∈ d.ids)
    (hb : b ∈ d.ids) (hax : a ≠ x) (hbx : b ≠ x) :
    (a, b) ∈ (decDesc d x e).ordList ↔ (a, b) ∈ d.ordList := by
  rw [mem_ord_dec]
  constructor
  · rintro (h1 | ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨h1, -⟩)
    · exact absurd ha (not_mem_ids_of_fr (fr_of_copy_ord h.ev h1).1)
    · exact absurd hb (not_mem_ids_of_fr h1)
    · exact absurd ha (not_mem_ids_of_fr h1)
    · exact h1
  · exact fun h1 => Or.inr (Or.inr (Or.inr ⟨h1, hax, hbx⟩))

/-- New tasks are ordered in `d₁` as in `e.2`. -/
theorem ord_dec_new (h : RegStepHyp d x e prim s₀) {z z' : ℕ} (hz : z ∈ e.2.ids)
    (hz' : z' ∈ e.2.ids) :
    (renOf e.2.ids (frOf d e) z, renOf e.2.ids (frOf d e) z') ∈ (decDesc d x e).ordList ↔
      (z, z') ∈ e.2.ordList := by
  rw [mem_ord_dec, ← mem_copy_ord h.ev hz hz']
  have hr : renOf e.2.ids (frOf d e) z ∈ frOf d e :=
    renOf_mem h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz
  constructor
  · rintro (h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact h1
    · exact absurd (h.ord_mem h1).1 (not_mem_ids_of_fr hr)
    · exact absurd h1 (h.no_succ _)
    · exact absurd (h.ord_mem h1).1 (not_mem_ids_of_fr hr)
  · exact Or.inl

theorem fr_eq_ren (h : RegStepHyp d x e prim s₀) {y : ℕ} (hy : y ∈ frOf d e) :
    ∃ z ∈ e.2.ids, renOf e.2.ids (frOf d e) z = y :=
  renOf_surj h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hy

/-- **Regularity is preserved.** -/
theorem regB_decDesc (h : RegStepHyp d x e prim s₀) (he : regB e.2 = true) :
    regB (decDesc d x e) = true := by
  have hc₁ := inv_decDesc (x := x) h.inv h.ev
  rw [regB_iff']
  intro y hy hyc w hw
  by_cases hyw : y = w
  · exact Or.inl hyw
  right
  rcases mem_ids_dec.1 hy with ⟨hy, hyx⟩ | hy
  · rw [lblOf_dec_old h.ev hy hyx, (h.old_prim hy hyx).1] at hyc; cases hyc
  obtain ⟨z, hz, rfl⟩ := fr_eq_ren h hy
  rw [lblOf_dec_new h.inv h.ev hz] at hyc
  rcases mem_ids_dec.1 hw with ⟨hw, hwx⟩ | hw
  · refine ⟨by rw [lblOf_dec_old h.ev hw hwx]; exact (h.old_prim hw hwx).1, ?_⟩
    exact mem_ord_dec.2 (Or.inr (Or.inl ⟨(h.old_prim hw hwx).2,
      renOf_mem h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz⟩))
  · obtain ⟨z', hz', rfl⟩ := fr_eq_ren h hw
    have hzz : z ≠ z' := fun e' => hyw (by rw [e'])
    rcases regB_iff'.1 he z hz hyc z' hz' with h1 | h1
    · exact absurd h1 hzz
    · exact ⟨by rw [lblOf_dec_new h.inv h.ev hz']; exact h1.1, (ord_dec_new h hz' hz).2 h1.2⟩

/-- **The compound names after the step are those of the method.** -/
theorem compL_decDesc (h : RegStepHyp d x e prim s₀) (he : regB e.2 = true) :
    compL (decDesc d x e) = compL e.2 := by
  have hc₁ := inv_decDesc (x := x) h.inv h.ev
  rcases compL_cases h.ev.nodup he with ⟨hn, hprim⟩ | ⟨z, hz, hcz, hzc⟩
  · rw [hn]
    refine compL_eq_nil fun y hy => ?_
    rcases mem_ids_dec.1 hy with ⟨hy, hyx⟩ | hy
    · rw [lblOf_dec_old h.ev hy hyx]; exact (h.old_prim hy hyx).1
    · obtain ⟨z, hz, rfl⟩ := fr_eq_ren h hy
      rw [lblOf_dec_new h.inv h.ev hz]; exact hprim z hz
  · rw [hcz]
    have hz' : renOf e.2.ids (frOf d e) z ∈ (decDesc d x e).ids := mem_ids_dec.2 (Or.inr
      (renOf_mem h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz))
    refine compL_eq_single hc₁.ids_nodup (regB_decDesc h he) hz' ?_
    rw [lblOf_dec_new h.inv h.ev hz, lblOf_eq_of_fst hzc]

theorem RegStepHyp.mem_primD_old (h : RegStepHyp d x e prim s₀) {y : ℕ} :
    y ∈ (primD d).ids ↔ y ∈ d.ids ∧ y ≠ x := by
  rw [mem_ids_primD]
  constructor
  · rintro ⟨hy, hp⟩
    refine ⟨hy, fun e' => ?_⟩
    subst e'
    simp [primB, h.hxc] at hp
  · rintro ⟨hy, hyx⟩
    exact ⟨hy, by simp [primB, (h.old_prim hy hyx).1]⟩

theorem RegStepHyp.primB_old (h : RegStepHyp d x e prim s₀) {y : ℕ} (hy : y ∈ d.ids)
    (hyx : y ≠ x) : primB (decDesc d x e) y = true := by
  simp [primB, lblOf_dec_old h.ev hy hyx, (h.old_prim hy hyx).1]

theorem RegStepHyp.primB_new (h : RegStepHyp d x e prim s₀) {z : ℕ} (hz : z ∈ e.2.ids) :
    primB (decDesc d x e) (renOf e.2.ids (frOf d e) z) = primB e.2 z := by
  simp [primB, lblOf_dec_new h.inv h.ev hz]

theorem RegStepHyp.mem_primD_new (h : RegStepHyp d x e prim s₀) {y : ℕ} :
    y ∈ (primD (decDesc d x e)).ids ↔ (y ∈ d.ids ∧ y ≠ x) ∨
      ∃ z ∈ e.2.ids, primB e.2 z = true ∧ renOf e.2.ids (frOf d e) z = y := by
  rw [mem_ids_primD, mem_ids_dec]
  constructor
  · rintro ⟨hy | hy, hp⟩
    · exact Or.inl hy
    · obtain ⟨z, hz, rfl⟩ := fr_eq_ren h hy
      exact Or.inr ⟨z, hz, by rw [← h.primB_new hz]; exact hp, rfl⟩
  · rintro (hy | ⟨z, hz, hp, rfl⟩)
    · exact ⟨Or.inl hy, h.primB_old hy.1 hy.2⟩
    · exact ⟨Or.inr (renOf_mem h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz),
        by rw [h.primB_new hz]; exact hp⟩

theorem ren_not_old (h : RegStepHyp d x e prim s₀) {z : ℕ} (hz : z ∈ e.2.ids) :
    renOf e.2.ids (frOf d e) z ∉ d.ids :=
  not_mem_ids_of_fr (renOf_mem h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz)

/-- **The old primitive tasks are a prefix.** -/
theorem prefix_decDesc (h : RegStepHyp d x e prim s₀) :
    Prefix (cfgNet (primD (decDesc d x e))) (primD d).ids.toFinset := by
  refine ⟨fun y hy => ?_, fun a ha b hb hbX => ?_⟩
  · rw [List.mem_toFinset, h.mem_primD_old] at hy
    show y ∈ (primD (decDesc d x e)).ids.toFinset
    exact List.mem_toFinset.2 (h.mem_primD_new.2 (Or.inl hy))
  · rw [List.mem_toFinset, h.mem_primD_old] at ha
    have hb' : b ∈ (primD (decDesc d x e)).ids := List.mem_toFinset.1 hb
    rcases h.mem_primD_new.1 hb' with hbo | ⟨z, hz, hzp, rfl⟩
    · exact absurd (List.mem_toFinset.2 (h.mem_primD_old.2 hbo)) hbX
    have hr := renOf_mem (dst := frOf d e) h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) hz
    refine ⟨?_, fun hba => ?_⟩
    · show (_, _) ∈ (primD (decDesc d x e)).ordList
      rw [mem_ordList_primD]
      refine ⟨mem_ord_dec.2 (Or.inr (Or.inl ⟨(h.old_prim ha.1 ha.2).2, hr⟩)),
        h.primB_old ha.1 ha.2, by rw [h.primB_new hz]; exact hzp⟩
    · have hba' : (_, _) ∈ (primD (decDesc d x e)).ordList := hba
      rw [mem_ordList_primD, mem_ord_dec] at hba'
      rcases hba'.1 with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact not_mem_ids_of_fr (fr_of_copy_ord h.ev h1).2 ha.1
      · exact ren_not_old h hz (h.ord_mem h1).1
      · exact h.no_succ _ h1
      · exact ren_not_old h hz (h.ord_mem h1).1

/-- **The old part agrees with the primitive part of `d`.** -/
theorem sameOn_old_decDesc (h : RegStepHyp d x e prim s₀) :
    FOND.TaskNetwork.SameOn (sub (cfgNet (primD (decDesc d x e))) (primD d).ids.toFinset)
      (cfgNet (primD d)) := by
  have hc₁ := inv_decDesc (x := x) h.inv h.ev
  refine ⟨rfl, fun a ha b hb => ?_, fun a ha => ?_⟩
  · have ha' := h.mem_primD_old.1 (List.mem_toFinset.1 ha)
    have hb' := h.mem_primD_old.1 (List.mem_toFinset.1 hb)
    show (a, b) ∈ (primD (decDesc d x e)).ordList ↔ (a, b) ∈ (primD d).ordList
    rw [mem_ordList_primD, mem_ordList_primD, ord_dec_old h ha'.1 hb'.1 ha'.2 hb'.2,
      h.primB_old ha'.1 ha'.2, h.primB_old hb'.1 hb'.2]
    have h1 : primB d a = true := (mem_ids_primD.1 (List.mem_toFinset.1 ha)).2
    have h2 : primB d b = true := (mem_ids_primD.1 (List.mem_toFinset.1 hb)).2
    rw [h1, h2]
  · have ha' := h.mem_primD_old.1 (List.mem_toFinset.1 ha)
    show (cfgNet (primD (decDesc d x e))).α a = (cfgNet (primD d)).α a
    have hp1 : (lblOf (decDesc d x e) a).1 = false := by
      rw [lblOf_dec_old h.ev ha'.1 ha'.2]; exact (h.old_prim ha'.1 ha'.2).1
    rw [cfgNet_label, cfgNet_label, lblOf_primD hc₁.lbl_nodup hp1,
      lblOf_primD h.inv.lbl_nodup (h.old_prim ha'.1 ha'.2).1, lblOf_dec_old h.ev ha'.1 ha'.2]

/-- **The new part is a copy of the primitive part of the method.** -/
theorem isoVia_new_decDesc (h : RegStepHyp d x e prim s₀) :
    HTN.TaskNetwork.IsoVia (renOf e.2.ids (frOf d e)) (cfgNet (primD e.2))
      (sub (cfgNet (primD (decDesc d x e)))
        ((cfgNet (primD (decDesc d x e))).T \ (primD d).ids.toFinset)) := by
  have hc₁ := inv_decDesc (x := x) h.inv h.ev
  have hen : (e.2.lbl.map Prod.fst).Nodup := h.ev.lbl_perm.nodup_iff.2 h.ev.nodup
  have hinj := fun a (ha : a ∈ e.2.ids) b (hb : b ∈ e.2.ids) hh =>
    renOf_inj (dst := frOf d e) h.ev.nodup (freshIds_nodup _ _) (length_freshIds _ _) ha hb hh
  have hmem : ∀ {z}, z ∈ (cfgNet (primD e.2)).T ↔ z ∈ e.2.ids ∧ primB e.2 z = true := by
    intro z; simp [cfgNet, mem_ids_primD]
  have hT : ∀ {y}, y ∈ (sub (cfgNet (primD (decDesc d x e)))
      ((cfgNet (primD (decDesc d x e))).T \ (primD d).ids.toFinset)).T ↔
        ∃ z ∈ e.2.ids, primB e.2 z = true ∧ renOf e.2.ids (frOf d e) z = y := by
    intro y
    simp only [sub, Finset.mem_sdiff, cfgNet, List.mem_toFinset]
    rw [h.mem_primD_new, h.mem_primD_old]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1
    · rintro ⟨z, hz, hp, rfl⟩
      exact ⟨Or.inr ⟨z, hz, hp, rfl⟩, fun h1 => ren_not_old h hz h1.1⟩
  refine ⟨⟨fun z hz => ?_, fun z hz z' hz' hh => ?_, fun y hy => ?_⟩, fun z hz z' hz' => ?_,
    fun z hz => ?_⟩
  · have hz' := hmem.1 hz
    exact hT.2 ⟨z, hz'.1, hz'.2, rfl⟩
  · exact hinj z (hmem.1 hz).1 z' (hmem.1 hz').1 hh
  · obtain ⟨z, hz, hp, rfl⟩ := hT.1 hy
    exact ⟨z, hmem.2 ⟨hz, hp⟩, rfl⟩
  · have h1 := hmem.1 hz
    have h2 := hmem.1 hz'
    show (z, z') ∈ (primD e.2).ordList ↔ (_, _) ∈ (primD (decDesc d x e)).ordList
    rw [mem_ordList_primD, mem_ordList_primD, ord_dec_new h h1.1 h2.1, h.primB_new h1.1,
      h.primB_new h2.1]
  · have h1 := hmem.1 hz
    have hp : (lblOf e.2 z).1 = false := by simpa [primB] using h1.2
    have hp1 : (lblOf (decDesc d x e) (renOf e.2.ids (frOf d e) z)).1 = false := by
      rw [lblOf_dec_new h.inv h.ev h1.1]; exact hp
    show (cfgNet (primD e.2)).α z = (cfgNet (primD (decDesc d x e))).α _
    rw [cfgNet_label, cfgNet_label, lblOf_primD hen hp, lblOf_primD hc₁.lbl_nodup hp1,
      lblOf_dec_new h.inv h.ev h1.1]

end Step

end SOD

end FOND
