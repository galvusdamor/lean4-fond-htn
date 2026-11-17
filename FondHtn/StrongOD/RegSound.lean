import FondHtn.StrongOD.RegSearch
/-!
# Soundness of the search for regular problems

An accepting run from an initial configuration yields a belief-set sequence
(`FOND.SOD.rsearch_sound`).  The proof runs backwards along the run with the invariant
`FOND.SOD.RInv`: in phase `0` the current belief set has a belief-set sequence for the remaining
names; in phase `1` the goals on the stack are won, the states still to be checked win the block
game, and the guessed next belief set has a belief-set sequence for the method's names.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ## One step of the depth-first evaluation -/

section DfsStep

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]
  {acc uni : α × σ → Bool} {succs : α × σ → List σ}

theorem dfsStep_won {a : α} {S S' : List (ℕ × σ)} (hst : dfsStep acc uni succs (a, S, S') = true)
    (ih : ∀ g ∈ S', gameVal acc uni succs a g.1 g.2 = true) :
    ∀ g ∈ S, gameVal acc uni succs a g.1 g.2 = true := by
  cases S with
  | nil => simp [dfsStep_nil] at hst
  | cons g rest =>
    rw [dfsStep_cons] at hst
    obtain ⟨k, c⟩ := g
    simp only [dfsFrom, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hst
    rcases hst with ⟨hac, rfl⟩ | ⟨hk, hst⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact gameVal_of_acc hac _
      · exact ih g hg
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hst
      cases hu : uni (a, c) <;> rw [hu] at hst <;> simp only [cond_true, cond_false,
        decide_eq_true_eq, List.any_eq_true] at hst
      · obtain ⟨c', hc', rfl⟩ := hst
        intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · simp only [gameVal, hu, cond_false, Bool.or_eq_true, List.any_eq_true]
          exact Or.inr ⟨c', hc', ih _ (List.mem_cons_self ..)⟩
        · exact ih g (List.mem_cons_of_mem _ hg)
      · subst hst
        intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · simp only [gameVal, hu, cond_true, Bool.or_eq_true, List.all_eq_true]
          exact Or.inr fun c' hc' => ih (k, c')
            (List.mem_append_left _ (List.mem_map.2 ⟨c', hc', rfl⟩))
        · exact ih g (List.mem_append_right _ hg)

end DfsStep

variable {p : FProbDesc}

/-! ## Primitive parts of methods -/

theorem cfgNet_wf_of_valid {prim : ℕ → Prop} {t : TnDesc} (hv : TnValid prim t) :
    (cfgNet t).WF := by
  refine (TnDesc.toTaskNetwork_wf t).of_agree ⟨rfl, ?_, fun _ _ => rfl⟩
  funext a b
  simp only [TnDesc.toTaskNetwork, cfgNet, eq_iff_iff]
  exact hv.ordOf_iff

theorem inv_primD_valid {prim : ℕ → Prop} {t : TnDesc} (hv : TnValid prim t) {s : List ℕ}
    (hs : s.Nodup) : CfgInv (s, primD t) := by
  have hn : (t.lbl.map Prod.fst).Nodup := hv.lbl_perm.nodup_iff.2 hv.nodup
  have hwf := cfgNet_wf_of_valid hv
  refine ⟨hv.nodup.filter _, fun q hq => ?_, hn.sublist (List.filter_sublist.map _),
    List.nodup_dedup _, hs, ?_⟩
  · obtain ⟨hq, hq2⟩ := List.mem_filter.1 hq
    refine mem_ids_primD.2 ⟨hv.lbl_perm.subset (List.mem_map_of_mem hq), ?_⟩
    unfold primB
    rw [lblOf_of_mem hn hq]
    simpa using hq2
  · refine ⟨fun {a b} hab => ?_, fun {a b} hab => ?_, fun a haa => ?_, fun {a b c} hab hbc => ?_⟩
    · have hab' := mem_ordList_primD.1 hab
      exact List.mem_toFinset.2 (mem_ids_primD.2 ⟨List.mem_toFinset.1
        (hwf.mem_left (t := a) (t' := b) hab'.1), hab'.2.1⟩)
    · have hab' := mem_ordList_primD.1 hab
      exact List.mem_toFinset.2 (mem_ids_primD.2 ⟨List.mem_toFinset.1
        (hwf.mem_right (t := a) (t' := b) hab'.1), hab'.2.2⟩)
    · exact hwf.irrefl a (mem_ordList_primD.1 haa).1
    · have h1 := mem_ordList_primD.1 hab
      have h2 := mem_ordList_primD.1 hbc
      exact mem_ordList_primD.2 ⟨hwf.trans (show (cfgNet t).ord a b from h1.1)
        (show (cfgNet t).ord b c from h2.1), h1.2.1, h2.2.2⟩

/-! ## The certificate -/

theorem regCert_reach {R : List ℕ} (h : regCertB p R = true) :
    ∀ c, Reach p c → c ∈ R := by
  simp only [regCertB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := h
  intro c hc
  induction hc with
  | @tnI t c ht hc =>
    have ht' : t ∈ p.tnI.ids := by
      simpa [FProbDesc.toProblem, Problem.toArt, HTN.Article.Problem.toPos,
        TnDesc.toTaskNetwork] using ht
    rcases h1 t ht' with h | h
    · rw [label_eq_inr.1 hc] at h; cases h
    · rw [label_eq_inr.1 hc] at h; exact h
  | @method m t c hm _ ht hc ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    rcases h2 e he with h | ⟨-, h⟩
    · exact absurd ih h
    · rcases h t ht' with h' | h'
      · rw [label_eq_inr.1 hc] at h'; cases h'
      · rw [label_eq_inr.1 hc] at h'; exact h'

theorem regCert_regB {R : List ℕ} (h : regCertB p R = true) :
    ∀ e ∈ p.methods, Reach p e.1 → regB e.2 = true := by
  intro e he hr
  have hR := regCert_reach h _ hr
  simp only [regCertB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not] at h
  rcases h.1.1.2 e he with h' | ⟨h', -⟩
  · exact absurd hR h'
  · exact h'

theorem regM_of_regB (hp : p.Valid) (hREG : ∀ e ∈ p.methods, Reach p e.1 → regB e.2 = true) :
    FClass.REG p.toProblem := by
  rintro m ⟨⟨e, he, rfl⟩, hr⟩
  exact (regB_iff (hp.methods e he)).1 (hREG e he hr)

/-! ## The invariants -/

/-- The forward invariant: the phase is `0` or `1`, and in phase `1` the block is
well-behaved. -/
def RFwd (X : RCore) : Prop :=
  (X.1 = 0 ∨ X.1 = 1) ∧ (X.1 = 1 → ∀ s : List ℕ, s.Nodup → CfgInv (s, X.2.2.2.1))

/-- The backward invariant. -/
def RInv (p : FProbDesc) (X : RCore) : Prop :=
  (X.1 = 0 → NW p X.2.1 (setW X.2.2.1)) ∧
  (X.1 = 1 → (∀ g ∈ X.2.2.2.2.2.2.2,
      gameVal bacc buni bsuccs (p, X.2.2.2.2.2.1) g.1 g.2 = true) ∧
    (∀ s ∈ X.2.2.2.2.2.2.1, BSW p.toProblem (setW X.2.2.2.2.2.1) (cfgNet X.2.2.2.1)
      {f | f ∈ s}) ∧ NW p X.2.2.2.2.1 (setW X.2.2.2.2.2.1))

theorem coreStep_cases {X Y : RCore}
    (h : (chooseB p X Y || loadB X Y || dfsB p X Y || finB X Y) = true) :
    chooseB p X Y = true ∨ loadB X Y = true ∨ dfsB p X Y = true ∨ finB X Y = true := by
  simp only [Bool.or_eq_true] at h
  tauto

theorem rstep_fwd (hp : p.Valid) {X Y : RCore}
    (h : (chooseB p X Y || loadB X Y || dfsB p X Y || finB X Y) = true) (hX : RFwd X) :
    RFwd Y := by
  obtain ⟨ph, cur, S, B, nx, S', R, st⟩ := X
  rcases coreStep_cases h with h | h | h | h
  · simp only [chooseB, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, e, he, -, hY⟩ := h
    rw [hY]
    exact ⟨Or.inr rfl, fun _ s hs => inv_primD_valid (hp.methods e he) hs⟩
  · simp only [loadB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, -⟩, -⟩, hY⟩ := h
    rw [hY]
    exact ⟨Or.inr rfl, hX.2⟩
  · simp only [dfsB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, -⟩, -⟩, hY⟩ := h
    rw [hY]
    exact ⟨Or.inr rfl, hX.2⟩
  · simp only [finB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨-, hY⟩ := h
    rw [hY]
    exact ⟨Or.inl rfl, fun h => absurd h (by norm_num)⟩

theorem nw_setW_cons {c : ℕ} {e : MethodDesc} (he : e ∈ p.methods) (hc : e.1 = c)
    (hreg : regB e.2 = true) {S S' : List (List ℕ)}
    (hblk : ∀ s ∈ S, BSW p.toProblem (setW S') (cfgNet (primD e.2)) {f | f ∈ s})
    (hn : NW p (compL e.2) (setW S')) : NW p [c] (setW S) :=
  .cons he hc hreg (fun _ ⟨w, hw, hws⟩ => hws ▸ hblk w hw) hn

theorem rstep_inv {X Y : RCore}
    (h : (chooseB p X Y || loadB X Y || dfsB p X Y || finB X Y) = true) (hX : RFwd X)
    (hY : RInv p Y) : RInv p X := by
  obtain ⟨ph, cur, S, B, nx, S', R, st⟩ := X
  rcases coreStep_cases h with h | h | h | h
  · simp only [chooseB, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨hph, e, he, ⟨hcur, hreg⟩, hYe⟩ := h
    rw [hYe] at hY
    obtain ⟨-, hY1⟩ := hY
    obtain ⟨-, hR, hn⟩ := hY1 rfl
    try simp only at hph hcur hR hn
    subst hph
    refine ⟨fun _ => ?_, fun h => absurd h (by norm_num)⟩
    simp only
    rw [← hcur]
    exact nw_setW_cons he rfl hreg hR hn
  · simp only [loadB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨⟨⟨hph, hst⟩, hRne⟩, hYe⟩ := h
    try simp only at hph hst hRne
    subst hph hst
    rw [hYe] at hY
    obtain ⟨-, hY1⟩ := hY
    obtain ⟨hg, hR', hn⟩ := hY1 rfl
    try simp only at hg hR' hn
    refine ⟨fun h => absurd h (by norm_num), fun _ => ⟨by simp, fun s hs => ?_, hn⟩⟩
    obtain ⟨r, R₀, rfl⟩ := List.exists_cons_of_ne_nil hRne
    rcases List.mem_cons.1 hs with rfl | hs
    · have hw := hg _ List.mem_cons_self
      have hb := block_sound _ _ _ _ (hX.2 rfl _ (List.nodup_dedup _)) hw
      rwa [setOf_mem_dedup] at hb
    · exact hR' s hs
  · simp only [dfsB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hph, -⟩, hdfs⟩, hYe⟩ := h
    try simp only at hph hdfs
    subst hph
    rw [hYe] at hY hdfs
    obtain ⟨-, hY1⟩ := hY
    obtain ⟨hg, hR', hn⟩ := hY1 rfl
    try simp only at hg hR' hn hdfs
    exact ⟨fun h => absurd h (by norm_num), fun _ => ⟨dfsStep_won hdfs hg, hR', hn⟩⟩
  · simp only [finB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨hph, hst⟩, hR⟩, hYe⟩ := h
    try simp only at hph hst hR
    subst hph hst hR
    rw [hYe] at hY
    obtain ⟨hY0, -⟩ := hY
    exact ⟨fun h => absurd h (by norm_num), fun _ => ⟨by simp, by simp, hY0 rfl⟩⟩

theorem rinv_of_run (hp : p.Valid) {Rel : RCfg → RCfg → Prop}
    (hR : ∀ x y, Rel x y → rstep (p, x, y) = true) {x z : RCfg}
    (hr : Relation.ReflTransGen Rel x z) (hz : racc (p, z) = true) :
    RFwd x.2 → RInv p x.2 := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _
    simp only [racc, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hz
    exact ⟨fun _ => by rw [hz.2]; exact .nil _, fun h => absurd (hz.1 ▸ h) (by norm_num)⟩
  | @head x y hxy _ ih =>
    intro hfx
    have hst := hR _ _ hxy
    simp only [rstep, Bool.and_eq_true] at hst
    exact rstep_inv hst.2 hfx (ih (rstep_fwd hp hst.2 hfx))

theorem rinit_iff (p : FProbDesc) (c : RCfg) :
    rinit (p, c) = true ↔ p.Valid ∧ regB p.tnI = true ∧ regCertB p c.1 = true ∧
      c.2 = (1, [], [], primD (d₀ p), compL (d₀ p), c.2.2.2.2.2.2.1, [p.init.dedup], []) := by
  simp only [rinit, Bool.and_eq_true, FProbDesc.validB_iff, decide_eq_true_eq, and_assoc]

/-- **Soundness of the search.** -/
theorem rsearch_sound {Rel : RCfg → RCfg → Prop} (hR : ∀ x y, Rel x y → rstep (p, x, y) = true)
    {c₀ c : RCfg} (hi : rinit (p, c₀) = true) (hr : Relation.ReflTransGen Rel c₀ c)
    (ha : racc (p, c) = true) :
    p.Valid ∧ FClass.REGtn p.toProblem ∧ p.toProblem.StrongODSolvable := by
  obtain ⟨hp, hreg0, hcert, hc₀⟩ := (rinit_iff p c₀).1 hi
  have hREG := regCert_regB hcert
  refine ⟨hp, ⟨regM_of_regB hp hREG, (regB_iff hp.tnI).1 hreg0⟩, ?_⟩
  have hfwd : RFwd c₀.2 := by
    rw [hc₀]
    exact ⟨Or.inr rfl, fun _ s hs => inv_primD (inv_d₀ hp) hs⟩
  have hinv := rinv_of_run hp hR hr ha hfwd
  rw [hc₀] at hinv
  obtain ⟨-, hinv⟩ := hinv
  obtain ⟨-, hR', hn⟩ := hinv rfl
  have hb := hR' _ List.mem_cons_self
  rw [setOf_mem_dedup] at hb
  exact (strongOD_iff_nw hp hREG hreg0).2 ⟨_, hb, hn⟩

end SOD

end FOND
