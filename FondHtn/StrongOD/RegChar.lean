import FondHtn.StrongOD.RegStep
/-!
# Strong OD solvability of regular problems by belief-set sequences

For a problem whose initial task network is regular and whose reachable methods are regular,
strong OD solvability is the existence of a **belief-set sequence**
(`FOND.SOD.strongOD_iff_nw`):

    ∃ S₁, (tn_I's primitive part is solvable from s_I with all leaves in S₁) ∧ NW (names of
    tn_I's compound tasks) S₁

where `FOND.SOD.NW p [c] S` holds iff some regular method `e` of `c` has a primitive part
solvable from every state of `S` with all leaves in some `S'`, and `NW (names of e's compound
tasks) S'`; `NW p [] S` always holds.  The fixed-method nature of strong OD solutions is visible
in the sets: one method sequence serves all states of a belief set.

The proof uses the description decomposition sequences of `FondHtn/StrongOD/RegDesc.lean`, the
structure of regular decomposition steps (`FondHtn/StrongOD/RegStep.lean`) and the sequential
composition `FOND.SOD.bsw_comp`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false

variable {p : FProbDesc}

/-- **A regular step on belief states with leaves.** -/
theorem bsw_dec_iff {d : TnDesc} {x : ℕ} {e : MethodDesc} {prim : ℕ → Prop} {s₀ : List ℕ}
    (h : RegStepHyp d x e prim s₀) {W : Set (Set ℕ)} {s : Set ℕ} :
    BSW p.toProblem W (cfgNet (primD (decDesc d x e))) s ↔
      BSW p.toProblem {s' | BSW p.toProblem W (cfgNet (primD e.2)) s'} (cfgNet (primD d)) s := by
  rw [bsw_comp (prefix_decDesc h)]
  have hiso := isoVia_new_decDesc h
  obtain ⟨τ, hτ, -⟩ := hiso.exists_inv
  have hset : {s' | BSW p.toProblem W (sub (cfgNet (primD (decDesc d x e)))
      ((cfgNet (primD (decDesc d x e))).T \ (primD d).ids.toFinset)) s'} =
      {s' | BSW p.toProblem W (cfgNet (primD e.2)) s'} := by
    ext s'
    exact ⟨fun hb => hb.isoVia hτ, fun hb => hb.isoVia hiso⟩
  rw [hset]
  exact ⟨fun hb => hb.congr (sameOn_old_decDesc h),
    fun hb => hb.congr (sameOn_symm (sameOn_old_decDesc h))⟩

/-- **Belief-set sequences along regular method chains.** -/
inductive NW (p : FProbDesc) : List ℕ → Set (Set ℕ) → Prop
  | nil (S : Set (Set ℕ)) : NW p [] S
  | cons {c : ℕ} {e : MethodDesc} {S S' : Set (Set ℕ)} (he : e ∈ p.methods) (hc : e.1 = c)
      (hreg : regB e.2 = true)
      (hblk : ∀ s ∈ S, BSW p.toProblem S' (cfgNet (primD e.2)) s)
      (hn : NW p (compL e.2) S') : NW p [c] S

theorem mem_compL {t : TnDesc} {c : ℕ} : c ∈ compL t ↔ ∃ z ∈ t.ids, lblOf t z = (true, c) := by
  simp only [compL, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨z, ⟨hz, hzc⟩, rfl⟩
    exact ⟨z, hz, lblOf_eq_of_fst hzc⟩
  · rintro ⟨z, hz, hl⟩
    exact ⟨z, ⟨hz, by rw [hl]⟩, by rw [hl]⟩

theorem nw_complete (hp : p.Valid) {o : List ℕ} {S' : Set (Set ℕ)} (hn : NW p o S') :
    ∀ (d : TnDesc) (s₀ : List ℕ) (S : Set (Set ℕ)), CfgInv (s₀, d) → regB d = true →
      compL d = o → (∀ s ∈ S, BSW p.toProblem S' (cfgNet (primD d)) s) →
        ∃ d', Relation.ReflTransGen (DStep p) d d' ∧ (∀ x ∈ d'.ids, (lblOf d' x).1 = false) ∧
          ∀ s ∈ S, p.toProblem.BeliefSolvable (cfgNet d') s := by
  induction hn with
  | nil S' =>
    intro d s₀ S hc hreg ho hS
    rcases compL_cases hc.ids_nodup hreg with ⟨-, hprim⟩ | ⟨x, -, hx, -⟩
    · refine ⟨d, Relation.ReflTransGen.refl, hprim, fun s hs => ?_⟩
      exact bsw_univ_iff.1 (((hS s hs).mono (Set.subset_univ _)).congr
        (sameOn_symm (sameOn_primD hc hprim)))
    · rw [hx] at ho; cases ho
  | @cons c e S₁ S₂ he hc hreg hblk _ ih =>
    intro d s₀ S hinv hregd ho hS
    rcases compL_cases hinv.ids_nodup hregd with ⟨hn, -⟩ | ⟨x, hx, hxo, hxc⟩
    · rw [hn] at ho; cases ho
    rw [hxo] at ho
    have hxl : lblOf d x = (true, e.1) := by
      rw [lblOf_eq_of_fst hxc, hc]; simp at ho; rw [ho]
    have hst : RegStepHyp d x e p.Declared s₀ := ⟨hinv, hregd, hx, hxc, hp.methods e he⟩
    obtain ⟨d', hr, hprim, hbs⟩ := ih (decDesc d x e) s₀ S (inv_decDesc hinv (hp.methods e he))
      (regB_decDesc hst hreg) (compL_decDesc hst hreg) fun s hs =>
        (bsw_dec_iff hst).2 ((hS s hs).mono fun s' hs' => hblk s' hs')
    exact ⟨d', Relation.ReflTransGen.head ⟨x, e, hx, hxl, he, rfl⟩ hr, hprim, hbs⟩

/-- Reachability of compound names. -/
abbrev Reach (p : FProbDesc) : ℕ → Prop := p.toProblem.toArt.toPos.ReachableName

theorem reach_compL_method {e : MethodDesc} (he : e ∈ p.methods) (hr : Reach p e.1) {c : ℕ}
    (hc : c ∈ compL e.2) : Reach p c := by
  obtain ⟨z, hz, hl⟩ := mem_compL.1 hc
  exact HTN.Problem.ReachableName.method (m := e.toMethod) ⟨e, he, rfl⟩ hr
    (by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hz) (label_eq_inr.2 hl)

theorem nw_sound (hp : p.Valid) (hREG : ∀ e ∈ p.methods, Reach p e.1 → regB e.2 = true)
    {d d' : TnDesc} (hr : Relation.ReflTransGen (DStep p) d d')
    (hprim : ∀ x ∈ d'.ids, (lblOf d' x).1 = false) :
    ∀ s₀, CfgInv (s₀, d) → regB d = true → (∀ c ∈ compL d, Reach p c) →
      ∀ S : Set (Set ℕ), (∀ s ∈ S, p.toProblem.BeliefSolvable (cfgNet d') s) →
        ∃ S', (∀ s ∈ S, BSW p.toProblem S' (cfgNet (primD d)) s) ∧ NW p (compL d) S' := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro s₀ hc _ _ S hS
    refine ⟨Set.univ, fun s hs => ?_, ?_⟩
    · exact (bsw_univ_iff.2 (hS s hs)).congr (sameOn_primD hc hprim)
    · rw [compL_eq_nil hprim]; exact .nil _
  | @head d d₁ h12 _ ih =>
    intro s₀ hinv hregd hreach S hS
    obtain ⟨x, e, hx, hl, he, rfl⟩ := h12
    have hxc : (lblOf d x).1 = true := by rw [hl]
    have hst : RegStepHyp d x e p.Declared s₀ := ⟨hinv, hregd, hx, hxc, hp.methods e he⟩
    have hcd : compL d = [e.1] := compL_eq_single hinv.ids_nodup hregd hx hl
    have hre : Reach p e.1 := hreach _ (by rw [hcd]; exact List.mem_singleton_self _)
    have hreg := hREG e he hre
    obtain ⟨S'', hS'', hn⟩ := ih s₀ (inv_decDesc hinv (hp.methods e he)) (regB_decDesc hst hreg)
      (fun c hc => reach_compL_method he hre (by rwa [compL_decDesc hst hreg] at hc)) S hS
    refine ⟨{s' | BSW p.toProblem S'' (cfgNet (primD e.2)) s'}, fun s hs =>
      (bsw_dec_iff hst).1 (hS'' s hs), ?_⟩
    rw [hcd]
    exact .cons he rfl hreg (fun s' hs' => hs') (by rwa [compL_decDesc hst hreg] at hn)

theorem regB_d₀ (p : FProbDesc) : regB (d₀ p) = regB p.tnI := by
  simp [regB, d₀, TnDesc.ordList, TnDesc.ids, lblOf, TnDesc.lbl]

theorem reach_compL_d₀ {c : ℕ} (hc : c ∈ compL (d₀ p)) : Reach p c := by
  obtain ⟨z, hz, hl⟩ := mem_compL.1 hc
  exact HTN.Problem.ReachableName.tnI (P := p.toProblem.toArt.toPos)
    (by simpa [FProbDesc.toProblem, Problem.toArt, HTN.Article.Problem.toPos,
      TnDesc.toTaskNetwork, d₀] using hz) (label_eq_inr.2 hl)

/-- **Strong OD solvability of regular problems by belief-set sequences.** -/
theorem strongOD_iff_nw (hp : p.Valid) (hREG : ∀ e ∈ p.methods, Reach p e.1 → regB e.2 = true)
    (hreg0 : regB p.tnI = true) :
    p.toProblem.StrongODSolvable ↔ ∃ S', BSW p.toProblem S' (cfgNet (primD (d₀ p)))
      {f | f ∈ p.init} ∧ NW p (compL (d₀ p)) S' := by
  rw [strongOD_iff_desc hp]
  have hr0 : regB (d₀ p) = true := by rw [regB_d₀]; exact hreg0
  constructor
  · rintro ⟨d', hr, hprim, hbs⟩
    obtain ⟨S', hS', hn⟩ := nw_sound hp hREG hr hprim _ (inv_d₀ hp) hr0
      (fun c hc => reach_compL_d₀ hc) {{f | f ∈ p.init}} (by simpa using hbs)
    exact ⟨S', hS' _ rfl, hn⟩
  · rintro ⟨S', hS', hn⟩
    obtain ⟨d', hr, hprim, hbs⟩ := nw_complete hp hn (d₀ p) _ {{f | f ∈ p.init}} (inv_d₀ hp)
      hr0 rfl (by simpa using hS')
    exact ⟨d', hr, hprim, hbs _ rfl⟩

end SOD

end FOND
