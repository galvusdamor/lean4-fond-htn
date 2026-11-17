import FondHtn.StrongOD.Play
/-!
# Strong OD plan existence of primitive problems is in PSPACE ([CB21, Thm. 5.1], membership)

For a primitive problem the only achievable primitive task network is `tn_I`
(`FOND.Problem.achievablePrimitive_iff_of_primitive`), so strong OD solvability is the
solvability of the belief state `(tn_I, s_I)` ([DB25], `FOND.Problem.strongODSolvable_iff_fmSolvableDB`).
This is the value of the play game of `FondHtn/StrongOD/Play.lean` from
`(0, 0, s_I, tn_I)` with budget `2 · |T_I|` (`FOND.SOD.play_sound`, `FOND.SOD.play_complete`);
every configuration of the game has polynomial size: the network only shrinks and the states
are duplicate-free lists of facts mentioned in the description.  The bounded-depth game tool
`HTN.Syn.PolyDom.inPSpace_codeLang_of_game` gives

* **`FOND.strongOD_PRIM_mem`** — `PlanExFM strongOD PRIM ∈ PSPACE`.

The published PSPACE-hardness proof is wrong (catalogue G9), so only membership is proved.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN PTime FOND.Prim

namespace SOD

/-! ## The initial network and the facts of a description -/

/-- The initial network with a duplicate-free order list. -/
def d₀ (p : FProbDesc) : TnDesc := (p.tnI.ids, p.tnI.ordList.dedup, p.tnI.lbl)

/-- The facts mentioned in the initial state or in an add list. -/
def factsU (p : FProbDesc) : List ℕ := p.init ++ p.actions.flatMap fun a => a.effs.flatMap Prod.fst

theorem agree_d₀ {p : FProbDesc} (hp : p.Valid) : p.toProblem.tnI.Agree (cfgNet (d₀ p)) := by
  refine ⟨rfl, ?_, fun _ _ => rfl⟩
  funext a b
  simp only [FProbDesc.toProblem, TnDesc.toTaskNetwork, cfgNet, d₀, TnDesc.ordList,
    List.mem_dedup, eq_iff_iff]
  exact hp.tnI.ordOf_iff

theorem inv_d₀ {p : FProbDesc} (hp : p.Valid) : CfgInv (p.init.dedup, d₀ p) := by
  have hperm := hp.tnI.lbl_perm
  refine ⟨hp.tnI.nodup, fun q hq => hperm.subset (List.mem_map.2 ⟨q, hq, rfl⟩),
    hperm.nodup_iff.2 hp.tnI.nodup, List.nodup_dedup _, List.nodup_dedup _, ?_⟩
  exact (TnDesc.toTaskNetwork_wf p.tnI).of_agree (agree_d₀ hp)

/-- Strong OD solvability of a primitive problem is the solvability of `(tn_I, s_I)`. -/
theorem strongOD_iff_of_primitive {P : Problem ℕ ℕ ℕ ℕ} (h : P.tnI.IsPrimitive) :
    P.StrongODSolvable ↔ P.BeliefSolvable P.tnI P.init := by
  rw [Problem.strongODSolvable_iff_fmSolvableDB]
  constructor
  · rintro ⟨tn, hach, hb⟩
    rwa [(P.achievablePrimitive_iff_of_primitive h).1 hach] at hb
  · exact fun hb => ⟨_, (P.achievablePrimitive_iff_of_primitive h).2 rfl, hb⟩

/-! ## The game instance -/

/-- The initial configuration test. -/
def primInit (y : FProbDesc × GCfg) : Bool :=
  y.1.validB && noHTNB y.1.tnI && decide (y.2 = (0, 0, y.1.init.dedup, d₀ y.1))

/-- The depth budget. -/
def primDepth (p : FProbDesc) : ℕ := 2 * p.tnI.ids.length

theorem pt_d₀ : PT d₀ := by
  have ht : PT fun p : FProbDesc => p.tnI := PT.snd.comp PT.snd
  unfold d₀
  exact PT.pair (PT.fst.comp ht) (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp ht)))
    (PT.snd.comp (PT.snd.comp ht)))

theorem pt_primInit : PT primInit := by
  unfold primInit
  exact PT.and (PT.and (FProbDesc.pt_validB.comp PT.fst)
    (pt_noHTNB.comp (PT.snd.comp (PT.snd.comp PT.fst))))
    (PT.eq PT.snd (PT.pair (PT.const 0) (PT.pair (PT.const 0)
      (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp PT.fst))) (pt_d₀.comp PT.fst)))))

theorem pt_primDepth : PT primDepth :=
  (PT.affine 2 0 (PT.length (PT.fst.comp (PT.snd.comp PT.snd)))).of_eq fun _ => by
    simp [primDepth, TnDesc.ids, FProbDesc.tnI]

/-! ## Sizes -/

theorem sz_flatMap_le {β γ : Type} [BEnc β] [BEnc γ] (l : List β) (g : β → List γ)
    (h : ∀ x ∈ l, sz (g x) ≤ sz x) : sz (l.flatMap g) ≤ sz l := by
  induction l with
  | nil => simp [sz_nil]
  | cons x l ih =>
    rw [List.flatMap_cons, sz_cons]
    have h1 := sz_append_le (g x) (l.flatMap g)
    have h2 := h x List.mem_cons_self
    have h3 := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

theorem sz_le_of_sublist' {β : Type} [BEnc β] {l l' : List β} (h : l.Sublist l') :
    sz l ≤ sz l' := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => rw [sz_cons]; omega
  | cons₂ a _ ih => rw [sz_cons, sz_cons]; omega

theorem sz_tnI_le (p : FProbDesc) : sz p.tnI ≤ sz p := by
  have := sz_snd_le p.2
  have := sz_snd_le p
  simp only [FProbDesc.tnI] at *
  omega

theorem sz_init_le (p : FProbDesc) : sz p.init ≤ sz p := by
  have := sz_fst_le p.2
  have := sz_snd_le p
  simp only [FProbDesc.init] at *
  omega

theorem sz_actions_le (p : FProbDesc) : sz p.actions ≤ sz p := by
  have := sz_fst_le p.1
  have := sz_fst_le p
  simp only [FProbDesc.actions] at *
  omega

theorem sz_dedupOrd_le (t : TnDesc) : sz (t.1, t.2.1.dedup, t.2.2) ≤ sz t := by
  obtain ⟨i, o, l⟩ := t
  simp only [sz_prod]
  have := sz_le_of_sublist' (List.dedup_sublist o)
  omega

theorem sz_d₀_le (p : FProbDesc) : sz (d₀ p) ≤ sz p :=
  (sz_dedupOrd_le p.tnI).trans (sz_tnI_le p)

theorem sz_factsU_le (p : FProbDesc) : sz (factsU p) ≤ 2 * sz p := by
  have h1 := sz_append_le p.init (p.actions.flatMap fun a => a.effs.flatMap Prod.fst)
  have h2 : sz (p.actions.flatMap fun a => a.effs.flatMap Prod.fst) ≤ sz p.actions := by
    refine sz_flatMap_le _ _ fun a _ => ?_
    refine (sz_flatMap_le _ _ fun e _ => sz_fst_le e).trans ?_
    have := sz_snd_le a.2.2
    have := sz_snd_le a.2
    have := sz_snd_le a
    simp only [FActDesc.effs] at *
    omega
  have := sz_init_le p
  have := sz_actions_le p
  unfold factsU
  omega

theorem actL_mem (p : FProbDesc) (a : ℕ) : actL p a = defAct ∨ ∃ x ∈ p.actions, actL p a = x.2 := by
  unfold actL
  cases h : (p.actions.filter fun x => x.name == a).map Prod.snd with
  | nil => left; rfl
  | cons y l =>
    right
    have hy : y ∈ (p.actions.filter fun x => x.name == a).map Prod.snd := by rw [h]; simp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact ⟨x, (List.mem_filter.1 hx).1, rfl⟩

theorem add_mem_factsU {p : FProbDesc} {a : ℕ} {e : List ℕ × List ℕ} (he : e ∈ (actL p a).2.2)
    {f : ℕ} (hf : f ∈ e.1) : f ∈ factsU p := by
  rcases actL_mem p a with h | ⟨x, hx, h⟩
  · rw [h] at he
    simp only [defAct, List.mem_singleton] at he
    subst he; simp at hf
  · rw [h] at he
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, List.mem_flatMap.2 ⟨e, he, hf⟩⟩)

theorem length_effs_le (p : FProbDesc) (a : ℕ) : (actL p a).2.2.length ≤ sz p := by
  rcases actL_mem p a with h | ⟨x, hx, h⟩
  · rw [h]
    have := six_le_sz p
    simp [defAct]; omega
  · rw [h]
    have := length_le_sz x.2.2.2
    have := sz_snd_le x.2.2
    have := sz_snd_le x.2
    have := sz_snd_le x
    have := sz_le_of_mem hx
    have := sz_actions_le p
    omega

/-! ## The size invariant -/

/-- The size invariant of the configurations reachable in the primitive game. -/
def SGood (p : FProbDesc) (c : GCfg) : Prop :=
  c.1 ≤ 1 ∧ sz c.2.1 ≤ sz p ∧ c.2.2.1.Nodup ∧ (∀ f ∈ c.2.2.1, f ∈ factsU p) ∧ sz c.2.2.2 ≤ sz p

theorem sz_progDesc_le (d : TnDesc) (x : ℕ) : sz (progDesc d x) ≤ sz d := by
  obtain ⟨i, o, l⟩ := d
  simp only [progDesc, sz_prod, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have := sz_filter_le i (fun y => decide (y ≠ x))
  have := sz_filter_le o (fun q => decide (q.1 ≠ x ∧ q.2 ≠ x))
  have := sz_filter_le l (fun q => decide (q.1 ≠ x))
  omega

theorem sz_ids_le_d (d : TnDesc) : sz d.ids ≤ sz d := sz_fst_le d

theorem sGood_succ {p : FProbDesc} {c c' : GCfg} (hc : SGood p c) (h : c' ∈ gsuccs (p, c)) :
    SGood p c' := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, hx, hsn, hsU, hd⟩ := hc
  simp only at ht hx hsn hsU hd
  have h6 := six_le_sz p
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · simp only [gsuccs, beq_self_eq_true, cond_true, playMoves, List.mem_map,
      List.mem_filter] at h
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := h
    have := (sz_le_of_mem hy).trans ((sz_ids_le_d d).trans hd)
    exact ⟨le_rfl, this, hsn, hsU, hd⟩
  · simp only [gsuccs, show ((1 : ℕ) == 0) = false from rfl, cond_false, beq_self_eq_true,
      cond_true, outMoves, List.mem_map] at h
    obtain ⟨e, he, rfl⟩ := h
    refine ⟨by simp, by simp [sz_nat]; omega, List.nodup_dedup _, fun f hf => ?_,
      (sz_progDesc_le d x).trans hd⟩
    rw [List.mem_dedup] at hf
    simp only [nextL, List.mem_append, List.mem_filter] at hf
    rcases hf with ⟨hf, -⟩ | hf
    · exact hsU f hf
    · exact add_mem_factsU he hf

/-- The size of a well-sized configuration. -/
def cfgBound (n : ℕ) : ℕ := 8 * n ^ 2 + 8 * n + 4

theorem sz_le_of_sGood {p : FProbDesc} {c : GCfg} (hc : SGood p c) : sz c ≤ cfgBound (sz p) := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, hx, hsn, hsU, hd⟩ := hc
  simp only at ht hx hsn hsU hd
  have hU := sz_factsU_le p
  have hlen : s.length ≤ 2 * sz p :=
    ((hsn.subperm hsU).length_le).trans ((length_le_sz _).trans hU)
  have hs := sz_list_le s (2 * sz p) fun f hf => (sz_le_of_mem (hsU f hf)).trans hU
  have hm : s.length * (2 * (2 * sz p) + 2) ≤ 2 * sz p * (2 * (2 * sz p) + 2) :=
    Nat.mul_le_mul_right _ hlen
  have htag : sz t ≤ 3 := (sz_nat_le t).trans (by omega)
  simp only [sz_prod, cfgBound]
  nlinarith

theorem length_gsuccs_le {p : FProbDesc} {c : GCfg} (hc : SGood p c) :
    (gsuccs (p, c)).length ≤ sz p := by
  obtain ⟨t, x, s, d⟩ := c
  obtain ⟨ht, hx, hsn, hsU, hd⟩ := hc
  simp only at ht hd
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
  · simp only [gsuccs, beq_self_eq_true, cond_true, playMoves, List.length_map]
    exact (List.length_filter_le _ _).trans ((length_le_sz _).trans ((sz_ids_le_d d).trans hd))
  · simp only [gsuccs, show ((1 : ℕ) == 0) = false from rfl, cond_false, beq_self_eq_true,
      cond_true, outMoves, List.length_map]
    exact length_effs_le p _

theorem sz_gsuccs_le {p : FProbDesc} {c : GCfg} (hc : SGood p c) :
    sz (gsuccs (p, c)) ≤ sz p * (2 * cfgBound (sz p) + 2) + 1 := by
  have h := sz_list_le (gsuccs (p, c)) (cfgBound (sz p)) fun c' hc' =>
    sz_le_of_sGood (sGood_succ hc hc')
  have := Nat.mul_le_mul_right (2 * cfgBound (sz p) + 2) (length_gsuccs_le hc)
  omega

theorem sGood_reach {p : FProbDesc} : ∀ (n : ℕ) (c c' : GCfg), SGood p c →
    GameReach gsuccs p n c c' → SGood p c' := by
  intro n
  induction n with
  | zero => rintro c c' hc rfl; exact hc
  | succ n ih =>
    rintro c c' hc ⟨c₁, h₁, hr⟩
    exact ih c₁ c' (sGood_succ hc h₁) hr

theorem sGood_init {p : FProbDesc} : SGood p ((0 : ℕ), (0 : ℕ), p.init.dedup, d₀ p) := by
  have h6 := six_le_sz p
  refine ⟨Nat.zero_le _, by simp [sz_nat]; omega, List.nodup_dedup _, fun f hf => ?_, sz_d₀_le p⟩
  exact List.mem_append_left _ (List.mem_dedup.1 hf)

/-! ## The theorem -/

/-- The polynomial bound. -/
noncomputable def qPrim : Polynomial ℕ := Polynomial.C 100 * (Polynomial.X + 1) ^ 3

theorem eval_qPrim (n : ℕ) : qPrim.eval n = 100 * (n + 1) ^ 3 := by
  simp [qPrim]

theorem primInit_iff (p : FProbDesc) (c : GCfg) :
    primInit (p, c) = true ↔ p.Valid ∧ p.tnI.toTaskNetwork.IsPrimitive ∧
      c = (0, 0, p.init.dedup, d₀ p) := by
  simp only [primInit, Bool.and_eq_true, FProbDesc.validB_iff, noHTNB_iff, decide_eq_true_eq,
    and_assoc]

end SOD

open SOD in
/-- **[CB21, Thm. 5.1], membership**: strong OD plan existence of primitive problems is in
PSPACE. -/
theorem strongOD_PRIM_mem : Cx.PSPACE (PlanExFM .strongOD FClass.PRIM) := by
  refine inPSpace_codeLang_of_game (α := FProbDesc) (σ := GCfg)
    (Q := fun p => p.Valid ∧ FClass.PRIM p.toProblem ∧ FMCrit.Solvable .strongOD p.toProblem)
    pt_primInit pt_gacc pt_guni pt_gsuccs pt_primDepth qPrim (fun p => ⟨?_, ?_⟩) (fun p => ?_)
  · rw [eval_qPrim]
    have h1 : p.tnI.ids.length ≤ sz p :=
      (length_le_sz _).trans ((sz_ids_le_d _).trans (sz_tnI_le p))
    have : sz p + 1 ≤ (sz p + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    simp only [primDepth]
    omega
  · intro c₀ hi
    obtain ⟨-, -, rfl⟩ := (primInit_iff p c₀).1 hi
    have hn := sz_le_of_sGood (sGood_init (p := p))
    rw [eval_qPrim]
    have hW : cfgBound (sz p) ≤ 100 * (sz p + 1) ^ 3 := by unfold cfgBound; nlinarith
    refine ⟨hn.trans hW, fun n _ c hr => ?_⟩
    refine (sz_gsuccs_le (sGood_reach n _ c sGood_init hr)).trans ?_
    unfold cfgBound
    nlinarith
  · show (p.Valid ∧ FClass.PRIM p.toProblem ∧ p.toProblem.StrongODSolvable) ↔ _
    rw [eval_qPrim]
    constructor
    · rintro ⟨hv, hprim, hs⟩
      rw [strongOD_iff_of_primitive hprim] at hs
      refine ⟨(0, 0, p.init.dedup, d₀ p), ?_, (primInit_iff p _).2 ⟨hv, hprim, rfl⟩, ?_⟩
      · have hn := sz_le_of_sGood (sGood_init (p := p))
        have hW : cfgBound (sz p) ≤ 100 * (sz p + 1) ^ 3 := by unfold cfgBound; nlinarith
        exact hn.trans hW
      · exact play_complete hs _ _ _ _ (sameOn_of_agree (agree_d₀ hv))
          (setOf_mem_dedup _).symm (inv_d₀ hv) le_rfl
    · rintro ⟨c₀, -, hi, hw⟩
      obtain ⟨hv, hprim, rfl⟩ := (primInit_iff p c₀).1 hi
      refine ⟨hv, hprim, (strongOD_iff_of_primitive hprim).2 ?_⟩
      have h := play_sound _ _ _ _ (inv_d₀ hv) hw
      rw [setOf_mem_dedup] at h
      exact Problem.BeliefSolvable.congr _ h (sameOn_of_agree (agree_d₀ hv).symm)

end FOND
