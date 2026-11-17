import FondHtn.StrongOD.RegDesc
import FondHtn.Upper.SemiDec
/-!
# Strong OD plan existence is semi-decidable ([CB21, Thm. 3.1], strong OD part)

A certificate (`FOND.SOD.SCert`) lists a description decomposition sequence from `tn_I`
(descriptions and steps) to a primitive description `d'`, and an accepting run of the
nondeterministic depth-first evaluation (`HTN.Syn.PolyDom.dfsStep`) of the play game of `d'`
from `(0, 0, s_I, d')`.  Its check (`FOND.SOD.sdCheck`) is polynomial time, hence computable,
and a description is in the language iff some certificate passes
(`FOND.SOD.strongOD_iff_cert`, using `FOND.SOD.strongOD_iff_desc`, `FOND.SOD.play_sound`,
`FOND.SOD.play_complete`, `HTN.Syn.PolyDom.dfs_sound`, `HTN.Syn.PolyDom.dfs_complete`).

* **`FOND.strongOD_semiDecidable`** — `PlanExFM strongOD UNRES` is semi-decidable;
* **`FOND.thm_3_1_strongOD`** — semi-decidable and undecidable.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ## Polynomial time is computable -/

theorem computable₂_of_pt {h : List Bool × List Bool → Bool} (hh : PT h) :
    Computable₂ fun w b => h (w, b) := by
  obtain ⟨H, hH, hHh⟩ := hh
  have hl : Computable lift := (polyTimeFun_of_uc uc_lift).computable
  have hc : Computable fun x : List Bool × List Bool => H (lift x.1 ++ lift x.2) :=
    (polyTimeFun_of_uc hH).computable.comp
      (Primrec.list_append.to_comp.comp (hl.comp Computable.fst) (hl.comp Computable.snd))
  refine (((Primrec.list_getD false).to_comp.comp hc (Computable.const 0)).of_eq fun x => ?_).to₂
  obtain ⟨w, b⟩ := x
  have := hHh (w, b)
  rw [enc_prod] at this
  show (H (enc w ++ enc b)).getD 0 false = _
  rw [this]; rfl

/-! ## Chains as indexed lists -/

theorem exists_chain_list {β : Type} [Inhabited β] {R : β → β → Prop} {a b : β}
    (h : Relation.ReflTransGen R a b) : ∃ L : List β, L ≠ [] ∧ L.headI = a ∧
      L.getI (L.length - 1) = b ∧ ∀ i, i + 1 < L.length → R (L.getI i) (L.getI (i + 1)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], by simp, rfl, rfl, fun i hi => by simp at hi⟩
  | @head a c hac _ ih =>
    obtain ⟨L, hL, hh, hl, hR⟩ := ih
    obtain ⟨x, L', rfl⟩ := List.exists_cons_of_ne_nil hL
    simp only [List.headI_cons] at hh
    subst hh
    refine ⟨a :: x :: L', by simp, rfl, ?_, fun i hi => ?_⟩
    · simpa using hl
    · rcases i with _ | i
      · simpa using hac
      · simpa using hR i (by simpa using hi)

theorem chain_of_list {β : Type} [Inhabited β] {R : β → β → Prop} :
    ∀ (L : List β) (j : ℕ), j < L.length → (∀ i, i + 1 < L.length → R (L.getI i) (L.getI (i + 1))) →
      Relation.ReflTransGen R (L.getI 0) (L.getI j) := by
  intro L j
  induction j with
  | zero => exact fun _ _ => Relation.ReflTransGen.refl
  | succ j ih =>
    intro hj hR
    exact (ih (by omega) hR).tail (hR j hj)

/-! ## Finitely many reachable configurations -/

section Finite

variable {α σ : Type} {succs : α × σ → List σ} {a : α}

/-- The configurations reachable in `n` steps, as a list. -/
def lvl (succs : α × σ → List σ) (a : α) : ℕ → σ → List σ
  | 0, c => [c]
  | n + 1, c => (succs (a, c)).flatMap (lvl succs a n)

theorem mem_lvl : ∀ (n : ℕ) (c c' : σ), GameReach succs a n c c' → c' ∈ lvl succs a n c := by
  intro n
  induction n with
  | zero => rintro c c' rfl; simp [lvl]
  | succ n ih =>
    rintro c c' ⟨c₁, h₁, hr⟩
    exact List.mem_flatMap.2 ⟨c₁, h₁, ih c₁ c' hr⟩

theorem exists_bound (f : σ → ℕ) (k : ℕ) (c : σ) :
    ∃ B, ∀ n < k, ∀ c', GameReach succs a n c c' → f c' ≤ B := by
  refine ⟨(((List.range k).flatMap fun n => lvl succs a n c).map f).sum, fun n hn c' hr => ?_⟩
  exact List.le_sum_of_mem (List.mem_map.2 ⟨c', List.mem_flatMap.2
    ⟨n, List.mem_range.2 hn, mem_lvl n c c' hr⟩, rfl⟩)

end Finite

/-! ## The certificate and its check -/

/-- A certificate: descriptions, decomposition steps, and the run of stacks. -/
abbrev SCert : Type := List TnDesc × List (ℕ × MethodDesc) × List (List (ℕ × GCfg))

/-- One decomposition step on descriptions, as a test. -/
def stepB (p : FProbDesc) (d : TnDesc) (q : ℕ × MethodDesc) (d' : TnDesc) : Bool :=
  decide (q.1 ∈ d.ids) && decide (lblOf d q.1 = (true, q.2.1)) && decide (q.2 ∈ p.methods) &&
    decide (d' = decDesc d q.1 q.2)

/-- The root of the play game of a description. -/
def rootSt (p : FProbDesc) (d : TnDesc) : List (ℕ × GCfg) :=
  [(2 * d.ids.length, ((0 : ℕ), (0 : ℕ), p.init.dedup, d))]

/-- **The certificate check.** -/
def sdCheck (x : FProbDesc × SCert) : Bool :=
  x.1.validB && decide (x.2.1.length = x.2.2.1.length + 1) && decide (x.2.1.headI = d₀ x.1) &&
    (List.range x.2.2.1.length).all (fun i =>
      stepB x.1 (x.2.1.getI i) (x.2.2.1.getI i) (x.2.1.getI (i + 1))) &&
    (x.2.1.getI x.2.2.1.length).ids.all (fun y => !(lblOf (x.2.1.getI x.2.2.1.length) y).1) &&
    !x.2.2.2.isEmpty && decide (x.2.2.2.headI = rootSt x.1 (x.2.1.getI x.2.2.1.length)) &&
    decide (x.2.2.2.getI x.2.2.2.tail.length = []) &&
    (List.range x.2.2.2.tail.length).all (fun i =>
      dfsStep gacc guni gsuccs (x.1, x.2.2.2.getI i, x.2.2.2.getI (i + 1)))

theorem pt_sdCheck : PT sdCheck := by
  have hp : PT fun x : FProbDesc × SCert => x.1 := PT.fst
  have hD : PT fun x : FProbDesc × SCert => x.2.1 := PT.fst.comp PT.snd
  have hS : PT fun x : FProbDesc × SCert => x.2.2.1 := PT.fst.comp (PT.snd.comp PT.snd)
  have hR : PT fun x : FProbDesc × SCert => x.2.2.2 := PT.snd.comp (PT.snd.comp PT.snd)
  have hlast : PT fun x : FProbDesc × SCert => x.2.1.getI x.2.2.1.length :=
    PT.getI hD (PT.length hS)
  have hstep : PT fun z : (FProbDesc × TnDesc) × (ℕ × MethodDesc) × TnDesc =>
      stepB z.1.1 z.1.2 z.2.1 z.2.2 := by
    unfold stepB
    have hd := PT.snd.comp (PT.fst (α := FProbDesc × TnDesc) (β := (ℕ × MethodDesc) × TnDesc))
    have hq := PT.fst.comp (PT.snd (α := FProbDesc × TnDesc) (β := (ℕ × MethodDesc) × TnDesc))
    exact PT.and (PT.and (PT.and (PT.elem (PT.fst.comp hd) (PT.fst.comp hq))
      (PT.eq (pt_lblOf hd (PT.fst.comp hq)) (PT.pair (PT.const true) (PT.fst.comp (PT.snd.comp hq)))))
      ((PT.elem (PT.snd.comp (PT.fst.comp (PT.fst.comp PT.fst))) (PT.snd.comp hq)).of_eq
        fun _ => by congr))
      (PT.eq (PT.snd.comp PT.snd) (pt_decDesc.comp (PT.pair hd (PT.pair (PT.fst.comp hq)
        (PT.snd.comp hq)))))
  have hroot : PT fun x : FProbDesc × SCert => rootSt x.1 (x.2.1.getI x.2.2.1.length) := by
    unfold rootSt
    exact PT.single (PT.pair (PT.affine 2 0 (PT.length (PT.fst.comp hlast)))
      (PT.pair (PT.const 0) (PT.pair (PT.const 0) (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp hp)))
        hlast))))
  unfold sdCheck
  refine PT.and (PT.and (PT.and (PT.and (PT.and (PT.and (PT.and (PT.and
    (FProbDesc.pt_validB.comp hp) (PT.eq (PT.length hD) (PT.succ (PT.length hS))))
    (PT.eq (PT.headI hD) (pt_d₀.comp hp))) ?_) ?_) (PT.not (PT.isEmpty hR)))
    (PT.eq (PT.headI hR) hroot)) (PT.eq (PT.getI hR (PT.length (PT.tail hR))) (PT.const [])))
    ?_
  · exact PT.all (PT.rangeLength hS) (hstep.comp (PT.pair (PT.pair (hp.comp PT.fst)
      (PT.getI (hD.comp PT.fst) PT.snd)) (PT.pair (PT.getI (hS.comp PT.fst) PT.snd)
        (PT.getI (hD.comp PT.fst) (PT.succ PT.snd)))))
  · exact PT.all (PT.fst.comp hlast) (PT.not (PT.fst.comp (pt_lblOf (hlast.comp PT.fst) PT.snd)))
  · exact PT.all (PT.rangeLength (PT.tail hR)) ((pt_dfsStep pt_gacc pt_guni pt_gsuccs).comp
      (PT.pair (hp.comp PT.fst) (PT.pair (PT.getI (hR.comp PT.fst) PT.snd)
        (PT.getI (hR.comp PT.fst) (PT.succ PT.snd)))))

/-! ## Soundness and completeness of the check -/

theorem getI_zero_eq {β : Type} [Inhabited β] (L : List β) : L.getI 0 = L.headI := by
  cases L <;> rfl

theorem getI_map_range {β : Type} [Inhabited β] (f : ℕ → β) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getI i = f i := by
  rw [List.getI_eq_getElem _ (by simpa using h)]
  simp

variable {p : FProbDesc}

theorem stepB_iff {d d' : TnDesc} {q : ℕ × MethodDesc} :
    stepB p d q d' = true ↔ q.1 ∈ d.ids ∧ lblOf d q.1 = (true, q.2.1) ∧ q.2 ∈ p.methods ∧
      d' = decDesc d q.1 q.2 := by
  simp [stepB, and_assoc]

/-- **Strong OD solvability by certificates.** -/
theorem strongOD_iff_cert (p : FProbDesc) :
    (p.Valid ∧ p.toProblem.StrongODSolvable) ↔ ∃ c : SCert, sdCheck (p, c) = true := by
  constructor
  · rintro ⟨hp, hs⟩
    obtain ⟨d', hr, hprim, hbs⟩ := (strongOD_iff_desc hp).1 hs
    obtain ⟨-, -, -, hinv⟩ := dreach_sound hp hr _ (inv_d₀ hp) _ (agree_d₀ hp)
    -- the decomposition sequence
    obtain ⟨L, hL, hLh, hLl, hLs⟩ := exists_chain_list hr
    classical
    let st : ℕ → ℕ × MethodDesc := fun i =>
      if h : DStep p (L.getI i) (L.getI (i + 1)) then (h.choose, h.choose_spec.choose) else default
    have hst : ∀ i, i + 1 < L.length → stepB p (L.getI i) (st i) (L.getI (i + 1)) = true := by
      intro i hi
      have h := hLs i hi
      simp only [st, dif_pos h]
      obtain ⟨hx, hl, he, hd⟩ := h.choose_spec.choose_spec
      exact stepB_iff.2 ⟨hx, hl, he, hd⟩
    let S := (List.range (L.length - 1)).map st
    have hSl : S.length = L.length - 1 := by simp [S]
    have hLlen : 1 ≤ L.length := List.length_pos_of_ne_nil hL
    have hlast : L.getI S.length = d' := by rw [hSl]; exact hLl
    -- the run
    have hw := play_complete hbs (2 * d'.ids.length) 0 p.init.dedup d' (sameOn_refl _)
      (setOf_mem_dedup _).symm hinv le_rfl
    obtain ⟨B, hB⟩ := exists_bound (succs := gsuccs) (a := p) (fun c => sz (gsuccs (p, c)))
      (2 * d'.ids.length) ((0 : ℕ), (0 : ℕ), p.init.dedup, d')
    have hrun := dfs_complete (acc := gacc) (uni := guni) (succs := gsuccs) (a := p) (B := B)
      (K := 2 * (2 * d'.ids.length) + 1) (N := sz ([] : List (ℕ × GCfg)) + 2 * d'.ids.length *
        dfsCost B (2 * (2 * d'.ids.length) + 1)) _ _ [] hw
      (fun k' hk' => (sz_nat_le k').trans (by omega)) hB le_rfl
    obtain ⟨Rn, hRn, hRh, hRl, hRs⟩ := exists_chain_list (hrun.mono fun _ _ h => h.1)
    refine ⟨(L, S, Rn), ?_⟩
    simp only [sdCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, hLh⟩, ?_⟩, ?_⟩, hRn⟩, ?_⟩, ?_⟩, ?_⟩
    · exact (FProbDesc.validB_iff p).2 hp
    · omega
    · intro i hi
      rw [getI_map_range st (by omega)]
      exact hst i (by omega)
    · intro y hy
      rw [hlast] at hy ⊢
      simp [hprim y hy]
    · rw [hlast]; exact hRh
    · rw [List.length_tail]; exact hRl
    · intro i hi
      rw [List.length_tail] at hi
      exact hRs i (by omega)
  · rintro ⟨⟨D, S, Rn⟩, hc⟩
    simp only [sdCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv, hDl⟩, hDh⟩, hsteps⟩, hprim⟩, hRn⟩, hRh⟩, hRl⟩, hruns⟩ := hc
    have hp := (FProbDesc.validB_iff p).1 hv
    refine ⟨hp, (strongOD_iff_desc hp).2 ⟨D.getI S.length, ?_, fun y hy => ?_, ?_⟩⟩
    · have := chain_of_list (R := DStep p) D S.length (by omega) fun i hi => by
        obtain ⟨hx, hl, he, hd⟩ := stepB_iff.1 (hsteps i (by omega))
        exact ⟨_, _, hx, hl, he, hd⟩
      rwa [getI_zero_eq, hDh] at this
    · simpa using hprim y hy
    · have hchain : Relation.ReflTransGen (DStep p) (d₀ p) (D.getI S.length) := by
        have := chain_of_list (R := DStep p) D S.length (by omega) fun i hi => by
          obtain ⟨hx, hl, he, hd⟩ := stepB_iff.1 (hsteps i (by omega))
          exact ⟨_, _, hx, hl, he, hd⟩
        rwa [getI_zero_eq, hDh] at this
      obtain ⟨-, -, -, hinv⟩ := dreach_sound hp hchain _ (inv_d₀ hp) _ (agree_d₀ hp)
      have hrun := chain_of_list (R := fun A B => dfsStep gacc guni gsuccs (p, A, B) = true) Rn
        Rn.tail.length (by rw [List.length_tail]; have := List.length_pos_of_ne_nil hRn; omega)
        fun i hi => hruns i (by rw [List.length_tail]; omega)
      rw [hRl, getI_zero_eq, hRh] at hrun
      have hwon := dfs_sound (fun _ _ h => h) hrun _ (List.mem_singleton_self _)
      have hb := play_sound _ 0 _ _ hinv hwon
      rwa [setOf_mem_dedup] at hb

/-! ## The language -/

/-- The check on raw strings. -/
def sdCheckRaw (x : List Bool × List Bool) : Bool :=
  isCode FProbDesc x.1 && isCode SCert x.2 &&
    sdCheck ((decR x.1 : FProbDesc × List Bool).1, (decR x.2 : SCert × List Bool).1)

theorem pt_sdCheckRaw : PT sdCheckRaw := by
  unfold sdCheckRaw
  exact PT.and (PT.and ((pt_isCode FProbDesc).comp PT.fst) ((pt_isCode SCert).comp PT.snd))
    (pt_sdCheck.comp (PT.pair (PT.fst.comp (BDec.pt_decR.comp PT.fst))
      (PT.fst.comp (BDec.pt_decR.comp PT.snd))))

theorem planEx_strongOD_iff (w : List Bool) :
    PlanExFM .strongOD FClass.UNRES w ↔ ∃ b, sdCheckRaw (w, b) = true := by
  constructor
  · rintro ⟨p, rfl, hp, -, hs⟩
    obtain ⟨c, hc⟩ := (strongOD_iff_cert p).1 ⟨hp, hs⟩
    refine ⟨enc c, ?_⟩
    simp only [sdCheckRaw, Bool.and_eq_true, (isCode_iff _).2 ⟨p, rfl⟩, (isCode_iff _).2 ⟨c, rfl⟩,
      decR_enc', hc, and_self]
  · rintro ⟨b, hb⟩
    simp only [sdCheckRaw, Bool.and_eq_true] at hb
    obtain ⟨⟨hw, hbc⟩, hc⟩ := hb
    obtain ⟨p, rfl⟩ := (isCode_iff _).1 hw
    obtain ⟨c, rfl⟩ := (isCode_iff _).1 hbc
    rw [decR_enc', decR_enc'] at hc
    obtain ⟨hp, hs⟩ := (strongOD_iff_cert p).2 ⟨c, hc⟩
    exact ⟨p, rfl, hp, trivial, hs⟩

end SOD

open SOD in
/-- **[CB21, Thm. 3.1], strong OD**: strong OD plan existence is semi-decidable. -/
theorem strongOD_semiDecidable : Cx.SemiDecidable (PlanExFM .strongOD FClass.UNRES) :=
  (rePred_exists (computable₂_of_pt pt_sdCheckRaw)).of_eq fun w => (planEx_strongOD_iff w).symm

/-- **[CB21, Thm. 3.1] for strong OD**: semi-decidable but undecidable. -/
theorem thm_3_1_strongOD : Cx.SemiDecidable (PlanExFM .strongOD FClass.UNRES) ∧
    ¬ Cx.Decidable (PlanExFM .strongOD FClass.UNRES) :=
  ⟨strongOD_semiDecidable, undecidable_fm .strongOD⟩

/-- **[CB21, Thm. 3.1] complete**: all four fixed-method criteria are semi-decidable but
undecidable. -/
theorem thm_3_1_all : ∀ c : FMCrit, Cx.SemiDecidable (PlanExFM c FClass.UNRES) ∧
    ¬ Cx.Decidable (PlanExFM c FClass.UNRES)
  | .weakLD => thm_3_1.1
  | .strongLD => thm_3_1.2.1
  | .weakOD => thm_3_1.2.2
  | .strongOD => thm_3_1_strongOD

end FOND
