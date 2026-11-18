import HtnComplexity.Article.NExpPT
import HtnComplexity.Article.ExpSpaceHard
import HtnComplexity.Space.NexpFamily
/-!
# Acyclic HTN planning with a totally ordered initial network is NEXPTIME-hard (Thm. 4.3.7)

**`HTN.Article.thm_4_3_7_acyc`** — `PlanEx^{ACYC ∩ TO-tn_I}_htn` is NEXPTIME-hard.

The article's route: a nondeterministic machine `N` with an exponential time bound is encoded in
an acyclic problem whose solutions write out the accepting runs (counters running in parallel
with the tape, Alford et al.).  The construction and its correctness are those of
`HtnComplexity/TMEnc/` (the repaired encoding `HTN.TMEnc.problemFix`, applied to the normalised
machine `HTN.TMEnc.homingMachine N`); here it is written down by the rendering
`HTN.TMEnc.U.rendU` with an explicit polynomial-size list of methods, computed in polynomial time
(`HtnComplexity/Article/NExpPT.lean`), and brought into the article's normal form.  The empty
word is mapped to a fixed problem.
-/

namespace HTN

namespace Article

open TM Syn Syn.PolyDom PTime TMEnc TMEnc.U

/-! ### Well-formedness of a rendering in normal form -/

section Valid

variable {F A C : Type} [Inhabited A] [DecidableEq A] {P : HTN.Problem F A C (ℕ × ℕ)}
  (R : Rendering P)

theorem shape_desc_lbl (s : Shape A C) (eA : A → ℕ) (eC : C → ℕ) :
    (s.desc eA eC).lbl = cellLbl (s.rows.map fun row => row.map (encLabel eA eC)) := rfl

theorem tnFacts_shape (s : Shape A C) (eA : A → ℕ) (eC : C → ℕ) :
    (s.desc eA eC).ids.Nodup ∧ ((s.desc eA eC).lbl.map Prod.fst).Perm (s.desc eA eC).ids ∧
      ∀ r ∈ (s.desc eA eC).lbl, r.2.1 = false → ∃ a, Sum.inl a ∈ s.rows.flatten ∧ r.2.2 = eA a := by
  refine ⟨by rw [Shape.desc_ids]; exact nodup_cellIds, ?_, fun r hr hf => ?_⟩
  · rw [shape_desc_lbl, Shape.desc_ids, map_fst_cellLbl]; rfl
  · rw [shape_desc_lbl] at hr
    have h := mem_cellLbl hr
    obtain ⟨l, hl, hr2⟩ := List.mem_flatten.1 h
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hl
    obtain ⟨x, hx, hxl⟩ := List.mem_map.1 hr2
    rcases x with a | c
    · refine ⟨a, List.mem_flatten.2 ⟨row, hrow, hx⟩, ?_⟩
      rw [← hxl]; rfl
    · rw [← hxl] at hf; simp [encLabel] at hf

/-- **The normal form of a rendering is well formed**, if its actions are distinct and cover the
actions of its bodies and of its initial network. -/
theorem valid_artOf_rend (hnd : R.acts.Nodup)
    (hb : ∀ p ∈ R.bodies, ∀ a, Sum.inl a ∈ p.2.rows.flatten → a ∈ R.acts)
    (hI : ∀ a, Sum.inl a ∈ R.tnIshape.rows.flatten → a ∈ R.acts) :
    (artOf R.domDesc R.instDesc).Valid := by
  have hnames : R.domDesc.actions.map Prod.fst = R.acts.map R.eA := by
    simp [Rendering.domDesc, DomDesc.actions, Function.comp_def]
  refine valid_artOf ?_ ?_ ?_
  · rw [hnames]; exact hnd.map R.eA_inj
  · obtain ⟨h1, h2, h3⟩ := tnFacts_shape R.tnIshape R.eA R.eC
    refine ⟨h1, h2, fun r hr hf => ?_⟩
    obtain ⟨a, ha, he⟩ := h3 r hr hf
    rw [hnames, he]; exact List.mem_map_of_mem (hI a ha)
  · intro m hm
    simp only [Rendering.domDesc, DomDesc.methods, List.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨h1, h2, h3⟩ := tnFacts_shape p.2 R.eA R.eC
    refine ⟨h1, h2, fun r hr hf => ?_⟩
    obtain ⟨a, ha, he⟩ := h3 r hr hf
    rw [hnames, he]; exact List.mem_map_of_mem (hb p hp a ha)

end Valid

/-! ### The empty word -/

section Empty

/-- The problem without tasks with the goal `g`. -/
def emptyDesc (g : List ℕ) : ProbDesc := (([], []), ([], ([], [], []), g, []))

theorem valid_emptyDesc (g : List ℕ) : (emptyDesc g).Valid :=
  ⟨List.nodup_nil, ⟨List.nodup_nil, by simp [TnDesc.ordList, emptyDesc, ProbDesc.tnI],
    by simp [TnDesc.ordList, emptyDesc, ProbDesc.tnI], by simp [TnDesc.ordList, emptyDesc, ProbDesc.tnI],
    by simp [TnDesc.lbl, TnDesc.ids, emptyDesc, ProbDesc.tnI],
    by simp [TnDesc.lbl, emptyDesc, ProbDesc.tnI]⟩,
    fun m hm => by simp [emptyDesc, ProbDesc.methods] at hm⟩

theorem not_reachable_emptyDesc (g : List ℕ) (c : ℕ) :
    ¬ (emptyDesc g).toProblem.toPos.ReachableName c := by
  intro h
  induction h with
  | tnI ht => simp [Problem.toPos, ProbDesc.toProblem, emptyDesc, ProbDesc.tnI,
      TnDesc.toTaskNetwork, TnDesc.ids] at ht
  | method _ _ _ _ ih => exact ih

theorem isACYC_emptyDesc (g : List ℕ) : (emptyDesc g).toProblem.IsACYC :=
  ⟨fun _ _ => True, ⟨⟨fun c h => absurd h (not_reachable_emptyDesc g c),
    fun c _ _ h => absurd h (not_reachable_emptyDesc g c),
    fun c _ h => absurd h (not_reachable_emptyDesc g c)⟩,
    fun c _ h => absurd h (not_reachable_emptyDesc g c),
    fun _ hm => absurd hm.2 (not_reachable_emptyDesc g _)⟩⟩

theorem isTO_tnI_emptyDesc (g : List ℕ) : (emptyDesc g).toProblem.IsTO_tnI := by
  intro t ht
  simp [Problem.toPos, ProbDesc.toProblem, emptyDesc, ProbDesc.tnI, TnDesc.toTaskNetwork,
    TnDesc.ids] at ht

theorem tnI_emptyDesc_TO (g : List ℕ) :
    (emptyDesc g).tnI.toTaskNetwork.IsTotallyOrdered := by
  intro t ht
  simp [emptyDesc, ProbDesc.tnI, TnDesc.toTaskNetwork, TnDesc.ids] at ht

theorem solvable_emptyDesc_iff (g : List ℕ) : (emptyDesc g).toProblem.Solvable ↔ g = [] := by
  rw [solvable_iff_chain (valid_emptyDesc g) (tnI_emptyDesc_TO g)]
  have hlin : TnDesc.lin (emptyDesc g).tnI = [] := by
    simp [TnDesc.lin, emptyDesc, ProbDesc.tnI, TnDesc.ids, TnDesc.linAt]
  rw [hlin]
  constructor
  · rintro ⟨s', hc, hg, -⟩
    cases hc
    cases g with
    | nil => rfl
    | cons f g =>
      have := hg (show f ∈ {x | x ∈ f :: g} by simp)
      simp [ProbDesc.toProblem, emptyDesc, ProbDesc.init] at this
  · rintro rfl
    refine ⟨_, .nil _, ?_, ?_⟩
    · intro f hf; simp [ProbDesc.toProblem, emptyDesc, ProbDesc.goalPos] at hf
    · simp [ProbDesc.toProblem, emptyDesc, ProbDesc.goalNeg]

end Empty

/-! ### The description of a word -/

section Word

variable {k : ℕ} (N : NTM (Fin k) Space.TapeSym)

/-- The rendering of the encoding of the word `x` with the time bound `K`. -/
noncomputable def rendW (x : List Bool) (K : ℕ) :=
  rendU (homingMachine N) (q := qN) (g := gN) qN_injective gN_injective (markInput N (x.map some)) K

/-- **The article's description of the word `x`.** -/
noncomputable def acDesc (x : List Bool) (K : ℕ) : ProbDesc :=
  artOf (rendW N x K).domDesc (rendW N x K).instDesc

theorem valid_acDesc (x : List Bool) (K : ℕ) : (acDesc N x K).Valid :=
  valid_artOf_rend _ (Finset.nodup_toList _) (fun _ _ a _ => Finset.mem_toList.2 (mem_opFinset_univ a))
    (fun a _ => Finset.mem_toList.2 (mem_opFinset_univ a))

theorem isACYC_acDesc (x : List Bool) (K : ℕ) : (acDesc N x K).toProblem.IsACYC :=
  isACYC_artOf _ (isAcyclic_rendU _ _ _ _ _)

theorem isTO_tnI_acDesc (x : List Bool) (K : ℕ) : (acDesc N x K).toProblem.IsTO_tnI :=
  isTO_tnI_artOf _ (isRooted_rendU _ _ _ _ _).isTO

theorem solvable_acDesc_iff (x : List Bool) (K : ℕ) :
    (acDesc N x K).toProblem.Solvable ↔
      (problemFix (homingMachine N) (markInput N (x.map some)) K).Solvable := by
  rw [acDesc, solvable_artOf_iff]
  exact solvable_rendU_iff _ _ _ _ _

end Word

/-! ### Polynomial time -/

section PTime

variable {k : ℕ} (N : NTM (Fin k) Space.TapeSym)

/-- The rows of the method of `sI`, numbered. -/
def rowsSI (K : ℕ) : List (List (Bool × ℕ)) :=
  ((initChainsFix (Q := QH k) (Γ := GH) K) ++ [[Sum.inr TMTask.done]]).map
    fun row : List (TMAct (QH k) GH ⊕ TMTask (QH k) GH) => row.map labH

theorem sIdesc_eq (K : ℕ) :
    (sIShapeU (Q := QH k) (Γ := GH) K).desc (encTMAct qN gN) (encTMTask gN) =
      gridAfterDesc (rowsSI (k := k) K) 3 := rfl

theorem tailOrd_rowsSI (K : ℕ) : tailOrd (rowsSI (k := k) K) 3 = tailOrd (rowsSI (k := k) 0) 3 := by
  simp [tailOrd, gridRow, rowsSI, initChainsFix, headChainFix, List.range_succ]

theorem methods_rendW (x : List Bool) (K : ℕ) :
    (rendW N x K).domDesc.methods =
      (methodsNum N x K).map (fun b => (b.1, gridDesc b.2)) ++
        [(encTMTask gN (TMTask.sI : TMTask (QH k) GH), gridAfterDesc (rowsSI (k := k) K) 3)] := by
  rw [← methodsL_num]
  simp only [rendW, rendU, Rendering.domDesc, DomDesc.methods, List.map_append, List.map_map,
    List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, encB, Shape.desc, gridAfterDescOf, SpaceEnc.gridAfterDesc_zero]
    rfl
  · rw [sIdesc_eq]

/-- The actions of the description, which do not depend on the word. -/
noncomputable def actsW : List ActionDesc := (rendW N [] 0).domDesc.actions

theorem actions_rendW (x : List Bool) (K : ℕ) : (rendW N x K).domDesc.actions = actsW N := by
  simp only [actsW, rendW, rendU, Rendering.domDesc, DomDesc.actions]

/-- The instance of the description, which does not depend on the word. -/
noncomputable def instW : InstDesc := (rendW N [] 0).instDesc

theorem instDesc_rendW (x : List Bool) (K : ℕ) : (rendW N x K).instDesc = instW N := by
  simp only [instW, rendW, rendU, Rendering.instDesc]

variable {α : Type} [BEnc α]

theorem pt_rowsSI {K : α → ℕ} (hK : PT K) : PT fun a => rowsSI (k := k) (K a) := by
  unfold rowsSI
  simp only [initChainsFix, headChainFix, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil]
  exact PT.cons (PT.cons (pt_lab_inr (pt_eT_cSeq _ hK)) (PT.cons (PT.const _) (PT.cons (PT.const _)
    (PT.single (pt_lab_inr (pt_eT_cSeq _ (PT.pred hK))))))) (PT.cons (PT.single (pt_lab_inr
      (pt_eT_checkers (PT.succ hK)))) (PT.cons (PT.cons (PT.const _) (PT.single (pt_lab_inr
        (pt_eT_cSeq _ hK)))) (PT.const _)))

theorem pt_gridAfter_rowsSI {K : α → ℕ} (hK : PT K) :
    PT fun a => gridAfterDesc (rowsSI (k := k) (K a)) 3 := by
  have h := pt_gridDesc (pt_rowsSI (k := k) hK)
  refine (PT.pair (PT.fst.comp h) (PT.pair (PT.append (PT.fst.comp (PT.snd.comp h))
    (PT.const (tailOrd (rowsSI (k := k) 0) 3))) (PT.snd.comp (PT.snd.comp h)))).of_eq fun a => ?_
  simp only [gridAfterDesc, gridDesc, tailOrd_rowsSI]

theorem pt_methodsW {x : α → List Bool} {K : α → ℕ} (hx : PT x) (hK : PT K) :
    PT fun a => (rendW N (x a) (K a)).domDesc.methods := by
  have hM0 : PT fun a => (methodsNum N (x a) (K a)).map (fun b => (b.1, gridDesc b.2)) ++
      [(encTMTask gN (TMTask.sI : TMTask (QH k) GH), gridAfterDesc (rowsSI (k := k) (K a)) 3)] :=
    PT.append (PT.map (pt_methodsNum N hx hK) (PT.pair (PT.fst.comp PT.snd)
      (pt_gridDesc (PT.snd.comp PT.snd)))) (PT.single (PT.pair (PT.const _)
        (pt_gridAfter_rowsSI hK)))
  exact hM0.of_eq fun a => (methods_rendW N (x a) (K a)).symm

theorem pt_domW {x : α → List Bool} {K : α → ℕ} (hx : PT x) (hK : PT K) :
    PT fun a => (rendW N (x a) (K a)).domDesc := by
  have h := PT.pair (PT.const (α := α) (actsW N)) (pt_methodsW N hx hK)
  refine h.of_eq fun a => ?_
  rw [← actions_rendW N (x a) (K a)]
  exact Prod.mk.eta

theorem pt_instW {x : α → List Bool} {K : α → ℕ} :
    PT fun a => (rendW N (x a) (K a)).instDesc :=
  (PT.const (instW N)).of_eq fun a => (instDesc_rendW N _ _).symm

theorem pt_acDesc {x : α → List Bool} {K : α → ℕ} (hx : PT x) (hK : PT K) :
    PT fun a => acDesc N (x a) (K a) :=
  pt_artOf (pt_domW N hx hK) (pt_instW N)

end PTime

/-! ### The theorem -/

/-- **Theorem 4.3.7** (first part). `PlanEx^{ACYC ∩ TO-tn_I}_htn` is NEXPTIME-hard. -/
theorem thm_4_3_7_acyc : Cx.Hard Cx.NEXPTIME (PlanEx fun P => P.IsACYC ∧ P.IsTO_tnI) := by
  classical
  rintro L ⟨k, N, p, hN, hL⟩
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen (p + Polynomial.X)
  set Kf : List Bool → ℕ := fun x => 2 * 2 ^ (g x).length + 1
  have hKf : PT Kf := by
    have hpow : PT fun x => 2 ^ (g x).length :=
      (PT.ofBits (PT.append (PT.map (g := fun _ _ => false) hg (PT.const false))
        (PT.const [true]))).of_eq fun x => by
        rw [natOfBits_append]; simp [natOfBits_replicate_false, natOfBits_cons]
    exact PT.affine 2 1 hpow
  set c₀ : ProbDesc := if L [] then emptyDesc [] else emptyDesc [0]
  set f : List Bool → ProbDesc := fun x => if x = [] then c₀ else acDesc N x (Kf x)
  have hf : PT f := PT.ite (PT.eq PT.id (PT.const [])) (PT.const c₀) (pt_acDesc N PT.id hKf)
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun x => ?_⟩
  show L x ↔ codeLang ProbDesc (fun p => p.Valid ∧ (p.toProblem.IsACYC ∧ p.toProblem.IsTO_tnI) ∧
    p.toProblem.Solvable) (enc (f x))
  rw [codeLang_enc]
  by_cases hx : x = []
  · subst hx
    simp only [f, if_true, c₀]
    by_cases h0 : L []
    · rw [if_pos h0]
      exact ⟨fun _ => ⟨valid_emptyDesc _, ⟨isACYC_emptyDesc _, isTO_tnI_emptyDesc _⟩,
        (solvable_emptyDesc_iff _).2 rfl⟩, fun _ => h0⟩
    · rw [if_neg h0]
      simp only [h0, false_iff]
      rintro ⟨-, -, hs⟩
      exact absurd ((solvable_emptyDesc_iff _).1 hs) (by simp)
  · simp only [f, hx, if_false]
    have hn : x.length ≠ 0 := by simpa using hx
    have hw1 : 1 ≤ (x.map some).length := by simp; omega
    have hKb : Kf x = 2 * Space.kBound p x.length + 1 := by
      simp only [Kf, Space.kBound, hglen, Polynomial.eval_add, Polynomial.eval_X]
    have hle : 2 ^ p.eval x.length ≤ Space.kBound p x.length :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hK : (x.map some).length ≤ Space.kBound p x.length := by
      rw [List.length_map]
      exact le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hclock : ClockedAt N (x.map some) (Space.kBound p x.length) :=
      fun m hm => N.acceptsWithin_mono hle (hN x m hm)
    rw [hL x, hKb, solvable_acDesc_iff,
      solvable_problemFix_homingMachine_iff N hw1 hK le_rfl hclock]
    unfold Space.NTMLang NTM.AcceptsExp
    rw [List.length_map]
    exact ⟨fun h => ⟨valid_acDesc N x _, ⟨isACYC_acDesc N x _, isTO_tnI_acDesc N x _⟩,
      N.acceptsWithin_mono hle h⟩, fun h => hN x _ h.2.2⟩

end Article

end HTN
