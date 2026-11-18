import HtnComplexity.Article.StripsShort
/-!
# Acyclic totally ordered problems are PSPACE-hard (Thm. 4.3.4)

The article's encoding (after Alford et al.): with `N = |V|`, the compound tasks
`c_1, …, c_{N+1}` (here the names `1, …, N + 1`), the methods `c_i → c_{i+1} c_{i+1}` for
`i ≤ N`, `c_{N+1} → p` for every action `p` and `c_{N+1} → ε`, and the initial task network
`c_1` (`HTN.Article.acycOfStrips`).  The problem is acyclic and totally ordered; its valid
decomposition trees yield exactly the sequences of at most `2 ^ N` actions, and a STRIPS problem
with a plan has one with fewer than `2 ^ N` actions (`HTN.Article.exists_short_plan`), so it has
a solution iff the STRIPS problem has a plan.

* **`HTN.Article.thm_4_3_4`** — `PlanEx^{ACYC∩TO}` and `PlanEx^{ACYC∩TO-M}` are PSPACE-hard.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-- The network `c c` of a doubling method. -/
def dblTn (c : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, true, c), (1, true, c)])

/-- The network `p` of an action method. -/
def leafTn (p : ℕ) : TnDesc := ([0], [], [(0, false, p)])

/-- The network of the single compound task `c_1`. -/
def rootTn1 : TnDesc := ([0], [], [(0, true, 1)])

/-- The methods of the encoding. -/
def acycMethods (d : StripsDesc) : List MethodDesc :=
  (List.range d.nV).map (fun i => (i + 1, dblTn (i + 2))) ++
    (d.nV + 1, emptyTnD) :: d.actions.map fun a => (d.nV + 1, leafTn a.name)

/-- **The acyclic encoding of a STRIPS problem** (Thm. 4.3.4). -/
def acycOfStrips (d : StripsDesc) : ProbDesc :=
  ((d.actions, acycMethods d), (d.init, rootTn1, d.goalPos, d.goalNeg))

/-! ### The networks -/

theorem dblTn_T (c : ℕ) : (dblTn c).toTaskNetwork.T = {0, 1} := by
  simp [dblTn, TnDesc.toTaskNetwork, TnDesc.ids]

theorem dblTn_ord (c : ℕ) : (dblTn c).toTaskNetwork.ord 0 1 := by
  refine ⟨by simp [dblTn, TnDesc.ids], by simp [dblTn, TnDesc.ids],
    .single (by simp [TnDesc.listRel, dblTn, TnDesc.ordList]), fun h => ?_⟩
  obtain ⟨e, he, -⟩ := Relation.TransGen.head'_iff.1 h
  simp [TnDesc.listRel, dblTn, TnDesc.ordList] at he

theorem dblTn_α (c : ℕ) {t : ℕ} (ht : t ∈ (dblTn c).toTaskNetwork.T) :
    (dblTn c).toTaskNetwork.α t = Sum.inr c := by
  rw [dblTn_T] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> simp [dblTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

theorem leafTn_T (p : ℕ) : (leafTn p).toTaskNetwork.T = {0} := by
  simp [leafTn, TnDesc.toTaskNetwork, TnDesc.ids]

theorem leafTn_α (p : ℕ) : (leafTn p).toTaskNetwork.α 0 = Sum.inl p := by
  simp [leafTn, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

theorem rootTn1_T : rootTn1.toTaskNetwork.T = {0} := by
  simp [rootTn1, TnDesc.toTaskNetwork, TnDesc.ids]

theorem rootTn1_α : rootTn1.toTaskNetwork.α 0 = Sum.inr 1 := by
  simp [rootTn1, TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl, List.lookup]

theorem acyc_methods_cases (d : StripsDesc) {m : Method ℕ ℕ ℕ}
    (hm : m ∈ (acycOfStrips d).toProblem.methods) :
    (∃ i < d.nV, m = MethodDesc.toMethod (i + 1, dblTn (i + 2))) ∨
      m = MethodDesc.toMethod (d.nV + 1, emptyTnD) ∨
      ∃ a ∈ d.actions, m = MethodDesc.toMethod (d.nV + 1, leafTn a.name) := by
  obtain ⟨e, he, rfl⟩ := hm
  simp only [ProbDesc.methods, acycOfStrips, acycMethods, List.mem_append, List.mem_map,
    List.mem_range, List.mem_cons] at he
  rcases he with ⟨i, hi, rfl⟩ | rfl | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)

/-! ### The trees -/

/-- Valid trees for `c_{N+1-j}` yield at most `2 ^ j` declared actions. -/
theorem acyc_yield (d : StripsDesc) : ∀ j ≤ d.nV, ∀ (dt : DTree ℕ ℕ ℕ) (π : List ℕ),
    dt.Valid (acycOfStrips d).toProblem.methods (Sum.inr (d.nV + 1 - j)) → dt.Yield π →
      π.length ≤ 2 ^ j ∧ ∀ a ∈ π, a ∈ d.actions.map ActDesc.name := by
  intro j
  induction j with
  | zero =>
    intro _ dt π hv hy
    obtain ⟨m, ch, rfl⟩ := DTree.Valid.eq_node_of_inr hv
    obtain ⟨-, hm, hc, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hmerge⟩ := hy.node_inv
    rcases acyc_methods_cases d hm with ⟨i, hi, rfl⟩ | rfl | ⟨a, ha, rfl⟩
    · simp [MethodDesc.toMethod] at hc; omega
    · rw [(ordMerge_empty emptyTnD_T).1 hmerge]; simp
    · simp only [MethodDesc.toMethod] at hmerge hch hys
      rw [(ordMerge_single (TnDesc.toTaskNetwork_wf _) (leafTn_T _)).1 hmerge]
      have h0 := hch 0 (by rw [leafTn_T]; simp)
      rw [leafTn_α] at h0
      have hy0 := hys 0 (by rw [leafTn_T]; simp)
      rw [DTree.Valid.eq_leaf_of_inl h0] at hy0
      rw [DTree.Yield.leaf_inv hy0]
      exact ⟨by simp, fun b hb => by simp at hb; subst hb; exact List.mem_map.2 ⟨a, ha, rfl⟩⟩
  | succ j ih =>
    intro hj dt π hv hy
    obtain ⟨m, ch, rfl⟩ := DTree.Valid.eq_node_of_inr hv
    obtain ⟨-, hm, hc, hch⟩ := hv.node_inv
    obtain ⟨ys, hys, hmerge⟩ := hy.node_inv
    rcases acyc_methods_cases d hm with ⟨i, hi, rfl⟩ | rfl | ⟨a, ha, rfl⟩
    · simp only [MethodDesc.toMethod] at hc hmerge hch hys
      rw [(ordMerge_pair (TnDesc.toTaskNetwork_wf _) (dblTn_T _) (by decide) (dblTn_ord _)).1 hmerge]
      have hc' : i + 2 = d.nV + 1 - j := by omega
      have h0 := hch 0 (by rw [dblTn_T]; simp)
      have h1 := hch 1 (by rw [dblTn_T]; simp)
      rw [dblTn_α _ (by rw [dblTn_T]; simp), hc'] at h0 h1
      obtain ⟨l0, d0⟩ := ih (by omega) _ _ h0 (hys 0 (by rw [dblTn_T]; simp))
      obtain ⟨l1, d1⟩ := ih (by omega) _ _ h1 (hys 1 (by rw [dblTn_T]; simp))
      refine ⟨by simp only [List.length_append, pow_succ]; omega, fun b hb => ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · exact d0 b hb
      · exact d1 b hb
    · simp [MethodDesc.toMethod] at hc; omega
    · simp [MethodDesc.toMethod] at hc; omega

/-- Every sequence of at most `2 ^ j` declared actions is the yield of a valid tree for
`c_{N+1-j}`. -/
theorem acyc_tree (d : StripsDesc) : ∀ j ≤ d.nV, ∀ π : List ℕ, π.length ≤ 2 ^ j →
    (∀ a ∈ π, a ∈ d.actions.map ActDesc.name) →
    ∃ dt : DTree ℕ ℕ ℕ, dt.Valid (acycOfStrips d).toProblem.methods (Sum.inr (d.nV + 1 - j)) ∧
      dt.Yield π := by
  intro j
  induction j with
  | zero =>
    intro _ π hl hdecl
    simp only [pow_zero] at hl
    rcases π with _ | ⟨p, _ | ⟨q, π⟩⟩
    · refine ⟨.node (d.nV + 1) (MethodDesc.toMethod (d.nV + 1, emptyTnD)) (fun _ => .leaf 0),
        .node ⟨(d.nV + 1, emptyTnD), by simp [ProbDesc.methods, acycOfStrips, acycMethods], rfl⟩
          (by simp [MethodDesc.toMethod]) (fun t ht => by
            simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht), ?_⟩
      exact .node (fun _ => []) (fun t ht => by
        simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht)
        ((ordMerge_empty emptyTnD_T).2 rfl)
    · obtain ⟨a, ha, hap⟩ := List.mem_map.1 (hdecl p (by simp))
      refine ⟨.node (d.nV + 1) (MethodDesc.toMethod (d.nV + 1, leafTn p)) (fun _ => .leaf p),
        .node ⟨(d.nV + 1, leafTn p), by
          simp only [ProbDesc.methods, acycOfStrips, acycMethods, List.mem_append, List.mem_map,
            List.mem_cons]
          exact Or.inr (Or.inr ⟨a, ha, by rw [hap]⟩), rfl⟩ (by simp [MethodDesc.toMethod])
          (fun t ht => ?_), ?_⟩
      · simp only [MethodDesc.toMethod, leafTn_T, Finset.mem_singleton] at ht
        subst ht
        show DTree.Valid _ (DTree.leaf p) ((leafTn p).toTaskNetwork.α 0)
        rw [leafTn_α]; exact .leaf p
      · refine .node (fun _ => [p]) (fun t ht => .leaf p) ?_
        show OrdMerge (leafTn p).toTaskNetwork _ _
        rw [ordMerge_single (TnDesc.toTaskNetwork_wf _) (leafTn_T _)]
    · simp at hl
  | succ j ih =>
    intro hj π hl hdecl
    obtain ⟨d0, hv0, hy0⟩ := ih (by omega) (π.take (2 ^ j)) (by simp)
      (fun a ha => hdecl a (List.mem_of_mem_take ha))
    obtain ⟨d1, hv1, hy1⟩ := ih (by omega) (π.drop (2 ^ j))
      (by simp only [List.length_drop, pow_succ] at hl ⊢; omega)
      (fun a ha => hdecl a (List.mem_of_mem_drop ha))
    have hc : d.nV + 1 - (j + 1) = (d.nV - (j + 1)) + 1 := by omega
    have hc' : d.nV - (j + 1) + 2 = d.nV + 1 - j := by omega
    refine ⟨.node (d.nV + 1 - (j + 1)) (MethodDesc.toMethod (d.nV - (j + 1) + 1,
      dblTn (d.nV - (j + 1) + 2))) (fun t => if t = 0 then d0 else d1), ?_, ?_⟩
    · refine .node ⟨(d.nV - (j + 1) + 1, dblTn (d.nV - (j + 1) + 2)), by
        simp only [ProbDesc.methods, acycOfStrips, acycMethods, List.mem_append, List.mem_map,
          List.mem_range]
        exact Or.inl ⟨d.nV - (j + 1), by omega, rfl⟩, rfl⟩ (by simp [MethodDesc.toMethod]; omega)
        (fun t ht => ?_)
      simp only [MethodDesc.toMethod] at ht ⊢
      rw [dblTn_α _ ht, hc']
      rw [dblTn_T] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simpa using hv0
      · simpa using hv1
    · refine .node (fun t => if t = 0 then π.take (2 ^ j) else π.drop (2 ^ j)) (fun t ht => ?_) ?_
      · simp only [MethodDesc.toMethod, dblTn_T, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · simpa using hy0
        · simpa using hy1
      · simp only [MethodDesc.toMethod]
        rw [ordMerge_pair (TnDesc.toTaskNetwork_wf _) (dblTn_T _) (by decide) (dblTn_ord _)]
        simp

/-! ### Solutions -/

theorem acycOfStrips_δ (d : StripsDesc) : (acycOfStrips d).toProblem.δ = d.toProbDesc.toProblem.δ := rfl

/-- **The encoding has a solution iff the STRIPS problem has a plan.** -/
theorem acycOfStrips_solvable_iff (d : StripsDesc) :
    (acycOfStrips d).toProblem.Solvable ↔ d.Solvable := by
  rw [Problem.solvable_iff_trees _ (toProblem_wf _)]
  have hT : (acycOfStrips d).toProblem.tnI.T = {0} := rootTn1_T
  have hα : (acycOfStrips d).toProblem.tnI.α 0 = Sum.inr (d.nV + 1 - d.nV) := by
    rw [show d.nV + 1 - d.nV = 1 by omega]; exact rootTn1_α
  have hwf : (acycOfStrips d).toProblem.tnI.WF := TnDesc.toTaskNetwork_wf _
  constructor
  · rintro ⟨trees, π, s, ⟨hval, ys, hys, hm⟩, hrun, hg⟩
    obtain rfl := (ordMerge_single hwf hT).1 hm
    have hv := hval 0 (by rw [hT]; simp)
    rw [hα] at hv
    obtain ⟨-, hdecl⟩ := acyc_yield d d.nV le_rfl (trees 0) (ys 0) hv (hys 0 (by rw [hT]; simp))
    exact ⟨ys 0, hdecl, s, (run_congr (acycOfStrips_δ d) _ _ _).1 hrun, hg⟩
  · intro h
    obtain ⟨π, hlen, hdecl, s, hrun, hg⟩ := exists_short_plan d h
    obtain ⟨dt, hv, hy⟩ := acyc_tree d d.nV le_rfl π hlen.le hdecl
    refine ⟨fun _ => dt, π, s, ⟨fun t ht => ?_, fun _ => π, fun t ht => hy,
      (ordMerge_single hwf hT).2 rfl⟩, (run_congr (acycOfStrips_δ d) _ _ _).2 hrun, hg⟩
    rw [hT] at ht
    obtain rfl : t = 0 := by simpa using ht
    rw [hα]; exact hv

/-! ### The class -/

theorem acycOfStrips_isACYC (d : StripsDesc) : (acycOfStrips d).toProblem.IsACYC := by
  refine HTN.Problem.isAcyclic_of_rank _ (fun c => d.nV + 2 - c) ?_
  rintro m ⟨hm, -⟩ t ht c hc
  rcases acyc_methods_cases d hm with ⟨i, hi, rfl⟩ | rfl | ⟨a, -, rfl⟩
  · simp only [MethodDesc.toMethod] at ht hc ⊢
    rw [dblTn_α _ ht] at hc
    cases hc
    omega
  · simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht
  · simp only [MethodDesc.toMethod, leafTn_T, Finset.mem_singleton] at ht hc
    subst ht
    rw [show (leafTn a.name).toTaskNetwork.α 0 = _ from leafTn_α _] at hc
    cases hc

theorem acycOfStrips_isTO (d : StripsDesc) : (acycOfStrips d).toProblem.IsTO := by
  refine ⟨fun t ht t' ht' hne => ?_, fun m hm' => ?_⟩
  · have hT : (acycOfStrips d).toProblem.toPos.tnI.T = {0} := rootTn1_T
    rw [hT] at ht ht'
    simp at ht ht'
    exact absurd (ht.trans ht'.symm) hne
  · obtain ⟨hm, -⟩ := hm'
    rcases acyc_methods_cases d hm with ⟨i, -, rfl⟩ | rfl | ⟨a, -, rfl⟩
    · intro t ht t' ht' hne
      simp only [MethodDesc.toMethod, dblTn_T, Finset.mem_insert, Finset.mem_singleton] at ht ht'
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl (dblTn_ord _)
      · exact Or.inr (dblTn_ord _)
      · exact absurd rfl hne
    · intro t ht; simp [MethodDesc.toMethod, emptyTnD, TnDesc.toTaskNetwork, TnDesc.ids] at ht
    · intro t ht t' ht' hne
      simp only [MethodDesc.toMethod, leafTn_T, Finset.mem_singleton] at ht ht'
      exact absurd (ht.trans ht'.symm) hne

/-! ### Well-formedness and polynomial time -/

theorem acycOfStrips_valid_iff (d : StripsDesc) : (acycOfStrips d).Valid ↔ d.Valid := by
  constructor
  · exact fun h => h.names_nodup
  · intro h
    refine ⟨h, ?_, fun m hm => ?_⟩
    · show TnValid _ rootTn1
      exact ⟨by simp [rootTn1, TnDesc.ids], by simp [rootTn1, TnDesc.ordList],
        by simp [rootTn1, TnDesc.ordList], by simp [rootTn1, TnDesc.ordList],
        by simp [rootTn1, TnDesc.lbl, TnDesc.ids], by simp [rootTn1, TnDesc.lbl]⟩
    simp only [ProbDesc.methods, acycOfStrips, acycMethods, List.mem_append, List.mem_map,
      List.mem_range, List.mem_cons] at hm
    rcases hm with ⟨i, -, rfl⟩ | rfl | ⟨a, ha, rfl⟩
    · refine ⟨by simp [dblTn, TnDesc.ids], by simp [dblTn, TnDesc.ordList, TnDesc.ids],
        by simp [dblTn, TnDesc.ordList], ?_, ?_, ?_⟩
      · intro x y z h1 h2; simp [dblTn, TnDesc.ordList] at h1 h2; omega
      · simp only [dblTn, TnDesc.lbl, TnDesc.ids, List.map_cons, List.map_nil]; exact List.Perm.refl _
      · intro q hq hf
        simp only [dblTn, TnDesc.lbl, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with rfl | rfl <;> simp at hf
    · exact ⟨by simp [emptyTnD, TnDesc.ids], by simp [emptyTnD, TnDesc.ordList],
        by simp [emptyTnD, TnDesc.ordList], by simp [emptyTnD, TnDesc.ordList],
        by simp [emptyTnD, TnDesc.lbl, TnDesc.ids], by simp [emptyTnD, TnDesc.lbl]⟩
    · refine ⟨by simp [leafTn, TnDesc.ids], by simp [leafTn, TnDesc.ordList],
        by simp [leafTn, TnDesc.ordList], by simp [leafTn, TnDesc.ordList],
        by simp [leafTn, TnDesc.lbl, TnDesc.ids], ?_⟩
      intro q hq hf
      simp only [leafTn, TnDesc.lbl, List.mem_cons, List.mem_nil_iff, or_false] at hq
      subst hq
      exact List.mem_map.2 ⟨a, ha, rfl⟩

theorem pt_facts : PT StripsDesc.facts := by
  unfold StripsDesc.facts StripsDesc.init StripsDesc.actions
  exact PT.dedup (PT.append (PT.fst.comp PT.snd) (PT.flatMap PT.fst
    (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))))

theorem pt_nV : PT StripsDesc.nV := PT.length pt_facts

theorem pt_acycOfStrips : PT acycOfStrips := by
  unfold acycOfStrips acycMethods
  have hdbl : PT fun p : StripsDesc × ℕ => ((p.2 + 1, dblTn (p.2 + 2)) : MethodDesc) := by
    unfold dblTn
    exact PT.pair (PT.succ PT.snd) (PT.pair (PT.const _) (PT.pair (PT.const _)
      (PT.cons (PT.pair (PT.const 0) (PT.pair (PT.const true) (PT.affine 1 2 PT.snd |>.of_eq
        fun _ => by ring))) (PT.single (PT.pair (PT.const 1) (PT.pair (PT.const true)
        (PT.affine 1 2 PT.snd |>.of_eq fun _ => by ring)))))))
  have hleaf : PT fun p : StripsDesc × ActDesc => ((p.1.nV + 1, leafTn p.2.name) : MethodDesc) := by
    unfold leafTn ActDesc.name
    exact PT.pair (PT.succ (pt_nV.comp PT.fst)) (PT.pair (PT.const _) (PT.pair (PT.const _)
      (PT.single (PT.pair (PT.const 0) (PT.pair (PT.const false) (PT.fst.comp PT.snd))))))
  have hR : PT fun d : StripsDesc => List.range d.nV := PT.rangeLength pt_facts
  exact PT.pair (PT.pair PT.fst (PT.append (PT.map hR hdbl)
    (PT.cons (PT.pair (PT.succ pt_nV) (PT.const _)) (PT.map PT.fst hleaf))))
    (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.const _) (PT.snd.comp PT.snd)))

/-- **Theorem 4.3.4.** `PlanEx^{ACYC∩TO}` and `PlanEx^{ACYC∩TO-M}` are PSPACE-hard. -/
theorem thm_4_3_4 :
    Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsACYC ∧ P.IsTO) ∧
      Cx.Hard Cx.PSPACE (PlanEx fun P => P.IsACYC ∧ P.IsTO_M) :=
  ⟨pspaceHard_of_strips pt_acycOfStrips acycOfStrips_valid_iff
      (fun d _ => ⟨acycOfStrips_isACYC d, acycOfStrips_isTO d⟩)
      (fun d _ => acycOfStrips_solvable_iff d),
    pspaceHard_of_strips pt_acycOfStrips acycOfStrips_valid_iff
      (fun d _ => ⟨acycOfStrips_isACYC d, (acycOfStrips_isTO d).2⟩)
      (fun d _ => acycOfStrips_solvable_iff d)⟩

end Article

end HTN
