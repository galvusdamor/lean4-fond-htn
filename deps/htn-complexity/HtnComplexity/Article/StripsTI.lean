import HtnComplexity.Article.StripsReg
import HtnPlanning.Core.Construction
/-!
# TIHTN planning is PSPACE-hard (Thm. 4.3.5)

With task insertion, a STRIPS problem is the TIHTN problem with the same actions, no methods and
the empty initial task network (`HTN.Article.StripsDesc.toProbDesc`): its TIHTN solutions are the
plans (`HTN.Article.toProbDesc_solvableTI_iff`).  The problem belongs to every class of the
article — it has no compound task at all — so

* **`HTN.Article.thm_4_3_5`** — `PlanEx^{Y∩Z}_tihtn` is PSPACE-hard for
  `Y ∈ {UNRES-REC, TAIL-REC, ACYC, REG, REG∩ACYC, noHTN}` and `Z ∈ {UNRES-REC, TO, TO-M, TO-tn_I}`.

Undeclared action names denote the empty action, which can be inserted but changes nothing; they
are dropped from a TIHTN plan (`HTN.Article.run_filter_declared`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-- The empty action of an undeclared name. -/
theorem δ_undeclared {p : ProbDesc} {a : ℕ} (h : ¬ p.Declared a) : p.δ a = ⟨∅, ∅, ∅, ∅⟩ := by
  unfold ProbDesc.δ
  rw [List.find?_eq_none.2 fun x hx hxa => h (List.mem_map.2 ⟨x, hx, by simpa using hxa⟩)]

/-- **Undeclared actions can be dropped from a run.** -/
theorem run_filter_declared (p : ProbDesc) [DecidablePred p.Declared] :
    ∀ (π : List ℕ) (s s' : Set ℕ), p.toProblem.Run π s s' →
      p.toProblem.Run (π.filter fun a => decide (p.Declared a)) s s' := by
  intro π
  induction π with
  | nil => intro s s' h; exact h
  | cons a π ih =>
    intro s s' h
    obtain ⟨happ, hr⟩ := h
    by_cases ha : p.Declared a
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      exact ⟨happ, ih _ _ hr⟩
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have hδ : p.toProblem.δ a = ⟨∅, ∅, ∅, ∅⟩ := δ_undeclared ha
      have : (p.toProblem.δ a).apply s = s := by
        rw [hδ]; simp [Action.apply]
      rw [this] at hr
      exact ih _ _ hr

theorem toProbDesc_tnI_T (d : StripsDesc) : d.toProbDesc.toProblem.tnI.T = ∅ := by
  simp [StripsDesc.toProbDesc, ProbDesc.toProblem, ProbDesc.tnI, StripsDesc.emptyTn,
    TnDesc.toTaskNetwork, TnDesc.ids]

theorem toProbDesc_methods (d : StripsDesc) : d.toProbDesc.toProblem.methods = ∅ := by
  ext m; simp [StripsDesc.toProbDesc, ProbDesc.toProblem, ProbDesc.methods]

/-- **TIHTN plan existence of the method-free problem is STRIPS plan existence.** -/
theorem toProbDesc_solvableTI_iff (d : StripsDesc) :
    d.toProbDesc.toProblem.SolvableTI ↔ d.Solvable := by
  classical
  rw [Problem.solvableTI_iff_trees _ (toProblem_wf _)]
  have hT := toProbDesc_tnI_T d
  constructor
  · rintro ⟨trees, as, π, s, ⟨-, ys, -, hm⟩, -, hrun, hg⟩
    refine ⟨π.filter fun a => decide (d.toProbDesc.Declared a), fun a ha => ?_, s,
      run_filter_declared _ π _ _ hrun, hg⟩
    simpa using (List.mem_filter.1 ha).2
  · rintro ⟨π, -, s, hrun, hg⟩
    exact ⟨fun _ => .leaf 0, [], π, s, ⟨fun t ht => by simp [hT] at ht, fun _ => [],
      fun t ht => by simp [hT] at ht, (ordMerge_empty hT).2 rfl⟩, List.nil_sublist _, hrun, hg⟩

/-! ### The method-free problem is in every class -/

section Trivial

variable (d : StripsDesc)

theorem toProbDesc_not_reachableName (c : ℕ) : ¬ d.toProbDesc.toProblem.toPos.ReachableName c := by
  intro h
  have hT : d.toProbDesc.toProblem.toPos.tnI.T = ∅ := toProbDesc_tnI_T d
  have hM : d.toProbDesc.toProblem.toPos.methods = ∅ := toProbDesc_methods d
  cases h with
  | tnI ht _ => rw [hT] at ht; simp at ht
  | method hm _ _ _ => rw [hM] at hm; simp at hm

theorem toProbDesc_isACYC : d.toProbDesc.toProblem.IsACYC :=
  HTN.Problem.isAcyclic_of_rank _ (fun _ => 0) fun _ ⟨hm, _⟩ => absurd hm (by
    rw [show d.toProbDesc.toProblem.toPos.methods = ∅ from toProbDesc_methods d]; simp)

theorem toProbDesc_isREG : d.toProbDesc.toProblem.IsREG := fun _ ⟨hm, _⟩ => absurd hm (by
  rw [show d.toProbDesc.toProblem.toPos.methods = ∅ from toProbDesc_methods d]; simp)

theorem toProbDesc_isTailREC : d.toProbDesc.toProblem.IsTailREC :=
  ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial, fun _ _ _ _ => Or.inl trivial⟩,
    fun _ ⟨hm, _⟩ => absurd hm (by
      rw [show d.toProbDesc.toProblem.toPos.methods = ∅ from toProbDesc_methods d]; simp),
    fun _ ⟨hm, _⟩ => absurd hm (by
      rw [show d.toProbDesc.toProblem.toPos.methods = ∅ from toProbDesc_methods d]; simp)⟩⟩

theorem toProbDesc_isNoHTN : d.toProbDesc.toProblem.IsNoHTN := fun t ht => by
  rw [show d.toProbDesc.toProblem.toPos.tnI.T = ∅ from toProbDesc_tnI_T d] at ht; simp at ht

theorem toProbDesc_isTO : d.toProbDesc.toProblem.IsTO := by
  have hT : d.toProbDesc.toProblem.toPos.tnI.T = ∅ := toProbDesc_tnI_T d
  have hM : d.toProbDesc.toProblem.toPos.methods = ∅ := toProbDesc_methods d
  refine ⟨fun t ht => ?_, fun m hm => ?_⟩
  · rw [hT] at ht; simp at ht
  · have := hm.1; rw [hM] at this; simp at this

end Trivial

theorem toProbDesc_valid_iff (d : StripsDesc) : d.toProbDesc.Valid ↔ d.Valid := by
  constructor
  · exact fun h => h.names_nodup
  · intro h
    refine ⟨h, ⟨by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.ids],
      by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.ordList],
      by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.ordList],
      by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.ordList],
      by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.lbl, TnDesc.ids],
      by simp [StripsDesc.toProbDesc, ProbDesc.tnI, StripsDesc.emptyTn, TnDesc.lbl]⟩,
      fun m hm => by simp [StripsDesc.toProbDesc, ProbDesc.methods] at hm⟩

theorem pt_toProbDesc : PT StripsDesc.toProbDesc := by
  unfold StripsDesc.toProbDesc StripsDesc.actions StripsDesc.init StripsDesc.goalPos StripsDesc.goalNeg
  exact PT.pair (PT.pair PT.fst PT.nil) (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.const _)
    (PT.snd.comp PT.snd)))

/-- PSPACE-hardness of TIHTN plan existence for every class containing the method-free problems. -/
theorem pspaceHardTI_of_trivial {Y : PClass} (hY : ∀ d : StripsDesc, Y d.toProbDesc.toProblem) :
    Cx.Hard Cx.PSPACE (PlanExTI Y) :=
  fun L hL => (strips_pspaceHard L hL).trans (redP_codeLang (α := StripsDesc) (β := ProbDesc)
    (R := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.SolvableTI) pt_toProbDesc
    (fun d => ⟨fun h => ⟨(toProbDesc_valid_iff d).2 h.1, hY d, (toProbDesc_solvableTI_iff d).2 h.2⟩,
      fun h => ⟨(toProbDesc_valid_iff d).1 h.1, (toProbDesc_solvableTI_iff d).1 h.2.2⟩⟩)
    badDesc (fun h => not_valid_badDesc h.1))

/-- **Theorem 4.3.5.** `PlanEx^{Y∩Z}_tihtn` is PSPACE-hard for
`Y ∈ {UNRES-REC, TAIL-REC, ACYC, REG, REG∩ACYC, noHTN}` and `Z ∈ {UNRES-REC, TO, TO-M, TO-tn_I}`
(`Z = UNRES-REC` gives the classes `Y` alone). -/
theorem thm_4_3_5 (Y Z : PClass)
    (hY : Y ∈ [UNRES, fun P => P.IsTailREC, fun P => P.IsACYC, fun P => P.IsREG,
      fun P => P.IsREG ∧ P.IsACYC, fun P => P.IsNoHTN])
    (hZ : Z ∈ [UNRES, fun P => P.IsTO, fun P => P.IsTO_M, fun P => P.IsTO_tnI]) :
    Cx.Hard Cx.PSPACE (PlanExTI fun P => Y P ∧ Z P) := by
  refine pspaceHardTI_of_trivial fun d => ⟨?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · exact toProbDesc_isTailREC d
    · exact toProbDesc_isACYC d
    · exact toProbDesc_isREG d
    · exact ⟨toProbDesc_isREG d, toProbDesc_isACYC d⟩
    · exact toProbDesc_isNoHTN d
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hZ
    rcases hZ with rfl | rfl | rfl | rfl
    · trivial
    · exact toProbDesc_isTO d
    · exact (toProbDesc_isTO d).2
    · exact (toProbDesc_isTO d).1

end Article

end HTN
