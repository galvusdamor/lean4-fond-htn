import HtnComplexity.Article.NExpRend
/-!
# The rendering of the acyclic encoding with the explicit method list

`HTN.TMEnc.U.rendU` writes `HTN.TMEnc.problemFix N w K` down with the method list
`HTN.TMEnc.U.methodsL` and the numberings of `HtnComplexity/Computable/TMNum.lean`:

* `HTN.TMEnc.U.solvable_rendU_iff` — the description is solvable iff the problem is;
* `HTN.TMEnc.U.isAcyclic_rendU`, `HTN.TMEnc.U.isRooted_rendU` — acyclic, rooted.
-/

namespace HTN

namespace TMEnc

namespace U

open scoped Classical

open TM TaskNetwork Syn Article

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-- The shape of the method of `sI`. -/
def sIShapeU (K : ℕ) : Shape (TMAct Q Γ) (TMTask Q Γ) :=
  ⟨initChainsFix K ++ [[Sum.inr TMTask.done]], (initChainsFix (Q := Q) (Γ := Γ) K).length⟩

/-- **The rendering of the encoding with the explicit method list.** -/
noncomputable def rendU (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ} (hq : Function.Injective q)
    (hg : Function.Injective g) (w : List Γ) (K : ℕ) : Rendering (problemFix N w K) where
  eF := encTMFact q g
  eA := encTMAct q g
  eC := encTMTask g
  eF_inj := encTMFact_injective hq hg
  eA_inj := encTMAct_injective hq hg
  eC_inj := encTMTask_injective hg
  acts := (opFinset (Finset.univ : Finset Q) (Finset.univ : Finset Γ)).toList
  precL := tmPrecL
  addL := tmAddL
  delL := tmDelL
  bodies := (methodsL N w K).map (fun p => (p.1, ⟨p.2, 0⟩)) ++ [(.sI, sIShapeU K)]
  tnIshape := ⟨[[Sum.inr TMTask.sI]], 0⟩
  initL := [TMFact.st N.init]
  goalL := []
  used_mem := fun o _ => Finset.mem_toList.2 (mem_opFinset_univ o)
  precL_eq := fun o _ => tmPrecL_eq o
  addL_eq := fun o _ => tmAddL_eq o
  delL_eq := fun o _ => tmDelL_eq o
  init_eq := by
    ext v
    simp [problemFix, instance_, Domain.mkProblem]
  goal_eq := by
    ext v
    simp [problemFix, instance_, Domain.mkProblem]
  tnI_wf := TaskNetwork.seq_wf
  tnI_iso := by
    rw [Shape.net_zero]
    exact TaskNetwork.Iso.refl _
  bodies_sub := by
    intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with ⟨p, hp, rfl⟩ | rfl
    · refine ⟨⟨p.1, grid p.2⟩, Or.inl ⟨p.2, mem_bodiesFix_of_mem_methodsL hp, rfl⟩, rfl, ?_⟩
      rw [Shape.net_zero]
    · refine ⟨⟨TMTask.sI, initNetFix K⟩, Or.inr rfl, rfl, ?_⟩
      show (initNetFix K).Iso (sIShapeU K).net
      rw [sIShapeU, Shape.net_length]
      exact TaskNetwork.Iso.refl _
  bodies_all := by
    intro m hm
    have ht := mem_taskFinsetFix_of_reachableName hm.2
    rcases hm.1 with ⟨ls, hls, hsub⟩ | hsI
    · obtain ⟨t, sub⟩ := m
      simp only at hsub hls ht
      subst hsub
      refine ⟨(t, ⟨ls, 0⟩), List.mem_append_left _ (List.mem_map.2
        ⟨(t, ls), mem_methodsL_of_mem_taskFinsetFix ht hls, rfl⟩), rfl, ?_⟩
      rw [Shape.net_zero]
    · have hm' : m = ⟨TMTask.sI, initNetFix K⟩ := hsI
      subst hm'
      refine ⟨(.sI, sIShapeU K), by simp, rfl, ?_⟩
      show (initNetFix K).Iso (sIShapeU K).net
      rw [sIShapeU, Shape.net_length]
      exact TaskNetwork.Iso.refl _

variable (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ} (hq : Function.Injective q)
  (hg : Function.Injective g) (w : List Γ) (K : ℕ)

theorem solvable_rendU_iff :
    Syn.Solvable (rendU N hq hg w K).domDesc (rendU N hq hg w K).instDesc ↔
      (problemFix N w K).Solvable :=
  (rendU N hq hg w K).solvable_iff

theorem isRooted_rendU : InstDesc.IsRooted (rendU N hq hg w K).instDesc :=
  (rendU N hq hg w K).isRooted_instDesc (c := TMTask.sI) rfl

theorem isAcyclic_rendU : DomDesc.IsAcyclic (rendU N hq hg w K).domDesc := by
  refine (rendU N hq hg w K).isAcyclic_domDesc (rank K w.length) ?_
  intro p hp row hrow x hx c hc
  subst hc
  simp only [rendU, List.mem_append, List.mem_map, List.mem_singleton] at hp
  rcases hp with ⟨p, hp, rfl⟩ | rfl
  · exact rank_lt_of_mem_bodiesFix (mem_bodiesFix_of_mem_methodsL hp)
      (List.mem_flatten.2 ⟨row, hrow, hx⟩)
  · have hmem : (Sum.inr c : TMAct Q Γ ⊕ TMTask Q Γ) ∈ (sIShapeU (Q := Q) (Γ := Γ) K).rows.flatten :=
      List.mem_flatten.2 ⟨row, hrow, hx⟩
    simp only [sIShapeU, initChainsFix, headChainFix, List.cons_append, List.nil_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false, Sum.inr.injEq, reduceCtorEq, false_or] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega

end U

end TMEnc

end HTN
