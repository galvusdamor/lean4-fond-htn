import HtnPlanning.Computable.Classes
/-!
# Rooted instance descriptions

The compound task `rootName q` of a rooted instance description, `STRIPS` instance descriptions
are rooted, and the inclusions of the rooted totally ordered regular class.  Split out of
`HTN.Computable.RegStrips`.
-/

namespace HTN

namespace Syn

/-- The compound task name of the initial task network of a rooted instance description. -/
def rootName (q : InstDesc) : ℕ := q.tnI.compoundNames.headI

/-! ### The source class: rooted instances -/

namespace InstDesc

/-- A `STRIPS` instance description is rooted. -/
theorem IsStrips.isRooted {q : InstDesc} (h : q.IsStrips) : q.IsRooted := by
  obtain ⟨t, hT, hα⟩ := h
  exact ⟨t, 0, hT, hα⟩

/-- The compound task of a rooted instance description is the one `rootName` computes. -/
theorem rootName_spec {q : InstDesc} (h : q.IsRooted) :
    ∃ t : ℕ, q.tnI.toTaskNetwork.T = {t} ∧
      q.tnI.toTaskNetwork.α t = Sum.inr (rootName q) := by
  obtain ⟨t, c, hT, hα⟩ := h
  refine ⟨t, hT, ?_⟩
  have hc : rootName q = c := by
    have hmem : t ∈ q.tnI.ids := by
      have : t ∈ q.tnI.toTaskNetwork.T := by rw [hT]; simp
      simpa using this
    have hlbl : q.tnI.lbl.lookup t = some (true, c) := by
      rcases hl : q.tnI.lbl.lookup t with _ | ⟨b, n⟩
      · rw [show q.tnI.toTaskNetwork.α t = q.tnI.label t from rfl,
          TnDesc.label, hl] at hα
        exact absurd hα (by simp)
      · cases b
        · rw [show q.tnI.toTaskNetwork.α t = q.tnI.label t from rfl,
            TnDesc.label, hl] at hα
          exact absurd hα (by simp)
        · rw [show q.tnI.toTaskNetwork.α t = q.tnI.label t from rfl,
            TnDesc.label, hl] at hα
          simp only [Sum.inr.injEq] at hα
          rw [hα]
    -- every listed identifier is `t`
    have hall : ∀ x ∈ q.tnI.ids, x = t := by
      intro x hx
      have : x ∈ q.tnI.toTaskNetwork.T := by simpa using hx
      rw [hT] at this
      simpa using this
    have hlab : ∀ x ∈ q.tnI.ids, TnDesc.labelList true q.tnI.lbl x = [c] := by
      intro x hx
      rw [hall x hx, TnDesc.labelList_eq, hlbl]
      simp
    rcases hids : q.tnI.ids with _ | ⟨x, xs⟩
    · rw [hids] at hmem; simp at hmem
    · have hx : x ∈ q.tnI.ids := by rw [hids]; simp
      simp only [rootName, TnDesc.compoundNames, hids, List.flatMap_cons, hlab x hx,
        List.cons_append, List.headI]
  rw [hc]
  exact hα

end InstDesc

/-! ### The class of rooted totally ordered regular descriptions -/

namespace SynClass

open Table

theorem sub_TO_HTN_REG_root_TO_HTN_REG : SynSub TO_HTN_REG_root TO_HTN_REG :=
  ⟨fun _ hd => hd, fun _ hq => ⟨hq.isTO, hq.isRegular⟩⟩

theorem sub_STRIPS_TO_HTN_REG_root : SynSub STRIPS TO_HTN_REG_root :=
  ⟨fun _ hd => ⟨isStrips_methodsTO hd, isStrips_methodsReg hd⟩, fun _ hq => hq.isRooted⟩

end SynClass

end Syn

end HTN
