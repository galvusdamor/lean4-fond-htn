import FondHtn.Transfer.DetFond
import FondHtn.Lang.Desc
/-!
# The structural classes are preserved by appending a last primitive task

`HTN.Problem.SameShape P P'`: same methods and the same reachable compound task names.  All
classes defined from methods and reachable names (acyclic, regular in the sense of Bercher et al.,
tail-recursive, totally ordered methods) agree on problems of the same shape.  Appending a
primitive task to the initial task network does not change the shape, and preserves total order
of the initial network and primitivity.  Hence `detFond Q i g` belongs to the FOND version of each
class iff `Q` belongs to it (`FOND.detFond_class_iff`).
-/

namespace HTN

namespace Problem

universe u u' v w x

variable {F : Type u} {F' : Type u'} {A : Type v} {C : Type w} {I : Type x}

theorem reachableName_of {P : HTN.Problem F A C I} {P' : HTN.Problem F' A C I}
    (hM : P.methods = P'.methods)
    (htn : ∀ t ∈ P.tnI.T, ∀ c, P.tnI.α t = Sum.inr c → ∃ t' ∈ P'.tnI.T, P'.tnI.α t' = Sum.inr c)
    {c : C} (h : P.ReachableName c) : P'.ReachableName c := by
  induction h with
  | tnI ht hc =>
    obtain ⟨t', ht', hc'⟩ := htn _ ht _ hc
    exact .tnI ht' hc'
  | method hm _ ht hc ih => exact .method (hM ▸ hm) ih ht hc

/-- Same methods and same reachable compound task names. -/
structure SameShape (P : HTN.Problem F A C I) (P' : HTN.Problem F' A C I) : Prop where
  methods : P.methods = P'.methods
  rn : ∀ c, P.ReachableName c ↔ P'.ReachableName c

variable {P : HTN.Problem F A C I} {P' : HTN.Problem F' A C I}

theorem SameShape.symm (h : SameShape P P') : SameShape P' P := ⟨h.methods.symm, fun c => (h.rn c).symm⟩

theorem SameShape.rm (h : SameShape P P') (m : Method I A C) :
    P.ReachableMethod m ↔ P'.ReachableMethod m := by
  unfold ReachableMethod; rw [h.methods, h.rn]

theorem SameShape.strat (h : SameShape P P') {le : C → C → Prop} (hs : P.IsStratification le) :
    P'.IsStratification le where
  refl c hc := hs.refl c ((h.rn c).2 hc)
  trans a b c ha hb hc := hs.trans a b c ((h.rn a).2 ha) ((h.rn b).2 hb) ((h.rn c).2 hc)
  total a b ha hb := hs.total a b ((h.rn a).2 ha) ((h.rn b).2 hb)

theorem SameShape.isAcyclic_of (h : SameShape P P') (hP : P.IsAcyclic) : P'.IsAcyclic := by
  obtain ⟨le, hs⟩ := hP
  exact ⟨le, ⟨h.strat hs.strat, fun a b ha hb => hs.antisymm a b ((h.rn a).2 ha) ((h.rn b).2 hb),
    fun m hm => hs.decreasing m ((h.rm m).2 hm)⟩⟩

theorem SameShape.isTailRecursive_of (h : SameShape P P') (hP : P.IsTailRecursive) :
    P'.IsTailRecursive := by
  obtain ⟨le, hs⟩ := hP
  exact ⟨le, ⟨h.strat hs.strat, fun m hm => hs.last m ((h.rm m).2 hm),
    fun m hm => hs.nonlast m ((h.rm m).2 hm)⟩⟩

theorem SameShape.isRegularM_of (h : SameShape P P') (hP : P.IsRegularM) : P'.IsRegularM :=
  fun m hm => hP m ((h.rm m).2 hm)

theorem SameShape.isTO_M_of (h : SameShape P P') (hP : P.IsTO_M) : P'.IsTO_M :=
  fun m hm => hP m ((h.rm m).2 hm)

theorem SameShape.isAcyclic (h : SameShape P P') : P.IsAcyclic ↔ P'.IsAcyclic :=
  ⟨h.isAcyclic_of, h.symm.isAcyclic_of⟩

theorem SameShape.isTailRecursive (h : SameShape P P') :
    P.IsTailRecursive ↔ P'.IsTailRecursive :=
  ⟨h.isTailRecursive_of, h.symm.isTailRecursive_of⟩

theorem SameShape.isRegularM (h : SameShape P P') : P.IsRegularM ↔ P'.IsRegularM :=
  ⟨h.isRegularM_of, h.symm.isRegularM_of⟩

theorem SameShape.isTO_M (h : SameShape P P') : P.IsTO_M ↔ P'.IsTO_M :=
  ⟨h.isTO_M_of, h.symm.isTO_M_of⟩

end Problem

namespace TaskNetwork

variable {I A C : Type} [DecidableEq I] {tn : TaskNetwork I A C} {i : I} {a : A}

theorem appendLast_isTotallyOrdered_iff (hwf : tn.WF) (hi : i ∉ tn.T) :
    (tn.appendLast i a).IsTotallyOrdered ↔ tn.IsTotallyOrdered := by
  have hne : ∀ {x}, x ∈ tn.T → x ≠ i := fun hx e => hi (e ▸ hx)
  constructor
  · intro h x hx y hy hxy
    rcases h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy with
      (⟨h, -, -⟩ | ⟨-, -, h⟩) | (⟨h, -, -⟩ | ⟨-, -, h⟩)
    · exact Or.inl h
    · exact absurd h (hne hy)
    · exact Or.inr h
    · exact absurd h (hne hx)
  · intro h x hx y hy hxy
    rcases Finset.mem_insert.1 hx with hx' | hx' <;> rcases Finset.mem_insert.1 hy with hy' | hy'
    · exact absurd (hx'.trans hy'.symm) hxy
    · exact Or.inr (Or.inr ⟨hy', hne hy', hx'⟩)
    · exact Or.inl (Or.inr ⟨hx', hne hx', hy'⟩)
    · rcases h x hx' y hy' hxy with h | h
      · exact Or.inl (Or.inl ⟨h, hne hx', hne hy'⟩)
      · exact Or.inr (Or.inl ⟨h, hne hy', hne hx'⟩)

theorem appendLast_isPrimitive_iff (hi : i ∉ tn.T) :
    (tn.appendLast i a).IsPrimitive ↔ tn.IsPrimitive := by
  have hne : ∀ {x}, x ∈ tn.T → x ≠ i := fun hx e => hi (e ▸ hx)
  constructor
  · intro h x hx
    obtain ⟨b, hb⟩ := h x (Finset.mem_insert_of_mem hx)
    exact ⟨b, by simpa [appendLast, hne hx] using hb⟩
  · intro h x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨a, by simp [appendLast]⟩
    · obtain ⟨b, hb⟩ := h x hx
      exact ⟨b, by simp [appendLast, hne hx, hb]⟩

end TaskNetwork

end HTN

namespace FOND

open HTN HTN.TaskNetwork HTN.Article

variable {Q : HTN.Article.Problem ℕ ℕ ℕ ℕ} {i g : ℕ}

theorem detFond_sameShape (hi : i ∉ Q.tnI.T) :
    HTN.Problem.SameShape (detFond Q i g).toArt.toPos Q.toPos := by
  have hM : (detFond Q i g).toArt.toPos.methods = Q.toPos.methods := rfl
  refine ⟨hM, fun c => ⟨HTN.Problem.reachableName_of hM ?_, HTN.Problem.reachableName_of hM.symm ?_⟩⟩
  · intro t ht c hc
    change t ∈ (Q.tnI.appendLast i g).T at ht
    change (Q.tnI.appendLast i g).α t = _ at hc
    by_cases hti : t = i
    · simp [appendLast, hti] at hc
    · refine ⟨t, ?_, ?_⟩
      · rcases Finset.mem_insert.1 ht with h | h
        · exact absurd h hti
        · exact h
      · simpa [appendLast, hti] using hc
  · intro t ht c hc
    refine ⟨t, Finset.mem_insert_of_mem ht, ?_⟩
    change (Q.tnI.appendLast i g).α t = _
    have hti : t ≠ i := fun e => hi (e ▸ ht)
    simp only [appendLast, hti, if_false]; exact hc

end FOND
