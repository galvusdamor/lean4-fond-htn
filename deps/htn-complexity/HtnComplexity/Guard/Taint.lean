import HtnPlanning.Core.DecompPersist
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Interleave.NetYield
/-!
# Tainted tasks: a plan that avoids an action avoids the methods that force it

The second half of the tool for *re-splitting* a construction (the first is
`HtnComplexity/Guard/Static.lean`).  A re-split domain offers, at each position of the
input, one method per symbol of the alphabet, and the instance admits only the methods of the
symbols of *its* word — by a guard that makes the other ones' actions inapplicable.  To read a
plan of the re-split problem as a plan of the original, word-carrying one, one has to know that
the inadmissible methods were never used.  That is what this file proves, in general.

## The argument

Call a compound task **tainted** when every method for it inserts either a **bad** action or
another tainted task (`HTN.Taint.Taintable`).  A tainted task can therefore never be got rid of:
whatever one decomposes it into still contains a bad action or a tainted task, and a *primitive*
network has no tainted task left — so a network containing one has no refinement whose actions
are all good (`HTN.Taint.not_taint_of_decomposesTo`).

Consequently a decomposition ending in a network whose actions are all good never applies a
method that inserts a bad action or a tainted task: such a method would leave a trace that no
later step can remove (`HTN.Taint.decomposesTo_of_clean`).  At the level of refinements this is

> `HTN.Taint.netYield_of_clean` — a refinement into a plan without bad actions is a refinement by
> the *smaller* method set.

Together with the trivial converse — a refinement by fewer methods is one by more
(`HTN.Taint.netYield_mono`) — this identifies the plans of the re-split domain that the guards
admit with the plans of the original domain.

## Main results

* `HTN.Taint.Taintable` — the closure condition on the tainted tasks;
* `HTN.Taint.not_taint_of_decomposesTo` — a tainted task has no good refinement;
* `HTN.Taint.decomposesTo_of_clean`, `HTN.Taint.netYield_of_clean` — a good plan only uses the
  methods of the smaller set;
* `HTN.Taint.netYield_mono` — refinements are monotone in the method set.
-/

namespace HTN

namespace Taint

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]
variable {M M' : Set (Method I A C)} {BadAct : A → Prop} {Taint : C → Prop}

/-- **The tainted tasks are closed**: every method for a tainted task inserts a bad action or
another tainted task.  A tainted task can then never be refined away without leaving a bad
action behind. -/
structure Taintable (M : Set (Method I A C)) (BadAct : A → Prop) (Taint : C → Prop) : Prop where
  /-- Every method decomposing a tainted task inserts a bad action or a tainted task. -/
  closed : ∀ m ∈ M, Taint m.abstractTask →
    ∃ t ∈ m.subtasks.T,
      (∃ a, m.subtasks.α t = Sum.inl a ∧ BadAct a) ∨ (∃ c, m.subtasks.α t = Sum.inr c ∧ Taint c)

omit [DecidableEq I] in
/-- A task of a method's subtask network has a counterpart, with the same name, in the fresh
copy that a decomposition step inserts. -/
lemma exists_mem_of_iso {u tn : TaskNetwork I A C} (hiso : u.Iso tn) {t : I} (ht : t ∈ tn.T) :
    ∃ x ∈ u.T, u.α x = tn.α t := by
  obtain ⟨σ, hbij, -, hα⟩ := hiso
  obtain ⟨x, hx, hxt⟩ := hbij.surjOn (by simpa using ht)
  have hxT : x ∈ u.T := by simpa using hx
  exact ⟨x, hxT, by rw [hα x hxT, hxt]⟩

/-- A primitive task keeps its name along a decomposition sequence. -/
lemma α_eq_of_isPrimitiveId {tn tn' : TaskNetwork I A C} (h : DecomposesTo M tn tn') {x : I}
    (hx : x ∈ tn.T) (hprim : tn.IsPrimitiveId x) : tn'.α x = tn.α x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a b hstep _ ih =>
      have hxb : x ∈ b.T := hstep.mem_of_isPrimitiveId hx hprim
      have hαb : b.α x = a.α x := hstep.α_eq hx
      have hprimb : b.IsPrimitiveId x := by
        obtain ⟨n, hn⟩ := hprim
        exact ⟨n, by rw [hαb]; exact hn⟩
      rw [ih hxb hprimb, hαb]

/-- **A tainted task has no good refinement.**  If a network can be decomposed into a primitive
network all of whose actions are good, then it carries no tainted task. -/
theorem not_taint_of_decomposesTo (h : Taintable M BadAct Taint) {tn tn' : TaskNetwork I A C}
    (hdec : DecomposesTo M tn tn') (hprim : tn'.IsPrimitive)
    (hclean : ∀ t ∈ tn'.T, ∀ a, tn'.α t = Sum.inl a → ¬ BadAct a) :
    ∀ t ∈ tn.T, ∀ c, tn.α t = Sum.inr c → ¬ Taint c := by
  induction hdec using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro t ht c hα hc
      obtain ⟨a, ha⟩ := hprim t ht
      rw [ha] at hα
      exact Sum.inl_ne_inr hα
  | @head tn tnb hstep hrest ih =>
      intro t ht c hα hc
      obtain ⟨s, m, hm, hsT, hsα, u, -, hiso, hdisj, rfl⟩ := hstep
      by_cases hts : t = s
      · -- the tainted task is the one being decomposed
        subst hts
        have hcm : m.abstractTask = c := by
          rw [hsα] at hα
          exact Sum.inr_injective hα
        obtain ⟨y, hy, hcase⟩ := h.closed m hm (by rw [hcm]; exact hc)
        obtain ⟨x, hx, hxα⟩ := exists_mem_of_iso hiso hy
        have hxT : x ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inr hx)
        have hxαd : (decomposeWith tn t u).α x = u.α x := by
          simp [decomposeWith_α, hx]
        rcases hcase with ⟨a, hau, hbad⟩ | ⟨c', hcu, hc'⟩
        · -- a bad action was inserted; it survives to the primitive network
          have hxprim : (decomposeWith tn t u).IsPrimitiveId x := ⟨a, by rw [hxαd, hxα, hau]⟩
          obtain ⟨hmem, -⟩ := HTN.DecomposesTo.mem_of_isPrimitiveId hrest hxT hxprim
          have hname : tn'.α x = (decomposeWith tn t u).α x :=
            α_eq_of_isPrimitiveId hrest hxT hxprim
          exact hclean x hmem a (by rw [hname, hxαd, hxα, hau]) hbad
        · -- a tainted task was inserted
          exact ih x hxT c' (by rw [hxαd, hxα, hcu]) hc'
      · -- the tainted task survives the step untouched
        have hxu : t ∉ u.T := Finset.disjoint_left.1 hdisj ht
        have hxT : t ∈ (decomposeWith tn s u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht, hts⟩)
        refine ih t hxT c ?_ hc
        simp [decomposeWith_α, hxu, hα]

/-- **A decomposition into a network without bad actions only uses the smaller method set** —
provided every method outside it inserts a bad action or a tainted task. -/
theorem decomposesTo_of_clean (h : Taintable M BadAct Taint)
    (hbad : ∀ m ∈ M, m ∉ M' → ∃ t ∈ m.subtasks.T,
      (∃ a, m.subtasks.α t = Sum.inl a ∧ BadAct a) ∨ (∃ c, m.subtasks.α t = Sum.inr c ∧ Taint c))
    {tn tn' : TaskNetwork I A C} (hdec : DecomposesTo M tn tn') (hprim : tn'.IsPrimitive)
    (hclean : ∀ t ∈ tn'.T, ∀ a, tn'.α t = Sum.inl a → ¬ BadAct a) :
    DecomposesTo M' tn tn' := by
  induction hdec using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head tn tnb hstep hrest ih =>
      obtain ⟨s, m, hm, hsT, hsα, u, huwf, hiso, hdisj, rfl⟩ := hstep
      have hmM' : m ∈ M' := by
        by_contra hnot
        obtain ⟨y, hy, hcase⟩ := hbad m hm hnot
        obtain ⟨x, hx, hxα⟩ := exists_mem_of_iso hiso hy
        have hxT : x ∈ (decomposeWith tn s u).T := mem_decomposeWith_T.2 (Or.inr hx)
        have hxαd : (decomposeWith tn s u).α x = u.α x := by
          simp [decomposeWith_α, hx]
        rcases hcase with ⟨a, hau, hbadact⟩ | ⟨c', hcu, hc'⟩
        · have hxprim : (decomposeWith tn s u).IsPrimitiveId x := ⟨a, by rw [hxαd, hxα, hau]⟩
          obtain ⟨hmem, -⟩ := HTN.DecomposesTo.mem_of_isPrimitiveId hrest hxT hxprim
          have hname : tn'.α x = (decomposeWith tn s u).α x :=
            α_eq_of_isPrimitiveId hrest hxT hxprim
          exact hclean x hmem a (by rw [hname, hxαd, hxα, hau]) hbadact
        · exact not_taint_of_decomposesTo h hrest hprim hclean x hxT c'
            (by rw [hxαd, hxα, hcu]) hc'
      exact Relation.ReflTransGen.head ⟨s, m, hmM', hsT, hsα, u, huwf, hiso, hdisj, rfl⟩ (ih)

/-! ### At the level of refinements -/

variable {D D' : Domain F A C I}

/-- **Refinements are monotone in the method set.** -/
theorem netYield_mono (hsub : D.methods ⊆ D'.methods) {tn : TaskNetwork I A C} {as : List A}
    (h : D.NetYield tn as) : D'.NetYield tn as := by
  obtain ⟨tn', hdec, hprim, l, hlin, hseq⟩ := Domain.netYield_iff.1 h
  exact Domain.netYield_iff.2
    ⟨tn', HTN.Problem.decomposesTo_mono hsub hdec, hprim, l, hlin, hseq⟩

/-- **A refinement into a plan without bad actions is a refinement by the smaller method set.**
This is the step that reads a plan of a re-split domain, whose guards have excluded the methods
of the wrong symbols, as a plan of the original, word-carrying domain. -/
theorem netYield_of_clean (h : Taintable D.methods BadAct Taint)
    (hbad : ∀ m ∈ D.methods, m ∉ D'.methods → ∃ t ∈ m.subtasks.T,
      (∃ a, m.subtasks.α t = Sum.inl a ∧ BadAct a) ∨ (∃ c, m.subtasks.α t = Sum.inr c ∧ Taint c))
    {tn : TaskNetwork I A C} {as : List A} (hy : D.NetYield tn as)
    (hclean : ∀ a ∈ as, ¬ BadAct a) : D'.NetYield tn as := by
  obtain ⟨tn', hdec, hprim, l, hlin, hseq⟩ := Domain.netYield_iff.1 hy
  have hcleanNet : ∀ t ∈ tn'.T, ∀ a, tn'.α t = Sum.inl a → ¬ BadAct a := by
    intro t ht a hα
    have htl : t ∈ l := (hlin.2.1 t).2 ht
    have hmem : (Sum.inl a : A ⊕ C) ∈ as.map Sum.inl := by
      rw [← hseq]
      exact hα ▸ List.mem_map_of_mem htl
    obtain ⟨b, hb, hba⟩ := List.mem_map.1 hmem
    exact hclean a (by rwa [Sum.inl_injective hba] at hb)
  exact Domain.netYield_iff.2
    ⟨tn', decomposesTo_of_clean h hbad hdec hprim hcleanNet, hprim, l, hlin, hseq⟩

end Taint

end HTN
