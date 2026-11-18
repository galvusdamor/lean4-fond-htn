import HtnPlanning.Computable.Syntax
import HtnPlanning.Computable.ClassesSound
import HtnPlanning.Classes.Basic
import HtnPlanning.SynClasses.Basic
/-!
# The eleven classes of the compilability table, as conditions on descriptions

This file turns the eleven problem classes of the compilability table into predicates on the
finite descriptions of `HtnPlanning/Computable/Syntax.lean` and proves each of them
**sound**: a description satisfying the predicate denotes a problem of the class.

A class is given by a pair of predicates — one on domain descriptions, one on instance
descriptions — which is what keeps the modularity of a compilation scheme (`δ` sees only the
domain, `π` only the instance) available at the level of descriptions.  The bundle is
`HTN.Syn.SynClass 𝒟`, whose field `sound` is the link to the semantic class family
`𝒟 : HTN.Table.Family` of `HtnCompilability/SemTable/TableCore.lean`.

## The predicates

| class | domain condition | instance condition |
| --- | --- | --- |
| `HTN` | — | — |
| `TO-HTN` | every listed method is totally ordered | the initial network is totally ordered |
| `HTN-NOOP` | every action is a no-op | — |
| `HTN-TR` | a rank function decreases outside last tasks | — |
| `HTN-REG` | every listed method is regular | — |
| `HTN-AC` | a rank function decreases | — |
| `STRIPS` | every method decomposes `0` into `ε` or into an action followed by `0` | the initial network is the single compound task `0` |

and the four `TO-` variants are the conjunctions.

Two deliberate choices.

* The structural conditions are imposed on **all listed methods**, while the classes of
  `HtnPlanning/Core/Classes.lean` constrain only the methods *reachable* from the initial
  task network.  Requiring more is sound (a reachable method is listed) and it is what makes
  the condition a condition on the domain alone, independently of the instance — exactly the
  split a compilation scheme needs.
* Acyclicity and tail recursion are stated with an explicit *rank function* `rk : ℕ → ℕ`
  (`∃ rk, …`).  A rank function is what a stratification of `Def. 3.5` / `Def. 3.9` amounts to
  for descriptions, and `HTN.Syn.DomDesc.IsAcyclic.isAcyclic` /
  `HTN.Syn.DomDesc.IsTailRec.isTailRecursive` turn it into the stratification the semantic
  definition asks for (for acyclicity the rank is refined lexicographically by the task name,
  so that the strata are singletons, as `Def. 3.5` requires).
* `STRIPS` descriptions use the compound task name `0`; this is a naming convention, not a
  restriction, since the names of a description may be renamed freely.
-/

namespace HTN

/-! ### Two lemmas on `IsStripsStep` -/

namespace TaskNetwork

variable {I : Type} {A C : Type} [DecidableEq I] {tn : TaskNetwork I A C} {c : C}

/-- The subtask network of a method of a STRIPS-like problem is totally ordered. -/
theorem IsStripsStep.isTotallyOrdered (h : tn.IsStripsStep c) : tn.IsTotallyOrdered := by
  rcases h with hempty | ⟨t₁, t₂, -, hT, -, -, hord⟩
  · intro x hx
    rw [hempty] at hx
    exact absurd hx (Finset.notMem_empty x)
  · intro x hx y hy hxy
    rw [hT] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact Or.inl ((hord x y).2 ⟨rfl, rfl⟩)
    · exact Or.inr ((hord y x).2 ⟨rfl, rfl⟩)
    · exact absurd rfl hxy

/-- The subtask network of a method of a STRIPS-like problem is regular. -/
theorem IsStripsStep.isRegular (h : tn.IsStripsStep c) : tn.IsRegular := by
  rcases h with hempty | ⟨t₁, t₂, hne, hT, hprim, hα₂, hord⟩
  · refine ⟨?_, ?_⟩ <;> intro x hx <;> rw [hempty] at hx <;>
      exact absurd hx (Finset.notMem_empty x)
  · have hmem : ∀ x, x ∈ tn.T ↔ x = t₁ ∨ x = t₂ := by
      intro x; rw [hT]; simp
    have habs₁ : ¬ tn.IsAbstractId t₁ := by
      obtain ⟨a, ha⟩ := hprim
      rintro ⟨c', hc'⟩
      rw [ha] at hc'
      exact absurd hc' (by simp)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hax hay
      rcases (hmem x).1 hx with rfl | rfl <;> rcases (hmem y).1 hy with rfl | rfl
      · rfl
      · exact absurd hax habs₁
      · exact absurd hay habs₁
      · rfl
    · intro x hx hax y hy hyx
      rcases (hmem x).1 hx with rfl | rfl
      · exact absurd hax habs₁
      · rcases (hmem y).1 hy with rfl | rfl
        · exact (hord y x).2 ⟨rfl, rfl⟩
        · exact absurd rfl hyx

end TaskNetwork

namespace Syn

/-! ### The conditions on descriptions -/

namespace DomDesc

end DomDesc

namespace InstDesc

end InstDesc



/-! ### The eleven classes -/

open Table

namespace SynClass

end SynClass

/-! ### Inclusions between the classes of descriptions

The counterpart of `HTN.Table.Sub`: every description of the smaller class is a description of
the larger one.  These are the entries marked `E` of the compilability table. -/

/-- **Inclusion of classes of descriptions.** -/
structure SynSub {𝒟 ℰ : Table.Family} (S : SynClass 𝒟) (T : SynClass ℰ) : Prop where
  /-- Domain descriptions of `S` are domain descriptions of `T`. -/
  dom : ∀ d, S.domOk d → T.domOk d
  /-- Instance descriptions of `S` are instance descriptions of `T`. -/
  inst : ∀ q, S.instOk q → T.instOk q

namespace SynSub

variable {𝒟 ℰ ℱ : Table.Family}

theorem refl (S : SynClass 𝒟) : SynSub S S := ⟨fun _ h => h, fun _ h => h⟩

theorem trans {S : SynClass 𝒟} {T : SynClass ℰ} {U : SynClass ℱ} (h₁ : SynSub S T)
    (h₂ : SynSub T U) : SynSub S U :=
  ⟨fun d hd => h₂.dom d (h₁.dom d hd), fun q hq => h₂.inst q (h₁.inst q hq)⟩

end SynSub

namespace SynClass

/-- Every class of descriptions is contained in `HTN`. -/
theorem sub_HTN {𝒟 : Table.Family} (S : SynClass 𝒟) : SynSub S HTN :=
  ⟨fun _ _ => trivial, fun _ _ => trivial⟩

theorem sub_TO_HTN_NOOP_TO_HTN : SynSub TO_HTN_NOOP TO_HTN :=
  ⟨fun _ hd => hd.1, fun _ hq => hq⟩

theorem sub_TO_HTN_NOOP_HTN_NOOP : SynSub TO_HTN_NOOP HTN_NOOP :=
  ⟨fun _ hd => hd.2, fun _ _ => trivial⟩

theorem sub_TO_HTN_TR_TO_HTN : SynSub TO_HTN_TR TO_HTN := ⟨fun _ hd => hd.1, fun _ hq => hq⟩

theorem sub_TO_HTN_TR_HTN_TR : SynSub TO_HTN_TR HTN_TR := ⟨fun _ hd => hd.2, fun _ _ => trivial⟩

/-- **A regular domain description is tail recursive**: in a regular subtask network every
compound task is a last task, so the constant rank function works. -/
theorem methodsReg_isTailRec {d : DomDesc} (h : d.MethodsReg) : d.IsTailRec := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he t ht c hc
  refine ⟨fun _ => le_rfl, fun hlast => absurd ?_ hlast⟩
  exact (h e he).isLastId ht ⟨c, hc⟩

/-- **An acyclic domain description is tail recursive**: the same rank function works. -/
theorem isAcyclic_isTailRec {d : DomDesc} (h : d.IsAcyclic) : d.IsTailRec := by
  obtain ⟨rk, hrk⟩ := h
  exact ⟨rk, fun e he t ht c hc => ⟨fun _ => (hrk e he t ht c hc).le, fun _ => hrk e he t ht c hc⟩⟩

theorem sub_HTN_REG_HTN_TR : SynSub HTN_REG HTN_TR :=
  ⟨fun _ hd => methodsReg_isTailRec hd, fun _ _ => trivial⟩

theorem sub_HTN_AC_HTN_TR : SynSub HTN_AC HTN_TR :=
  ⟨fun _ hd => isAcyclic_isTailRec hd, fun _ _ => trivial⟩

theorem sub_TO_HTN_REG_TO_HTN_TR : SynSub TO_HTN_REG TO_HTN_TR :=
  ⟨fun _ hd => ⟨hd.1, methodsReg_isTailRec hd.2⟩, fun _ hq => hq.1⟩

theorem sub_TO_HTN_REG_HTN_REG : SynSub TO_HTN_REG HTN_REG :=
  ⟨fun _ hd => hd.2, fun _ hq => hq.2⟩

theorem sub_TO_HTN_AC_TO_HTN_TR : SynSub TO_HTN_AC TO_HTN_TR :=
  ⟨fun _ hd => ⟨hd.1, isAcyclic_isTailRec hd.2⟩, fun _ hq => hq⟩

theorem sub_TO_HTN_AC_HTN_AC : SynSub TO_HTN_AC HTN_AC := ⟨fun _ hd => hd.2, fun _ _ => trivial⟩

/-- A `STRIPS` domain description has totally ordered methods. -/
theorem isStrips_methodsTO {d : DomDesc} (h : d.IsStrips) : d.MethodsTO :=
  fun e he => (h e he).2.isTotallyOrdered

/-- A `STRIPS` domain description has regular methods. -/
theorem isStrips_methodsReg {d : DomDesc} (h : d.IsStrips) : d.MethodsReg :=
  fun e he => (h e he).2.isRegular

theorem sub_STRIPS_TO_HTN_REG : SynSub STRIPS TO_HTN_REG :=
  ⟨fun _ hd => ⟨isStrips_methodsTO hd, isStrips_methodsReg hd⟩, fun _ hq => ⟨hq.isTO, hq.isRegular⟩⟩

theorem sub_STRIPS_TO_HTN_TR : SynSub STRIPS TO_HTN_TR :=
  sub_STRIPS_TO_HTN_REG.trans sub_TO_HTN_REG_TO_HTN_TR

/-! Derived inclusions. -/

theorem sub_TO_HTN_REG_TO_HTN : SynSub TO_HTN_REG TO_HTN :=
  sub_TO_HTN_REG_TO_HTN_TR.trans sub_TO_HTN_TR_TO_HTN

theorem sub_TO_HTN_REG_HTN_TR : SynSub TO_HTN_REG HTN_TR :=
  sub_TO_HTN_REG_HTN_REG.trans sub_HTN_REG_HTN_TR

theorem sub_TO_HTN_AC_TO_HTN : SynSub TO_HTN_AC TO_HTN :=
  sub_TO_HTN_AC_TO_HTN_TR.trans sub_TO_HTN_TR_TO_HTN

theorem sub_TO_HTN_AC_HTN_TR : SynSub TO_HTN_AC HTN_TR :=
  sub_TO_HTN_AC_HTN_AC.trans sub_HTN_AC_HTN_TR

theorem sub_STRIPS_TO_HTN : SynSub STRIPS TO_HTN :=
  sub_STRIPS_TO_HTN_REG.trans sub_TO_HTN_REG_TO_HTN

theorem sub_STRIPS_HTN_REG : SynSub STRIPS HTN_REG :=
  sub_STRIPS_TO_HTN_REG.trans sub_TO_HTN_REG_HTN_REG

theorem sub_STRIPS_HTN_TR : SynSub STRIPS HTN_TR :=
  sub_STRIPS_HTN_REG.trans sub_HTN_REG_HTN_TR

end SynClass

end Syn

end HTN
