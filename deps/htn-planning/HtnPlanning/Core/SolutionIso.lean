import HtnPlanning.Core.DecompositionIso
import HtnPlanning.Core.Problem
/-!
# Solvability does not depend on the choice of task identifiers

Building on `HtnPlanning.Core.DecompositionIso`, this file shows that the *solvability* of an
HTN planning problem only depends on its initial task network up to isomorphism
(`HTN.Problem.solvable_congr_tnI`).

Note that solution*hood* of a fixed task network is not invariant under isomorphism: a network
isomorphic to a reachable one need not itself be reachable, because decomposition may only
insert identifiers that are fresh for the current network.  What is invariant are the two
identifier-independent solution criteria, primitiveness (`HTN.TaskNetwork.Iso.isPrimitive`) and
executability (`HTN.Problem.Executable.iso`), together with reachability *up to isomorphism*.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace TaskNetwork

/-- Primitiveness is invariant under isomorphism. -/
lemma Iso.isPrimitive {tn tn' : TaskNetwork I A C} (h : tn.Iso tn') (hprim : tn.IsPrimitive) :
    tn'.IsPrimitive := by
  obtain ⟨σ, hbij, -, hα⟩ := h
  intro t ht
  obtain ⟨s, hs, rfl⟩ := hbij.surjOn (by simpa using ht)
  have hsT : s ∈ tn.T := by simpa using hs
  obtain ⟨a, ha⟩ := hprim s hsT
  exact ⟨a, by rw [← hα s hsT]; exact ha⟩

end TaskNetwork

namespace Problem

/-- Executability is invariant under isomorphism of task networks. -/
lemma Executable.iso [Nonempty I] {P : Problem F A C I} {tn tn' : TaskNetwork I A C}
    (h : P.Executable tn) (hiso : tn.Iso tn') : P.Executable tn' := by
  obtain ⟨l, as, hlin, has, happ, hgoal⟩ := h
  obtain ⟨l', hlin', has'⟩ := (hiso.exists_linearization_actionSeq_iff as).1 ⟨l, hlin, has⟩
  exact ⟨l', as, hlin', has', happ, hgoal⟩

/-- The same planning problem with a different initial task network. -/
def withTnI (P : Problem F A C I) (tn : TaskNetwork I A C) : Problem F A C I :=
  { P with tnI := tn }

@[simp] lemma withTnI_tnI (P : Problem F A C I) (tn : TaskNetwork I A C) :
    (P.withTnI tn).tnI = tn := rfl

@[simp] lemma withTnI_methods (P : Problem F A C I) (tn : TaskNetwork I A C) :
    (P.withTnI tn).methods = P.methods := rfl

/-- **Solvability only depends on the initial task network up to isomorphism.** -/
theorem solvable_congr_tnI [DecidableEq I] [Infinite I] (P : Problem F A C I)
    {tn tn' : TaskNetwork I A C} (hwf : tn.WF) (hwf' : tn'.WF) (hiso : tn.Iso tn') :
    (P.withTnI tn).Solvable → (P.withTnI tn').Solvable := by
  rintro ⟨sol, hreach, hprim, hexec⟩
  obtain ⟨sol', hreach', hsoliso⟩ :=
    HTN.DecomposesTo.iso (M := P.methods) hreach hwf hwf' hiso
  exact ⟨sol', hreach', hsoliso.isPrimitive hprim, hexec.iso hsoliso⟩

/-- **Solvability only depends on the initial task network up to isomorphism** (iff version). -/
theorem solvable_congr_tnI_iff [DecidableEq I] [Infinite I] (P : Problem F A C I)
    {tn tn' : TaskNetwork I A C} (hwf : tn.WF) (hwf' : tn'.WF) (hiso : tn.Iso tn') :
    (P.withTnI tn).Solvable ↔ (P.withTnI tn').Solvable :=
  ⟨P.solvable_congr_tnI hwf hwf' hiso, P.solvable_congr_tnI hwf' hwf hiso.symm⟩

end Problem

end HTN
