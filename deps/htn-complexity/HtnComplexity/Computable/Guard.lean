import HtnPlanning.Computable.Bodies
import HtnPlanning.Computable.Classes
/-!
# The guard gadget

A **guard domain** is the simplest described domain that reads a state and does nothing else:
for a list `P` of precondition lists it has one action per entry of `P`, with that entry as its
precondition and with no effect, and one method per entry, decomposing the compound task `0`
into the single primitive task of that action.  A **guard instance** holds a list `L` of facts,
has no goal and has the single compound task `0` as its initial task network.

The described problem is solvable exactly when one of the guards is satisfied:

    HTN.Syn.solvable_guard_iff : Solvable (guardDom P) (guardInst L) ↔
      ∃ i < P.length, ∀ f ∈ P.getI i, f ∈ L

The gadget is totally ordered, regular and acyclic, and its instance is rooted, so it lies in
every class of the table except the `NOOP` ones (whose actions must have no precondition).  It
is used in `HtnCompilability/Computable/SizeFree.lean` as the target of a compilation that
carries a single bit of information from the instance to the domain.
-/

namespace HTN

namespace Syn

/-! ### Two lemmas on lists indexed by `List.range` -/

/-- Looking up an index in a list indexed by `List.range`. -/
theorem lookup_range_map {β : Type} (f : ℕ → β) {n i : ℕ} (h : i < n) :
    ((List.range n).map (fun j => (j, f j))).lookup i = some (f i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.lookup_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [ih h']
      rfl
    · have hn : ((List.range i).map (fun j => (j, f j))).lookup i = none := by
        rw [List.lookup_eq_none_iff]
        simp
        omega
      rw [hn]
      simp

/-- The `i`-th entry of a list indexed by `List.range`. -/
theorem getI_range_map {β : Type} [Inhabited β] (f : ℕ → β) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getI i = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using h
  rw [List.getI_eq_getElem _ hlen]
  simp

/-! ### The gadget -/

/-- The **guard domain** of a list of precondition lists: one effect-free action per entry, and
one method decomposing the compound task `0` into it. -/
def guardDom (P : List (List ℕ)) : DomDesc :=
  ((List.range P.length).map fun i => (i, P.getI i, ([] : List ℕ), ([] : List ℕ)),
    (List.range P.length).map fun i => ((0 : ℕ), (([0], [], [(0, false, i)]) : TnDesc)))

/-- The **guard instance** of a list of facts: those facts hold initially, there is no goal, and
the initial task network is the single compound task `0`. -/
def guardInst (L : List ℕ) : InstDesc := (L, [], (([0], [], [(0, true, 0)]) : TnDesc))

variable {P : List (List ℕ)} {L : List ℕ}

@[simp] theorem guardDom_methods :
    (guardDom P).methods =
      (List.range P.length).map fun i => ((0 : ℕ), (([0], [], [(0, false, i)]) : TnDesc)) := rfl

@[simp] theorem guardDom_actions :
    (guardDom P).actions =
      (List.range P.length).map fun i => (i, P.getI i, ([] : List ℕ), ([] : List ℕ)) := rfl

@[simp] theorem guardInst_initList : (guardInst L).initList = L := rfl

@[simp] theorem guardInst_goalList : (guardInst L).goalList = [] := rfl

@[simp] theorem guardInst_tnI : (guardInst L).tnI = (([0], [], [(0, true, 0)]) : TnDesc) := rfl

theorem length_guardDom_methods : (guardDom P).methods.length = P.length := by
  simp

/-! ### The gadget is in the classes -/

theorem guardInst_isRooted : (guardInst L).IsRooted := by
  refine ⟨0, 0, ?_, rfl⟩
  simp [guardInst, InstDesc.tnI, TnDesc.toTaskNetwork, TnDesc.ids]

theorem guardInst_isTO : (guardInst L).IsTO := guardInst_isRooted.isTO

/-- The subtask network of a method of a guard domain has the single identifier `0`, labelled
with an action. -/
theorem guardDom_method_mem {e : MethodDesc} (he : e ∈ (guardDom P).methods) :
    ∃ i, e = ((0 : ℕ), (([0], [], [(0, false, i)]) : TnDesc)) := by
  simp only [guardDom_methods, List.mem_map, List.mem_range] at he
  obtain ⟨i, -, rfl⟩ := he
  exact ⟨i, rfl⟩

theorem guardDom_mem_T {i x : ℕ}
    (hx : x ∈ (TnDesc.toTaskNetwork (([0], [], [(0, false, i)]) : TnDesc)).T) : x = 0 := by
  simpa [TnDesc.toTaskNetwork, TnDesc.ids] using hx

theorem guardDom_not_abstract {i : ℕ} :
    ¬ (TnDesc.toTaskNetwork (([0], [], [(0, false, i)]) : TnDesc)).IsAbstractId 0 := by
  rintro ⟨c, hc⟩
  simp [TnDesc.toTaskNetwork, TnDesc.label, TnDesc.lbl] at hc

theorem guardDom_methodsTO : (guardDom P).MethodsTO := by
  intro e he
  obtain ⟨i, rfl⟩ := guardDom_method_mem he
  intro x hx y hy hxy
  exact absurd ((guardDom_mem_T hx).trans (guardDom_mem_T hy).symm) hxy

theorem guardDom_methodsReg : (guardDom P).MethodsReg := by
  intro e he
  obtain ⟨i, rfl⟩ := guardDom_method_mem he
  refine ⟨fun x hx y hy _ _ => (guardDom_mem_T hx).trans (guardDom_mem_T hy).symm,
    fun x hx hax y _ _ => ?_⟩
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, i)]) : TnDesc)).IsAbstractId 0
    from guardDom_mem_T hx ▸ hax) guardDom_not_abstract

theorem guardDom_isAcyclic : (guardDom P).IsAcyclic := by
  refine ⟨fun _ => 0, ?_⟩
  intro e he t ht c hc
  obtain ⟨i, rfl⟩ := guardDom_method_mem he
  exact absurd (show (TnDesc.toTaskNetwork (([0], [], [(0, false, i)]) : TnDesc)).IsAbstractId 0
    from ⟨c, guardDom_mem_T ht ▸ hc⟩) guardDom_not_abstract

theorem guardDom_isTailRec : (guardDom P).IsTailRec :=
  SynClass.isAcyclic_isTailRec guardDom_isAcyclic

theorem domOk_guardDom_TO_HTN_AC_root : SynClass.TO_HTN_AC_root.domOk (guardDom P) :=
  ⟨guardDom_methodsTO, guardDom_isAcyclic⟩

theorem instOk_guardInst_TO_HTN_AC_root : SynClass.TO_HTN_AC_root.instOk (guardInst L) :=
  guardInst_isRooted

/-! ### The bodies and the preconditions -/

/-- The head of the `m`-th method of a guard domain is the compound task `0`. -/
theorem hd_guardDom {m : ℕ} (h : m < P.length) : (guardDom P).hd m = 0 := by
  rw [DomDesc.hd, guardDom_methods, getI_range_map _ h]

/-- The body of the `m`-th method of a guard domain is the single primitive task `m`. -/
theorem bd_guardDom {m : ℕ} (h : m < P.length) : (guardDom P).bd m = [Sum.inl m] := by
  rw [DomDesc.bd, guardDom_methods, getI_range_map _ h]
  rfl

/-- The precondition of the `i`-th action of a guard domain is the `i`-th entry of `P`. -/
theorem prec_guardDom {i : ℕ} (h : i < P.length) :
    (guardDom P).prec i = {f | f ∈ P.getI i} := by
  have hlookup := lookup_range_map (fun j => (P.getI j, ([] : List ℕ), ([] : List ℕ))) h
  simp only [DomDesc.prec, guardDom_actions]
  rw [hlookup]
  rfl

/-! ### Solvability of the gadget -/

/-- The refinements of the compound task `0` in a guard domain are the one-element action
sequences of the guards. -/
theorem yieldSeq_guardDom_iff {as : List ℕ} :
    (guardDom P).toDomain.YieldSeq [Sum.inr 0] as ↔ ∃ i, i < P.length ∧ as = [i] := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      obtain ⟨m, hm', hhd, hbd⟩ := (DomDesc.seqBody_iff guardDom_methodsTO).1 hm
      rw [length_guardDom_methods] at hm'
      rw [bd_guardDom hm'] at hbd
      subst hbd
      rw [List.append_nil] at h
      cases h with
      | prim h =>
        cases h
        exact ⟨m, hm', rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine Domain.YieldSeq.comp (bs := [Sum.inl i]) ?_ ?_
    · refine (DomDesc.seqBody_iff guardDom_methodsTO).2 ⟨i, ?_, ?_, bd_guardDom hi⟩
      · rwa [length_guardDom_methods]
      · exact hd_guardDom hi
    · simpa using Domain.YieldSeq.prim (as := []) Domain.YieldSeq.nil

/-- **The guard gadget is solvable exactly when one of its guards holds.** -/
theorem solvable_guard_iff :
    Solvable (guardDom P) (guardInst L) ↔ ∃ i, i < P.length ∧ ∀ f ∈ P.getI i, f ∈ L := by
  have hseq : ((guardInst L).tnI).toTaskNetwork.IsSeqNet
      (TnDesc.lin (guardInst L).tnI) (TnDesc.seqBody (guardInst L).tnI) :=
    TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (guardInst L).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (guardDom P) (guardInst L))
    (isTO_problem guardDom_methodsTO guardInst_isTO).2 hseq
  rw [show Solvable (guardDom P) (guardInst L) = (problem (guardDom P) (guardInst L)).Solvable
    from rfl, hnorm, hbody]
  constructor
  · rintro ⟨as, hy, happ, -⟩
    obtain ⟨i, hi, rfl⟩ := yieldSeq_guardDom_iff.1 hy
    refine ⟨i, hi, fun f hf => ?_⟩
    have : (problem (guardDom P) (guardInst L)).prec i ⊆ {f | f ∈ (guardInst L).initList} :=
      happ.1
    have hmem : f ∈ (problem (guardDom P) (guardInst L)).prec i := by
      rw [problem_prec, prec_guardDom hi]
      exact hf
    exact this hmem
  · rintro ⟨i, hi, hsub⟩
    refine ⟨[i], yieldSeq_guardDom_iff.2 ⟨i, hi, rfl⟩, ⟨?_, trivial⟩, ?_⟩
    · intro f hf
      rw [problem_prec, prec_guardDom hi] at hf
      exact hsub f hf
    · intro f hf
      simp only [problem_goal, guardInst_goalList, Set.mem_setOf_eq, List.not_mem_nil] at hf

/-- **The guard gadget is solvable exactly when one of its guards holds** — the membership
form. -/
theorem solvable_guard_iff' :
    Solvable (guardDom P) (guardInst L) ↔ ∃ p ∈ P, ∀ f ∈ p, f ∈ L := by
  rw [solvable_guard_iff]
  constructor
  · rintro ⟨i, hi, hsub⟩
    refine ⟨P.getI i, ?_, hsub⟩
    rw [List.getI_eq_getElem (l := P) hi]
    exact List.getElem_mem hi
  · rintro ⟨p, hp, hsub⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    exact ⟨i, hi, by rwa [List.getI_eq_getElem (l := P) hi]⟩

end Syn

end HTN
