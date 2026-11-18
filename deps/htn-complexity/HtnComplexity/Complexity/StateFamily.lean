import HtnComplexity.Complexity.AutFamily
/-!
# A hardness family whose fixed part is a machine with a memory

`HtnComplexity/Complexity/AutFamily.lean` puts a *finite automaton* into the fixed domain
description: the state of the machine is carried by the name of the compound task, so a domain
of polynomial size can only have polynomially many states, and the languages the family covers
are the regular ones.

This file keeps the same shape — the input is read from the initial state through the positional
facts `HTN.Syn.posFact`, the instance description is `HTN.Syn.posEnc`, the initial task network
is the single compound task `0` — but gives the machine a **memory**: the state of the machine
is the *planning state*, a set of facts, and a transition is an ordinary planning action.  The
compound task name now carries only the number `k` of bits still to be read, so the domain has
`n + 1` compound tasks and `n · |trans| + 1` actions for words of length `n` — a description of
size linear in `n` — while the machine has `2^m` configurations over `m` facts.  This is the
shape of the space-bounded hardness constructions of the literature.

* `HTN.Syn.BitMach` — a machine: a list of transitions `(precondition, bit, add, delete)` and a
  goal; `HTN.Syn.BitMach.Halts M k s` — from the state `s`, reading the `k` bits that remain,
  the machine reaches a state satisfying its goal;
* `HTN.Syn.machDom M n` — the domain description, and
  `HTN.Syn.solvable_machDom_iff : Solvable (machDom M w.length) (posEnc w) ↔ LMach M w`;
* `HTN.Syn.machFamily M : Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root (LMach M)`,
  transported to `TO-HTN`, `HTN-TR` and `HTN-AC`.

The hierarchy is used for exactly one thing: counting the positions.  That is not an accident —
a `STRIPS` description has a single compound task name, so a domain of the `STRIPS` class cannot
count the positions of the input at all unless a counter is supplied in the initial state, which
the positional encoding does not do.
-/

namespace HTN

namespace Syn

open Binarise

/-! ### Machines with a memory -/

/-- A **transition** of a bit machine: its precondition, the bit it reads, its add list and its
delete list. -/
abbrev BitTr : Type := List ℕ × Bool × List ℕ × List ℕ

namespace BitTr

/-- The precondition of a transition. -/
def prec (t : BitTr) : List ℕ := t.1

/-- The bit a transition reads. -/
def bit (t : BitTr) : Bool := t.2.1

/-- The add list of a transition. -/
def add (t : BitTr) : List ℕ := t.2.2.1

/-- The delete list of a transition. -/
def del (t : BitTr) : List ℕ := t.2.2.2

/-- The number of facts a transition mentions. -/
def size (t : BitTr) : ℕ := t.prec.length + t.add.length + t.del.length

/-- The state a transition leads to. -/
def step (t : BitTr) (s : Set ℕ) : Set ℕ := (s \ {f | f ∈ t.del}) ∪ {f | f ∈ t.add}

end BitTr

/-- A **machine with a memory**: a list of transitions and a goal.  Its configurations are sets
of facts; it reads one bit per step from the positional facts of the input. -/
structure BitMach where
  /-- The transitions. -/
  trans : List BitTr
  /-- The goal the machine has to reach. -/
  goal : List ℕ

namespace BitMach

/-- **The machine reaches its goal** from the state `s` with `k` bits still to read. -/
inductive Halts (M : BitMach) : ℕ → Set ℕ → Prop
  /-- With no bit left the state must satisfy the goal. -/
  | nil {s : Set ℕ} (h : ∀ f ∈ M.goal, f ∈ s) : Halts M 0 s
  /-- A transition whose precondition holds and whose bit is the one at the position with `k`
  bits after it is taken. -/
  | cons {k : ℕ} {s : Set ℕ} {t : BitTr} (ht : t ∈ M.trans) (hp : ∀ f ∈ t.prec, f ∈ s)
      (hpos : posFact k t.bit ∈ s) (h' : Halts M k (t.step s)) : Halts M (k + 1) s

end BitMach

/-- **The language of a machine**: it reaches its goal from the facts of the word. -/
def LMach (M : BitMach) (w : List Bool) : Prop := M.Halts w.length {f | f ∈ posFacts w}

/-! ### The names of the encoding -/

/-- The compound task standing for "`k` bits are still to be read" in a word of length `n`.  The
configuration `k = n` is named `0`, the name of the root task of `HTN.Syn.posEnc`. -/
def sName (n k : ℕ) : ℕ := swapZero n k

@[simp] theorem sName_root (n : ℕ) : sName n n = 0 := by simp [sName, swapZero]

theorem sName_inj {n k k' : ℕ} (h : sName n k = sName n k') : k = k' :=
  swapZero_injective _ h

variable {M : BitMach}

/-- The action of the `i`-th transition taken when `k` bits have already been read. -/
def aIdx (M : BitMach) (k i : ℕ) : ℕ := i + M.trans.length * k

theorem aIdx_lt {n k i : ℕ} (hk : k < n) (hi : i < M.trans.length) :
    aIdx M k i < n * M.trans.length := by
  have h : i + M.trans.length * k < M.trans.length * (k + 1) := by
    rw [Nat.mul_succ]
    omega
  calc aIdx M k i < M.trans.length * (k + 1) := h
    _ ≤ M.trans.length * n := Nat.mul_le_mul_left _ hk
    _ = n * M.trans.length := Nat.mul_comm _ _

theorem aIdx_div {k i : ℕ} (hi : i < M.trans.length) : aIdx M k i / M.trans.length = k := by
  rw [aIdx, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem aIdx_mod {k i : ℕ} (hi : i < M.trans.length) : aIdx M k i % M.trans.length = i := by
  rw [aIdx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

/-! ### The domain description -/

/-- The data of the action `j`: the transition it takes, guarded by the fact of the bit it reads,
or — for the last action — the goal check. -/
def machActData (M : BitMach) (n j : ℕ) : List ℕ × List ℕ × List ℕ :=
  if j < n * M.trans.length then
    (posFact (j / M.trans.length) (M.trans.getI (j % M.trans.length)).bit
        :: (M.trans.getI (j % M.trans.length)).prec,
      (M.trans.getI (j % M.trans.length)).add,
      (M.trans.getI (j % M.trans.length)).del)
  else (M.goal, [], [])

/-- The actions of the encoding. -/
def machActions (M : BitMach) (n : ℕ) : List ActionDesc :=
  (List.range (n * M.trans.length + 1)).map fun j => (j, machActData M n j)

/-- The reading methods: one per position and per transition. -/
def machReadMethods (M : BitMach) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => (List.range M.trans.length).map fun i =>
    (sName n (k + 1), pairBody (Sum.inl (aIdx M k i)) (Sum.inr (sName n k)))

/-- The description of the network with the single primitive task `a`. -/
def singleBody (a : ℕ) : TnDesc := ([0], [], [(0, false, a)])

/-- The final method: when no bit is left, check the goal. -/
def machGoalMethods (M : BitMach) (n : ℕ) : List MethodDesc :=
  [(sName n 0, singleBody (n * M.trans.length))]

/-- **The domain description of the encoding** for the words of length `n`. -/
def machDom (M : BitMach) (n : ℕ) : DomDesc :=
  (machActions M n, machReadMethods M n ++ machGoalMethods M n)

@[simp] theorem machDom_actions (n : ℕ) : (machDom M n).actions = machActions M n := rfl

@[simp] theorem machDom_methods (n : ℕ) :
    (machDom M n).methods = machReadMethods M n ++ machGoalMethods M n := rfl

theorem mem_machReadMethods {n : ℕ} {e : MethodDesc} (he : e ∈ machReadMethods M n) :
    ∃ k < n, ∃ i < M.trans.length,
      e = (sName n (k + 1), pairBody (Sum.inl (aIdx M k i)) (Sum.inr (sName n k))) := by
  simp only [machReadMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, i, hi, rfl⟩ := he
  exact ⟨k, hk, i, hi, rfl⟩

theorem mem_machGoalMethods {n : ℕ} {e : MethodDesc} (he : e ∈ machGoalMethods M n) :
    e = (sName n 0, singleBody (n * M.trans.length)) := by
  simpa [machGoalMethods] using he

/-! ### The single-task body -/

theorem singleBody_isSeqNet (a : ℕ) :
    (singleBody a).toTaskNetwork.IsSeqNet [0] [Sum.inl a] := by
  refine ⟨by simp, fun x => ?_, rfl, fun x y => ?_⟩
  · simp [singleBody, TnDesc.toTaskNetwork, TnDesc.ids]
  · constructor
    · rintro ⟨hx, hy, hpre, -⟩
      exfalso
      rcases Relation.TransGen.head'_iff.1 hpre with ⟨c, hc, -⟩
      simp [TnDesc.listRel, singleBody, TnDesc.ordList] at hc
    · rintro ⟨hx, hy, hidx⟩
      simp only [List.mem_singleton] at hx hy
      subst hx
      subst hy
      simp at hidx

theorem singleBody_isTO (a : ℕ) : (singleBody a).toTaskNetwork.IsTotallyOrdered :=
  (singleBody_isSeqNet a).isTotallyOrdered

/-! ### The domain is in the class -/

theorem machDom_methodsTO (n : ℕ) : (machDom M n).MethodsTO := by
  intro e he
  rw [machDom_methods, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, -, i, -, rfl⟩ := mem_machReadMethods he
    exact pairBody_isTO _ _
  · rw [mem_machGoalMethods he]
    exact singleBody_isTO _

/-- The rank of a compound task name: the number of bits still to be read. -/
def machRank (n c : ℕ) : ℕ := swapZero n c

@[simp] theorem machRank_sName (n k : ℕ) : machRank n (sName n k) = k := by
  simp [machRank, sName, swapZero_swapZero]

theorem machDom_isAcyclic (n : ℕ) : (machDom M n).IsAcyclic := by
  refine ⟨machRank n, ?_⟩
  intro e he t ht c hc
  rw [machDom_methods, List.mem_append] at he
  rcases he with he | he
  · obtain ⟨k, -, i, -, rfl⟩ := mem_machReadMethods he
    have ht' : t = 0 ∨ t = 1 := by
      simpa [TnDesc.toTaskNetwork, pairBody, TnDesc.ids] using ht
    rcases ht' with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp
  · rw [mem_machGoalMethods he] at hc ht
    have ht' : t = 0 := by
      simpa [TnDesc.toTaskNetwork, singleBody, TnDesc.ids] using ht
    subst ht'
    simp [TnDesc.toTaskNetwork, TnDesc.label, singleBody, TnDesc.lbl] at hc

theorem machDom_domOk (n : ℕ) : SynClass.TO_HTN_AC_root.domOk (machDom M n) :=
  ⟨machDom_methodsTO n, machDom_isAcyclic n⟩

/-! ### The bodies the domain offers -/

theorem seqBody_machDom_iff {n k : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (machDom M n).toDomain.SeqBody (sName n k) xs ↔
      (∃ j < n, ∃ i < M.trans.length, k = j + 1 ∧
        xs = [Sum.inl (aIdx M j i), Sum.inr (sName n j)]) ∨
      (k = 0 ∧ xs = [Sum.inl (n * M.trans.length)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rw [machDom_methods, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨j, hj, i, hi, rfl⟩ := mem_machReadMethods he
      have hk := sName_inj hc
      subst hk
      exact Or.inl ⟨j, hj, i, hi, rfl,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · rw [mem_machGoalMethods he] at hc hbody
      have hk := sName_inj hc
      subst hk
      exact Or.inr ⟨rfl, (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).1 hbody⟩
  · rintro (⟨j, hj, i, hi, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨(sName n (j + 1), pairBody (Sum.inl (aIdx M j i)) (Sum.inr (sName n j))), ?_, rfl,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl⟩
      rw [machDom_methods, List.mem_append]
      refine Or.inl ?_
      simp only [machReadMethods, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨j, hj, i, hi, rfl⟩
    · refine ⟨(sName n 0, singleBody (n * M.trans.length)), ?_, rfl,
        (Method.hasSeqBody_iff_of_isSeqNet (singleBody_isSeqNet _)).2 rfl⟩
      rw [machDom_methods, List.mem_append]
      exact Or.inr (by simp [machGoalMethods])

/-! ### The actions of the encoding -/

theorem lookup_machActions {n j : ℕ} (hj : j < n * M.trans.length + 1) :
    (machActions M n).lookup j = some (machActData M n j) :=
  lookup_range_map (fun j => machActData M n j) hj

theorem prec_machDom {n j : ℕ} (hj : j < n * M.trans.length + 1) :
    (machDom M n).prec j = {f | f ∈ (machActData M n j).1} := by
  simp only [DomDesc.prec, machDom_actions, lookup_machActions hj]
  rfl

theorem add_machDom {n j : ℕ} (hj : j < n * M.trans.length + 1) :
    (machDom M n).add j = {f | f ∈ (machActData M n j).2.1} := by
  simp only [DomDesc.add, machDom_actions, lookup_machActions hj]
  rfl

theorem del_machDom {n j : ℕ} (hj : j < n * M.trans.length + 1) :
    (machDom M n).del j = {f | f ∈ (machActData M n j).2.2} := by
  simp only [DomDesc.del, machDom_actions, lookup_machActions hj]
  rfl

theorem machActData_read {n k i : ℕ} (hk : k < n) (hi : i < M.trans.length) :
    machActData M n (aIdx M k i) =
      (posFact k (M.trans.getI i).bit :: (M.trans.getI i).prec,
        (M.trans.getI i).add, (M.trans.getI i).del) := by
  rw [machActData, if_pos (aIdx_lt hk hi), aIdx_div hi, aIdx_mod hi]

theorem machActData_goal (n : ℕ) :
    machActData M n (n * M.trans.length) = (M.goal, [], []) := by
  rw [machActData, if_neg (by omega)]

theorem transition_machDom_read {n k i : ℕ} (hk : k < n) (hi : i < M.trans.length) (s : Set ℕ) :
    (machDom M n).toDomain.transition (aIdx M k i) s = (M.trans.getI i).step s := by
  have hj : aIdx M k i < n * M.trans.length + 1 := by
    have := aIdx_lt (M := M) hk hi
    omega
  show ((s \ (machDom M n).del (aIdx M k i)) ∪ (machDom M n).add (aIdx M k i)) = _
  rw [add_machDom hj, del_machDom hj, machActData_read hk hi]
  rfl

/-! ### The simulation -/

theorem yieldSeq_machDom_iff (M : BitMach) (n : ℕ) : ∀ k, k ≤ n → ∀ s : Set ℕ,
    ((∃ as : List ℕ, (machDom M n).toDomain.YieldSeq [Sum.inr (sName n k)] as ∧
      (machDom M n).toDomain.SeqApplicable as s) ↔ M.Halts k s) := by
  intro k
  induction k with
  | zero =>
    intro _ s
    constructor
    · rintro ⟨as, hy, happ⟩
      cases hy with
      | comp hm h =>
        rcases seqBody_machDom_iff.1 hm with ⟨j, -, i, -, hj, -⟩ | ⟨-, rfl⟩
        · exact absurd hj.symm (by simp)
        · rw [List.cons_append, List.nil_append] at h
          cases h with
          | prim h =>
            cases h with
            | nil =>
              refine BitMach.Halts.nil fun f hf => ?_
              have happ1 : (machDom M n).prec (n * M.trans.length) ⊆ s := happ.1
              refine happ1 ?_
              rw [prec_machDom (by omega), machActData_goal]
              exact hf
    · intro h
      cases h with
      | nil hg =>
        refine ⟨[n * M.trans.length], ?_, ?_⟩
        · refine Domain.YieldSeq.comp
            (bs := [Sum.inl (n * M.trans.length)]) (seqBody_machDom_iff.2 (Or.inr ⟨rfl, rfl⟩)) ?_
          rw [List.cons_append, List.nil_append]
          exact Domain.YieldSeq.prim Domain.YieldSeq.nil
        · refine ⟨fun f hf => ?_, trivial⟩
          rw [DomDesc.toDomain_prec,
            prec_machDom (M := M) (n := n) (j := n * M.trans.length) (by omega),
            machActData_goal] at hf
          exact hg f hf
  | succ k ih =>
    intro hk s
    have hkn : k < n := by omega
    constructor
    · rintro ⟨as, hy, happ⟩
      cases hy with
      | comp hm h =>
        rcases seqBody_machDom_iff.1 hm with ⟨j, hj, i, hi, hjk, rfl⟩ | ⟨hk0, -⟩
        · have hjk' : j = k := by omega
          subst hjk'
          rw [List.cons_append, List.cons_append, List.nil_append] at h
          cases h with
          | prim h =>
            rename_i as'
            have hjlt : aIdx M j i < n * M.trans.length + 1 := by
              have := aIdx_lt (M := M) hj hi
              omega
            obtain ⟨happ1, happ2⟩ := happ
            have hprec : (machDom M n).prec (aIdx M j i) ⊆ s := happ1
            rw [prec_machDom hjlt, machActData_read hj hi] at hprec
            refine BitMach.Halts.cons (t := M.trans.getI i) ?_ ?_ ?_ ?_
            · rw [List.getI_eq_getElem (l := M.trans) hi]
              exact List.getElem_mem hi
            · exact fun f hf => hprec (List.mem_cons_of_mem _ hf)
            · exact hprec (List.mem_cons_self)
            · refine (ih (by omega) _).1 ⟨as', h, ?_⟩
              rwa [transition_machDom_read hj hi] at happ2
        · exact absurd hk0 (by simp)
    · intro h
      cases h with
      | cons ht hp hpos h' =>
        rename_i t
        obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.1 ht
        have hgi : M.trans.getI i = t := by
          rw [List.getI_eq_getElem (l := M.trans) hi, hti]
        obtain ⟨as', hy', happ'⟩ := (ih (by omega) (t.step s)).2 h'
        have hjlt : aIdx M k i < n * M.trans.length + 1 := by
          have := aIdx_lt (M := M) hkn hi
          omega
        refine ⟨aIdx M k i :: as', ?_, ?_⟩
        · refine Domain.YieldSeq.comp
            (bs := [Sum.inl (aIdx M k i), Sum.inr (sName n k)])
            (seqBody_machDom_iff.2 (Or.inl ⟨k, hkn, i, hi, rfl, rfl⟩)) ?_
          rw [List.cons_append, List.cons_append, List.nil_append]
          exact Domain.YieldSeq.prim hy'
        · refine ⟨?_, ?_⟩
          · intro f hf
            rw [DomDesc.toDomain_prec, prec_machDom hjlt, machActData_read hkn hi, hgi] at hf
            rcases List.mem_cons.1 hf with rfl | hf
            · exact hpos
            · exact hp f hf
          · rw [transition_machDom_read hkn hi, hgi]
            exact happ'

/-- **The encoded problem is solvable exactly when the machine reaches its goal.** -/
theorem solvable_machDom_iff (w : List Bool) :
    Solvable (machDom M w.length) (posEnc w) ↔ LMach M w := by
  have hseq : ((posEnc w).tnI).toTaskNetwork.IsSeqNet (TnDesc.lin (posEnc w).tnI)
      (TnDesc.seqBody (posEnc w).tnI) := TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (posEnc w).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (machDom M w.length) (posEnc w))
    (isTO_problem (machDom_methodsTO (M := M) w.length) guardInst_isTO).2 hseq
  rw [show Solvable (machDom M w.length) (posEnc w)
      = (problem (machDom M w.length) (posEnc w)).Solvable from rfl, hnorm, hbody]
  have key := yieldSeq_machDom_iff M w.length w.length le_rfl {f | f ∈ posFacts w}
  rw [sName_root] at key
  constructor
  · rintro ⟨as, hy, happ, -⟩
    exact key.1 ⟨as, hy, happ⟩
  · intro h
    obtain ⟨as, hy, happ⟩ := key.2 h
    refine ⟨as, hy, happ, ?_⟩
    intro f hf
    simp only [problem_goal, InstDesc.goalList, posEnc, guardInst, Set.mem_setOf_eq,
      List.not_mem_nil] at hf

/-! ### Size -/

/-- The total number of facts the transitions of the machine mention. -/
def trBudget (M : BitMach) : ℕ := (M.trans.map BitTr.size).sum

theorem size_getI_le (i : ℕ) : (M.trans.getI i).size ≤ trBudget M := by
  by_cases hi : i < M.trans.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.trans) hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

/-- A bound on the size of every action of the encoding. -/
def actBudget (M : BitMach) : ℕ := 2 + trBudget M + M.goal.length

theorem size_machActData_le (n j : ℕ) :
    ActionDesc.size (j, machActData M n j) ≤ actBudget M := by
  rw [ActionDesc.size, machActData]
  by_cases hj : j < n * M.trans.length
  · have h := size_getI_le (M := M) (j % M.trans.length)
    rw [BitTr.size] at h
    simp only [if_pos hj, List.length_cons]
    rw [actBudget]
    omega
  · simp only [if_neg hj, List.length_nil]
    rw [actBudget]
    omega

theorem size_machActions_le (n : ℕ) :
    ((machActions M n).map ActionDesc.size).sum ≤ (n * M.trans.length + 1) * actBudget M := by
  have hb : ∀ x ∈ (machActions M n).map ActionDesc.size, x ≤ actBudget M := by
    intro x hx
    simp only [List.mem_map, machActions] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simp only [List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact size_machActData_le n j
  have h := List.sum_le_card_nsmul _ (actBudget M) hb
  rwa [List.length_map, machActions, List.length_map, List.length_range, smul_eq_mul] at h

theorem length_machReadMethods_le (n : ℕ) :
    (machReadMethods M n).length ≤ n * M.trans.length := by
  have h := length_flatMap_le (List.range n)
    (fun k => (List.range M.trans.length).map fun i =>
      (sName n (k + 1), pairBody (Sum.inl (aIdx M k i)) (Sum.inr (sName n k))))
    M.trans.length (fun _ _ => by simp)
  simp only [machReadMethods, List.length_range] at h ⊢
  exact h

theorem size_machReadMethods_le (n : ℕ) :
    ((machReadMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.trans.length) := by
  have hb : ∀ x ∈ (machReadMethods M n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, i, -, rfl⟩ := mem_machReadMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((machReadMethods M n).map MethodDesc.size).sum ≤ (machReadMethods M n).length * 6 := h
    _ ≤ (n * M.trans.length) * 6 := Nat.mul_le_mul_right _ (length_machReadMethods_le n)
    _ = 6 * (n * M.trans.length) := Nat.mul_comm _ _

theorem size_machGoalMethods (n : ℕ) :
    ((machGoalMethods M n).map MethodDesc.size).sum = 3 := by
  simp [machGoalMethods, MethodDesc.size, TnDesc.size, singleBody, TnDesc.ids, TnDesc.ordList,
    TnDesc.lbl]

theorem size_machDom_le (n : ℕ) :
    (machDom M n).size
      ≤ (M.trans.length * actBudget M + 6 * M.trans.length + 1) * n + (actBudget M + 3) := by
  have hsplit : (machDom M n).size = ((machActions M n).map ActionDesc.size).sum
      + (((machReadMethods M n).map MethodDesc.size).sum
        + ((machGoalMethods M n).map MethodDesc.size).sum) := by
    simp [DomDesc.size, machDom, DomDesc.actions, DomDesc.methods, List.map_append,
      List.sum_append]
  rw [hsplit, size_machGoalMethods]
  calc ((machActions M n).map ActionDesc.size).sum
        + (((machReadMethods M n).map MethodDesc.size).sum + 3)
      ≤ (n * M.trans.length + 1) * actBudget M + (6 * (n * M.trans.length) + 3) :=
        Nat.add_le_add (size_machActions_le n) (Nat.add_le_add_right (size_machReadMethods_le n) 3)
    _ ≤ (M.trans.length * actBudget M + 6 * M.trans.length + 1) * n + (actBudget M + 3) :=
        Nat.le.intro (k := n) (by ring)

/-! ### Computability -/

theorem primrec_machActData : Primrec (fun p : ℕ × ℕ => machActData M p.1 p.2) := by
  have hdiv : Primrec fun p : ℕ × ℕ => p.2 / M.trans.length :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const M.trans.length)
  have hmod : Primrec fun p : ℕ × ℕ => p.2 % M.trans.length :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const M.trans.length)
  have hget : Primrec fun p : ℕ × ℕ => M.trans.getI (p.2 % M.trans.length) :=
    Primrec.list_getI.comp (Primrec.const M.trans) hmod
  have hbit : Primrec fun p : ℕ × ℕ => (M.trans.getI (p.2 % M.trans.length)).bit :=
    Primrec.fst.comp (Primrec.snd.comp hget)
  have hpos : Primrec fun p : ℕ × ℕ =>
      posFact (p.2 / M.trans.length) (M.trans.getI (p.2 % M.trans.length)).bit := by
    have h : Primrec fun p : ℕ × ℕ =>
        2 * (p.2 / M.trans.length + 1) + (M.trans.getI (p.2 % M.trans.length)).bit.toNat :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp hdiv (Primrec.const 1)))
        (primrec_toNat.comp hbit)
    refine h.of_eq fun p => ?_
    cases (M.trans.getI (p.2 % M.trans.length)).bit <;> simp [posFact]
  refine Primrec.ite (c := fun p : ℕ × ℕ => p.2 < p.1 * M.trans.length) ?_ ?_
    (Primrec.const (M.goal, [], []))
  · exact PrimrecRel.comp Primrec.nat_lt Primrec.snd
      (Primrec.nat_mul.comp Primrec.fst (Primrec.const M.trans.length))
  · refine Primrec.pair (Primrec.list_cons.comp hpos
      (Primrec.fst.comp hget)) (Primrec.pair ?_ ?_)
    · exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    · exact Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))

theorem primrec_machActions : Primrec (machActions M) := by
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp Primrec.id (Primrec.const M.trans.length)) (Primrec.const 1))) ?_
  exact Primrec.pair Primrec.snd primrec_machActData

/-- The reading methods, with the two-task bodies written out. -/
theorem machReadMethods_raw (n : ℕ) :
    machReadMethods M n = List.flatMap (fun k =>
      (List.range M.trans.length).map fun i =>
        ((swapZero n (k + 1) : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, i + M.trans.length * k), (1, true, swapZero n k)] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := rfl

theorem primrec_machReadMethods : Primrec (machReadMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k =>
      (List.range M.trans.length).map fun i =>
        ((swapZero n (k + 1) : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, i + M.trans.length * k), (1, true, swapZero n k)] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const (List.range M.trans.length)) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have ii : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hhead : Primrec fun w : (ℕ × ℕ) × ℕ => swapZero w.1.1 (w.1.2 + 1) :=
      primrec_swapZero.comp nn (Primrec.nat_add.comp kk (Primrec.const 1))
    have htail : Primrec fun w : (ℕ × ℕ) × ℕ => swapZero w.1.1 w.1.2 :=
      primrec_swapZero.comp nn kk
    have hact : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 + M.trans.length * w.1.2 :=
      Primrec.nat_add.comp ii
        (Primrec.nat_mul.comp (Primrec.const M.trans.length) kk)
    refine Primrec.pair hhead (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) htail))
        (Primrec.const []))
  exact key.of_eq fun n => (machReadMethods_raw n).symm

theorem primrec_machGoalMethods : Primrec (machGoalMethods M) := by
  have key : Primrec fun n : ℕ =>
      [((swapZero n 0 : ℕ), (([0] : List ℕ), ([] : List (ℕ × ℕ)),
        ([(0, false, n * M.trans.length)] : List (ℕ × Bool × ℕ))))] := by
    refine Primrec.list_cons.comp ?_ (Primrec.const [])
    refine Primrec.pair (primrec_swapZero.comp Primrec.id (Primrec.const 0)) ?_
    refine Primrec.pair (Primrec.const [0]) (Primrec.pair (Primrec.const []) ?_)
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false)
        (Primrec.nat_mul.comp Primrec.id (Primrec.const M.trans.length))))
      (Primrec.const [])
  exact key.of_eq fun n => rfl

theorem computable_machDom : Computable (machDom M) :=
  (Primrec.pair primrec_machActions
    (Primrec.list_append.comp primrec_machReadMethods primrec_machGoalMethods)).to_comp

/-! ### A sanity check

The machine with the single transition "on a `true` bit, set the fact `0`" and the goal `0`
accepts the one-bit word `true` and rejects the one-bit word `false`: the guard `posFact` really
does make the machine read the word. -/

example : LMach ⟨[([], true, [0], [])], [0]⟩ [true] := by
  refine BitMach.Halts.cons (t := ([], true, [0], [])) (by simp) (by simp [BitTr.prec]) ?_ ?_
  · simp [posFacts, posFact, BitTr.bit]
  · exact BitMach.Halts.nil (by simp [BitTr.step, BitTr.add])

example : ¬ LMach ⟨[([], true, [0], [])], [0]⟩ [false] := by
  intro h
  cases h with
  | cons ht hp hpos h' =>
    rename_i t
    simp only [List.mem_singleton] at ht
    subst ht
    simp [posFacts, posFact, BitTr.bit] at hpos

/-! ### The family -/

variable (M)

/-- **A polynomial-time hardness family whose fixed part is a machine with a memory**, reading
its input from the initial state, in `TO-HTN-AC` with a rooted instance. -/
noncomputable def machFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root (LMach M) where
  dom := machDom M
  inst := posEnc
  bound := Polynomial.C (M.trans.length * actBudget M + 6 * M.trans.length + 1) * Polynomial.X +
    Polynomial.C (actBudget M + 3 + 2)
  dom_size := fun n => by
    have h := size_machDom_le (M := M) n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  inst_size := fun w => by
    have h := size_posEnc w
    have h2 : w.length
        ≤ (M.trans.length * actBudget M + 6 * M.trans.length + 1) * w.length :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  dom_ok := fun _ => machDom_domOk _
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_machDom_iff
  dom_computable := computable_machDom
  inst_polyTime := polyTimeCode_posEnc

/-- **The machine family, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_mach_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root (LMach M)) :=
  ⟨(machFamily M).mono ⟨fun _ h => h.1, fun _ h => h⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_mach_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root (LMach M)) :=
  ⟨(machFamily M).mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h.2, fun _ h => h⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_mach_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root (LMach M)) :=
  ⟨(machFamily M).mono ⟨fun _ h => h.2, fun _ h => h⟩⟩

end Syn

end HTN
