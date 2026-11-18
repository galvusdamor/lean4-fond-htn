import HtnComplexity.Complexity.AltMemSim
import HtnComplexity.Complexity.RecMemDom
/-!
# The recursive encoding: the simulation

This file proves that the domain description `HTN.Syn.rmDom` of
`HtnComplexity/Complexity/RecMemDom.lean` simulates the recursive alternating machine with a
memory, with the instance encoder `HTN.Syn.posEnc` unchanged:

    HTN.Syn.solvable_rmDom_iff :
      M.PosBelow W.length → (Solvable (rmDom M W.length) (posEnc W) ↔ M.Accepts W)

and, in the sharper form the exponential lower bounds need,

    HTN.Syn.accFromN_of_plan : every plan of the encoded problem has `k + 1` actions, where `k`
    is the number of actions an accepting computation of the machine is worth.

Two things make the proof different from the one of
`HtnComplexity/Complexity/AltMemSim.lean`.  There the refinements of a configuration task
are bounded by the number of input bits still to be read, and the proof is an induction on the
remaining word.  Here there is no such bound — that is the point of the encoding — so the
induction is on the **refinement itself**, and the invariant has to speak about an arbitrary
list of tasks.  `HTN.Syn.RmRun` is that invariant: it reads a list of tasks as an obligation on
the memory, and the soundness theorem says that an executable refinement of a list of tasks
meets it.
-/

namespace HTN

namespace Syn

open Binarise

variable {M : RecAltMem}

/-! ### The states of the encoding -/

/-- **The planning state holding the word `W` and the `m`-bit memory `μ`**: the position facts of
the word, and one rail per memory bit. -/
def rmState (m : ℕ) (W : List Bool) (μ : ℕ → Bool) : Set ℕ :=
  {f | f ∈ posFacts W} ∪ {f | ∃ i < m, f = amRail W.length i (μ i)}

variable {m : ℕ} {W : List Bool} {μ : ℕ → Bool}

theorem mem_rmState_rail {i : ℕ} {b : Bool} :
    amRail W.length i b ∈ rmState m W μ ↔ i < m ∧ μ i = b := by
  constructor
  · rintro (h | ⟨i', hi', h⟩)
    · exact absurd h (amRail_not_mem_posFacts W i b)
    · obtain ⟨hpos, hval⟩ := posFact_inj h
      have hii : i = i' := by omega
      subst hii
      exact ⟨hi', hval.symm⟩
  · rintro ⟨hi, rfl⟩
    exact Or.inr ⟨i, hi, rfl⟩

theorem mem_rmState_pos {k : ℕ} (hk : k < W.length) {b : Bool} :
    posFact k b ∈ rmState m W μ ↔ posFact k b ∈ posFacts W := by
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact h
    · exact absurd h (posFact_lt_ne_amRail hk b _ i)
  · exact fun h => Or.inl h

/-- **Writing a memory bit** is what the corresponding change of the state does. -/
theorem rmState_write {i : ℕ} {u : Bool} (hi : i < m) (hu : μ i = u) (v : Bool) :
    (rmState m W μ \ {amRail W.length i u}) ∪ {amRail W.length i v}
      = rmState m W (memUpd μ i v) := by
  subst hu
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, rmState, Set.mem_setOf_eq]
  constructor
  · rintro (⟨hf, hne⟩ | rfl)
    · rcases hf with hf | ⟨i', hi', rfl⟩
      · exact Or.inl hf
      · refine Or.inr ⟨i', hi', ?_⟩
        by_cases hii : i' = i
        · subst hii
          exact absurd rfl hne
        · rw [memUpd_of_ne hii]
    · exact Or.inr ⟨i, hi, by rw [memUpd_self]⟩
  · rintro (hf | ⟨i', hi', rfl⟩)
    · refine Or.inl ⟨Or.inl hf, ?_⟩
      rintro rfl
      exact absurd hf (amRail_not_mem_posFacts W i (μ i))
    · by_cases hii : i' = i
      · subst hii
        rw [memUpd_self]
        exact Or.inr rfl
      · refine Or.inl ⟨Or.inr ⟨i', hi', by rw [memUpd_of_ne hii]⟩, ?_⟩
        intro h
        rw [memUpd_of_ne hii] at h
        have := (posFact_inj h).1
        omega

/-- **A memory guard is satisfied in the state** exactly when it is satisfied in the memory. -/
theorem rmMemSat_iff_subset (g : List MemLit) :
    (∀ f ∈ g.map (amRailOf W.length), f ∈ rmState m W μ) ↔ MemSat m μ g := by
  constructor
  · intro h p hp
    exact mem_rmState_rail.1 (h (amRailOf W.length p) (List.mem_map_of_mem hp))
  · intro h f hf
    simp only [List.mem_map] at hf
    obtain ⟨p, hp, rfl⟩ := hf
    obtain ⟨h1, h2⟩ := h p hp
    exact mem_rmState_rail.2 ⟨h1, h2⟩

/-- **An input guard is satisfied in the state** exactly when the word has the bits it asks
for — provided it reads no position beyond the end of the word, since the memory rails are the
position facts of the positions beyond it. -/
theorem rmInSat_iff_subset {g : List InLit} (hg : PosLt W.length g) :
    (∀ f ∈ g.map rmInFact, f ∈ rmState m W μ) ↔ InSat W g := by
  constructor
  · intro h p hp
    exact (mem_rmState_pos (hg p hp)).1 (h (rmInFact p) (List.mem_map_of_mem hp))
  · intro h f hf
    simp only [List.mem_map] at hf
    obtain ⟨p, hp, rfl⟩ := hf
    exact Or.inl (h p hp)

/-! ### The actions on the states -/

/-- **A forward action is applicable** exactly when the machine may take the transition. -/
theorem applicable_rmFwd_iff {i : ℕ} (hi : i < M.ex.length)
    (hpb : PosLt W.length (M.ex.getI i).inG) :
    (rmDom M W.length).toDomain.Applicable (rmFwd i) (rmState M.mem W μ) ↔
      (InSat W (M.ex.getI i).inG ∧ (M.ex.getI i).wr.idx < M.mem ∧
        μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old ∧
        MemSat M.mem μ (M.ex.getI i).memG) := by
  have hj : rmFwd i < rmNumActs M := rmFwd_lt hi
  have hp : (rmDom M W.length).toDomain.prec (rmFwd i)
      = {f | f ∈ (rmFwdData M W.length i).1} := by
    rw [DomDesc.toDomain_prec, prec_rmDom hj, rmActData_fwd]
  constructor
  · intro happ
    have hsub : {f | f ∈ (rmFwdData M W.length i).1} ⊆ rmState M.mem W μ := by
      rw [← hp]; exact happ
    have h2 : amRail W.length (M.ex.getI i).wr.idx (M.ex.getI i).wr.old ∈ rmState M.mem W μ :=
      hsub (by simp [rmFwdData])
    obtain ⟨h2a, h2b⟩ := mem_rmState_rail.1 h2
    refine ⟨(rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).1 ?_, h2a, h2b, (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).1 ?_⟩
    · intro f hf
      exact hsub (by simp only [rmFwdData, List.mem_append]; exact Or.inl hf)
    · intro f hf
      exact hsub (by
        simp only [rmFwdData, List.mem_append, List.mem_cons]
        exact Or.inr (Or.inr hf))
  · rintro ⟨h1, h2, h3, h4⟩
    rw [ActionModel.Applicable, hp]
    intro f hf
    simp only [rmFwdData, Set.mem_setOf_eq, List.mem_append, List.mem_cons] at hf
    rcases hf with hf | rfl | hf
    · exact (rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).2 h1 f hf
    · exact mem_rmState_rail.2 ⟨h2, h3⟩
    · exact (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).2 h4 f hf

/-- **A forward action writes the memory bit of its transition.** -/
theorem transition_rmFwd {i : ℕ} (hi : i < M.ex.length)
    (hidx : (M.ex.getI i).wr.idx < M.mem)
    (hu : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old) :
    (rmDom M W.length).toDomain.transition (rmFwd i) (rmState M.mem W μ)
      = rmState M.mem W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) := by
  have hj : rmFwd i < rmNumActs M := rmFwd_lt hi
  show ((rmState M.mem W μ \ (rmDom M W.length).del (rmFwd i))
    ∪ (rmDom M W.length).add (rmFwd i)) = _
  rw [add_rmDom hj, del_rmDom hj, rmActData_fwd]
  simp only [rmFwdData]
  rw [setOf_mem_singleton, setOf_mem_singleton]
  exact rmState_write hidx hu _

/-- **An undoing action is applicable** exactly when the bit it restores holds the value the
write installed. -/
theorem applicable_rmUndo_iff {i : ℕ} (hi : i < M.ex.length) :
    (rmDom M W.length).toDomain.Applicable (rmUndo i) (rmState M.mem W μ) ↔
      ((M.ex.getI i).wr.idx < M.mem ∧ μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.new) := by
  have hj : rmUndo i < rmNumActs M := rmUndo_lt hi
  have hp : (rmDom M W.length).toDomain.prec (rmUndo i)
      = {f | f ∈ (rmUndoData M W.length i).1} := by
    rw [DomDesc.toDomain_prec, prec_rmDom hj, rmActData_undo]
  rw [ActionModel.Applicable, hp]
  constructor
  · intro hsub
    have := hsub (show amRail W.length (M.ex.getI i).wr.idx (M.ex.getI i).wr.new ∈
      {f | f ∈ (rmUndoData M W.length i).1} by simp [rmUndoData])
    exact mem_rmState_rail.1 this
  · rintro ⟨h1, h2⟩ f hf
    simp only [rmUndoData, Set.mem_setOf_eq, List.mem_singleton] at hf
    subst hf
    exact mem_rmState_rail.2 ⟨h1, h2⟩

/-- **An undoing action restores the memory the write changed.** -/
theorem transition_rmUndo {i : ℕ} (hi : i < M.ex.length)
    (hidx : (M.ex.getI i).wr.idx < M.mem)
    (hnew : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.new) :
    (rmDom M W.length).toDomain.transition (rmUndo i) (rmState M.mem W μ)
      = rmState M.mem W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) := by
  have hj : rmUndo i < rmNumActs M := rmUndo_lt hi
  show ((rmState M.mem W μ \ (rmDom M W.length).del (rmUndo i))
    ∪ (rmDom M W.length).add (rmUndo i)) = _
  rw [add_rmDom hj, del_rmDom hj, rmActData_undo]
  simp only [rmUndoData]
  rw [setOf_mem_singleton, setOf_mem_singleton]
  exact rmState_write hidx hnew _

/-- **A universal guard is applicable** exactly when the machine may take the transition. -/
theorem applicable_rmGrd_iff {j : ℕ} (hj : j < M.un.length)
    (hpb : PosLt W.length (M.un.getI j).inG) :
    (rmDom M W.length).toDomain.Applicable (rmGrd j) (rmState M.mem W μ) ↔
      (InSat W (M.un.getI j).inG ∧ MemSat M.mem μ (M.un.getI j).memG) := by
  have hlt : rmGrd j < rmNumActs M := rmGrd_lt hj
  have hp : (rmDom M W.length).toDomain.prec (rmGrd j)
      = {f | f ∈ (rmGrdData M W.length j).1} := by
    rw [DomDesc.toDomain_prec, prec_rmDom hlt, rmActData_grd]
  constructor
  · intro happ
    have hsub : {f | f ∈ (rmGrdData M W.length j).1} ⊆ rmState M.mem W μ := by
      rw [← hp]; exact happ
    refine ⟨(rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).1 ?_, (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).1 ?_⟩
    · intro f hf
      exact hsub (by simp only [rmGrdData, List.mem_append]; exact Or.inl hf)
    · intro f hf
      exact hsub (by simp only [rmGrdData, List.mem_append]; exact Or.inr hf)
  · rintro ⟨h1, h2⟩
    rw [ActionModel.Applicable, hp]
    intro f hf
    simp only [rmGrdData, Set.mem_setOf_eq, List.mem_append] at hf
    rcases hf with hf | hf
    · exact (rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).2 h1 f hf
    · exact (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).2 h2 f hf

/-- A universal guard has no effect. -/
theorem transition_rmGrd {j : ℕ} (hj : j < M.un.length) (s : Set ℕ) :
    (rmDom M W.length).toDomain.transition (rmGrd j) s = s := by
  have hlt : rmGrd j < rmNumActs M := rmGrd_lt hj
  show ((s \ (rmDom M W.length).del (rmGrd j)) ∪ (rmDom M W.length).add (rmGrd j)) = _
  rw [add_rmDom hlt, del_rmDom hlt, rmActData_grd]
  simp [rmGrdData]

/-- **An accepting check is applicable** exactly when its guards hold. -/
theorem applicable_rmAccA_iff {a : ℕ} (ha : a < M.acc.length)
    (hpb : PosLt W.length (M.acc.getI a).inG) :
    (rmDom M W.length).toDomain.Applicable (rmAccA a) (rmState M.mem W μ) ↔
      (InSat W (M.acc.getI a).inG ∧ MemSat M.mem μ (M.acc.getI a).memG) := by
  have hlt : rmAccA a < rmNumActs M := rmAccA_lt ha
  have hp : (rmDom M W.length).toDomain.prec (rmAccA a)
      = {f | f ∈ (rmAccData M W.length a).1} := by
    rw [DomDesc.toDomain_prec, prec_rmDom hlt, rmActData_acc ha]
  constructor
  · intro happ
    have hsub : {f | f ∈ (rmAccData M W.length a).1} ⊆ rmState M.mem W μ := by
      rw [← hp]; exact happ
    refine ⟨(rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).1 ?_, (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).1 ?_⟩
    · intro f hf
      exact hsub (by simp only [rmAccData, List.mem_append]; exact Or.inl hf)
    · intro f hf
      exact hsub (by simp only [rmAccData, List.mem_append]; exact Or.inr hf)
  · rintro ⟨h1, h2⟩
    rw [ActionModel.Applicable, hp]
    intro f hf
    simp only [rmAccData, Set.mem_setOf_eq, List.mem_append] at hf
    rcases hf with hf | hf
    · exact (rmInSat_iff_subset (m := M.mem) (W := W) (μ := μ) hpb).2 h1 f hf
    · exact (rmMemSat_iff_subset (m := M.mem) (W := W) (μ := μ) _).2 h2 f hf

/-- An accepting check has no effect. -/
theorem transition_rmAccA {a : ℕ} (ha : a < M.acc.length) (s : Set ℕ) :
    (rmDom M W.length).toDomain.transition (rmAccA a) s = s := by
  have hlt : rmAccA a < rmNumActs M := rmAccA_lt ha
  show ((s \ (rmDom M W.length).del (rmAccA a)) ∪ (rmDom M W.length).add (rmAccA a)) = _
  rw [add_rmDom hlt, del_rmDom hlt, rmActData_acc ha]
  simp [rmAccData]

/-- The initialising action is always applicable. -/
theorem applicable_rmInit (s : Set ℕ) :
    (rmDom M W.length).toDomain.Applicable (rmInit M) s := by
  rw [ActionModel.Applicable, DomDesc.toDomain_prec, prec_rmDom rmInit_lt, rmActData_init]
  intro f hf
  simp [rmInitData] at hf

/-- **The initialising action creates the empty memory.** -/
theorem transition_rmInit :
    (rmDom M W.length).toDomain.transition (rmInit M) {f | f ∈ posFacts W}
      = rmState M.mem W (fun _ => false) := by
  show (({f | f ∈ posFacts W} \ (rmDom M W.length).del (rmInit M))
    ∪ (rmDom M W.length).add (rmInit M)) = _
  rw [add_rmDom rmInit_lt, del_rmDom rmInit_lt, rmActData_init]
  simp only [rmInitData]
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.not_mem_nil, not_false_iff,
    and_true, List.mem_map, List.mem_range, rmState]
  constructor
  · rintro (hf | ⟨i, hi, rfl⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨i, hi, rfl⟩
  · rintro (hf | ⟨i, hi, rfl⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨i, hi, rfl⟩

/-! ### The invariant: what a list of tasks demands of the memory

`RmRun M W ts N μ ν` reads the list of tasks `ts` as an obligation: run in the memory `μ`, it
produces `N` actions and leaves the memory `ν`, every compound task standing for an accepting
computation of the machine.  A configuration task and a branching task restore the memory they
are started in; an undoing task undoes the write of its transition. -/

/-- The machine-level reading of a list of tasks of the encoding. -/
inductive RmRun (M : RecAltMem) (W : List Bool) :
    List (ℕ ⊕ ℕ) → ℕ → (ℕ → Bool) → (ℕ → Bool) → Prop
  /-- Nothing to do. -/
  | nil {μ : ℕ → Bool} : RmRun M W [] 0 μ μ
  /-- A configuration task is an accepting computation, and restores the memory. -/
  | cfg {q k l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool} (hacc : M.AccFromN W k q μ)
      (h : RmRun M W ts l μ ν) : RmRun M W (Sum.inr (rmCName q) :: ts) (k + l) μ ν
  /-- A branching task is a pair of accepting computations, and restores the memory. -/
  | br {j k₁ k₂ l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool}
      (h₁ : M.AccFromN W k₁ (M.un.getI j).tgt₁ μ) (h₂ : M.AccFromN W k₂ (M.un.getI j).tgt₂ μ)
      (h : RmRun M W ts l μ ν) : RmRun M W (Sum.inr (rmBrName j) :: ts) (k₁ + k₂ + l) μ ν
  /-- An undoing task is an accepting computation followed by the inverse write. -/
  | dund {i k l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool}
      (hacc : M.AccFromN W k (M.ex.getI i).tgt μ)
      (h : RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν) :
      RmRun M W (Sum.inr (rmDName i) :: ts) (k + 1 + l) μ ν
  /-- A forward action checks the guards of its transition and writes. -/
  | fwd {i l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool} (hin : InSat W (M.ex.getI i).inG)
      (hg : MemSat M.mem μ (M.ex.getI i).memG) (hidx : (M.ex.getI i).wr.idx < M.mem)
      (hold : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old)
      (h : RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) ν) :
      RmRun M W (Sum.inl (rmFwd i) :: ts) (1 + l) μ ν
  /-- An undoing action restores the bit its transition wrote. -/
  | undo {i l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool}
      (hidx : (M.ex.getI i).wr.idx < M.mem)
      (hnew : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.new)
      (h : RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν) :
      RmRun M W (Sum.inl (rmUndo i) :: ts) (1 + l) μ ν
  /-- A universal guard checks the guards of its transition. -/
  | grd {j l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool} (hin : InSat W (M.un.getI j).inG)
      (hg : MemSat M.mem μ (M.un.getI j).memG) (h : RmRun M W ts l μ ν) :
      RmRun M W (Sum.inl (rmGrd j) :: ts) (1 + l) μ ν
  /-- An accepting check checks the guards of its condition. -/
  | accA {a l : ℕ} {ts : List (ℕ ⊕ ℕ)} {μ ν : ℕ → Bool} (hin : InSat W (M.acc.getI a).inG)
      (hg : MemSat M.mem μ (M.acc.getI a).memG) (h : RmRun M W ts l μ ν) :
      RmRun M W (Sum.inl (rmAccA a) :: ts) (1 + l) μ ν

namespace RmRun

variable {ts : List (ℕ ⊕ ℕ)} {N : ℕ} {ν : ℕ → Bool}

/-- Inversion at a leading compound task. -/
theorem inr_inv {c : ℕ} (h : RmRun M W (Sum.inr c :: ts) N μ ν) :
    (∃ q k l, c = rmCName q ∧ N = k + l ∧ M.AccFromN W k q μ ∧ RmRun M W ts l μ ν) ∨
      (∃ j k₁ k₂ l, c = rmBrName j ∧ N = k₁ + k₂ + l ∧
        M.AccFromN W k₁ (M.un.getI j).tgt₁ μ ∧ M.AccFromN W k₂ (M.un.getI j).tgt₂ μ ∧
        RmRun M W ts l μ ν) ∨
      (∃ i k l, c = rmDName i ∧ N = k + 1 + l ∧ M.AccFromN W k (M.ex.getI i).tgt μ ∧
        RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν) := by
  cases h with
  | cfg hacc h => exact Or.inl ⟨_, _, _, rfl, rfl, hacc, h⟩
  | br h₁ h₂ h => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, rfl, h₁, h₂, h⟩)
  | dund hacc h => exact Or.inr (Or.inr ⟨_, _, _, rfl, rfl, hacc, h⟩)

/-- Inversion at a leading action. -/
theorem inl_inv {a : ℕ} (h : RmRun M W (Sum.inl a :: ts) N μ ν) :
    (∃ i l, a = rmFwd i ∧ N = 1 + l ∧ InSat W (M.ex.getI i).inG ∧
        MemSat M.mem μ (M.ex.getI i).memG ∧ (M.ex.getI i).wr.idx < M.mem ∧
        μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old ∧
        RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) ν) ∨
      (∃ i l, a = rmUndo i ∧ N = 1 + l ∧ (M.ex.getI i).wr.idx < M.mem ∧
        μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.new ∧
        RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν) ∨
      (∃ j l, a = rmGrd j ∧ N = 1 + l ∧ InSat W (M.un.getI j).inG ∧
        MemSat M.mem μ (M.un.getI j).memG ∧ RmRun M W ts l μ ν) ∨
      (∃ b l, a = rmAccA b ∧ N = 1 + l ∧ InSat W (M.acc.getI b).inG ∧
        MemSat M.mem μ (M.acc.getI b).memG ∧ RmRun M W ts l μ ν) := by
  cases h with
  | fwd hin hg hidx hold h => exact Or.inl ⟨_, _, rfl, rfl, hin, hg, hidx, hold, h⟩
  | undo hidx hnew h => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hidx, hnew, h⟩)
  | grd hin hg h => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, hin, hg, h⟩))
  | accA hin hg h => exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, rfl, hin, hg, h⟩))

theorem cfg_inv {q : ℕ} (h : RmRun M W (Sum.inr (rmCName q) :: ts) N μ ν) :
    ∃ k l, N = k + l ∧ M.AccFromN W k q μ ∧ RmRun M W ts l μ ν := by
  rcases h.inr_inv with ⟨q', k, l, hc, hN, hacc, h'⟩ | ⟨j, _, _, _, hc, -⟩ |
    ⟨i, _, _, hc, -⟩
  · obtain rfl : q = q' := rmCName_inj hc
    exact ⟨k, l, hN, hacc, h'⟩
  · exact absurd hc rmCName_ne_brName
  · exact absurd hc rmCName_ne_dName

theorem br_inv {j : ℕ} (h : RmRun M W (Sum.inr (rmBrName j) :: ts) N μ ν) :
    ∃ k₁ k₂ l, N = k₁ + k₂ + l ∧ M.AccFromN W k₁ (M.un.getI j).tgt₁ μ ∧
      M.AccFromN W k₂ (M.un.getI j).tgt₂ μ ∧ RmRun M W ts l μ ν := by
  rcases h.inr_inv with ⟨q, _, _, hc, -⟩ | ⟨j', k₁, k₂, l, hc, hN, h₁, h₂, h'⟩ |
    ⟨i, _, _, hc, -⟩
  · exact absurd hc.symm rmCName_ne_brName
  · obtain rfl : j = j' := rmBrName_inj hc
    exact ⟨k₁, k₂, l, hN, h₁, h₂, h'⟩
  · exact absurd hc rmBrName_ne_dName

theorem dund_inv {i : ℕ} (h : RmRun M W (Sum.inr (rmDName i) :: ts) N μ ν) :
    ∃ k l, N = k + 1 + l ∧ M.AccFromN W k (M.ex.getI i).tgt μ ∧
      RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν := by
  rcases h.inr_inv with ⟨q, _, _, hc, -⟩ | ⟨j, _, _, _, hc, -⟩ |
    ⟨i', k, l, hc, hN, hacc, h'⟩
  · exact absurd hc.symm rmCName_ne_dName
  · exact absurd hc.symm rmBrName_ne_dName
  · obtain rfl : i = i' := rmDName_inj hc
    exact ⟨k, l, hN, hacc, h'⟩

theorem fwd_inv {i : ℕ} (h : RmRun M W (Sum.inl (rmFwd i) :: ts) N μ ν) :
    ∃ l, N = 1 + l ∧ InSat W (M.ex.getI i).inG ∧ MemSat M.mem μ (M.ex.getI i).memG ∧
      (M.ex.getI i).wr.idx < M.mem ∧ μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old ∧
      RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) ν := by
  rcases h.inl_inv with ⟨i', l, ha, hN, hin, hg, hidx, hold, h'⟩ | ⟨i', _, ha, -⟩ |
    ⟨j, _, ha, -⟩ | ⟨b, _, ha, -⟩
  · obtain rfl : i = i' := rmFwd_inj ha
    exact ⟨l, hN, hin, hg, hidx, hold, h'⟩
  · exact absurd ha rmFwd_ne_undo
  · exact absurd ha rmFwd_ne_grd
  · exact absurd ha rmFwd_ne_accA

theorem undo_inv {i : ℕ} (h : RmRun M W (Sum.inl (rmUndo i) :: ts) N μ ν) :
    ∃ l, N = 1 + l ∧ (M.ex.getI i).wr.idx < M.mem ∧
      μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.new ∧
      RmRun M W ts l (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.old) ν := by
  rcases h.inl_inv with ⟨i', _, ha, -⟩ | ⟨i', l, ha, hN, hidx, hnew, h'⟩ |
    ⟨j, _, ha, -⟩ | ⟨b, _, ha, -⟩
  · exact absurd ha.symm rmFwd_ne_undo
  · obtain rfl : i = i' := rmUndo_inj ha
    exact ⟨l, hN, hidx, hnew, h'⟩
  · exact absurd ha rmUndo_ne_grd
  · exact absurd ha rmUndo_ne_accA

theorem grd_inv {j : ℕ} (h : RmRun M W (Sum.inl (rmGrd j) :: ts) N μ ν) :
    ∃ l, N = 1 + l ∧ InSat W (M.un.getI j).inG ∧ MemSat M.mem μ (M.un.getI j).memG ∧
      RmRun M W ts l μ ν := by
  rcases h.inl_inv with ⟨i, _, ha, -⟩ | ⟨i, _, ha, -⟩ |
    ⟨j', l, ha, hN, hin, hg, h'⟩ | ⟨b, _, ha, -⟩
  · exact absurd ha.symm rmFwd_ne_grd
  · exact absurd ha.symm rmUndo_ne_grd
  · obtain rfl : j = j' := rmGrd_inj ha
    exact ⟨l, hN, hin, hg, h'⟩
  · exact absurd ha rmGrd_ne_accA

theorem accA_inv {a : ℕ} (h : RmRun M W (Sum.inl (rmAccA a) :: ts) N μ ν) :
    ∃ l, N = 1 + l ∧ InSat W (M.acc.getI a).inG ∧ MemSat M.mem μ (M.acc.getI a).memG ∧
      RmRun M W ts l μ ν := by
  rcases h.inl_inv with ⟨i, _, ha, -⟩ | ⟨i, _, ha, -⟩ | ⟨j, _, ha, -⟩ |
    ⟨a', l, ha, hN, hin, hg, h'⟩
  · exact absurd ha.symm rmFwd_ne_accA
  · exact absurd ha.symm rmUndo_ne_accA
  · exact absurd ha.symm rmGrd_ne_accA
  · obtain rfl : a = a' := rmAccA_inj ha
    exact ⟨l, hN, hin, hg, h'⟩

theorem nil_inv (h : RmRun M W [] N μ ν) : N = 0 ∧ ν = μ := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

end RmRun

/-! ### The tasks the encoding uses -/

/-- A task of the encoding. -/
def RmTaskOk (M : RecAltMem) (t : ℕ ⊕ ℕ) : Prop :=
  (∃ i < M.ex.length, t = Sum.inl (rmFwd i)) ∨ (∃ i < M.ex.length, t = Sum.inl (rmUndo i)) ∨
    (∃ j < M.un.length, t = Sum.inl (rmGrd j)) ∨ (∃ a < M.acc.length, t = Sum.inl (rmAccA a)) ∨
    (∃ q, t = Sum.inr (rmCName q)) ∨ (∃ j < M.un.length, t = Sum.inr (rmBrName j)) ∨
    (∃ i < M.ex.length, t = Sum.inr (rmDName i))

/-- A list of tasks of the encoding. -/
def RmTasksOk (M : RecAltMem) (ts : List (ℕ ⊕ ℕ)) : Prop := ∀ t ∈ ts, RmTaskOk M t

theorem rmTasksOk_append {ts us : List (ℕ ⊕ ℕ)} (h₁ : RmTasksOk M ts) (h₂ : RmTasksOk M us) :
    RmTasksOk M (ts ++ us) := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact h₁ t ht
  · exact h₂ t ht

theorem rmTasksOk_cons {t : ℕ ⊕ ℕ} {ts : List (ℕ ⊕ ℕ)} (h : RmTasksOk M (t :: ts)) :
    RmTasksOk M ts := fun u hu => h u (List.mem_cons_of_mem _ hu)

/-! ### Soundness: an executable refinement is an accepting computation -/

/-- **Soundness of the recursive encoding.**  An executable refinement of a list of tasks of the
encoding meets the obligation the list stands for, and the actions it produces take the state
from the memory it started in to the memory the obligation ends in. -/
theorem rmRun_of_yieldSeq (hpb : M.PosBelow W.length) :
    ∀ {ts : List (ℕ ⊕ ℕ)} {as : List ℕ}, (rmDom M W.length).toDomain.YieldSeq ts as →
      RmTasksOk M ts → ∀ μ : ℕ → Bool,
        (rmDom M W.length).toDomain.SeqApplicable as (rmState M.mem W μ) →
        ∃ ν, RmRun M W ts as.length μ ν ∧
          (rmDom M W.length).toDomain.transitionSeq as (rmState M.mem W μ)
            = rmState M.mem W ν := by
  intro ts as hy
  induction hy with
  | nil =>
    intro _ μ _
    exact ⟨μ, RmRun.nil, rfl⟩
  | @prim a xs as h ih =>
    intro hok μ happ
    obtain ⟨happ1, happ2⟩ := happ
    have hok' := rmTasksOk_cons hok
    have ha := hok (Sum.inl a) (List.mem_cons_self ..)
    rcases ha with ⟨i, hi, hia⟩ | ⟨i, hi, hia⟩ | ⟨j, hj, hja⟩ | ⟨a', ha', haa⟩ |
      ⟨q, hq⟩ | ⟨j, hj, hjq⟩ | ⟨i, hi, hiq⟩
    · have hia' : a = rmFwd i := by injection hia
      subst hia'
      obtain ⟨hin, hidx, hold, hg⟩ :=
        (applicable_rmFwd_iff hi (hpb.ex_getI hi)).1 happ1
      have hst := transition_rmFwd (W := W) (μ := μ) hi hidx hold
      rw [hst] at happ2
      obtain ⟨ν, hrun, htr⟩ := ih hok' _ happ2
      refine ⟨ν, ?_, ?_⟩
      · simpa [List.length_cons, Nat.add_comm] using RmRun.fwd hin hg hidx hold hrun
      · rw [ActionModel.transitionSeq_cons, hst, htr]
    · have hia' : a = rmUndo i := by injection hia
      subst hia'
      obtain ⟨hidx, hnew⟩ := (applicable_rmUndo_iff hi).1 happ1
      have hst := transition_rmUndo (W := W) (μ := μ) hi hidx hnew
      rw [hst] at happ2
      obtain ⟨ν, hrun, htr⟩ := ih hok' _ happ2
      refine ⟨ν, ?_, ?_⟩
      · simpa [List.length_cons, Nat.add_comm] using RmRun.undo hidx hnew hrun
      · rw [ActionModel.transitionSeq_cons, hst, htr]
    · have hja' : a = rmGrd j := by injection hja
      subst hja'
      obtain ⟨hin, hg⟩ := (applicable_rmGrd_iff hj (hpb.un_getI hj)).1 happ1
      rw [transition_rmGrd hj] at happ2
      obtain ⟨ν, hrun, htr⟩ := ih hok' _ happ2
      refine ⟨ν, ?_, ?_⟩
      · simpa [List.length_cons, Nat.add_comm] using RmRun.grd hin hg hrun
      · rw [ActionModel.transitionSeq_cons, transition_rmGrd hj, htr]
    · have haa' : a = rmAccA a' := by injection haa
      subst haa'
      obtain ⟨hin, hg⟩ := (applicable_rmAccA_iff ha' (hpb.acc_getI ha')).1 happ1
      rw [transition_rmAccA ha'] at happ2
      obtain ⟨ν, hrun, htr⟩ := ih hok' _ happ2
      refine ⟨ν, ?_, ?_⟩
      · simpa [List.length_cons, Nat.add_comm] using RmRun.accA hin hg hrun
      · rw [ActionModel.transitionSeq_cons, transition_rmAccA ha', htr]
    · exact absurd hq (by simp)
    · exact absurd hjq (by simp)
    · exact absurd hiq (by simp)
  | @comp c bs xs as hm h ih =>
    intro hok μ happ
    have hok' := rmTasksOk_cons hok
    have hc := hok (Sum.inr c) (List.mem_cons_self ..)
    rcases hc with ⟨i, hi, hia⟩ | ⟨i, hi, hia⟩ | ⟨j, hj, hja⟩ | ⟨a', ha', haa⟩ |
      ⟨q, hq⟩ | ⟨j, hj, hjq⟩ | ⟨i, hi, hiq⟩
    · exact absurd hia (by simp)
    · exact absurd hia (by simp)
    · exact absurd hja (by simp)
    · exact absurd haa (by simp)
    · have hq' : c = rmCName q := by injection hq
      subst hq'
      rcases seqBody_rmDom_c_iff.1 hm with ⟨i, hi, hsrc, rfl⟩ | ⟨j, hj, hsrc, rfl⟩ |
        ⟨a, ha, hst, rfl⟩
      · have hbok : RmTasksOk M ([Sum.inl (rmFwd i), Sum.inr (rmDName i)] ++ xs) := by
          refine rmTasksOk_append ?_ hok'
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact Or.inl ⟨i, hi, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))
        obtain ⟨ν, hrun, htr⟩ := ih hbok μ happ
        rw [List.cons_append, List.cons_append, List.nil_append] at hrun
        obtain ⟨l, hN, hin, hg, hidx, hold, hrun'⟩ := hrun.fwd_inv
        obtain ⟨k, l', hl, hacc, hrun''⟩ := hrun'.dund_inv
        rw [memUpd_memUpd, memUpd_eq_self hold] at hrun''
        refine ⟨ν, ?_, htr⟩
        have hstep : M.AccFromN W (k + 2) q μ := by
          refine RecAltMem.AccFromN.ex (t := M.ex.getI i) ?_ hsrc hin hg hidx hold hacc
          rw [List.getI_eq_getElem (l := M.ex) hi]
          exact List.getElem_mem hi
        have := RmRun.cfg (M := M) (W := W) (ts := xs) hstep hrun''
        have hcount : as.length = k + 2 + l' := by omega
        rw [hcount]
        exact this
      · have hbok : RmTasksOk M ([Sum.inl (rmGrd j), Sum.inr (rmBrName j)] ++ xs) := by
          refine rmTasksOk_append ?_ hok'
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, rfl⟩)))))
        obtain ⟨ν, hrun, htr⟩ := ih hbok μ happ
        rw [List.cons_append, List.cons_append, List.nil_append] at hrun
        obtain ⟨l, hN, hin, hg, hrun'⟩ := hrun.grd_inv
        obtain ⟨k₁, k₂, l', hl, h₁, h₂, hrun''⟩ := hrun'.br_inv
        refine ⟨ν, ?_, htr⟩
        have hstep : M.AccFromN W (k₁ + k₂ + 1) q μ := by
          refine RecAltMem.AccFromN.un (t := M.un.getI j) ?_ hsrc hin hg h₁ h₂
          rw [List.getI_eq_getElem (l := M.un) hj]
          exact List.getElem_mem hj
        have := RmRun.cfg (M := M) (W := W) (ts := xs) hstep hrun''
        have hcount : as.length = k₁ + k₂ + 1 + l' := by omega
        rw [hcount]
        exact this
      · have hbok : RmTasksOk M ([Sum.inl (rmAccA a)] ++ xs) := by
          refine rmTasksOk_append ?_ hok'
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          subst ht
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, ha, rfl⟩)))
        obtain ⟨ν, hrun, htr⟩ := ih hbok μ happ
        rw [List.cons_append, List.nil_append] at hrun
        obtain ⟨l, hN, hin, hg, hrun'⟩ := hrun.accA_inv
        refine ⟨ν, ?_, htr⟩
        have hstep : M.AccFromN W 1 q μ := by
          refine RecAltMem.AccFromN.nil (c := M.acc.getI a) ?_ hst hin hg
          rw [List.getI_eq_getElem (l := M.acc) ha]
          exact List.getElem_mem ha
        have := RmRun.cfg (M := M) (W := W) (ts := xs) hstep hrun'
        have hcount : as.length = 1 + l := by omega
        rw [hcount]
        exact this
    · have hj' : c = rmBrName j := by injection hjq
      subst hj'
      obtain ⟨-, rfl⟩ := seqBody_rmDom_br_iff.1 hm
      have hbok : RmTasksOk M ([Sum.inr (rmCName (M.un.getI j).tgt₁),
          Sum.inr (rmCName (M.un.getI j).tgt₂)] ++ xs) := by
        refine rmTasksOk_append ?_ hok'
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
      obtain ⟨ν, hrun, htr⟩ := ih hbok μ happ
      rw [List.cons_append, List.cons_append, List.nil_append] at hrun
      obtain ⟨k₁, l, hN, h₁, hrun'⟩ := hrun.cfg_inv
      obtain ⟨k₂, l', hl, h₂, hrun''⟩ := hrun'.cfg_inv
      refine ⟨ν, ?_, htr⟩
      have := RmRun.br (M := M) (W := W) (j := j) (ts := xs) h₁ h₂ hrun''
      have hcount : as.length = k₁ + k₂ + l' := by omega
      rw [hcount]
      exact this
    · have hi' : c = rmDName i := by injection hiq
      subst hi'
      obtain ⟨-, rfl⟩ := seqBody_rmDom_d_iff.1 hm
      have hbok : RmTasksOk M ([Sum.inr (rmCName (M.ex.getI i).tgt),
          Sum.inl (rmUndo i)] ++ xs) := by
        refine rmTasksOk_append ?_ hok'
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
        · exact Or.inr (Or.inl ⟨i, hi, rfl⟩)
      obtain ⟨ν, hrun, htr⟩ := ih hbok μ happ
      rw [List.cons_append, List.cons_append, List.nil_append] at hrun
      obtain ⟨k, l, hN, hacc, hrun'⟩ := hrun.cfg_inv
      obtain ⟨l', hl, hidx, hnew, hrun''⟩ := hrun'.undo_inv
      refine ⟨ν, ?_, htr⟩
      have := RmRun.dund (M := M) (W := W) (i := i) (ts := xs) hacc hrun''
      have hcount : as.length = k + 1 + l' := by omega
      rw [hcount]
      exact this

/-! ### Completeness: an accepting computation is an executable refinement -/

/-- **Completeness of the recursive encoding**: an accepting computation of the machine is an
executable refinement of the configuration task, of exactly as many actions as the computation is
worth, and it restores the state it started in. -/
theorem yieldSeq_of_accFromN (hpb : M.PosBelow W.length) :
    ∀ {k q : ℕ} {μ : ℕ → Bool}, M.AccFromN W k q μ →
      ∃ as : List ℕ, as.length = k ∧
        (rmDom M W.length).toDomain.YieldSeq [Sum.inr (rmCName q)] as ∧
        (rmDom M W.length).toDomain.SeqApplicable as (rmState M.mem W μ) ∧
        (rmDom M W.length).toDomain.transitionSeq as (rmState M.mem W μ)
          = rmState M.mem W μ := by
  intro k q μ hacc
  induction hacc with
  | @nil q μ c hc hq hin hg =>
    obtain ⟨a, ha, hca⟩ := List.mem_iff_getElem.1 hc
    have hgi : M.acc.getI a = c := by rw [List.getI_eq_getElem (l := M.acc) ha, hca]
    refine ⟨[rmAccA a], rfl, ?_, ?_, ?_⟩
    · refine Domain.YieldSeq.comp (bs := [Sum.inl (rmAccA a)])
        (seqBody_rmDom_c_iff.2 (Or.inr (Or.inr ⟨a, ha, by rw [hgi]; exact hq, rfl⟩))) ?_
      rw [List.cons_append, List.nil_append]
      exact Domain.YieldSeq.prim Domain.YieldSeq.nil
    · exact ⟨(applicable_rmAccA_iff ha (hpb.acc_getI ha)).2
        ⟨by rw [hgi]; exact hin, by rw [hgi]; exact hg⟩, trivial⟩
    · rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
        transition_rmAccA ha]
  | @ex k q μ t ht hq hin hg hw hu h' ih =>
    obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.1 ht
    have hgi : M.ex.getI i = t := by rw [List.getI_eq_getElem (l := M.ex) hi, hti]
    obtain ⟨as₁, hlen₁, hy₁, happ₁, hres₁⟩ := ih
    have hst : (rmDom M W.length).toDomain.transition (rmFwd i) (rmState M.mem W μ)
        = rmState M.mem W (memUpd μ t.wr.idx t.wr.new) := by
      have := transition_rmFwd (M := M) (W := W) (μ := μ) hi (by rw [hgi]; exact hw)
        (by rw [hgi]; exact hu)
      rwa [hgi] at this
    refine ⟨rmFwd i :: (as₁ ++ [rmUndo i]), by simp [hlen₁], ?_, ?_, ?_⟩
    · refine Domain.YieldSeq.comp
        (bs := [Sum.inl (rmFwd i), Sum.inr (rmDName i)])
        (seqBody_rmDom_c_iff.2 (Or.inl ⟨i, hi, by rw [hgi]; exact hq, rfl⟩)) ?_
      rw [List.cons_append, List.cons_append, List.nil_append]
      refine Domain.YieldSeq.prim ?_
      refine Domain.YieldSeq.comp
        (bs := [Sum.inr (rmCName (M.ex.getI i).tgt), Sum.inl (rmUndo i)])
        (seqBody_rmDom_d_iff.2 ⟨hi, rfl⟩) ?_
      rw [List.append_nil, hgi]
      exact Domain.YieldSeq.append hy₁ (Domain.YieldSeq.prim Domain.YieldSeq.nil)
    · refine ⟨?_, ?_⟩
      · refine (applicable_rmFwd_iff hi (hpb.ex_getI hi)).2 ⟨?_, ?_, ?_, ?_⟩
        · rw [hgi]; exact hin
        · rw [hgi]; exact hw
        · rw [hgi]; exact hu
        · rw [hgi]; exact hg
      · rw [hst, ActionModel.seqApplicable_append]
        refine ⟨happ₁, ?_⟩
        rw [hres₁]
        refine ⟨?_, trivial⟩
        refine (applicable_rmUndo_iff hi).2 ⟨by rw [hgi]; exact hw, ?_⟩
        rw [hgi, memUpd_self]
    · rw [ActionModel.transitionSeq_cons, hst, ActionModel.transitionSeq_append, hres₁,
        ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil]
      have hun := transition_rmUndo (M := M) (W := W)
        (μ := memUpd μ t.wr.idx t.wr.new) hi (by rw [hgi]; exact hw)
        (by rw [hgi, memUpd_self])
      rw [hgi] at hun
      rw [hun, memUpd_memUpd, memUpd_eq_self hu]
  | @un k₁ k₂ q μ t ht hq hin hg h₁ h₂ ih₁ ih₂ =>
    obtain ⟨j, hj, htj⟩ := List.mem_iff_getElem.1 ht
    have hgj : M.un.getI j = t := by rw [List.getI_eq_getElem (l := M.un) hj, htj]
    obtain ⟨as₁, hlen₁, hy₁, happ₁, hres₁⟩ := ih₁
    obtain ⟨as₂, hlen₂, hy₂, happ₂, hres₂⟩ := ih₂
    refine ⟨rmGrd j :: (as₁ ++ as₂), by simp [hlen₁, hlen₂], ?_, ?_, ?_⟩
    · refine Domain.YieldSeq.comp
        (bs := [Sum.inl (rmGrd j), Sum.inr (rmBrName j)])
        (seqBody_rmDom_c_iff.2 (Or.inr (Or.inl ⟨j, hj, by rw [hgj]; exact hq, rfl⟩))) ?_
      rw [List.cons_append, List.cons_append, List.nil_append]
      refine Domain.YieldSeq.prim ?_
      refine Domain.YieldSeq.comp
        (bs := [Sum.inr (rmCName (M.un.getI j).tgt₁), Sum.inr (rmCName (M.un.getI j).tgt₂)])
        (seqBody_rmDom_br_iff.2 ⟨hj, rfl⟩) ?_
      rw [List.append_nil, hgj]
      exact Domain.YieldSeq.append hy₁ hy₂
    · refine ⟨?_, ?_⟩
      · refine (applicable_rmGrd_iff hj (hpb.un_getI hj)).2 ⟨?_, ?_⟩
        · rw [hgj]; exact hin
        · rw [hgj]; exact hg
      · rw [transition_rmGrd hj, ActionModel.seqApplicable_append]
        exact ⟨happ₁, by rw [hres₁]; exact happ₂⟩
    · rw [ActionModel.transitionSeq_cons, transition_rmGrd hj,
        ActionModel.transitionSeq_append, hres₁, hres₂]

/-! ### The correctness of the encoding -/

/-- **Every plan of the encoded problem is an accepting computation of the machine**, and its
length is that of the computation plus one — the action initialising the memory. -/
theorem accFromN_of_plan (hpb : M.PosBelow W.length) {as : List ℕ}
    (hy : (rmDom M W.length).toDomain.YieldSeq [Sum.inr 0] as)
    (happ : (rmDom M W.length).toDomain.SeqApplicable as {f | f ∈ posFacts W}) :
    ∃ k, as.length = k + 1 ∧ M.AccFromN W k M.start (fun _ => false) := by
  cases hy with
  | comp hm h =>
    rw [seqBody_rmDom_root_iff.1 hm, List.cons_append, List.cons_append,
      List.nil_append] at h
    cases h with
    | @prim _ _ as' h1 =>
      obtain ⟨-, happ2⟩ := happ
      rw [transition_rmInit] at happ2
      have hok : RmTasksOk M [Sum.inr (rmCName M.start)] := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
      obtain ⟨ν, hrun, -⟩ := rmRun_of_yieldSeq hpb h1 hok (fun _ => false) happ2
      obtain ⟨k, l, hN, hacc, hrun'⟩ := hrun.cfg_inv
      obtain ⟨hl, -⟩ := hrun'.nil_inv
      refine ⟨k, ?_, hacc⟩
      simp only [List.length_cons]
      omega

/-- **The encoded problem is solvable exactly when the machine accepts the word.** -/
theorem solvable_rmDom_iff (hpb : M.PosBelow W.length) :
    Solvable (rmDom M W.length) (posEnc W) ↔ M.Accepts W := by
  have hseq : ((posEnc W).tnI).toTaskNetwork.IsSeqNet (TnDesc.lin (posEnc W).tnI)
      (TnDesc.seqBody (posEnc W).tnI) := TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (posEnc W).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (rmDom M W.length) (posEnc W))
    (isTO_problem (rmDom_methodsTO (M := M) W.length) guardInst_isTO).2 hseq
  have hinit : (problem (rmDom M W.length) (posEnc W)).transition (rmInit M)
      (problem (rmDom M W.length) (posEnc W)).init = rmState M.mem W (fun _ => false) :=
    transition_rmInit (M := M) (W := W)
  rw [show Solvable (rmDom M W.length) (posEnc W)
      = (problem (rmDom M W.length) (posEnc W)).Solvable from rfl, hnorm, hbody]
  constructor
  · rintro ⟨as, hy, happ, -⟩
    obtain ⟨k, -, hacc⟩ := accFromN_of_plan hpb hy happ
    exact ⟨k, hacc⟩
  · rintro ⟨k, h⟩
    obtain ⟨as, -, hy, happ, -⟩ := yieldSeq_of_accFromN (M := M) (W := W) hpb h
    refine ⟨rmInit M :: as, ?_, ?_, ?_⟩
    · refine Domain.YieldSeq.comp
        (bs := [Sum.inl (rmInit M), Sum.inr (rmCName M.start)])
        (seqBody_rmDom_root_iff.2 rfl) ?_
      rw [List.cons_append, List.cons_append, List.nil_append]
      exact Domain.YieldSeq.prim hy
    · refine ⟨applicable_rmInit _, ?_⟩
      rw [hinit]
      exact happ
    · intro f hf
      simp only [problem_goal, InstDesc.goalList, posEnc, guardInst, Set.mem_setOf_eq,
        List.not_mem_nil] at hf

end Syn

end HTN
