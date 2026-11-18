import HtnComplexity.Complexity.AltMemDom
/-!
# Alternation with a memory: the simulation

This file proves that the domain description `HTN.Syn.amDom` of
`HtnComplexity/Complexity/AltMemDom.lean` simulates the alternating machine with a memory,
with the instance encoder `HTN.Syn.posEnc` unchanged:

    HTN.Syn.solvable_amDom_iff : Solvable (amDom M w.length) (posEnc w) ↔ M.Accepts w

The invariant that carries the proof is the one the backtracking device buys:

> every refinement of a configuration task which is executable in a state of the form
> `amState M W μ` **ends in that same state**

(`HTN.Syn.yieldSeq_amDom_iff`).  This is what makes the branching method sound although the
memory is mutable: the second branch of a universal step starts in the state the first branch
restored, namely the state in which the universal step was taken.
-/

namespace HTN

namespace Syn

open Binarise

variable {M : BitAltMem}

/-! ### The states of the encoding -/

/-- **The planning state holding the word `W` and the memory `μ`**: the position facts of the
word, and one rail per memory bit. -/
def amState (M : BitAltMem) (W : List Bool) (μ : ℕ → Bool) : Set ℕ :=
  {f | f ∈ posFacts W} ∪ {f | ∃ i < M.mem, f = amRail W.length i (μ i)}

theorem amRail_not_mem_posFacts (W : List Bool) (i : ℕ) (b : Bool) :
    amRail W.length i b ∉ posFacts W := by
  intro h
  obtain ⟨v, hv, hl⟩ := mem_posFacts_iff.1 h
  have := hv.length_le
  simp only [List.length_cons] at this
  omega

theorem posFact_lt_ne_amRail {W : List Bool} {k : ℕ} (hk : k < W.length) (b c : Bool) (i : ℕ) :
    posFact k b ≠ amRail W.length i c := by
  intro h
  have := (posFact_inj h).1
  omega

theorem mem_amState_rail {W : List Bool} {μ : ℕ → Bool} {i : ℕ} {b : Bool} :
    amRail W.length i b ∈ amState M W μ ↔ i < M.mem ∧ μ i = b := by
  constructor
  · rintro (h | ⟨i', hi', h⟩)
    · exact absurd h (amRail_not_mem_posFacts W i b)
    · obtain ⟨hpos, hval⟩ := posFact_inj h
      have hii : i = i' := by omega
      subst hii
      exact ⟨hi', hval.symm⟩
  · rintro ⟨hi, rfl⟩
    exact Or.inr ⟨i, hi, rfl⟩

theorem mem_amState_pos {W : List Bool} {μ : ℕ → Bool} {k : ℕ} (hk : k < W.length) {b : Bool} :
    posFact k b ∈ amState M W μ ↔ posFact k b ∈ posFacts W := by
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact h
    · exact absurd h (posFact_lt_ne_amRail hk b _ i)
  · exact fun h => Or.inl h

/-- **Writing a memory bit** is what the corresponding change of the state does. -/
theorem amState_write {W : List Bool} {μ : ℕ → Bool} {i : ℕ} {u : Bool} (hi : i < M.mem)
    (hu : μ i = u) (v : Bool) :
    (amState M W μ \ {amRail W.length i u}) ∪ {amRail W.length i v}
      = amState M W (memUpd μ i v) := by
  subst hu
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, amState, Set.mem_setOf_eq]
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
theorem memSat_iff_subset {W : List Bool} {μ : ℕ → Bool} (g : List MemLit) :
    (∀ f ∈ g.map (amRailOf W.length), f ∈ amState M W μ) ↔ MemSat M.mem μ g := by
  constructor
  · intro h p hp
    have := h (amRailOf W.length p) (List.mem_map_of_mem hp)
    exact mem_amState_rail.1 this
  · intro h f hf
    simp only [List.mem_map] at hf
    obtain ⟨p, hp, rfl⟩ := hf
    obtain ⟨h1, h2⟩ := h p hp
    exact mem_amState_rail.2 ⟨h1, h2⟩

/-! ### The actions on the states -/

variable {W : List Bool} {μ : ℕ → Bool}

/-- **A forward action is applicable** exactly when the machine may take the transition. -/
theorem applicable_amFwd_iff {k i : ℕ} (hk : k < W.length) (hi : i < M.ex.length) :
    (amDom M W.length).toDomain.Applicable (amFwd M k i) (amState M W μ) ↔
      (posFact k (M.ex.getI i).bit ∈ posFacts W ∧ (M.ex.getI i).wr.idx < M.mem ∧
        μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old ∧
        MemSat M.mem μ (M.ex.getI i).guard) := by
  have hj : amFwd M k i < amNumActs M W.length := amFwd_lt hk hi
  have hp : (amDom M W.length).toDomain.prec (amFwd M k i)
      = {f | f ∈ (amFwdData M W.length k i).1} := by
    rw [DomDesc.toDomain_prec, prec_amDom hj, amActData_fwd hi]
  constructor
  · intro happ
    have hsub : {f | f ∈ (amFwdData M W.length k i).1} ⊆ amState M W μ := by
      rw [← hp]; exact happ
    have h1 : posFact k (M.ex.getI i).bit ∈ amState M W μ :=
      hsub (by simp [amFwdData])
    have h2 : amRail W.length (M.ex.getI i).wr.idx (M.ex.getI i).wr.old ∈ amState M W μ :=
      hsub (by simp [amFwdData])
    obtain ⟨h2a, h2b⟩ := mem_amState_rail.1 h2
    refine ⟨(mem_amState_pos hk).1 h1, h2a, h2b, (memSat_iff_subset (W := W) _).1 ?_⟩
    intro f hf
    exact hsub (by simp only [amFwdData, List.mem_cons]; exact Or.inr (Or.inr hf))
  · rintro ⟨h1, h2, h3, h4⟩
    rw [ActionModel.Applicable, hp]
    intro f hf
    simp only [amFwdData, Set.mem_setOf_eq, List.mem_cons] at hf
    rcases hf with rfl | rfl | hf
    · exact (mem_amState_pos hk).2 h1
    · exact mem_amState_rail.2 ⟨h2, h3⟩
    · exact (memSat_iff_subset (W := W) _).2 h4 f hf

/-- **A forward action writes the memory bit of its transition.** -/
theorem transition_amFwd {k i : ℕ} (hk : k < W.length) (hi : i < M.ex.length)
    (hidx : (M.ex.getI i).wr.idx < M.mem)
    (hu : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old) :
    (amDom M W.length).toDomain.transition (amFwd M k i) (amState M W μ)
      = amState M W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) := by
  have hj : amFwd M k i < amNumActs M W.length := amFwd_lt hk hi
  show ((amState M W μ \ (amDom M W.length).del (amFwd M k i))
    ∪ (amDom M W.length).add (amFwd M k i)) = _
  rw [add_amDom hj, del_amDom hj, amActData_fwd hi]
  simp only [amFwdData]
  rw [setOf_mem_singleton, setOf_mem_singleton]
  exact amState_write hidx hu _

/-- **An undoing action is applicable** after the write it undoes. -/
theorem applicable_amUndo {i : ℕ} (hi : i < M.ex.length)
    (hidx : (M.ex.getI i).wr.idx < M.mem) :
    (amDom M W.length).toDomain.Applicable (amUndo i)
      (amState M W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new)) := by
  have hj : amUndo i < amNumActs M W.length := amUndo_lt hi
  rw [ActionModel.Applicable, DomDesc.toDomain_prec, prec_amDom hj, amActData_undo]
  intro f hf
  simp only [amUndoData, Set.mem_setOf_eq, List.mem_singleton] at hf
  subst hf
  exact mem_amState_rail.2 ⟨hidx, by rw [memUpd_self]⟩

/-- **An undoing action restores the memory the write changed.** -/
theorem transition_amUndo {i : ℕ} (hi : i < M.ex.length)
    (hidx : (M.ex.getI i).wr.idx < M.mem)
    (hu : μ (M.ex.getI i).wr.idx = (M.ex.getI i).wr.old) :
    (amDom M W.length).toDomain.transition (amUndo i)
        (amState M W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new))
      = amState M W μ := by
  have hj : amUndo i < amNumActs M W.length := amUndo_lt hi
  show ((amState M W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new)
    \ (amDom M W.length).del (amUndo i)) ∪ (amDom M W.length).add (amUndo i)) = _
  rw [add_amDom hj, del_amDom hj, amActData_undo]
  simp only [amUndoData]
  rw [setOf_mem_singleton, setOf_mem_singleton,
    amState_write hidx (memUpd_self μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new)
      ((M.ex.getI i).wr.old),
    memUpd_memUpd, memUpd_eq_self hu]

/-- **A universal guard is applicable** exactly when the machine may take the transition. -/
theorem applicable_amGrd_iff {k j : ℕ} (hk : k < W.length) (hj : j < M.un.length) :
    (amDom M W.length).toDomain.Applicable (amGrd M k j) (amState M W μ) ↔
      (posFact k (M.un.getI j).bit ∈ posFacts W ∧ MemSat M.mem μ (M.un.getI j).guard) := by
  have hlt : amGrd M k j < amNumActs M W.length := amGrd_lt hk hj
  have hp : (amDom M W.length).toDomain.prec (amGrd M k j)
      = {f | f ∈ (amGrdData M W.length k j).1} := by
    rw [DomDesc.toDomain_prec, prec_amDom hlt, amActData_grd hj]
  constructor
  · intro happ
    have hsub : {f | f ∈ (amGrdData M W.length k j).1} ⊆ amState M W μ := by
      rw [← hp]; exact happ
    refine ⟨(mem_amState_pos hk).1 (hsub (by simp [amGrdData])), (memSat_iff_subset (W := W) _).1 ?_⟩
    intro f hf
    exact hsub (by simp only [amGrdData, List.mem_cons]; exact Or.inr hf)
  · rintro ⟨h1, h2⟩
    rw [ActionModel.Applicable, hp]
    intro f hf
    simp only [amGrdData, Set.mem_setOf_eq, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact (mem_amState_pos hk).2 h1
    · exact (memSat_iff_subset (W := W) _).2 h2 f hf

/-- A universal guard has no effect. -/
theorem transition_amGrd {k j : ℕ} (hk : k < W.length) (hj : j < M.un.length) (s : Set ℕ) :
    (amDom M W.length).toDomain.transition (amGrd M k j) s = s := by
  have hlt : amGrd M k j < amNumActs M W.length := amGrd_lt hk hj
  show ((s \ (amDom M W.length).del (amGrd M k j)) ∪ (amDom M W.length).add (amGrd M k j)) = _
  rw [add_amDom hlt, del_amDom hlt, amActData_grd hj]
  simp [amGrdData]

/-- **An accepting check is applicable** exactly when its memory guard holds. -/
theorem applicable_amAccA_iff {a : ℕ} (ha : a < M.acc.length) :
    (amDom M W.length).toDomain.Applicable (amAccA a) (amState M W μ) ↔
      MemSat M.mem μ (M.acc.getI a).guard := by
  have hlt : amAccA a < amNumActs M W.length := amAccA_lt ha
  have hp : (amDom M W.length).toDomain.prec (amAccA a)
      = {f | f ∈ (amAccData M W.length a).1} := by
    rw [DomDesc.toDomain_prec, prec_amDom hlt, amActData_acc ha]
  rw [ActionModel.Applicable, hp]
  constructor
  · intro hsub
    exact (memSat_iff_subset (W := W) _).1 fun f hf => hsub hf
  · intro hg f hf
    exact (memSat_iff_subset (W := W) _).2 hg f hf

/-- An accepting check has no effect. -/
theorem transition_amAccA {a : ℕ} (ha : a < M.acc.length) (s : Set ℕ) :
    (amDom M W.length).toDomain.transition (amAccA a) s = s := by
  have hlt : amAccA a < amNumActs M W.length := amAccA_lt ha
  show ((s \ (amDom M W.length).del (amAccA a)) ∪ (amDom M W.length).add (amAccA a)) = _
  rw [add_amDom hlt, del_amDom hlt, amActData_acc ha]
  simp [amAccData]

/-- The initialising action is always applicable. -/
theorem applicable_amInit (s : Set ℕ) :
    (amDom M W.length).toDomain.Applicable (amInit M) s := by
  have hlt : amInit M < amNumActs M W.length := amInit_lt _
  rw [ActionModel.Applicable, DomDesc.toDomain_prec, prec_amDom hlt, amActData_init]
  intro f hf
  simp [amInitData] at hf

/-- **The initialising action creates the empty memory.** -/
theorem transition_amInit :
    (amDom M W.length).toDomain.transition (amInit M) {f | f ∈ posFacts W}
      = amState M W (fun _ => false) := by
  have hlt : amInit M < amNumActs M W.length := amInit_lt (M := M) W.length
  show (({f | f ∈ posFacts W} \ (amDom M W.length).del (amInit M))
    ∪ (amDom M W.length).add (amInit M)) = _
  rw [add_amDom hlt, del_amDom hlt, amActData_init]
  simp only [amInitData]
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, List.not_mem_nil, not_false_iff,
    and_true, List.mem_map, List.mem_range, amState]
  constructor
  · rintro (hf | ⟨i, hi, rfl⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨i, hi, rfl⟩
  · rintro (hf | ⟨i, hi, rfl⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨i, hi, rfl⟩

/-! ### The simulation -/

/-- The bit a position fact of the word names is the bit the word has there. -/
theorem bit_eq_of_mem_posFacts {W : List Bool} {b c : Bool} {v : List Bool}
    (hv : (b :: v) <:+ W) (h : posFact v.length c ∈ posFacts W) : c = b := by
  obtain ⟨u, hu, hul⟩ := mem_posFacts_iff.1 h
  have hbu : c :: u = b :: v := eq_of_suffix_of_length_eq hu hv (by simp [hul])
  exact (List.cons_eq_cons.1 hbu).1

/-- **Soundness of the encoding**: an executable refinement of a configuration task is an
accepting computation of the machine, *and it restores the state it started in*. -/
theorem accFrom_of_yieldSeq_amDom {W : List Bool} : ∀ {v : List Bool}, v <:+ W →
    ∀ (q : ℕ) (μ : ℕ → Bool) (as : List ℕ),
      (amDom M W.length).toDomain.YieldSeq [Sum.inr (amCName v.length q)] as →
      (amDom M W.length).toDomain.SeqApplicable as (amState M W μ) →
      M.AccFrom q v μ ∧
        (amDom M W.length).toDomain.transitionSeq as (amState M W μ) = amState M W μ := by
  intro v
  induction v with
  | nil =>
    intro _ q μ as hy happ
    simp only [List.length_nil] at hy
    cases hy with
    | comp hm h =>
      rcases seqBody_amDom_c_iff.1 hm with ⟨j, -, hk, -⟩ | ⟨j, -, hk, -⟩ | ⟨-, a, ha, hq, rfl⟩
      · exact absurd hk (by simp)
      · exact absurd hk (by simp)
      · rw [List.cons_append, List.nil_append] at h
        cases h with
        | prim h' =>
          cases h' with
          | nil =>
            obtain ⟨happ1, -⟩ := happ
            refine ⟨BitAltMem.AccFrom.nil (c := M.acc.getI a) ?_ hq
              ((applicable_amAccA_iff ha).1 happ1), ?_⟩
            · rw [List.getI_eq_getElem (l := M.acc) ha]
              exact List.getElem_mem ha
            · rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
                transition_amAccA ha]
  | cons b v ih =>
    intro hv q μ as hy happ
    have hvW : v <:+ W := (List.suffix_cons b v).trans hv
    have hlen : v.length < W.length := by
      have := hv.length_le
      simp only [List.length_cons] at this
      omega
    simp only [List.length_cons] at hy
    cases hy with
    | comp hm h =>
      rcases seqBody_amDom_c_iff.1 hm with ⟨j, hj, hjeq, i, hi, hsrc, rfl⟩ |
        ⟨j, hj, hjeq, i, hi, hsrc, rfl⟩ | ⟨hk0, -⟩
      · have hjv : j = v.length := by omega
        subst hjv
        rw [List.cons_append, List.cons_append, List.nil_append] at h
        cases h with
        | prim h1 =>
          obtain ⟨happ1, happ2⟩ := happ
          obtain ⟨hbit, hidx, hu, hg⟩ := (applicable_amFwd_iff hlen hi).1 happ1
          have hb : (M.ex.getI i).bit = b := bit_eq_of_mem_posFacts hv hbit
          have hst : (amDom M W.length).toDomain.transition (amFwd M v.length i)
              (amState M W μ)
              = amState M W (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) :=
            transition_amFwd hlen hi hidx hu
          rw [hst] at happ2
          cases h1 with
          | comp hm2 h2 =>
            obtain ⟨-, -, rfl⟩ := seqBody_amDom_d_iff.1 hm2
            rw [List.append_nil] at h2
            obtain ⟨as₁, as₂, rfl, hy₁, hy₂⟩ :=
              Domain.YieldSeq.split (xs := [Sum.inr (amCName v.length (M.ex.getI i).tgt)])
                (ys := [Sum.inl (amUndo i)]) h2
            rw [ActionModel.seqApplicable_append] at happ2
            obtain ⟨happA, happB⟩ := happ2
            obtain ⟨hacc, hres⟩ := ih hvW (M.ex.getI i).tgt
              (memUpd μ (M.ex.getI i).wr.idx (M.ex.getI i).wr.new) as₁ hy₁ happA
            cases hy₂ with
            | prim h3 =>
              cases h3 with
              | nil =>
                refine ⟨BitAltMem.AccFrom.ex (t := M.ex.getI i) ?_ hsrc hb hg hidx hu hacc, ?_⟩
                · rw [List.getI_eq_getElem (l := M.ex) hi]
                  exact List.getElem_mem hi
                · rw [ActionModel.transitionSeq_cons, hst, ActionModel.transitionSeq_append,
                    hres, ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
                    transition_amUndo hi hidx hu]
      · have hjv : j = v.length := by omega
        subst hjv
        rw [List.cons_append, List.cons_append, List.nil_append] at h
        cases h with
        | prim h1 =>
          obtain ⟨happ1, happ2⟩ := happ
          obtain ⟨hbit, hg⟩ := (applicable_amGrd_iff hlen hi).1 happ1
          have hb : (M.un.getI i).bit = b := bit_eq_of_mem_posFacts hv hbit
          rw [transition_amGrd hlen hi] at happ2
          cases h1 with
          | comp hm2 h2 =>
            obtain ⟨-, -, rfl⟩ := seqBody_amDom_br_iff.1 hm2
            rw [List.append_nil] at h2
            obtain ⟨as₁, as₂, rfl, hy₁, hy₂⟩ :=
              Domain.YieldSeq.split (xs := [Sum.inr (amCName v.length (M.un.getI i).tgt₁)])
                (ys := [Sum.inr (amCName v.length (M.un.getI i).tgt₂)]) h2
            rw [ActionModel.seqApplicable_append] at happ2
            obtain ⟨hA, hB⟩ := happ2
            obtain ⟨hacc₁, hres₁⟩ := ih hvW (M.un.getI i).tgt₁ μ as₁ hy₁ hA
            rw [hres₁] at hB
            obtain ⟨hacc₂, hres₂⟩ := ih hvW (M.un.getI i).tgt₂ μ as₂ hy₂ hB
            refine ⟨BitAltMem.AccFrom.un (t := M.un.getI i) ?_ hsrc hb hg hacc₁ hacc₂, ?_⟩
            · rw [List.getI_eq_getElem (l := M.un) hi]
              exact List.getElem_mem hi
            · rw [ActionModel.transitionSeq_cons, transition_amGrd hlen hi,
                ActionModel.transitionSeq_append, hres₁, hres₂]
      · exact absurd hk0 (by simp)

/-- **Completeness of the encoding**: an accepting computation of the machine is an executable
refinement of the configuration task, and it restores the state. -/
theorem yieldSeq_amDom_of_accFrom {W : List Bool} : ∀ {v : List Bool}, v <:+ W →
    ∀ (q : ℕ) (μ : ℕ → Bool), M.AccFrom q v μ →
      ∃ as : List ℕ, (amDom M W.length).toDomain.YieldSeq [Sum.inr (amCName v.length q)] as ∧
        (amDom M W.length).toDomain.SeqApplicable as (amState M W μ) ∧
        (amDom M W.length).toDomain.transitionSeq as (amState M W μ) = amState M W μ := by
  intro v
  induction v with
  | nil =>
    intro _ q μ hacc
    cases hacc with
    | nil hc hq hg =>
      rename_i c
      obtain ⟨a, ha, hca⟩ := List.mem_iff_getElem.1 hc
      have hgi : M.acc.getI a = c := by rw [List.getI_eq_getElem (l := M.acc) ha, hca]
      refine ⟨[amAccA a], ?_, ?_, ?_⟩
      · refine Domain.YieldSeq.comp (bs := [Sum.inl (amAccA a)])
          (seqBody_amDom_c_iff.2 (Or.inr (Or.inr ⟨rfl, a, ha, by rw [hgi]; exact hq, rfl⟩))) ?_
        rw [List.cons_append, List.nil_append]
        exact Domain.YieldSeq.prim Domain.YieldSeq.nil
      · exact ⟨(applicable_amAccA_iff ha).2 (by rw [hgi]; exact hg), trivial⟩
      · rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil,
          transition_amAccA ha]
  | cons b v ih =>
    intro hv q μ hacc
    have hvW : v <:+ W := (List.suffix_cons b v).trans hv
    have hlen : v.length < W.length := by
      have := hv.length_le
      simp only [List.length_cons] at this
      omega
    cases hacc with
    | ex ht hsrc hb hg hidx hu h' =>
      rename_i t
      obtain ⟨i, hi, hti⟩ := List.mem_iff_getElem.1 ht
      have hgi : M.ex.getI i = t := by rw [List.getI_eq_getElem (l := M.ex) hi, hti]
      obtain ⟨as₁, hy₁, happ₁, hres₁⟩ := ih hvW t.tgt (memUpd μ t.wr.idx t.wr.new) h'
      have hst : (amDom M W.length).toDomain.transition (amFwd M v.length i)
          (amState M W μ) = amState M W (memUpd μ t.wr.idx t.wr.new) := by
        have := transition_amFwd (M := M) (W := W) (μ := μ) hlen hi (by rw [hgi]; exact hidx)
          (by rw [hgi]; exact hu)
        rwa [hgi] at this
      refine ⟨amFwd M v.length i :: (as₁ ++ [amUndo i]), ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        refine Domain.YieldSeq.comp
          (bs := [Sum.inl (amFwd M v.length i), Sum.inr (amDName v.length i)])
          (seqBody_amDom_c_iff.2 (Or.inl ⟨v.length, hlen, rfl, i, hi, by rw [hgi]; exact hsrc,
            rfl⟩)) ?_
        rw [List.cons_append, List.cons_append, List.nil_append]
        refine Domain.YieldSeq.prim ?_
        refine Domain.YieldSeq.comp
          (bs := [Sum.inr (amCName v.length (M.ex.getI i).tgt), Sum.inl (amUndo i)])
          (seqBody_amDom_d_iff.2 ⟨hlen, hi, rfl⟩) ?_
        rw [List.append_nil]
        rw [hgi]
        exact Domain.YieldSeq.append hy₁ (Domain.YieldSeq.prim Domain.YieldSeq.nil)
      · refine ⟨?_, ?_⟩
        · refine (applicable_amFwd_iff hlen hi).2 ⟨?_, ?_, ?_, ?_⟩
          · rw [hgi, hb]
            exact mem_posFacts_iff.2 ⟨v, hv, rfl⟩
          · rw [hgi]; exact hidx
          · rw [hgi]; exact hu
          · rw [hgi]; exact hg
        · rw [hst, ActionModel.seqApplicable_append]
          refine ⟨happ₁, ?_⟩
          rw [hres₁]
          refine ⟨?_, trivial⟩
          have := applicable_amUndo (M := M) (W := W) (μ := μ) hi (by rw [hgi]; exact hidx)
          rwa [hgi] at this
      · rw [ActionModel.transitionSeq_cons, hst, ActionModel.transitionSeq_append, hres₁,
          ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil]
        have := transition_amUndo (M := M) (W := W) (μ := μ) hi (by rw [hgi]; exact hidx)
          (by rw [hgi]; exact hu)
        rwa [hgi] at this
    | un ht hsrc hb hg h₁ h₂ =>
      rename_i t
      obtain ⟨j, hj, htj⟩ := List.mem_iff_getElem.1 ht
      have hgj : M.un.getI j = t := by rw [List.getI_eq_getElem (l := M.un) hj, htj]
      obtain ⟨as₁, hy₁, happ₁, hres₁⟩ := ih hvW t.tgt₁ μ h₁
      obtain ⟨as₂, hy₂, happ₂, hres₂⟩ := ih hvW t.tgt₂ μ h₂
      refine ⟨amGrd M v.length j :: (as₁ ++ as₂), ?_, ?_, ?_⟩
      · simp only [List.length_cons]
        refine Domain.YieldSeq.comp
          (bs := [Sum.inl (amGrd M v.length j),
            Sum.inr (amBrName v.length (M.un.getI j).tgt₁ (M.un.getI j).tgt₂)])
          (seqBody_amDom_c_iff.2 (Or.inr (Or.inl ⟨v.length, hlen, rfl, j, hj,
            by rw [hgj]; exact hsrc, rfl⟩))) ?_
        rw [List.cons_append, List.cons_append, List.nil_append]
        refine Domain.YieldSeq.prim ?_
        refine Domain.YieldSeq.comp
          (bs := [Sum.inr (amCName v.length (M.un.getI j).tgt₁),
            Sum.inr (amCName v.length (M.un.getI j).tgt₂)])
          (seqBody_amDom_br_iff.2 ⟨hlen, ⟨j, hj, rfl, rfl⟩, rfl⟩) ?_
        rw [List.append_nil, hgj]
        exact Domain.YieldSeq.append hy₁ hy₂
      · refine ⟨?_, ?_⟩
        · refine (applicable_amGrd_iff hlen hj).2 ⟨?_, ?_⟩
          · rw [hgj, hb]
            exact mem_posFacts_iff.2 ⟨v, hv, rfl⟩
          · rw [hgj]; exact hg
        · rw [transition_amGrd hlen hj, ActionModel.seqApplicable_append]
          exact ⟨happ₁, by rw [hres₁]; exact happ₂⟩
      · rw [ActionModel.transitionSeq_cons, transition_amGrd hlen hj,
          ActionModel.transitionSeq_append, hres₁, hres₂]

/-- **The encoded problem is solvable exactly when the machine accepts the word.** -/
theorem solvable_amDom_iff (w : List Bool) :
    Solvable (amDom M w.length) (posEnc w) ↔ M.Accepts w := by
  have hseq : ((posEnc w).tnI).toTaskNetwork.IsSeqNet (TnDesc.lin (posEnc w).tnI)
      (TnDesc.seqBody (posEnc w).tnI) := TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (posEnc w).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (amDom M w.length) (posEnc w))
    (isTO_problem (amDom_methodsTO (M := M) w.length) guardInst_isTO).2 hseq
  have hinit : (problem (amDom M w.length) (posEnc w)).transition (amInit M)
      (problem (amDom M w.length) (posEnc w)).init = amState M w (fun _ => false) :=
    transition_amInit (M := M) (W := w)
  rw [show Solvable (amDom M w.length) (posEnc w)
      = (problem (amDom M w.length) (posEnc w)).Solvable from rfl, hnorm, hbody]
  constructor
  · rintro ⟨as, hy, happ, -⟩
    cases hy with
    | comp hm h =>
      rw [seqBody_amDom_root_iff.1 hm, List.cons_append, List.cons_append,
        List.nil_append] at h
      cases h with
      | prim h1 =>
        obtain ⟨-, happ2⟩ := happ
        rw [hinit] at happ2
        exact (accFrom_of_yieldSeq_amDom (List.suffix_refl w) M.start (fun _ => false) _ h1
          happ2).1
  · intro h
    obtain ⟨as, hy, happ, -⟩ := yieldSeq_amDom_of_accFrom (M := M) (W := w)
      (List.suffix_refl w) M.start (fun _ => false) h
    refine ⟨amInit M :: as, ?_, ?_, ?_⟩
    · refine Domain.YieldSeq.comp
        (bs := [Sum.inl (amInit M), Sum.inr (amCName w.length M.start)])
        (seqBody_amDom_root_iff.2 rfl) ?_
      rw [List.cons_append, List.cons_append, List.nil_append]
      exact Domain.YieldSeq.prim hy
    · refine ⟨applicable_amInit _, ?_⟩
      rw [hinit]
      exact happ
    · intro f hf
      simp only [problem_goal, InstDesc.goalList, posEnc, guardInst, Set.mem_setOf_eq,
        List.not_mem_nil] at hf

end Syn

end HTN
