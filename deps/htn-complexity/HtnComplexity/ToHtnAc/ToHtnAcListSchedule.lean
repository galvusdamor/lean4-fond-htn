import HtnPlanning.Core.ProofList
import HtnComplexity.ToHtnAc.ToHtnAcComplete
import HtnComplexity.ToHtnAc.ToHtnAcLength
import HtnPlanning.Interleave.InterleaveGrow
/-!
# Scheduling a proof **list**: the polynomial form of completeness

`HtnComplexity/ToHtnAc/ToHtnAcComplete.lean` schedules a *derivation tree* of the proof-tuple
calculus: one proof step and one memory cell per node of the tree.  That is enough for
correctness, but not for the size claim of the source paper: the smallest derivation tree of a
provable triple can be exponentially larger than the number of triples, so the number of memory
cells would be doubly exponential in the source signature and its logarithm — which is what the
size of the compiled domain depends on — would not be polynomial.

The source paper therefore uses a proof **list** (`HtnPlanning/Core/ProofList.lean`), in which
an entry may be used by arbitrarily many later entries.  The construction supports this: a proof
step ends with `w` write requests, so it can fill `w` memory cells with its triple, one per later
use.

This file schedules a proof list.  The induction is along the list, in chronological order; its
invariant is a *multiset of pending memory cells* — cells whose write phase has run inside the
block of the proof step that produced their triple and whose read phase is still to come.  The
result, `HTN.ToAc.exists_listSchedule`, produces a plan of the compiled problem using at most
`2 · |l|` memory cells and `|l|` proof steps, and `HTN.ToAc.solvable_problem'_of_provable_le`
turns it into the completeness theorem with an **explicit** bound on the number of memory cells.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open Domain

/-! ### Memory cells of a triple -/

/-- The write phase of a memory cell holding the triple `t` — the part of its run that the
proof step producing `t` performs. -/
noncomputable def cellHalf (vars : List F) (t : Trip F A C) : List (AcAct F A C) :=
  memWrite t.1 t.2.2 t.2.1 vars

/-- The whole run of a memory cell holding the triple `t`. -/
noncomputable def cellFull (vars : List F) (t : Trip F A C) : List (AcAct F A C) :=
  memWrite t.1 t.2.2 t.2.1 vars ++ memRead t.1 t.2.2 t.2.1 vars

lemma cellHalf_append_memRead (t : Trip F A C) (vars : List F) :
    cellHalf vars t ++ memRead t.1 t.2.2 t.2.1 vars = cellFull vars t := rfl

lemma yieldSeq_cellFull (t : Trip F A C) :
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.MEM : AcTask F A C)] (cellFull vars t) :=
  yieldSeq_MEM_memPhases _ _ _

lemma memWrites_eq_flatten (t : Trip F A C) (vars : List F) (w : ℕ) :
    memWrites t.1 t.2.2 t.2.1 vars w = (List.replicate w (cellHalf vars t)).flatten := rfl

/-- **An interleaving of refinements of `𝔠` is a refinement of the grid of copies of `𝔠`.** -/
lemma gridYield_of_interleaveList {c : AcTask F A C} (hc : IsSeqTask c) :
    ∀ {ls : List (List (AcAct F A C))} {X : List (AcAct F A C)}, InterleaveList ls X →
      (∀ r ∈ ls, (domain D vars bound).YieldSeq [Sum.inr c] r) →
      (domain D vars bound).GridYield (List.replicate ls.length [Sum.inr c]) X := by
  intro ls X h
  induction h with
  | nil => intro _; simp
  | @cons as bs cs ls h hint ih =>
      intro hall
      have h1 : (domain D vars bound).GridYield (List.replicate 1 [Sum.inr c]) as :=
        gridYield_replicate_one hc (hall as (by simp))
      have h2 := ih fun r hr => hall r (by simp [hr])
      have := gridYield_replicate_add hc 1 ls.length h1 h2 hint
      simpa [Nat.add_comm] using this

lemma gridYield_of_interleaveMS {c : AcTask F A C} (hc : IsSeqTask c)
    {s : Multiset (List (AcAct F A C))} {X : List (AcAct F A C)} (h : InterleaveMS s X)
    (hall : ∀ r ∈ s, (domain D vars bound).YieldSeq [Sum.inr c] r) :
    (domain D vars bound).GridYield
      (List.replicate (Multiset.card s) [Sum.inr c]) X := by
  obtain ⟨ls, hls, hint⟩ := h
  subst hls
  have : ∀ r ∈ ls, (domain D vars bound).YieldSeq [Sum.inr c] r := by
    intro r hr; exact hall r (by simpa using hr)
  simpa using gridYield_of_interleaveList hc hint this

/-- Rearranging a family of components. -/
lemma add_cons_comm {β : Type} (a : β) (s u : Multiset β) : s + (a ::ₘ u) = a ::ₘ (s + u) := by
  rw [add_comm s, Multiset.cons_add, add_comm u s]

/-! ### The invariant of the scheduling induction -/

/-- `Scheduled D vars bnd pend m k P`: the action sequence `P` is an interleaving of `m`
complete memory cells and of the write phases of the pending cells `pend` with the runs of `k`
proof steps. -/
def Scheduled (D : Domain F A C I) (vars : List F) (bnd : ℕ) (pend : Multiset (Trip F A C))
    (m k : ℕ) (P : List (AcAct F A C)) : Prop :=
  ∃ (cells : Multiset (List (AcAct F A C))) (Xmem Xtup : List (AcAct F A C)),
    Multiset.card cells = m ∧
    (∀ r ∈ cells, (domain D vars bnd).YieldSeq [Sum.inr AcTask.MEM] r) ∧
    InterleaveMS (cells + pend.map (cellHalf vars)) Xmem ∧
    (domain D vars bnd).GridYield (List.replicate k [Sum.inr AcTask.TUPLE]) Xtup ∧
    Interleave Xmem Xtup P

/-! ### The scheduling theorem for a proof list -/

open scoped Classical in
/-- **The scheduling theorem, for a proof list.**  A proof list of length `n` is executed by a
plan that uses at most `2n` memory cells and `n` proof steps, provided the compiled problem
offers `2n` of each.  The plan may be asked to leave any multiset `pend` of *pending* memory
cells — cells filled with a triple of the list whose read phase is still to come; at the end of
the plan the state is clean again and holds the last triple of the list. -/
theorem exists_listSchedule (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y]) :
    ∀ {l : List (Trip F A C)}, D.ProofList l →
      ∀ pend : Multiset (Trip F A C), (∀ u ∈ pend, u ∈ l) →
        2 * l.length + Multiset.card pend ≤ bound →
        ∀ s : Set (AcFact F A C), Clean s →
        ∃ (m k : ℕ) (P : List (AcAct F A C)),
          Scheduled D vars bound pend m k P ∧ m ≤ 2 * l.length ∧ k ≤ l.length ∧
          P.length ≤ (2 * l.length + Multiset.card pend) * (2 * vars.length + 5) +
            l.length * (11 * vars.length + 15) ∧
          (domain D vars bound).SeqApplicable P s ∧
          Clean ((domain D vars bound).transitionSeq P s) ∧
          ∀ (t : Trip F A C) (l' : List (Trip F A C)), l = t :: l' →
            RepresentsOn ((domain D vars bound).transitionSeq P s) 0 t.1 vars ∧
            RepresentsOn ((domain D vars bound).transitionSeq P s) 2 t.2.2 vars ∧
            AcFact.task t.2.1 ∈ (domain D vars bound).transitionSeq P s := by
  intro l hl
  induction hl with
  | nil =>
      intro pend hpend _ s hs
      have hp0 : pend = 0 := by
        rw [← Multiset.card_eq_zero]
        by_contra hc
        obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero
          (fun h : pend = 0 => hc (by simp [h]))
        simpa using hpend u hu
      subst hp0
      refine ⟨0, 0, [], ⟨0, [], [], by simp, by simp, ?_, ?_, Interleave.nil⟩, by simp, by simp,
        by simp, by simp, by simpa using hs, ?_⟩
      · simpa using InterleaveMS.nil
      · exact gridYield_replicate_zero.2 rfl
      · intro t l' hcontra; exact absurd hcontra (by simp)
  | @cons t l hl hj ih =>
      intro pend hpend hbnd s hs
      -- split the demand into the copies of `t` and the rest
      obtain ⟨w, pend', hsplit, hnot⟩ :
          ∃ (w : ℕ) (pend' : Multiset (Trip F A C)),
            pend = Multiset.replicate w t + pend' ∧ t ∉ pend' := by
        refine ⟨Multiset.count t pend, pend.filter (fun u => ¬ (u = t)), ?_, ?_⟩
        · rw [← Multiset.filter_eq' pend t]
          exact (Multiset.filter_add_not _ _).symm
        · intro hc
          exact (Multiset.mem_filter.1 hc).2 rfl
      have hle : pend' ≤ pend := by rw [hsplit]; exact Multiset.le_add_left _ _
      have hmem' : ∀ u ∈ pend', u ∈ l := by
        intro u hu
        have hu' : u ∈ pend := Multiset.mem_of_le hle hu
        have := hpend u hu'
        rcases List.mem_cons.1 this with rfl | h
        · exact absurd hu hnot
        · exact h
      have hcard : Multiset.card pend = w + Multiset.card pend' := by
        rw [hsplit]; simp
      have hlen : (t :: l).length = l.length + 1 := by simp
      have hwb : w ≤ bound := by omega
      cases hj with
      | @prim a S ha =>
          obtain ⟨m', k', P', ⟨cells', Xmem', Xtup', hcard', hcells', hIMS', hXtup', hIL'⟩,
            hm', hk', hlen', happ', hclean', -⟩ := ih pend' hmem' (by omega) s hs
          obtain ⟨g₁, g₂, g₃, e₁, e₂, hg₁, hg₂, hg₃, he₁, he₂, happB, hcleanB, hrep0, hrep2,
            htask⟩ := exists_primBlock (D := D) (vars := vars) (bound := bound) hvars ha
              (hdisj a) w hclean'
          refine ⟨m', k' + 1,
            P' ++ primBlock a S (D.transition a S) g₁ g₂ g₃ e₁ e₂ vars w, ?_, by omega, by omega,
            ?_, ?_, ?_, ?_⟩
          · refine ⟨cells', Xmem' ++ memWrites S (D.transition a S) (Sum.inl a) vars w,
              Xtup' ++ tuplePrimitiveSeq a g₁ g₂ g₃ e₁ e₂ w, hcard', hcells', ?_, ?_, ?_⟩
            · have h := hIMS'.append_replicate
                (y := cellHalf vars (S, Sum.inl a, D.transition a S)) w
              rw [hsplit]
              simpa [Multiset.map_add, Multiset.map_replicate, cellHalf, memWrites,
                add_comm, add_left_comm, add_assoc] using h
            · exact gridYield_replicate_add isSeqTask_TUPLE k' 1 hXtup'
                (gridYield_replicate_one isSeqTask_TUPLE
                  (yieldSeq_TUPLE_of_primitive hwb hg₁ hg₂ hg₃ he₁ he₂))
                (Interleave.append _ _)
            · exact hIL'.append_append
                (interleave_primBlock a S (D.transition a S) g₁ g₂ g₃ e₁ e₂ vars w)
          · rw [List.length_append]
            simp only [List.length_cons, hcard]
            refine sched_len_step (by omega) hlen' ?_
            have hb := length_primBlock_le (D := D) (vars := vars) (bound := bound)
              (o := a) (S := S) (T := D.transition a S) (w := w) hg₁ hg₂ hg₃ he₁ he₂
            unfold blockLen at hb
            omega
          · rw [ActionModel.seqApplicable_append]
            exact ⟨happ', happB⟩
          · rw [ActionModel.transitionSeq_append]
            exact hcleanB
          · rintro t' l' heq
            obtain ⟨rfl, rfl⟩ := List.cons.inj heq
            rw [ActionModel.transitionSeq_append]
            exact ⟨hrep0, hrep2, htask⟩
      | @zero c S hbody => exact absurd (hbin c [] hbody) (by simp)
      | @one c x S S' hbody _ => exact absurd (hbin c [x] hbody) (by simp)
      | @two c x y S S'' S' hbody hx hy =>
          obtain ⟨m', k', P', ⟨cells', Xmem', Xtup', hcard', hcells', hIMS', hXtup', hIL'⟩,
            hm', hk', hlen', happ', hclean', -⟩ :=
            ih ((S, x, S'') ::ₘ (S'', y, S') ::ₘ pend')
              (by
                intro u hu
                rcases Multiset.mem_cons.1 hu with rfl | hu
                · exact hx
                rcases Multiset.mem_cons.1 hu with rfl | hu
                · exact hy
                · exact hmem' u hu)
              (by simp; omega) s hs
          obtain ⟨g₁, g₂, g₃, e₁, e₂, e₃, e₄, hg₁, hg₂, hg₃, he₁, he₂, he₃, he₄, happB,
            hcleanB, hrep0, hrep2, htask⟩ :=
            exists_compoundBlock (D := D) (vars := vars) (bound := bound) c x y S S'' S' w
              hclean'
          -- the two cells that this step reads are completed
          have hIMS1 : InterleaveMS
              (cellHalf vars (S, x, S'') ::ₘ
                (cells' + (cellHalf vars (S'', y, S') ::ₘ pend'.map (cellHalf vars)))) Xmem' := by
            simpa [Multiset.map_cons, add_cons_comm] using hIMS'
          have hIMS2 := hIMS1.extend (u := memRead S S'' x vars)
          have hIMS3 : InterleaveMS
              (cellHalf vars (S'', y, S') ::ₘ
                (cellFull vars (S, x, S'') ::ₘ (cells' + pend'.map (cellHalf vars))))
              (Xmem' ++ memRead S S'' x vars) := by
            rw [cellHalf_append_memRead] at hIMS2
            simpa [add_cons_comm, Multiset.cons_swap] using hIMS2
          have hIMS4 := hIMS3.extend (u := memRead S'' S' y vars)
          rw [cellHalf_append_memRead] at hIMS4
          have hIMS5 := hIMS4.append_replicate (y := cellHalf vars (S, Sum.inr c, S')) w
          refine ⟨m' + 2, k' + 1,
            P' ++ compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w, ?_, by omega,
            by omega, ?_, ?_, ?_, ?_⟩
          · refine ⟨cellFull vars (S'', y, S') ::ₘ cellFull vars (S, x, S'') ::ₘ cells',
              Xmem' ++ memRead S S'' x vars ++ memRead S'' S' y vars ++
                memWrites S S' (Sum.inr c) vars w,
              Xtup' ++ tupleCompoundSeq c x y g₁ g₂ g₃ e₁ e₂ e₃ e₄ w, by simp [hcard'], ?_, ?_,
              ?_, ?_⟩
            · intro r hr
              rcases Multiset.mem_cons.1 hr with rfl | hr
              · exact yieldSeq_cellFull _
              rcases Multiset.mem_cons.1 hr with rfl | hr
              · exact yieldSeq_cellFull _
              · exact hcells' r hr
            · rw [hsplit]
              simpa [Multiset.map_add, Multiset.map_replicate, cellHalf, memWrites,
                add_comm, add_left_comm, add_assoc] using hIMS5
            · exact gridYield_replicate_add isSeqTask_TUPLE k' 1 hXtup'
                (gridYield_replicate_one isSeqTask_TUPLE
                  (yieldSeq_TUPLE_of_compound hbody hwb hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄))
                (Interleave.append _ _)
            · have h := hIL'.append_append
                (interleave_compoundBlock c x y S S'' S' g₁ g₂ g₃ e₁ e₂ e₃ e₄ vars w)
              simpa [List.append_assoc] using h
          · rw [List.length_append]
            simp only [List.length_cons, hcard]
            refine sched_len_step (c₀ := Multiset.card pend' + 2) (by omega) ?_ ?_
            · simpa [Multiset.card_cons, Nat.add_assoc] using hlen'
            · have hb := length_compoundBlock_le (D := D) (vars := vars) (bound := bound)
                (c := c) (x := x) (y := y) (S := S) (S'' := S'') (S' := S') (w := w)
                hg₁ hg₂ hg₃ he₁ he₂ he₃ he₄
              unfold blockLen at hb
              omega
          · rw [ActionModel.seqApplicable_append]
            exact ⟨happ', happB⟩
          · rw [ActionModel.transitionSeq_append]
            exact hcleanB
          · rintro t' l' heq
            obtain ⟨rfl, rfl⟩ := List.cons.inj heq
            rw [ActionModel.transitionSeq_append]
            exact ⟨hrep0, hrep2, htask⟩

/-! ### Completeness with an explicit number of memory cells -/

open scoped Classical in
/-- **Completeness of the compilation, with an explicit bound.**  If the triple
`(s₀, t_I, S')` occurs in a proof list `l` and `S'` satisfies the goal, then the compiled
problem is solvable as soon as it offers `2·(|l| + 1)` memory cells and proof steps. -/
theorem solvable_problem'_of_proofList (hvars : ∀ v : F, v ∈ vars)
    (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {Q : Instance F A C I} {tI0 : C} {S' : Set F} {l : List (Trip F A C)}
    (hl : D.ProofList l) (hmem : (Q.init, Sum.inr tI0, S') ∈ l) (hgoal : Q.goal ⊆ S')
    (hbnd : 2 * (l.length + 1) ≤ bound) : (problem' D Q vars bound tI0).Solvable := by
  obtain ⟨m, k, P, ⟨cells, Xmem, Xtup, hcard, hcells, hIMS, hXtup, hint⟩, hm, hk, -, happ,
    -, hfin⟩ :=
    exists_listSchedule (D := D) (vars := vars) (bound := bound) hvars hdisj hbin
      (hl.cons_of_mem hmem) 0 (by simp) (by simpa using hbnd) _
      (clean_init (vars := vars) Q tI0)
  obtain ⟨hrep0, hrep2, htask⟩ := hfin _ l rfl
  have hXmem : (domain D vars bound).GridYield
      (List.replicate m [Sum.inr (AcTask.MEM : AcTask F A C)]) Xmem := by
    have h := gridYield_of_interleaveMS (D := D) (vars := vars) (bound := bound)
      isSeqTask_MEM (by simpa using hIMS) hcells
    rwa [hcard] at h
  refine Problem.solvable_iff_netYield.2 ⟨P, ?_, happ, ?_⟩
  · refine (netYield_tnI_iff (D := D) (vars := vars) (bound := bound) (Q := Q) (tI0 := tI0)).2
      ⟨m, k, Xmem, Xtup, ?_, ?_, hXmem, hXtup, hint⟩
    · simp only [List.length_cons] at hm; omega
    · simp only [List.length_cons] at hk; omega
  · rintro f (((⟨v, hv, rfl⟩ | ⟨v, ⟨hv, hnv⟩, rfl⟩) | ⟨v, hv, rfl⟩) | rfl)
    · exact (hrep0 v (hvars v)).1.2 hv
    · exact (hrep0 v (hvars v)).2.2 hnv
    · exact (hrep2 v (hvars v)).1.2 (hgoal hv)
    · exact htask

/-- The number of proof tuples of a finite signature — the length of a duplicate-free proof
list, and hence, up to the factor `2`, the number of memory cells the compiled problem needs. -/
def tripleCount (F A C : Type) [Fintype F] [Fintype A] [Fintype C] : ℕ :=
  2 ^ Fintype.card F * ((Fintype.card A + Fintype.card C) * 2 ^ Fintype.card F)

/-- **The number of memory cells that always suffices**: twice the number of proof tuples of
the signature, plus two.  It is exponential in the source signature — but only exponential, so
its logarithm, which is what the size of the compiled domain depends on, is polynomial. -/
def cellCount (F A C : Type) [Fintype F] [Fintype A] [Fintype C] : ℕ :=
  2 * (tripleCount F A C + 1)

open scoped Classical in
/-- **Completeness of the compilation, with a bound depending only on the signature.**  If the
proof-tuple calculus derives `(s₀, t_I, S')` and `S'` satisfies the goal, then the compiled
problem is solvable as soon as it offers `HTN.ToAc.cellCount F A C` memory cells and proof
steps. -/
theorem solvable_problem'_of_provable_cellCount [Fintype F] [Fintype A] [Fintype C]
    (hvars : ∀ v : F, v ∈ vars) (hdisj : ∀ o : A, Disjoint (D.add o) (D.del o))
    (hbin : ∀ (c : C) (xs : List (A ⊕ C)), D.SeqBody c xs → ∃ x y, xs = [x, y])
    {Q : Instance F A C I} {tI0 : C} {S' : Set F}
    (hprov : D.Provable Q.init (Sum.inr tI0) S') (hgoal : Q.goal ⊆ S')
    (hbnd : cellCount F A C ≤ bound) : (problem' D Q vars bound tI0).Solvable := by
  obtain ⟨l, hl, hmem, hlen⟩ := Domain.exists_proofList_length_le hprov
  refine solvable_problem'_of_proofList hvars hdisj hbin hl hmem hgoal ?_
  have h : 2 * (l.length + 1) ≤ cellCount F A C := by
    unfold cellCount tripleCount
    omega
  omega

end ToAc

end HTN
