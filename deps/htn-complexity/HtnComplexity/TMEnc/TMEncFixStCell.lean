import HtnComplexity.TMEnc.TMEncFixCellRead
import HtnComplexity.TMEnc.TMEncFixStRead
/-!
# The state of the machine along the cells of a solution plan

`HTN.TMEnc.exists_cellCut` cuts a solution plan at the `assert` of the cell `n`.  This file reads
the *state* of the machine off such a cut.

The state after a prefix of the plan is the target state of the last transition executed
(`HTN.TMEnc.lastStQ`), and transitions are the only actions of a plan that change it.  A prefix
that has completed the first `n` cells of the tape contains, by `HTN.TMEnc.parts_eq_cells`,
exactly the first `n` cells of every cell counter, so the *number* of transitions it contains is
a function of `n` alone (`HTN.TMEnc.numTr`).  Since the transitions of a prefix are a prefix of
the transitions of the whole plan, the state at the end of the cell `n` is therefore also a
function of `n` alone:

* `HTN.TMEnc.stAt` — **the state of the machine when the tape has written its first `n` cells**;
* `HTN.TMEnc.stAt_zero` — it starts at the initial state of the machine;
* `HTN.TMEnc.stAt_full` — at the end of the plan it is the accepting state the plan tests for;
* `HTN.TMEnc.stAt_cellChunk` — **what happens to it during the cell `n`**: the actions of the
  counter that is due there are consistent with it, and it is transformed by them.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The cut, together with the split of the prefix -/

/-- **A solution plan, cut at the `assert` of the cell `n` of the tape**, together with the split
of the prefix: this is `HTN.TMEnc.exists_cellCut` with the information about the piece *before*
the cut kept. -/
theorem exists_cellCutSplit (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    ∃ (u m v Hu Hm : List (TMAct Q Γ)) (partsU parts : List (List (TMAct Q Γ))),
      D.as₁ = u ++ TMAct.assert (D.sym n) :: (m ++ v) ∧
        IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) u partsU Hu
          (tapePrefix Q Γ K n D.sym) ∧
        (∀ j, ∀ hj : j < partsU.length,
          partsU[j] = roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))) ∧
        PlanInter parts Hm (cellTail Q Γ K) m ∧ Hm.Sublist (headStream Q Γ K) ∧
        Hu ++ Hm <+: headStream Q Γ K ∧
        parts.length = K + 1 ∧
        ∀ j, ∀ hj : j < parts.length,
          parts[j] = counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n := by
  classical
  obtain ⟨pss, H₁, H₂, W₁, W₂, hass, hH, hW, hp₁, hp₂⟩ :=
    D.planInter.cut (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym)
      (n := n + 1) (by omega))
  obtain ⟨qss, H₁₁, H₁₂, u, m, hpss, hH₁, hW₁, hq₁, hq₂⟩ :=
    hp₁.cut_at (tapePrefix_succ (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) n)
  have hlenq : qss.length = pss.length := by
    have := congrArg List.length hpss
    simpa using this.symm
  have hlenp : pss.length = K + 1 := by
    have := congrArg List.length hass
    rw [D.card] at this
    simpa using this.symm
  have hu : u <+: D.as₁ := by
    refine ⟨TMAct.assert (D.sym n) :: (m ++ W₂), ?_⟩
    rw [hW, hW₁]; simp
  have hW₁pre : W₁ <+: D.as₁ := ⟨W₂, hW.symm⟩
  have hforallp : List.Forall₂ (· <+: ·) (pss.map Prod.fst) D.ass := by
    rw [hass]; exact forall₂_prefix_map_fst pss
  have hforallq : List.Forall₂ (· <+: ·) (qss.map Prod.fst) D.ass := by
    refine forall₂_prefix_trans ?_ hforallp
    rw [hpss]; exact forall₂_prefix_map_fst qss
  have hsplitp : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) W₁ (pss.map Prod.fst) H₁
      (tapePrefix Q Γ K (n + 1) D.sym) :=
    isPlanSplit_of_planInter hp₁ hforallp ⟨H₂, hH.symm⟩
      ⟨_, (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) (n := n + 1)
        (by omega)).symm⟩
  have hsplitq : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) u (qss.map Prod.fst) H₁₁
      (tapePrefix Q Γ K n D.sym) := by
    refine isPlanSplit_of_planInter hq₁ hforallq ?_ ?_
    · exact (List.prefix_append H₁₁ H₁₂).trans (hH₁ ▸ ⟨H₂, hH.symm⟩)
    · exact ⟨_, (tapeStream_split (Q := Q) (Γ := Γ) (K := K) (sym := D.sym) (n := n)
        (by omega)).symm⟩
  have hcellsp := parts_eq_cells D (n := n + 1) (by omega) hW₁pre hsplitp
  have hcellsq := parts_eq_cells D (n := n) (by omega) hu hsplitq
  refine ⟨u, m, W₂, H₁₁, H₁₂, qss.map Prod.fst, qss.map Prod.snd, ?_, hsplitq, hcellsq, hq₂,
    ?_, ?_, ?_, ?_⟩
  · rw [hW, hW₁]; simp
  · refine List.Sublist.trans ?_ (List.IsPrefix.sublist (⟨H₂, hH.symm⟩ : H₁ <+: headStream Q Γ K))
    exact hH₁ ▸ List.sublist_append_right H₁₁ H₁₂
  · exact hH₁ ▸ (⟨H₂, hH.symm⟩ : H₁ <+: headStream Q Γ K)
  · simp [hlenq, hlenp]
  · intro j hj
    have hjq : j < qss.length := by simpa using hj
    have hjp : j < pss.length := by omega
    have hsum : (pss.map Prod.fst)[j]'(by simpa using hjp) =
        (qss.map Prod.fst)[j]'(by simpa using hjq) ++
          (qss.map Prod.snd)[j]'(by simpa using hjq) := by
      have h := congrArg (fun l => l[j]?) hpss
      simp only [List.getElem?_map] at h
      have h1 : qss[j]? = some qss[j] := List.getElem?_eq_getElem hjq
      have h2 : pss[j]? = some pss[j] := List.getElem?_eq_getElem hjp
      rw [h2, h1] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp [List.getElem_map, h]
    have e1 := hcellsq j (by simpa using hjq)
    have e2 := hcellsp j (by simpa using hjp)
    rw [roundStream_succ] at e2
    have key : roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) ++
        counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n =
        roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j)) ++
          (qss.map Prod.snd)[j]'(by simpa using hjq) := by
      rw [← e2, hsum, e1]
    exact (List.append_cancel_left key).symm

/-! ### How many transitions the first `n` cells contain -/

lemma sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-- **The number of transitions that the cell counters take during the first `n` cells.** -/
def numTr (D : SolutionPlanData N w K) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (K + 1),
    (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP stRel

@[simp] lemma numTr_zero (D : SolutionPlanData N w K) : numTr D 0 = 0 := by
  simp [numTr]

/-- Only the counter that is due in the cell `n` can take a transition there. -/
lemma numTr_succ (D : SolutionPlanData N w K) (n : ℕ) :
    numTr D (n + 1) = numTr D n +
      (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).countP stRel := by
  have hsplit : ∀ j, (roundStream (n + 1) (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP
      stRel = (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP stRel +
        (counterCell Q Γ K (D.d j) (D.P j) (D.cc j) n).countP stRel := by
    intro j
    rw [roundStream_succ, List.countP_append]
  simp only [numTr, hsplit, Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_eq_single (due D n) ?_ ?_
  · intro j hj hne
    rw [counterCell_of_ne_due D (Finset.mem_range.1 hj) hne]
    rw [List.countP_eq_length_filter, filter_stRel_waitCellActs]
    rfl
  · intro hmem
    exact absurd (Finset.mem_range.2 (due_lt D n)) hmem

/-- The head counter takes no transition. -/
lemma countP_stRel_headStream_eq_zero : (headStream Q Γ K).countP stRel = 0 := by
  rw [List.countP_eq_length_filter, filter_stRel_headStream]
  rfl

/-- The tape takes no transition. -/
lemma countP_stRel_tapePrefix_eq_zero (n : ℕ) (sym : ℕ → Option Γ) :
    (tapePrefix Q Γ K n sym).countP (stRel (Q := Q)) = 0 := by
  rw [List.countP_eq_length_filter, filter_stRel_tapePrefix]
  rfl

/-- **The number of transitions in a prefix of the plan that has completed the first `n` cells of
the tape is `numTr D n`** — in particular it does not depend on the prefix. -/
lemma countP_stRel_of_split (D : SolutionPlanData N w K) {n : ℕ} {u Hu : List (TMAct Q Γ)}
    {partsU : List (List (TMAct Q Γ))}
    (hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) u partsU Hu
      (tapePrefix Q Γ K n D.sym))
    (hcells : ∀ j, ∀ hj : j < partsU.length,
      partsU[j] = roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))) :
    u.countP stRel = numTr D n := by
  have hlen : partsU.length = K + 1 := parts_length hsplit
  have hHu : Hu.countP (stRel (Q := Q) (Γ := Γ)) = 0 := by
    have hle := hsplit.2.1.sublist.countP_le (p := stRel (Q := Q) (Γ := Γ))
    rw [countP_stRel_headStream_eq_zero] at hle
    omega
  have hmap : (partsU.map fun l => l.countP stRel) =
      (List.range (K + 1)).map fun j =>
        (roundStream n (counterCell Q Γ K (D.d j) (D.P j) (D.cc j))).countP stRel := by
    refine List.ext_getElem (by simp [hlen]) ?_
    intro j hj₁ hj₂
    have hj : j < partsU.length := by simpa using hj₁
    simp only [List.getElem_map, List.getElem_range]
    rw [hcells j hj]
  rw [countP_of_isPlanSplit hsplit stRel, hHu, hmap, sum_map_range,
    countP_stRel_tapePrefix_eq_zero]
  simp [numTr]

/-! ### The state at the end of a cell -/

/-- **The state of the machine when the tape has written its first `n` cells.** -/
def stAt (D : SolutionPlanData N w K) (n : ℕ) : Q :=
  lastStQ N.init ((D.as₁.filter stRel).take (numTr D n))

/-- The state after a prefix of the plan is determined by the number of transitions it
contains. -/
lemma lastStQ_prefix (D : SolutionPlanData N w K) {u : List (TMAct Q Γ)} (hu : u <+: D.as₁) :
    lastStQ N.init u = lastStQ N.init ((D.as₁.filter stRel).take (u.countP stRel)) := by
  have hpre : u.filter stRel <+: D.as₁.filter stRel := List.IsPrefix.filter stRel hu
  have hlen : (u.filter stRel).length = u.countP stRel :=
    List.countP_eq_length_filter.symm
  rw [← lastStQ_filter, ← hlen, ← List.prefix_iff_eq_take.mp hpre]

@[simp] lemma stAt_zero (D : SolutionPlanData N w K) : stAt D 0 = N.init := by
  simp [stAt]

/-- **At the end of the plan the machine is in the accepting state the plan tests for.** -/
theorem stAt_full (D : SolutionPlanData N w K) : stAt D ((K + 1) * (K + 1)) = D.f := by
  have hsplit : IsPlanSplit Q Γ K D.ass (tapeStream Q Γ K D.sym) D.as₁ D.ass
      (headStream Q Γ K) (tapePrefix Q Γ K ((K + 1) * (K + 1)) D.sym) := by
    refine ⟨?_, List.prefix_rfl, List.prefix_rfl, D.ac, D.bs, D.hil, D.hac, D.hbs⟩
    exact List.forall₂_same.2 fun l _ => List.prefix_rfl
  have hcells := parts_eq_cells D (n := (K + 1) * (K + 1)) le_rfl List.prefix_rfl hsplit
  have hcount := countP_stRel_of_split D hsplit hcells
  have happ : (problemFix N w K).SeqApplicable (D.as₁ ++ [TMAct.check (TMFact.st D.f)])
      (problemFix N w K).init := (Problem.isSolutionPlan_iff.1 D.isPlan).2.1
  have hf : D.f = lastStQ N.init D.as₁ :=
    lastStQ_of_check (N := N) (w := w) (K := K) (p := D.as₁) (rest := []) (by simpa using happ)
  rw [stAt, ← hcount, ← lastStQ_prefix D List.prefix_rfl, ← hf]

/-! ### What happens during a cell -/

/-- **The cell `n` of a solution plan, seen from the state**: the actions of the counter that is
due there are consistent with the state `stAt D n` the machine is in when the tape has written
the cell `n`, and they take it to the state `stAt D (n + 1)`. -/
theorem stAt_cellChunk (D : SolutionPlanData N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    StConsistent (stAt D n)
        (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n) ∧
      stAt D (n + 1) = lastStQ (stAt D n)
        (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n) := by
  obtain ⟨u, m, v, Hu, Hm, partsU, parts, heq, hsplit, hcellsU, hpi, hsub, -, hlen, hcells⟩ :=
    exists_cellCutSplit D hn
  -- the actions of the chunk that touch the state are those of the due counter
  have hHm : Hm.filter stRel = [] := by
    have hs := hsub.filter stRel
    rw [filter_stRel_headStream] at hs
    exact List.sublist_nil.1 hs
  have hj : due D n < parts.length := by rw [hlen]; exact due_lt D n
  have hothers : ∀ i, ∀ hi : i < parts.length, i ≠ due D n → (parts[i]).filter stRel = [] := by
    intro i hi hne
    rw [hcells i hi, counterCell_of_ne_due D (by omega) hne, filter_stRel_waitCellActs]
  have hfilter : m.filter stRel =
      (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).filter stRel := by
    rw [hpi.filter_eq_getElem stRel hHm filter_stRel_cellTail hj hothers, hcells _ hj]
  -- the state at the cut
  have hu : u <+: D.as₁ := ⟨TMAct.assert (D.sym n) :: (m ++ v), heq.symm⟩
  have hcountu : u.countP stRel = numTr D n := countP_stRel_of_split D hsplit hcellsU
  have hstu : lastStQ N.init u = stAt D n := by
    rw [lastStQ_prefix D hu, hcountu, stAt]
  -- the state after the chunk
  have hu' : u ++ TMAct.assert (D.sym n) :: m <+: D.as₁ := ⟨v, by rw [heq]; simp⟩
  have hcountm : m.countP stRel =
      (counterCell Q Γ K (D.d (due D n)) (D.P (due D n)) (D.cc (due D n)) n).countP stRel := by
    rw [List.countP_eq_length_filter, hfilter, ← List.countP_eq_length_filter]
  have hcountu' : (u ++ TMAct.assert (D.sym n) :: m).countP stRel = numTr D (n + 1) := by
    rw [List.countP_append, List.countP_cons_of_neg (by simp [stRel]), hcountu, hcountm,
      numTr_succ]
  have hst' : lastStQ N.init (u ++ TMAct.assert (D.sym n) :: m) = stAt D (n + 1) := by
    rw [lastStQ_prefix D hu', hcountu', stAt]
  -- consistency of the chunk
  have happ : (problemFix N w K).SeqApplicable (D.as₁ ++ [TMAct.check (TMFact.st D.f)])
      (problemFix N w K).init := (Problem.isSolutionPlan_iff.1 D.isPlan).2.1
  have hsplit' : D.as₁ ++ [TMAct.check (TMFact.st D.f)] =
      (u ++ [TMAct.assert (D.sym n)]) ++ (m ++ (v ++ [TMAct.check (TMFact.st D.f)])) := by
    rw [heq]; simp
  rw [hsplit'] at happ
  have hcons := stConsistent_of_seqApplicable m (u ++ [TMAct.assert (D.sym n)])
    (v ++ [TMAct.check (TMFact.st D.f)]) happ
  have hlast : lastStQ N.init (u ++ [TMAct.assert (D.sym n)]) = stAt D n := by
    rw [lastStQ_append, hstu]; rfl
  rw [hlast] at hcons
  refine ⟨?_, ?_⟩
  · rw [← stConsistent_filter, ← hfilter, stConsistent_filter]
    exact hcons
  · rw [← hst', lastStQ_append, hstu, lastStQ_cons, ← lastStQ_filter, hfilter, lastStQ_filter]
    rfl

end TMEnc

end HTN
