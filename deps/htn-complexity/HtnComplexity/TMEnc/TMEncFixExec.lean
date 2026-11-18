import HtnComplexity.TMEnc.TMEncFixExecBasic
/-!
# The plan of a witness is executable

This file proves the last missing half of the simulation correctness of the repaired encoding of
Theorem 4.3.7: the plan that `HtnComplexity/TMEnc/TMEncFixPlan.lean` builds from a witness is
executable in the initial state, so the encoded problem is solvable.

The proof is one induction over the `(K+1)²` cells of the plan, with the invariant

`the state at the beginning of the cell n contains
   st (the state of the machine at that point)`

(`HTN.TMEnc.PlanData.cellStart`) — in the repaired construction nothing of the head channel
crosses the boundary between two cells.  Inside a cell the argument is the protocol of the
construction: the tape writes the symbol and issues its request on the `head` channel, which the
head counter answers on the spot with the unit of that cell; then the `K + 1` counters answer on
the `check` channel — the one whose decision cell it is applies the transition of the machine or
tests that the head is elsewhere, each extra request of the transition again carrying its own
unit — and then they answer on the `sync` channel.
-/

namespace HTN

namespace TMEnc

open TM ActionModel

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

namespace PlanData

variable (D : PlanData Q Γ) (K)

/-- The index of the state of the machine at the beginning of the cell `n`: the number of
transitions the counters have taken before it. -/
def stIdx (n : ℕ) : ℕ :=
  min (n / (K + 1)) K +
    (if n / (K + 1) < K ∧ D.hd (n / (K + 1)) + 1 < n % (K + 1) then 1 else 0)

/-- Whether the head of the machine is at the cell `n`. -/
def headB (n : ℕ) : Bool := decide (n % (K + 1) = D.hd (n / (K + 1)) + 1)

/-- **The state at the beginning of the cell `n` of the plan.**

In the repaired construction the unit of the head counter that a cell runs sits inside the very
request of that cell, so nothing of the head channel crosses the boundary between two cells: the
whole invariant of the induction is the state of the machine. -/
def cellStart (n : ℕ) : Set (TMFact Q Γ) := {TMFact.st (D.st (D.stIdx K n))}

/-- The data of a plan that comes from an accepting run of the machine: a witness, its
transitions, and the two assumptions on the head movement that the construction needs. -/
structure Valid (D : PlanData Q Γ) (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop where
  /-- The space–time diagram is a witness of an accepting run. -/
  wit : IsWitness N w K D.sym D.st D.hd
  /-- The input is not empty. -/
  hw : 1 ≤ w.length
  /-- The input fits on the tape. -/
  hwK : w.length ≤ K
  /-- The time bound is positive. -/
  hK : 1 ≤ K
  /-- The symbol the transition of the block `i` reads. -/
  symIn : ∀ i < K, D.sym i (D.hd i + 1) = some (D.cIn i)
  /-- The symbol it writes. -/
  symOut : ∀ i < K, D.sym (i + 1) (D.hd i + 1) = some (D.cOut i)
  /-- It is a transition of the machine. -/
  step : ∀ i < K, (D.st (i + 1), D.cOut i, D.mv i) ∈ N.step (D.st i) (D.cIn i)
  /-- It moves the head as it says. -/
  move : ∀ i < K, D.hd (i + 1) = (D.mv i).apply (D.hd i)
  /-- The head never moves left from the first cell. -/
  bump : ∀ i < K, D.mv i = Move.left → 1 ≤ D.hd i

end PlanData

/-! ### The bookkeeping of the invariant -/

section Arith

variable (D : PlanData Q Γ) (K : ℕ)

lemma headBase_succ (n : ℕ) :
    headBase K D.hd D.mv (n + 1) = headBase K D.hd D.mv n + extraCnt K D.hd D.mv n + 1 := by
  unfold headBase headCnt
  rw [Finset.sum_range_succ]
  omega

lemma extraCnt_cell {t c : ℕ} (hc : c < K + 1) :
    extraCnt K D.hd D.mv (t * (K + 1) + c) =
      if t < K ∧ c = D.hd t + 1 then moveExtra (D.mv t) else 0 := by
  obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t) hc
  unfold extraCnt
  rw [hdiv, hmod]

lemma stIdx_cell {t c : ℕ} (ht : t ≤ K) (hc : c < K + 1) :
    D.stIdx K (t * (K + 1) + c) = t + (if t < K ∧ D.hd t + 1 < c then 1 else 0) := by
  obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t) hc
  unfold PlanData.stIdx
  rw [hdiv, hmod, min_eq_left ht]

lemma headB_cell {t c : ℕ} (hc : c < K + 1) :
    D.headB K (t * (K + 1) + c) = decide (c = D.hd t + 1) := by
  obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t) hc
  unfold PlanData.headB
  rw [hdiv, hmod]

lemma stIdx_succ_cell (hdlt : ∀ i ≤ K, D.hd i < K) {t c : ℕ} (ht : t ≤ K) (hc : c < K + 1) :
    D.stIdx K (t * (K + 1) + c + 1) = t + (if t < K ∧ D.hd t + 1 ≤ c then 1 else 0) := by
  rcases Nat.lt_or_ge (c + 1) (K + 1) with hlt | hge
  · have heq : t * (K + 1) + c + 1 = t * (K + 1) + (c + 1) := by ring
    rw [heq, stIdx_cell D K ht hlt]
    by_cases hcase : t < K ∧ D.hd t + 1 ≤ c
    · rw [if_pos ⟨hcase.1, by omega⟩, if_pos hcase]
    · rw [if_neg (by omega), if_neg hcase]
  · have hcK : c = K := by omega
    rw [hcK]
    have heq : t * (K + 1) + K + 1 = (t + 1) * (K + 1) + 0 := by ring
    rw [heq]
    by_cases htK : t < K
    · have hhd : D.hd t < K := hdlt t (by omega)
      rw [stIdx_cell D K (by omega) (by omega), if_neg (by omega), if_pos ⟨htK, by omega⟩]
    · have htK' : t = K := by omega
      unfold PlanData.stIdx
      obtain ⟨hdiv, hmod⟩ := div_mod_cell (K := K) (t := t + 1) (j := 0) (by omega)
      rw [hdiv, hmod, min_eq_right (by omega), if_neg (by omega), if_neg (by omega)]
      omega

end Arith

/-! ### The shape of the check phase of a counter in a cell -/

section Shape

variable (D : PlanData Q Γ) (K : ℕ)

lemma AZ_eq_relCheck {j n : ℕ} (hj : j < K + 1) (hne : j ≠ n % (K + 1)) :
    D.AZ K j n = relCheckActs Q Γ := by
  unfold PlanData.AZ staggeredSegA
  split_ifs with h1 h2
  · rfl
  · have hmod : (n - j) % (K + 1) ≠ 0 := by
      intro hz
      obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hz
      have hq' : n - j = q * (K + 1) := by rw [hq, Nat.mul_comm]
      have hn : n = q * (K + 1) + j := by omega
      exact hne (by rw [hn, (div_mod_cell (K := K) (t := q) hj).2])
    simp [counterSegAZ, hmod]
  · rfl

lemma AZ_eq_due {t c : ℕ} (hc : c < K + 1) (ht : t ≤ K) :
    D.AZ K c (t * (K + 1) + c) =
      counterSegAZ Q Γ K (planPZ K D.st D.hd D.cIn D.cOut D.mv c) (planC D.sym c)
        (cellUnitsExtra Q Γ K D.hd D.mv (K * (K + 1) + c)) (t * (K + 1)) := by
  have h2 : t * (K + 1) + c < (K + 1) * (K + 1) - (K + 1 - 1 - c) := by
    have h : t * (K + 1) ≤ K * (K + 1) := Nat.mul_le_mul_right _ ht
    have hK : K * (K + 1) + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  unfold PlanData.AZ staggeredSegA
  rw [if_neg (by omega), if_pos h2, show t * (K + 1) + c - c = t * (K + 1) by omega]

end Shape

/-! ### The rounds of a cell -/

section Rounds

variable (D : PlanData Q Γ) (K : ℕ)

/-- **A round in which the counter only answers the request**: the state does not change. -/
lemma runs_answerRound {T : Set (TMFact Q Γ)} {x : SyncKind}
    (h1 : TMFact.stepF x ∉ T) (h2 : TMFact.steppedF x ∉ T) :
    (am Q Γ).Runs T (TMAct.call x :: ([TMAct.start x, TMAct.respond x] ++ [TMAct.wait x])) T := by
  refine runs_call (U := insert (TMFact.stepF x) T) le_rfl ?_
  refine runs_start (x := x) (Set.mem_insert _ _) (U := T) ?_ ?_
  · intro f hf
    exact ⟨Set.mem_insert_of_mem _ hf, by rintro rfl; exact h1 hf⟩
  refine runs_respond (U := insert (TMFact.steppedF x) T) le_rfl ?_
  refine runs_wait (x := x) (Set.mem_insert _ _) (U := T) ?_ (ActionModel.runs_nil T)
  intro f hf
  exact ⟨Set.mem_insert_of_mem _ hf, by rintro rfl; exact h2 hf⟩

end Rounds

/-! ### The units of the head counter -/

section Units

@[simp] lemma headF_ne_sym {b : Bool} {c : Option Γ} : headF Q Γ b ≠ TMFact.sym c := by
  cases b <;> simp

@[simp] lemma sym_ne_headF {b : Bool} {c : Option Γ} : TMFact.sym c ≠ headF Q Γ b := by
  cases b <;> simp

@[simp] lemma headF_ne_st {b : Bool} {q : Q} : headF Q Γ b ≠ TMFact.st q := by
  cases b <;> simp

@[simp] lemma st_ne_headF {b : Bool} {q : Q} : TMFact.st q ≠ headF Q Γ b := by
  cases b <;> simp

@[simp] lemma headF_ne_stepF {b : Bool} {x : SyncKind} : headF Q Γ b ≠ TMFact.stepF x := by
  cases b <;> simp

@[simp] lemma stepF_ne_headF {b : Bool} {x : SyncKind} : TMFact.stepF x ≠ headF Q Γ b := by
  cases b <;> simp

@[simp] lemma headF_ne_steppedF {b : Bool} {x : SyncKind} : headF Q Γ b ≠ TMFact.steppedF x := by
  cases b <;> simp

@[simp] lemma steppedF_ne_headF {b : Bool} {x : SyncKind} : TMFact.steppedF x ≠ headF Q Γ b := by
  cases b <;> simp

/-- The tracked state inside the decision of a counter: the symbol of the cell, the state of the
machine, the head fact the unit of the cell has just set, and the answer of the `check` channel
that the counter is holding. -/
def decAt (s : Option Γ) (q : Q) (b : Bool) : Set (TMFact Q Γ) :=
  {TMFact.sym s, TMFact.st q, headF Q Γ b, TMFact.steppedF SyncKind.check}

/-- The same, with the head fact dropped: what is left of the decision once it is taken. -/
def decEnd (s : Option Γ) (q : Q) : Set (TMFact Q Γ) :=
  {TMFact.sym s, TMFact.st q, TMFact.steppedF SyncKind.check}

lemma decEnd_subset_decAt {s : Option Γ} {q : Q} {b : Bool} :
    decEnd s q ⊆ decAt (Q := Q) (Γ := Γ) s q b := by
  intro f hf
  simp only [decEnd, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl <;> simp [decAt]

/-- **One extra request of a transition**: the decision issues it and the head counter answers
it with a unit of its own, which the decision then waits for. -/
lemma runs_headStep {s : Option Γ} {q : Q} {b0 b : Bool} :
    (am Q Γ).Runs (decAt s q b0)
      (TMAct.call SyncKind.head :: (headUnitActs Q Γ b ++ [TMAct.wait SyncKind.head]))
      (decAt s q b) := by
  refine runs_call (U := insert (TMFact.stepF SyncKind.head) (decAt s q b0)) le_rfl ?_
  refine runs_headUnit (b := b) (Set.mem_insert _ _)
    (U := insert (TMFact.steppedF SyncKind.head) (decAt s q b)) ?_ ?_
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, decAt] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> cases b0 <;> cases b <;> simp [decAt]
  · refine runs_wait (x := SyncKind.head) (Set.mem_insert _ _) (U := decAt s q b) ?_
      (ActionModel.runs_nil _)
    intro f hf
    refine ⟨Set.mem_insert_of_mem _ hf, ?_⟩
    simp only [decAt, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> cases b <;> simp

/-- **The extra requests of a transition are answered one by one.** -/
lemma runs_extraLoop {s : Option Γ} {q : Q} (base : ℕ) : ∀ m : ℕ,
    (am Q Γ).Runs (decAt s q (headMark K base))
      (roundStream m fun k => TMAct.call SyncKind.head ::
        (headUnitActs Q Γ (headMark K (base + 1 + k)) ++ [TMAct.wait SyncKind.head]))
      (decAt s q (headMark K (base + m))) := by
  intro m
  have h := ActionModel.runs_roundStream (δ := am Q Γ)
    (S := fun k => decAt s q (headMark K (base + k)))
    (seg := fun k => TMAct.call SyncKind.head ::
      (headUnitActs Q Γ (headMark K (base + 1 + k)) ++ [TMAct.wait SyncKind.head])) m ?_
  · simpa using h
  · intro r _
    simp only []
    rw [show base + 1 + r = base + (r + 1) from by omega]
    exact runs_headStep

end Units

/-! ### The decision of the counter that is due in a cell -/

namespace PlanData

variable (D : PlanData Q Γ) (K)

/-- The mark of the unit the cell `n` runs is the head fact of the cell `n`: the unit answers
the request of the very cell it belongs to. -/
lemma headMark_cell (hV : D.Valid N w K) {n : ℕ} (hn : n < (K + 1) * (K + 1)) :
    headMark K (headBase K D.hd D.mv n) = D.headB K n :=
  headMark_headBase hV.wit.headInit hV.wit.headHome hV.wit.headLt hV.move hV.bump hn

/-- Away from the head, the symbol of a cell is the symbol of the cell below it. -/
lemma symNext (hV : D.Valid N w K) {t c : ℕ} (htK : t < K) (hc : c < K + 1)
    (hne : c ≠ D.hd t + 1) : D.sym (t + 1) c = D.sym t c := by
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · rw [hV.wit.sep (t + 1) (by omega), hV.wit.sep t (by omega)]
  · exact hV.wit.copy t htK c hpos (by omega) hne

/-- **The decision of the counter that is due in the cell `t * (K + 1) + c`**, in a block that
still takes a transition: the transition of the machine, with the extra requests of its head
movement, or the test that the head is elsewhere. -/
lemma runs_planPZ (hV : D.Valid N w K) {t c : ℕ} (htK : t < K) (hc : c < K + 1) :
    (am Q Γ).Runs
      (decAt (planSym K D.sym (t * (K + 1) + c)) (D.st (D.stIdx K (t * (K + 1) + c)))
        (D.headB K (t * (K + 1) + c)))
      (planPZ K D.st D.hd D.cIn D.cOut D.mv c t)
      (decEnd (D.sym (t + 1) c) (D.st (D.stIdx K (t * (K + 1) + c + 1)))) := by
  have hn : t * (K + 1) + c < (K + 1) * (K + 1) := by
    have h : t * (K + 1) + (K + 1) ≤ K * (K + 1) + (K + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    have hK : K * (K + 1) + (K + 1) = (K + 1) * (K + 1) := by ring
    omega
  have hsym : planSym K D.sym (t * (K + 1) + c) = D.sym t c := by
    unfold planSym
    rw [(div_mod_cell (K := K) (t := t) hc).1, (div_mod_cell (K := K) (t := t) hc).2]
  have hb := headB_cell D K (t := t) hc
  have hst := stIdx_cell D K (le_of_lt htK) hc
  have hst' := stIdx_succ_cell D K hV.wit.headLt (le_of_lt htK) hc
  have hmark := D.headMark_cell K hV hn
  by_cases hhead : c = D.hd t + 1
  · have hb' : D.headB K (t * (K + 1) + c) = true := by rw [hb, hhead]; simp
    have hst0 : D.stIdx K (t * (K + 1) + c) = t := by rw [hst, if_neg (by omega)]; omega
    have hst1 : D.stIdx K (t * (K + 1) + c + 1) = t + 1 := by
      rw [hst', if_pos ⟨htK, by omega⟩]
    have hextra : extraCnt K D.hd D.mv (t * (K + 1) + c) = moveExtra (D.mv t) := by
      rw [extraCnt_cell D K hc, if_pos ⟨htK, hhead⟩]
    have hin : D.sym t c = some (D.cIn t) := by rw [hhead]; exact hV.symIn t htK
    have hout : D.sym (t + 1) c = some (D.cOut t) := by rw [hhead]; exact hV.symOut t htK
    rw [hsym, hin, hb', hst0, hst1, hout]
    unfold planPZ
    rw [if_pos hhead]
    refine runs_machineStep (by simp [decAt]) (by simp [decAt]) (by simp [decAt])
      (U := decAt (some (D.cOut t)) (D.st (t + 1)) true) ?_ ?_
    · intro f hf
      simp only [decAt, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> simp [decAt]
    · have hloop := runs_extraLoop (K := K) (s := some (D.cOut t)) (q := D.st (t + 1))
        (headBase K D.hd D.mv (t * (K + 1) + c)) (moveExtra (D.mv t))
      rw [hmark, hb'] at hloop
      exact hloop.weaken_post decEnd_subset_decAt
  · have hb' : D.headB K (t * (K + 1) + c) = false := by rw [hb]; simp [hhead]
    have hst0 : D.stIdx K (t * (K + 1) + c + 1) = D.stIdx K (t * (K + 1) + c) := by
      rw [hst, hst']
      split_ifs <;> omega
    have hsym' : D.sym (t + 1) c = D.sym t c := D.symNext K hV htK hc hhead
    rw [hsym, hsym', hst0, hb']
    unfold planPZ
    rw [if_neg hhead]
    exact runs_check (by simp [decAt]) ((ActionModel.runs_nil _).weaken_post decEnd_subset_decAt)

end PlanData

/-! ### The check round of the counter that is due -/

section Due

/-- The tracked state at the beginning of the check phase of a cell: the symbol of the cell is
written and the head counter has reported whether the head is there. -/
def preCell (s : Option Γ) (q : Q) (b : Bool) : Set (TMFact Q Γ) :=
  {TMFact.sym s, TMFact.st q, headF Q Γ b}

/-- The end of the check round of the counter that is due: it compares the symbol of the cell
with the one it remembers, and releases the tape. -/
lemma runs_endDue {s : Option Γ} {q : Q} :
    (am Q Γ).Runs (decEnd s q) [chkAct Q Γ s, TMAct.wait SyncKind.check] {TMFact.st q} := by
  refine runs_check (by simp [decEnd]) ?_
  refine runs_wait (x := SyncKind.check) (by simp [decEnd]) (U := {TMFact.st q}) ?_
    (ActionModel.runs_nil _)
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst hf
  simp [decEnd]

/-- The same, in the last block, where the counter has no symbol left to compare. -/
lemma runs_endDue' {s : Option Γ} {q : Q} :
    (am Q Γ).Runs (decEnd s q) [TMAct.wait SyncKind.check] {TMFact.st q} := by
  refine runs_wait (x := SyncKind.check) (by simp [decEnd]) (U := {TMFact.st q}) ?_
    (ActionModel.runs_nil _)
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst hf
  simp [decEnd]

/-- The frame of the check round of the counter that is due: the tape calls, the counter takes
the `check` channel, does its work, and the tape is released. -/
lemma runs_wrapCheck {s : Option Γ} {q : Q} {b : Bool} {rest : List (TMAct Q Γ)}
    {U : Set (TMFact Q Γ)} (h : (am Q Γ).Runs (decAt s q b) rest U) :
    (am Q Γ).Runs (preCell s q b) (TMAct.call SyncKind.check :: (relCheckActs Q Γ ++ rest)) U := by
  refine runs_call (U := insert (TMFact.stepF SyncKind.check) (preCell s q b)) le_rfl ?_
  simp only [relCheckActs, List.cons_append, List.nil_append]
  refine runs_release (x := SyncKind.check) (Set.mem_insert _ _) (U := decAt s q b) ?_ h
  intro f hf
  simp only [decAt, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> cases b <;>
    simp [preCell, Set.mem_insert_iff, Set.mem_singleton_iff]

end Due

namespace PlanData

variable (D : PlanData Q Γ)

/-- **The check round of the counter that is due in the cell `t * (K + 1) + c`.** -/
lemma runs_dueRound (hV : D.Valid N w K) {t c : ℕ} (ht : t ≤ K) (hc : c < K + 1) :
    (am Q Γ).Runs
      (preCell (planSym K D.sym (t * (K + 1) + c)) (D.st (D.stIdx K (t * (K + 1) + c)))
        (D.headB K (t * (K + 1) + c)))
      (TMAct.call SyncKind.check ::
        (D.AZ K c (t * (K + 1) + c) ++ [TMAct.wait SyncKind.check]))
      (D.cellStart K (t * (K + 1) + c + 1)) := by
  have hsym : planSym K D.sym (t * (K + 1) + c) = D.sym t c := by
    unfold planSym
    rw [(div_mod_cell (K := K) (t := t) hc).1, (div_mod_cell (K := K) (t := t) hc).2]
  have hK0 : ¬ K = 0 := by have := hV.hK; omega
  have hmod : (t * (K + 1)) % (K + 1) = 0 := Nat.mul_mod_left _ _
  have hdiv : (t * (K + 1)) / (K + 1) = t := Nat.mul_div_cancel _ (by omega)
  rw [AZ_eq_due D K hc ht]
  unfold counterSegAZ
  rw [if_neg (by simp [hmod]), if_neg hK0, hdiv]
  by_cases ht0 : t = 0
  · subst ht0
    rw [if_pos rfl, List.append_assoc]
    refine runs_wrapCheck ?_
    rw [List.append_assoc]
    refine (D.runs_planPZ K hV (by omega) hc).trans ?_
    have := runs_endDue (Q := Q) (Γ := Γ) (s := D.sym (0 + 1) c)
      (q := D.st (D.stIdx K (0 * (K + 1) + c + 1)))
    simpa [planC, cellStart] using this
  · rw [if_neg ht0]
    by_cases htK : t < K
    · rw [if_pos htK, List.append_assoc]
      refine runs_wrapCheck ?_
      simp only [List.cons_append, List.append_assoc]
      refine runs_check ?_ ?_
      · have hc' : planC D.sym c (t - 1) = D.sym t c := by
          unfold planC
          congr 1
          omega
        rw [hc', ← hsym]
        simp [decAt]
      refine (D.runs_planPZ K hV htK hc).trans ?_
      have := runs_endDue (Q := Q) (Γ := Γ) (s := D.sym (t + 1) c)
        (q := D.st (D.stIdx K (t * (K + 1) + c + 1)))
      simpa [planC, cellStart] using this
    · have htK' : t = K := by omega
      rw [if_neg htK, List.append_assoc]
      refine runs_wrapCheck ?_
      simp only [List.cons_append]
      have hstIdx : D.stIdx K (t * (K + 1) + c + 1) = D.stIdx K (t * (K + 1) + c) := by
        rw [stIdx_cell D K ht hc, stIdx_succ_cell D K hV.wit.headLt ht hc, if_neg (by omega),
          if_neg (by omega)]
      have hextra : extraCnt K D.hd D.mv (K * (K + 1) + c) = 0 := by
        rw [extraCnt_cell D K hc, if_neg (by omega)]
      refine runs_check ?_ ?_
      · have hc' : planC D.sym c (K - 1) = D.sym t c := by
          unfold planC
          congr 1
          omega
        rw [hc', ← hsym]
        simp [decAt]
      rw [show cellUnitsExtra Q Γ K D.hd D.mv (K * (K + 1) + c) = [] by
        rw [cellUnitsExtra, hextra]; rfl]
      rw [show D.cellStart K (t * (K + 1) + c + 1) =
        {TMFact.st (D.st (D.stIdx K (t * (K + 1) + c)))} by rw [cellStart, hstIdx]]
      simpa using (runs_endDue' (Q := Q) (Γ := Γ)
        (s := planSym K D.sym (t * (K + 1) + c))
        (q := D.st (D.stIdx K (t * (K + 1) + c)))).weaken_pre decEnd_subset_decAt

/-! ### A whole cell of the plan -/

/-- **The check phase of a cell**: the `K + 1` cell counters answer on the `check` channel, the
one whose decision cell it is doing its work in between. -/
lemma runs_checkPhase (hV : D.Valid N w K) {t c : ℕ} (ht : t ≤ K) (hc : c < K + 1) :
    (am Q Γ).Runs
      (preCell (planSym K D.sym (t * (K + 1) + c)) (D.st (D.stIdx K (t * (K + 1) + c)))
        (D.headB K (t * (K + 1) + c)))
      (roundStream (K + 1) fun j =>
        TMAct.call SyncKind.check :: (D.AZ K j (t * (K + 1) + c) ++ [TMAct.wait SyncKind.check]))
      (D.cellStart K (t * (K + 1) + c + 1)) := by
  have hmod : (t * (K + 1) + c) % (K + 1) = c := (div_mod_cell (K := K) (t := t) hc).2
  set P := preCell (planSym K D.sym (t * (K + 1) + c)) (D.st (D.stIdx K (t * (K + 1) + c)))
    (D.headB K (t * (K + 1) + c)) with hP
  set R := D.cellStart K (t * (K + 1) + c + 1) with hR
  have h := ActionModel.runs_roundStream (δ := am Q Γ) (S := fun j => if j ≤ c then P else R)
    (seg := fun j => TMAct.call SyncKind.check ::
      (D.AZ K j (t * (K + 1) + c) ++ [TMAct.wait SyncKind.check])) (K + 1) ?_
  · rw [if_pos (Nat.zero_le _), if_neg (by omega)] at h
    exact h
  · intro j hj
    simp only []
    rcases lt_trichotomy j c with hlt | rfl | hgt
    · rw [if_pos (by omega), if_pos (by omega), AZ_eq_relCheck D K hj (by omega)]
      exact runs_answerRound (by simp [hP, preCell]) (by simp [hP, preCell])
    · rw [if_pos le_rfl, if_neg (by omega), hP, hR]
      exact D.runs_dueRound hV ht hc
    · rw [if_neg (by omega), if_neg (by omega),
        AZ_eq_relCheck D K hj (by omega)]
      exact runs_answerRound (by simp [hR, cellStart]) (by simp [hR, cellStart])

/-- **The sync phase of a cell**: the `K + 1` cell counters answer on the `sync` channel. -/
lemma runs_syncPhase (T : Set (TMFact Q Γ)) (h1 : TMFact.stepF SyncKind.sync ∉ T)
    (h2 : TMFact.steppedF SyncKind.sync ∉ T) :
    (am Q Γ).Runs T
      (roundStream (K + 1) fun _ =>
        TMAct.call SyncKind.sync :: (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync])) T := by
  have h := ActionModel.runs_roundStream (δ := am Q Γ) (S := fun _ => T)
    (seg := fun _ : ℕ => TMAct.call SyncKind.sync ::
      (relSyncActs Q Γ ++ [TMAct.wait SyncKind.sync])) (K + 1) ?_
  · exact h
  · intro j _
    exact runs_answerRound h1 h2

/-- **A cell of the plan.** -/
lemma runs_cell (hV : D.Valid N w K) {n : ℕ} (hn : n + 1 ≤ (K + 1) * (K + 1)) :
    (am Q Γ).Runs (D.cellStart K n) (D.cell K n) (D.cellStart K (n + 1)) := by
  have hc : n % (K + 1) < K + 1 := Nat.mod_lt _ (by omega)
  have ht : n / (K + 1) ≤ K := by
    by_contra hcon
    have : (K + 1) * (K + 1) ≤ n / (K + 1) * (K + 1) := Nat.mul_le_mul_right _ (by omega)
    have hle : n / (K + 1) * (K + 1) ≤ n := Nat.div_mul_le_self _ _
    omega
  have hcell : n / (K + 1) * (K + 1) + n % (K + 1) = n := Nat.div_add_mod' n (K + 1)
  have hmark : headMark K (headBase K D.hd D.mv n) = D.headB K n :=
    D.headMark_cell K hV (by omega)
  unfold cell
  refine runs_assert (U := {TMFact.sym (planSym K D.sym n),
    TMFact.st (D.st (D.stIdx K n))}) ?_ ?_
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨by simp [cellStart], by simp⟩
  simp only [List.cons_append, List.append_assoc]
  refine runs_call (U := insert (TMFact.stepF SyncKind.head)
    {TMFact.sym (planSym K D.sym n), TMFact.st (D.st (D.stIdx K n))}) le_rfl ?_
  rw [cellUnit0, hmark]
  refine runs_headUnit (b := D.headB K n) (Set.mem_insert _ _)
    (U := insert (TMFact.steppedF SyncKind.head)
      (preCell (planSym K D.sym n) (D.st (D.stIdx K n)) (D.headB K n))) ?_ ?_
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, preCell] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp
  simp only [List.nil_append]
  refine runs_wait (x := SyncKind.head) (Set.mem_insert _ _)
    (U := preCell (planSym K D.sym n) (D.st (D.stIdx K n)) (D.headB K n)) ?_ ?_
  · intro f hf
    refine ⟨Set.mem_insert_of_mem _ hf, ?_⟩
    simp only [preCell, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl <;> simp
  have hcheck := D.runs_checkPhase hV (t := n / (K + 1)) (c := n % (K + 1)) ht hc
  rw [hcell] at hcheck
  refine (hcheck.trans ?_)
  exact runs_syncPhase _ (by simp [cellStart]) (by simp [cellStart])

/-- **The plan of a witness is executable.** -/
theorem runs_plan (hV : D.Valid N w K) :
    (am Q Γ).Runs {TMFact.st (D.st 0)} (D.plan K) {TMFact.st (D.st K)} := by
  have hcells := ActionModel.runs_roundStream (δ := am Q Γ) (S := D.cellStart K)
    (seg := D.cell K) ((K + 1) * (K + 1)) fun r hr => D.runs_cell hV (by omega)
  have hstart : D.cellStart K 0 = {TMFact.st (D.st 0)} := by
    unfold cellStart stIdx
    simp
  have hidx : D.stIdx K ((K + 1) * (K + 1)) = K := by
    unfold stIdx
    rw [Nat.mul_div_cancel _ (by omega), min_eq_right (by omega), if_neg (by omega)]
    omega
  have hend : D.cellStart K ((K + 1) * (K + 1)) = {TMFact.st (D.st K)} := by
    unfold cellStart
    rw [hidx]
  rw [hstart, hend] at hcells
  unfold plan
  refine hcells.trans ?_
  refine runs_check (by simp) ?_
  refine (ActionModel.runs_nil _).weaken_post ?_
  intro f hf
  simp only [Set.mem_singleton_iff] at hf
  subst hf
  simp

/-- **The completeness half of the simulation correctness of the repaired encoding**: a witness
of an accepting run of the machine yields a solution of the encoded problem. -/
theorem solvable_of_valid (hV : D.Valid N w K) : (problemFix N w K).Solvable := by
  refine D.solvable_of_plan_seqApplicable K hV.wit hV.hw hV.hwK hV.step hV.move hV.bump ?_
  have h := D.runs_plan hV (N := N) (w := w)
  have hinit : (problemFix N w K).init = {TMFact.st (D.st 0)} := by
    show {TMFact.st N.init} = _
    rw [hV.wit.initState]
  rw [hinit]
  exact (h _ le_rfl).1

end PlanData

/-! ### Completeness of the repaired encoding -/

/-- **The completeness half of the simulation correctness of the repaired encoding.**

A witness of an accepting run, *together with the transitions it takes*, yields a solution of
the encoded problem.  Besides the homing condition of `HTN.TMEnc.IsWitness` (the head returns to
the first tape cell), the construction needs one further tacit assumption of the source: a
transition must not move the head left from the first tape cell.  The head counter of the
construction spends `2` of its units on a left move but the position of the head does not
change there, so the number of units of the counter — which is fixed by `K` — would not match
the run. -/
theorem solvable_of_witness_transitions {sym : ℕ → ℕ → Option Γ} {st : ℕ → Q} {hd : ℕ → ℕ}
    {cIn cOut : ℕ → Γ} {mv : ℕ → Move} (hK : 1 ≤ K) (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (hwit : IsWitness N w K sym st hd)
    (hsymIn : ∀ i < K, sym i (hd i + 1) = some (cIn i))
    (hsymOut : ∀ i < K, sym (i + 1) (hd i + 1) = some (cOut i))
    (hstep : ∀ i < K, (st (i + 1), cOut i, mv i) ∈ N.step (st i) (cIn i))
    (hmove : ∀ i < K, hd (i + 1) = (mv i).apply (hd i))
    (hbump : ∀ i < K, mv i = Move.left → 1 ≤ hd i) :
    (problemFix N w K).Solvable :=
  PlanData.solvable_of_valid ⟨sym, st, hd, cIn, cOut, mv⟩
    { wit := hwit, hw := hw, hwK := hwK, hK := hK, symIn := hsymIn, symOut := hsymOut,
      step := hstep, move := hmove, bump := hbump }

/-- **Completeness of the repaired encoding, for a witness alone.**

The transitions do not have to be given: it is enough that the witness *can* be justified by
transitions that never move the head left from the first tape cell (`m = Move.left → 1 ≤ hd i`
below).  Without that last clause the statement is exactly `HTN.TMEnc.IsWitness.step`. -/
theorem solvable_of_isWitness_bumpFree {sym : ℕ → ℕ → Option Γ} {st : ℕ → Q} {hd : ℕ → ℕ}
    (hK : 1 ≤ K) (hw : 1 ≤ w.length) (hwK : w.length ≤ K) (hwit : IsWitness N w K sym st hd)
    (hstep : ∀ i < K, ∃ c c' : Γ, ∃ m : Move, sym i (hd i + 1) = some c ∧
      sym (i + 1) (hd i + 1) = some c' ∧ (st (i + 1), c', m) ∈ N.step (st i) c ∧
      hd (i + 1) = m.apply (hd i) ∧ (m = Move.left → 1 ≤ hd i)) :
    (problemFix N w K).Solvable := by
  classical
  obtain ⟨c0, -, -, -⟩ := hstep 0 hK
  have H : ∀ i : ℕ, ∃ p : Γ × Γ × Move, i < K →
      (sym i (hd i + 1) = some p.1 ∧ sym (i + 1) (hd i + 1) = some p.2.1 ∧
        (st (i + 1), p.2.1, p.2.2) ∈ N.step (st i) p.1 ∧
        hd (i + 1) = p.2.2.apply (hd i) ∧ (p.2.2 = Move.left → 1 ≤ hd i)) := by
    intro i
    by_cases h : i < K
    · obtain ⟨c, c', m, h1, h2, h3, h4, h5⟩ := hstep i h
      exact ⟨(c, c', m), fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(c0, c0, Move.right), fun hh => absurd hh h⟩
  choose p hp using H
  exact solvable_of_witness_transitions (cIn := fun i => (p i).1) (cOut := fun i => (p i).2.1)
    (mv := fun i => (p i).2.2) hK hw hwK hwit (fun i hi => (hp i hi).1) (fun i hi => (hp i hi).2.1)
    (fun i hi => (hp i hi).2.2.1) (fun i hi => (hp i hi).2.2.2.1)
    (fun i hi => (hp i hi).2.2.2.2)

/-! ### From a run of the machine to a solution -/

/-- One step of the machine that does not move the head left from the first tape cell.  This is
`TM.NTM.Step` with the single extra clause `m = Move.left → 1 ≤ c.head`, which is vacuous unless
the head sits on the first tape cell. -/
def StepBumpFree (N : NTM Q Γ) (c c' : Config Q Γ) : Prop :=
  ∃ q' : Q, ∃ γ' : Γ, ∃ m : Move,
    (q', γ', m) ∈ N.step c.state (c.tape c.head) ∧
      c' = ⟨q', m.apply c.head, Function.update c.tape c.head γ'⟩ ∧
      (m = Move.left → 1 ≤ c.head)

lemma step_of_stepBumpFree {c c' : Config Q Γ} (h : StepBumpFree N c c') : N.Step c c' := by
  obtain ⟨q', γ', m, hmem, heq, -⟩ := h
  exact ⟨q', γ', m, hmem, heq⟩

/-- **A homing accepting run of exactly `K` steps whose transitions never move the head left
from the first tape cell.**  This is `HTN.TMEnc.HomingRun` with the extra clause of
`HTN.TMEnc.StepBumpFree`. -/
def HomingRunBumpFree (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  ∃ hist : ℕ → Config Q Γ, hist 0 = N.initConfig w ∧
    (∀ i < K, StepBumpFree N (hist i) (hist (i + 1))) ∧ (hist K).state ∈ N.accept ∧
      (hist K).head = 0

lemma isHistory_of_homingRunBumpFree {hist : ℕ → Config Q Γ} (h0 : hist 0 = N.initConfig w)
    (hstep : ∀ i < K, StepBumpFree N (hist i) (hist (i + 1)))
    (hacc : (hist K).state ∈ N.accept) : IsHistory N w K hist :=
  ⟨h0, fun i hi => step_of_stepBumpFree (hstep i hi), hacc⟩

/-- **Completeness of the repaired encoding for the runs the construction can write out.**

Together with the homing condition of the source, the assumption on left moves at the first tape
cell is exactly what the head counter of the construction needs; see
`HTN.TMEnc.solvable_of_witness_transitions`. -/
theorem solvable_of_homingRunBumpFree (hK : 1 ≤ K) (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    (h : HomingRunBumpFree N w K) : (problemFix N w K).Solvable := by
  obtain ⟨hist, h0, hstep, hacc, hhome⟩ := h
  have hhist := isHistory_of_homingRunBumpFree h0 hstep hacc
  have hwit := isWitness_of_homingRun (N := N) (w := w) hK hhist hhome
  refine solvable_of_isWitness_bumpFree hK hw hwK hwit ?_
  intro i hi
  obtain ⟨q', γ', m, hmem, heq, hbump⟩ := hstep i hi
  have hhd : (hist i).head < K := hwit.headLt i (by omega)
  refine ⟨(hist i).tape ((hist i).head), γ', m, ?_, ?_, ?_, ?_, hbump⟩
  · simp [runSym, hhd]
  · have : (hist (i + 1)).tape ((hist i).head) = γ' := by rw [heq]; simp
    simp [runSym, hhd, this]
  · rw [heq]
    exact hmem
  · rw [heq]

end TMEnc

end HTN
