import HtnComplexity.TMEnc.TMEncHead
/-!
# The budget of the cell counters — and why the printed construction has no solution

Every produced tape cell of the Turing-machine encoding asks the `K + 1` cell counters for one
synchronisation step each: the body of `produce` is
`(assert c, acquire head, C^{K+1} acquire check, C^{K+1} acquire sync)`.  Conversely each cell
counter answers one such request per cell it runs through, its answers being the `release check`
tasks of its expansion.  By the handshake counting theorem of
`HtnComplexity/TMEnc/TMEncCount.lean` the two numbers must agree in every solution plan:
`#call check = #start check`.

This file computes both numbers, with one integer weight (`HTN.TMEnc.wChk`, the difference
"answers − requests" of the channel `check`), and finds that they **cannot** agree:

* the tape consists of `(K+1)²` cells (`HTN.TMEnc.countP_assert_eq_sq`), so it asks
  `(K+1)³` times;
* a single cell counter — the expansion of `checkers 1`, namely
  `(release check, check, C^K transitionAndCheck, release sync)` — answers `(K+1)² + 1` times.
  It contains `K + 1` `check` tasks, each of which compares a cell with the cell `K + 1`
  positions later, i.e. one comparison for each of `K + 1` steps of the machine — but the
  witness `W = #w₀#w₁…#w_K` only has `K` such steps.  The counter therefore runs `(K+1)² + 1`
  cells, one more than the whole tape has, and its last `check` tests a cell `K + 1` positions
  behind the end of the last tape.  Padding never removes answers, so the `K + 1` counters of
  `checkers (K+1)` answer at least `(K+1)·((K+1)² + 1)` times
  (`HTN.TMEnc.le_checkersCount`).

Hence **`HTN.TMEnc.not_solvable`**: the encoded problem has no solution plan at all, for every
machine, every nonempty input fitting into the time bound and every `K`.  In particular
`HTN.TMEnc.EncodingComplete` is false for the construction as printed, and so is
`HTN.EncodingCorrect` for every machine that accepts some input.

The repair is local and is discussed in `NOTES.md`: dropping the leading `check` task of
`checkers 1`, i.e. `checkers 1 → (release check, C^K transitionAndCheck, release sync)`, makes
every counter answer exactly `K·(K+1) + 1` times, which together with the `K` padding waits that
`checkers (K+1)` puts around it is exactly one answer per tape cell, and all three channels
balance.  This file does not carry out that repair; it records precisely what has to be
repaired.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

private lemma sync_ne_check : ¬ (SyncKind.sync = SyncKind.check) := by decide

/-! ### The number of answers of a bank of cell counters -/

/-- The number of `release check` tasks in the full expansion of `checkers i`: one counter
answers `(K+1)² + 1` times, and the recursive splitting of `checkers i` adds the padding
`wait` tasks that keep the counters aligned. -/
def checkersCount (K : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => ((K + 1) ^ 2 : ℤ) + 1
  | (i + 2) =>
      if (i + 2) % 2 = 0 then
        2 * (((i + 2) / 2 : ℕ) : ℤ) * (((i + 2) / 2 : ℕ) : ℤ) +
          2 * checkersCount K ((i + 2) / 2)
      else ((i + 1 : ℕ) : ℤ) * 2 + checkersCount K (i + 1) + (((K + 1) ^ 2 : ℤ) + 1)
  decreasing_by
    · omega
    · omega

lemma checkersCount_of_two_le {K i : ℕ} (hi : 2 ≤ i) :
    checkersCount K i =
      if i % 2 = 0 then 2 * ((i / 2 : ℕ) : ℤ) * ((i / 2 : ℕ) : ℤ) + 2 * checkersCount K (i / 2)
      else ((i - 1 : ℕ) : ℤ) * 2 + checkersCount K (i - 1) + (((K + 1) ^ 2 : ℤ) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [checkersCount]
  have hj : j + 2 - 1 = j + 1 := by omega
  rw [hj]

/-- **A bank of `i` cell counters answers at least `i·((K+1)² + 1)` times.** -/
lemma le_checkersCount (K : ℕ) : ∀ i : ℕ, (i : ℤ) * (((K + 1) ^ 2 : ℤ) + 1) ≤ checkersCount K i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      match i with
      | 0 => simp [checkersCount]
      | 1 => simp [checkersCount]
      | (j + 2) =>
          have hi : 2 ≤ j + 2 := by omega
          rw [checkersCount_of_two_le hi]
          by_cases hpar : (j + 2) % 2 = 0
          · rw [if_pos hpar]
            have hlt : (j + 2) / 2 < j + 2 := by omega
            have hhalf := ih ((j + 2) / 2) hlt
            have hcast : (((j + 2) / 2 : ℕ) : ℤ) * 2 = ((j + 2 : ℕ) : ℤ) := by
              exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : (j + 2) / 2 * 2 = j + 2)
            have hpos : (0 : ℤ) ≤ (((j + 2) / 2 : ℕ) : ℤ) := by positivity
            nlinarith [hhalf, hcast, hpos]
          · rw [if_neg hpar]
            have hlt : j + 1 < j + 2 := by omega
            have hprev := ih (j + 1) hlt
            have hsub : (j + 2 - 1 : ℕ) = j + 1 := by omega
            rw [hsub]
            have hcast : ((j + 2 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
            rw [hcast]
            have hpos : (0 : ℤ) ≤ ((j + 1 : ℕ) : ℤ) := by positivity
            nlinarith

/-! ### The weight: answers minus requests on the channel `check` -/

/-- The number of answers minus the number of requests of the channel `check` in the full
expansion of a compound task. -/
def chkBal (w : List Γ) (K : ℕ) : TMTask Q Γ → ℤ
  | .acquire x => if x = SyncKind.check then -1 else 0
  | .release x => if x = SyncKind.check then 1 else 0
  | .produce => -((K : ℤ) + 1)
  | .produceSym _ => -((K : ℤ) + 1)
  | .tapeProduce => -(((K : ℤ) + 1) * ((K : ℤ) + 1))
  | .waitCell => 1
  | .waitN i => (i : ℤ)
  | .chk => (K : ℤ) + 1
  | .headCell => 0
  | .noHeadCell => 0
  | .heads => 0
  | .transition => 0
  | .transitionAndCheck => (K : ℤ) + 1
  | .checkers i => checkersCount K i
  | .produceInit =>
      -((K : ℤ) + 1) * ((1 + max w.length 1 + (K - w.length) : ℕ) : ℤ)
  | .produceWord i => -((K : ℤ) + 1) * ((max (w.length - i) 1 : ℕ) : ℤ)
  | .done => 0
  | .cSeq t k => (k : ℤ) * chkBal w K t
  | .cPar t k => (k : ℤ) * chkBal w K t
  | .sI => checkersCount K (K + 1) -
      ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ)

/-- The weight counting the answers minus the requests of the channel `check`. -/
def wChk (w : List Γ) (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => (if isStart SyncKind.check a then 1 else 0) -
      (if isCall SyncKind.check a then 1 else 0)
  | Sum.inr t => chkBal w K t

lemma sum_wChk_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wChk w K)).sum = wChk w K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wChk, chkBal, isStart, isCall]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wChk, chkBal, isStart, isCall]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wChk, chkBal, isStart, isCall]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal, isStart, isCall]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp only [wChk, chkBal, isStart, isCall, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num [sync_ne_check]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal, isStart, isCall]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal, isStart, isCall]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wChk, chkBal]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wChk, chkBal, isStart, isCall, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wChk, chkBal, isStart, isCall]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wChk, chkBal, checkersCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wChk, chkBal, checkersCount, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil]
        norm_num [sync_ne_check]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hi : 2 ≤ i := by omega
        rw [wChk, chkBal, checkersCount_of_two_le hi, if_pos he]
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hi : 2 ≤ i := by omega
        rw [wChk, chkBal, checkersCount_of_two_le hi, if_neg he]
        have h1' : checkersCount K 1 = ((K : ℤ) + 1) ^ 2 + 1 := by
          simp [checkersCount]
        simp only [wChk, chkBal, h1', List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        ring
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wChk, chkBal, Nat.sub_zero, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      push_cast
      ring
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls with hlt
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 + max (w.length - (i + 1)) 1 = max (w.length - i) 1 := by omega
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have : ((max (w.length - i) 1 : ℕ) : ℤ) =
            1 + ((max (w.length - (i + 1)) 1 : ℕ) : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
        rw [this]
        ring
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : (1 : ℕ) = max (w.length - i) 1 := by omega
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have : ((max (w.length - i) 1 : ℕ) : ℤ) = 1 := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
        rw [this]
        ring
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wChk, chkBal, isStart, isCall]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wChk, chkBal]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wChk, chkBal]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
        have hx : ((k / 2 : ℕ) : ℤ) * chkBal w K u + ((k / 2 : ℕ) : ℤ) * chkBal w K u
            = (k : ℤ) * chkBal w K u := by
          rw [← hhalf]; ring
        linarith [hx]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
          have : 1 ≤ k := by omega
          push_cast [this]
          ring
        rw [hk1]
        ring
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wChk, chkBal]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wChk, chkBal]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
        have hx : ((k / 2 : ℕ) : ℤ) * chkBal w K u + ((k / 2 : ℕ) : ℤ) * chkBal w K u
            = (k : ℤ) * chkBal w K u := by
          rw [← hhalf]; ring
        linarith [hx]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        simp only [wChk, chkBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
          have : 1 ≤ k := by omega
          push_cast [this]
          ring
        rw [hk1]
        ring
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The balance weight of the channel `check` is balanced.** -/
lemma balanced_wChk : Balanced (methods N w K) (wChk (Q := Q) (Γ := Γ) w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wChk_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wChk, chkBal, isStart, isCall]
    ring

lemma sum_map_wChk (as : List (TMAct Q Γ)) :
    (as.map fun a => wChk (Q := Q) (Γ := Γ) w K (Sum.inl a)).sum =
      (as.countP (isStart SyncKind.check) : ℤ) - (as.countP (isCall SyncKind.check) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      by_cases h₁ : isStart SyncKind.check a = true <;>
        by_cases h₂ : isCall SyncKind.check a = true <;>
        simp [wChk, h₁, h₂] <;> ring

/-- **The cell counters answer more often than the tape asks.**  Every refinement of the initial
task network contains `checkersCount K (K+1) − (K+1)·(K+1)²` more `start check` actions than
`call check` actions — a number which is at least `K + 1`, hence positive. -/
theorem countP_startCheck_sub_callCheck {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    (as.countP (isStart SyncKind.check) : ℤ) - (as.countP (isCall SyncKind.check) : ℤ) =
      checkersCount K (K + 1) -
        ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ) := by
  have hw := weight_of_netYield (balanced_wChk (N := N) (w := w) (K := K)) h
  rw [sum_map_wChk, weight_tnI] at hw
  simpa [wChk, chkBal] using hw

/-- **The encoded problem has no solution plan.**  The `K + 1` cell counters of the construction
answer at least `(K+1)·((K+1)² + 1)` synchronisation requests of the channel `check`, while the
`(K+1)²` cells of the tape only issue `(K+1)³` of them; since a solution plan must issue exactly
as many as it answers, there is no solution plan.

This is a statement about the construction *as printed in the source*; see the file header and
`NOTES.md` for the repair. -/
theorem not_isSolutionPlan (hw0 : w ≠ []) (hwK : w.length ≤ K) (as : List (TMAct Q Γ)) :
    ¬ (problem N w K).IsSolutionPlan as := by
  intro h
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨h₁, h₂, h₃⟩ :=
    countP_sync_eq_of_isSolutionPlan' SyncKind.check (by simp) h
  have heq : (as.countP (isStart SyncKind.check) : ℤ) = (as.countP (isCall SyncKind.check) : ℤ) := by
    have : as.countP (isCall SyncKind.check) = as.countP (isStart SyncKind.check) := by
      omega
    exact_mod_cast this.symm
  have hbal := countP_startCheck_sub_callCheck (N := N) (w := w) (K := K) hy
  rw [heq] at hbal
  simp only [sub_self] at hbal
  -- the balance is at least `K + 1`, so it cannot be zero
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  have hA : (1 + max w.length 1 + (K - w.length)) + K * (1 + K) = (K + 1) ^ 2 := by
    have : max w.length 1 = w.length := by omega
    rw [this]
    ring_nf
    omega
  rw [hA] at hbal
  have hlow := le_checkersCount K (K + 1)
  have hcast : (((K + 1) ^ 2 : ℕ) : ℤ) = ((K : ℤ) + 1) ^ 2 := by push_cast; ring
  rw [hcast] at hbal
  have hk1 : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
  rw [hk1] at hlow
  nlinarith [hlow, hbal]

/-- **The encoded problem is unsolvable**, for every machine, every nonempty input that fits
into the time bound, and every `K`. -/
theorem not_solvable (hw0 : w ≠ []) (hwK : w.length ≤ K) : ¬ (problem N w K).Solvable := by
  intro h
  obtain ⟨as, hplan⟩ := Problem.solvable_iff_exists_solutionPlan.1 h
  exact not_isSolutionPlan hw0 hwK as hplan

/-- **The construction as printed is not complete.**  If the machine accepts its nonempty input
within the time bound, the encoded problem is nevertheless unsolvable. -/
theorem not_encodingComplete (hw0 : w ≠ []) (hwK : w.length ≤ K)
    (hacc : N.AcceptsWithin w K) : ¬ EncodingComplete N w K := fun h =>
  not_solvable hw0 hwK (h hacc)

/-- **The construction as printed is not simulation correct.**  For a machine that accepts some
nonempty input within its exponential time bound, the property `HTN.EncodingCorrect` — the
hypothesis under which the non-compilability theorem of
`HtnCompilability/TMEnc/NonCompilability.lean` is stated — fails. -/
theorem not_encodingCorrect {p : Polynomial ℕ} (hw0 : w ≠ [])
    (hwK : w.length ≤ 2 ^ p.eval w.length) (hacc : N.AcceptsExp p w) :
    ¬ EncodingCorrect N p := fun h => not_solvable hw0 hwK ((h w).2 hacc)

/-! ### The budget of the repaired counters

The defect found above is that `checkers 1` performs `K + 1` comparisons `check` while the
witness has only `K` tape-to-tape steps.  Dropping the leading `check`, i.e.

    checkers 1 → (release check, C^K transitionAndCheck, release sync)

— and leaving everything else as printed — repairs the budget: the following two results verify
that with that body every one of the `K + 1` counters answers exactly once per tape cell.  They
speak about the counting only; the repaired construction itself is *not* formalised here (see
`NOTES.md`). -/

/-- The number of `release check` tasks generated by `checkers i` if the leading `check` task of
`checkers 1` is dropped; the two recursive rules are the ones of the source. -/
def checkersCountFixed (K : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => (K : ℤ) * ((K : ℤ) + 1) + 1
  | (i + 2) =>
      if (i + 2) % 2 = 0 then
        2 * (((i + 2) / 2 : ℕ) : ℤ) * (((i + 2) / 2 : ℕ) : ℤ) +
          2 * checkersCountFixed K ((i + 2) / 2)
      else ((i + 1 : ℕ) : ℤ) * 2 + checkersCountFixed K (i + 1) + ((K : ℤ) * ((K : ℤ) + 1) + 1)
  decreasing_by
    · omega
    · omega

lemma checkersCountFixed_of_two_le {K i : ℕ} (hi : 2 ≤ i) :
    checkersCountFixed K i =
      if i % 2 = 0 then
        2 * ((i / 2 : ℕ) : ℤ) * ((i / 2 : ℕ) : ℤ) + 2 * checkersCountFixed K (i / 2)
      else ((i - 1 : ℕ) : ℤ) * 2 + checkersCountFixed K (i - 1) + ((K : ℤ) * ((K : ℤ) + 1) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
  rw [checkersCountFixed]
  have hj : j + 2 - 1 = j + 1 := by omega
  rw [hj]

/-- **Each of the `i` repaired counters runs through exactly `K·(K+1) + i` cells.** -/
theorem checkersCountFixed_eq (K : ℕ) :
    ∀ i : ℕ, checkersCountFixed K i = (i : ℤ) * ((K : ℤ) * ((K : ℤ) + 1) + (i : ℤ)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      match i with
      | 0 => simp [checkersCountFixed]
      | 1 => simp [checkersCountFixed]
      | (j + 2) =>
          rw [checkersCountFixed_of_two_le (by omega : 2 ≤ j + 2)]
          have hsub : (j + 2 - 1 : ℕ) = j + 1 := by omega
          rw [hsub]
          by_cases hpar : (j + 2) % 2 = 0
          · rw [if_pos hpar, ih ((j + 2) / 2) (by omega)]
            have hcast : (((j + 2) / 2 : ℕ) : ℤ) * 2 = ((j + 2 : ℕ) : ℤ) := by
              exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : (j + 2) / 2 * 2 = j + 2)
            rw [← hcast]
            ring
          · rw [if_neg hpar, ih (j + 1) (by omega)]
            push_cast
            ring

/-- **With the repaired `checkers 1` the channel `check` balances exactly**: the `K + 1`
counters answer `(K+1)²·(K+1)` times, which is exactly once for each of the `K + 1`
synchronisation requests of each of the `(K+1)²` tape cells (`HTN.TMEnc.countP_assert_eq_sq`).
The same count is the number of `release sync` tasks, so the channel `sync` balances as
well. -/
theorem checkersCountFixed_succ (K : ℕ) :
    checkersCountFixed K (K + 1) = (((K : ℤ) + 1) ^ 2) * ((K : ℤ) + 1) := by
  rw [checkersCountFixed_eq]
  push_cast
  ring

end TMEnc

end HTN
