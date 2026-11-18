import HtnComplexity.TMEnc.TMEncCheck
/-!
# The repaired Turing-machine encoding

`HtnComplexity/TMEnc/TMEncCheck.lean` shows that the translation of Theorem 4.3.7 *as printed in
the source* has no solution at all: the body

    checkers¹ → (release_check, check, C^K_{transitionAndCheck}, release_sync)

makes one cell counter answer `(K+1)² + 1` synchronisation requests of the channel `check`,
while the tape of `(K+1)²` cells issues only `(K+1)²` of them per counter.  The defect is the
leading `check` task: a counter has to compare a cell with the cell `K + 1` positions later
once per *tape-to-tape step* of the machine, and there are `K` of those, while the printed body
performs `K + 1` comparisons.

This file carries out the repair — drop that leading `check`, i.e.

    checkers¹ → (release_check, C^K_{transitionAndCheck}, release_sync)

— and re-establishes for the repaired construction everything that
`HtnComplexity/TMEnc/TMEncoding.lean` proves for the printed one, plus the counting statement
that the printed one fails:

* `HTN.TMEnc.wfFix`, `HTN.TMEnc.isTO_tnIFix`, `HTN.TMEnc.isAcyclicFix` — the repaired problem is
  a well-formed, acyclic HTN planning problem with a totally ordered initial task network, i.e.
  it still lies in `TO-tn_I ∩ ACYC`;
* `HTN.TMEnc.method_card_leFix`, `HTN.TMEnc.method_size_leFix` — its methods are still of
  bounded size, independently of the (exponential) time bound `K`;
* `HTN.TMEnc.countP_start_eq_countP_call_fix` — **the two cell channels balance**: every
  refinement of the initial task network of the repaired problem contains exactly as many
  `start x` as `call x` actions, for `x` either of the two cell channels `check` and `sync`.
  This is precisely the identity whose failure refutes the printed construction, and it is a
  necessary condition for solvability (`HTN.TMEnc.countP_sync_eq_of_isSolutionPlan'`).

The structure of the repaired construction differs from the printed one at the single task
`checkers¹`, so every statement of the form "… for every method body …" is proved here by
transferring the corresponding statement of the printed construction
(`HTN.TMEnc.bodiesFix_eq_or`) and treating that one body separately.  The one exception is the
weight of the channel, which changes at *every* `checkers^i`, and is therefore redone.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

private lemma sync_ne_check' : ¬ (SyncKind.sync = SyncKind.check) := by decide

private lemma check_ne_sync' : ¬ (SyncKind.check = SyncKind.sync) := by decide

/-! ### The repaired construction -/

/-- The repaired body of `checkers¹`: `(release_check, C^K_{transitionAndCheck}, release_sync)`.
The printed body has an additional leading `check` task; see the file header. -/
def checkerBodyFix (K : ℕ) : List (List (TMAct Q Γ ⊕ TMTask Q Γ)) :=
  [[Sum.inr (TMTask.release SyncKind.check), Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K),
    Sum.inr (TMTask.release SyncKind.sync)]]

/-- **The repaired head-counter chain**: `C^K_heads ; noHead ; head ; C^{K-1}_noHead`.

The chain the source prints is `retract_head ; respond_head ; head ; C^K_noHead ; C^K_heads`;
its leading `retract_head` is a toggle of the head fact that answers no request of its own, and
its leading `respond_head` answers the request of the first cell for free.  That free answer is
exactly the one-unit slack that makes the source's construction unsound: the counter may run one
unit ahead of the tape, so a plan may take the transition of a block one cell beside the cell the
head of the machine is on (see `NOTES.md`).

In the repaired chain every toggle consumes a request of its own, so the counter is in lock-step
with the tape (`HTN.TMEnc.headMark_at_decision`).  It runs through the same
`K² + 3K + 1 = (K+1)(K+2) - 1` units — one per request of the tape, the `(K+1)²` cells and the
`K` extra ones of the transitions — but the marks are shifted by one unit: the head is reported
at the units `u` with `u ≡ 1 (mod K + 2)`.  The last cycle is therefore truncated after `K + 1`
of its `K + 2` units. -/
def headChainFix (K : ℕ) : List (TMAct Q Γ ⊕ TMTask Q Γ) :=
  [Sum.inr (TMTask.cSeq TMTask.heads K), Sum.inr TMTask.noHeadCell, Sum.inr TMTask.headCell,
    Sum.inr (TMTask.cSeq TMTask.noHeadCell (K - 1))]

/-- The three parallel chains of the initial task network of the repaired construction: the
repaired head counter (`HTN.TMEnc.headChainFix`), the `K + 1` cell counters and the production
of the tape. -/
def initChainsFix (K : ℕ) : List (List (TMAct Q Γ ⊕ TMTask Q Γ)) :=
  [headChainFix K,
   [Sum.inr (TMTask.checkers (K + 1))],
   [Sum.inr TMTask.produceInit, Sum.inr (TMTask.cSeq TMTask.tapeProduce K)]]

/-- The initial task network of the repaired construction. -/
def initNetFix (K : ℕ) : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ) :=
  TaskNetwork.gridTail (initChainsFix K) [Sum.inr TMTask.done]

/-- The method bodies of the repaired construction: those of `HTN.TMEnc.bodies`, except at
`checkers¹`. -/
def bodiesFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    TMTask Q Γ → Set (List (List (TMAct Q Γ ⊕ TMTask Q Γ)))
  | .checkers i => if i = 1 then {checkerBodyFix K} else bodies N w K (.checkers i)
  | t => bodies N w K t

@[simp] lemma bodiesFix_checkers (i : ℕ) :
    bodiesFix N w K (TMTask.checkers i) =
      if i = 1 then {checkerBodyFix K} else bodies N w K (TMTask.checkers i) := rfl

lemma bodiesFix_checkers_one :
    bodiesFix N w K (TMTask.checkers 1) = {checkerBodyFix (Q := Q) (Γ := Γ) K} := by simp

/-- The bodies of the repaired construction are those of the printed one, except at the single
task `checkers¹`. -/
lemma bodiesFix_eq_or (t : TMTask Q Γ) :
    bodiesFix N w K t = bodies N w K t ∨
      (t = TMTask.checkers 1 ∧ bodiesFix N w K t = {checkerBodyFix (Q := Q) (Γ := Γ) K}) := by
  cases t with
  | checkers i =>
      by_cases hi : i = 1
      · subst hi; exact Or.inr ⟨rfl, bodiesFix_checkers_one⟩
      · exact Or.inl (by simp [hi])
  | _ => exact Or.inl rfl

/-- The methods of the repaired domain. -/
def methodsFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Set (Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)) :=
  {m | ∃ ls ∈ bodiesFix N w K m.abstractTask, m.subtasks = TaskNetwork.grid ls} ∪
    {⟨.sI, initNetFix K⟩}

/-- The repaired HTN planning domain. -/
def domainFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Domain (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  toActionModel := actionModel
  methods := methodsFix N w K

/-- The repaired HTN planning problem.  Only the domain changes; the problem instance is the
one of the printed construction. -/
def problemFix (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Problem (TMFact Q Γ) (TMAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) :=
  (domainFix N w K).mkProblem (instance_ N)

/-! ### Well-formedness, total orderedness, acyclicity -/

lemma methodsFix_wf : ∀ m ∈ methodsFix N w K, m.subtasks.WF := by
  rintro ⟨c, tn⟩ (⟨ls, -, rfl⟩ | hm)
  · exact TaskNetwork.grid_wf
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact TaskNetwork.gridTail_wf

/-- **The repaired problem is well formed.** -/
theorem wfFix : (problemFix N w K).WF where
  tnI := TaskNetwork.seq_wf
  methods := methodsFix_wf

/-- **The initial task network of the repaired problem is totally ordered.** -/
theorem isTO_tnIFix : (problemFix N w K).IsTO_tnI := TaskNetwork.seq_isTotallyOrdered

/-- Every compound task occurring in a body of the repaired construction has a strictly smaller
rank than the task that the method decomposes. -/
lemma rank_lt_of_mem_bodiesFix {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) :
    rank K w.length c < rank K w.length t := by
  rcases bodiesFix_eq_or (N := N) (w := w) (K := K) t with heq | ⟨rfl, heq⟩
  · rw [heq] at hls
    exact rank_lt_of_mem_bodies hls hc
  · rw [heq, Set.mem_singleton_iff] at hls
    subst hls
    simp only [checkerBodyFix, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
    rcases hc with rfl | rfl | rfl <;> simp only [rank] <;> omega

/-- Every compound task of the repaired initial task network has a smaller rank than `sI`. -/
lemma rank_lt_of_mem_initNetFix {c : TMTask Q Γ} {p : ℕ × ℕ}
    (hp : p ∈ (initNetFix (Q := Q) (Γ := Γ) K).T)
    (hc : (initNetFix (Q := Q) (Γ := Γ) K).α p = Sum.inr c) :
    rank K w.length c < rank K w.length (TMTask.sI (Q := Q) (Γ := Γ)) := by
  have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChainsFix (Q := Q) (Γ := Γ) K)
    (tl := [Sum.inr TMTask.done]) hp
  rw [show (initNetFix (Q := Q) (Γ := Γ) K) =
    TaskNetwork.gridTail (initChainsFix (Q := Q) (Γ := Γ) K) [Sum.inr TMTask.done] from rfl] at hc
  rw [hc] at hmem
  simp only [initChainsFix, headChainFix, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    Sum.inr.injEq] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega

/-- **The repaired problem is acyclic**, witnessed by the same rank function as the printed
one. -/
theorem isAcyclicFix : (problemFix N w K).IsAcyclic := by
  refine Problem.isAcyclic_of_rank _ (rank K w.length) ?_
  rintro ⟨ct, tn⟩ ⟨hm, -⟩ t ht c hc
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · subst hsub
    refine rank_lt_of_mem_bodiesFix hls ?_
    have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) ht
    rwa [hc] at hmem
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hsI
    obtain ⟨rfl, rfl⟩ := hsI
    exact rank_lt_of_mem_initNetFix (w := w) ht hc

/-! ### The size of the methods -/

/-- Every body of the repaired construction consists of at most two parallel chains of at most
five tasks each. -/
lemma bodiesFix_small {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) : ls.length ≤ 2 ∧ ∀ l ∈ ls, l.length ≤ 5 := by
  rcases bodiesFix_eq_or (N := N) (w := w) (K := K) t with heq | ⟨rfl, heq⟩
  · rw [heq] at hls
    exact bodies_small hls
  · rw [heq, Set.mem_singleton_iff] at hls
    subst hls
    simp [checkerBodyFix]

/-- **Every method of the repaired domain has at most `20` subtasks.** -/
theorem method_card_leFix {m : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    (hm : m ∈ methodsFix N w K) : m.subtasks.T.card ≤ 20 := by
  obtain ⟨ct, tn⟩ := m
  rcases hm with ⟨ls, hls, rfl⟩ | hsI
  · obtain ⟨h1, h2⟩ := bodiesFix_small hls
    calc (TaskNetwork.grid ls).T.card ≤ ls.length * 5 := TaskNetwork.grid_card_le h2
      _ ≤ 20 := by omega
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hsI
    obtain ⟨rfl, rfl⟩ := hsI
    have h2 : ∀ l ∈ initChainsFix (Q := Q) (Γ := Γ) K, l.length ≤ 5 := by
      intro l hl; simp only [initChainsFix, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [headChainFix]
    have := TaskNetwork.gridTail_card_le (ls := initChainsFix (Q := Q) (Γ := Γ) K)
      (tl := [Sum.inr TMTask.done]) (m := 5) h2 (by simp)
    simpa [initNetFix, initChainsFix, headChainFix] using this

/-- **Every method of the repaired domain has size at most `421`.** -/
theorem method_size_leFix {m : Method (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)}
    (hm : m ∈ methodsFix N w K) : m.size ≤ 421 := by
  have hc := method_card_leFix hm
  have h := m.subtasks.size_le
  have : m.subtasks.T.card * m.subtasks.T.card ≤ 20 * 20 := Nat.mul_le_mul hc hc
  simp only [Method.size]
  omega

/-! ### The balance of the two cell channels

The two cell channels `check` and `sync` are used symmetrically by the construction: every body
contains exactly as many `acquire_check` as `acquire_sync` tasks and exactly as many
`release_check` as `release_sync` tasks.  The weights below are therefore the same function of
the tasks for both channels; only the leaves distinguish them. -/

/-- The number of answers minus the number of requests of a cell channel (`check` or `sync`) in
the full expansion of a compound task, for the **repaired** construction.  It differs from
`HTN.TMEnc.chkBal` at the cell counters, where the repaired `checkers¹` answers
`K·(K+1) + 1` instead of `(K+1)² + 1` times. -/
def cellBal (x : SyncKind) (w : List Γ) (K : ℕ) : TMTask Q Γ → ℤ
  | .acquire y => if y = x then -1 else 0
  | .release y => if y = x then 1 else 0
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
  | .checkers i => checkersCountFixed K i
  | .produceInit =>
      -((K : ℤ) + 1) * ((1 + max w.length 1 + (K - w.length) : ℕ) : ℤ)
  | .produceWord i => -((K : ℤ) + 1) * ((max (w.length - i) 1 : ℕ) : ℤ)
  | .done => 0
  | .cSeq t k => (k : ℤ) * cellBal x w K t
  | .cPar t k => (k : ℤ) * cellBal x w K t
  | .sI => checkersCountFixed K (K + 1) -
      ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ)

/-- The weight counting the answers minus the requests of a cell channel. -/
def wCell (x : SyncKind) (w : List Γ) (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => (if isStart x a then 1 else 0) - (if isCall x a then 1 else 0)
  | Sum.inr t => cellBal x w K t

/-- The bodies of the repaired construction outside the single repaired task. -/
lemma bodiesFix_eq_of_ne {t : TMTask Q Γ} (h : t ≠ TMTask.checkers 1) :
    bodiesFix N w K t = bodies N w K t := by
  rcases bodiesFix_eq_or (N := N) (w := w) (K := K) t with heq | ⟨rfl, -⟩
  · exact heq
  · exact absurd rfl h

/-- **The channel balance is preserved by every method body of the repaired construction.** -/
lemma sum_wCell_bodiesFix (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wCell x w K)).sum = wCell x w K (Sum.inr t) := by
  by_cases ht1 : t = TMTask.checkers 1
  · subst ht1
    rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
    subst hls
    rcases hx with rfl | rfl
    all_goals
      simp only [wCell, cellBal, checkerBodyFix, checkersCountFixed, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      norm_num [sync_ne_check', check_ne_sync']
      try ring
  · rw [bodiesFix_eq_of_ne ht1] at hls
    rcases hx with rfl | rfl
    all_goals
    cases t with
    | acquire y =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        cases y <;> simp [wCell, cellBal, isStart, isCall]
    | release y =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        cases y <;> simp [wCell, cellBal, isStart, isCall]
    | produce =>
        simp only [bodies, Set.mem_setOf_eq] at hls
        obtain ⟨c, rfl⟩ := hls
        simp [wCell, cellBal, isStart, isCall]
    | produceSym c =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal, isStart, isCall]
    | tapeProduce =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        ring
    | waitCell =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal]
    | waitN i =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal]
    | chk =>
        simp only [bodies, Set.mem_setOf_eq] at hls
        obtain ⟨c, rfl⟩ := hls
        simp only [wCell, cellBal, isStart, isCall, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        norm_num [sync_ne_check', check_ne_sync'] <;> ring
    | headCell =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal, isStart, isCall]
    | noHeadCell =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal, isStart, isCall]
    | heads =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp [wCell, cellBal]
    | transition =>
        simp only [bodies, Set.mem_setOf_eq] at hls
        obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
        simp [wCell, cellBal, isStart, isCall, List.map_replicate, List.sum_replicate]
    | transitionAndCheck =>
        simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
        rcases hls with rfl | rfl <;> simp [wCell, cellBal, isStart, isCall]
    | checkers i =>
        have hi1 : i ≠ 1 := by simpa using ht1
        simp only [bodies, if_neg hi1] at hls
        split_ifs at hls with h0 he
        · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
          simp [wCell, cellBal, checkersCountFixed]
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          have hi : 2 ≤ i := by omega
          rw [wCell, cellBal, checkersCountFixed_of_two_le hi, if_pos he]
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil]
          ring
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          have hi : 2 ≤ i := by omega
          rw [wCell, cellBal, checkersCountFixed_of_two_le hi, if_neg he]
          have h1' : checkersCountFixed K 1 = (K : ℤ) * ((K : ℤ) + 1) + 1 := by
            simp [checkersCountFixed]
          simp only [wCell, cellBal, h1', List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil]
          ring
    | produceInit =>
        simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
        simp only [wCell, cellBal, Nat.sub_zero, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        push_cast
        ring
    | produceWord i =>
        simp only [bodies] at hls
        split_ifs at hls with hlt
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          have hk : 1 + max (w.length - (i + 1)) 1 = max (w.length - i) 1 := by omega
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          have : ((max (w.length - i) 1 : ℕ) : ℤ) =
              1 + ((max (w.length - (i + 1)) 1 : ℕ) : ℤ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
          rw [this]
          ring
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          have hk : (1 : ℕ) = max (w.length - i) 1 := by omega
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          have : ((max (w.length - i) 1 : ℕ) : ℤ) = 1 := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk.symm
          rw [this]
          ring
    | done =>
        simp only [bodies, Set.mem_setOf_eq] at hls
        obtain ⟨f, -, rfl⟩ := hls
        simp [wCell, cellBal, isStart, isCall]
    | cSeq u k =>
        simp only [bodies] at hls
        split_ifs at hls with h0 h1 he
        · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
          simp [wCell, cellBal]
        · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
          simp [wCell, cellBal]
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
          rw [← hhalf]
          ring
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
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
          simp [wCell, cellBal]
        · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
          simp [wCell, cellBal]
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil]
          have hhalf : ((k / 2 : ℕ) : ℤ) * 2 = (k : ℤ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (by omega : k / 2 * 2 = k)
          rw [← hhalf]
          ring
        · simp only [Set.mem_singleton_iff] at hls; subst hls
          simp only [wCell, cellBal, List.flatten_cons, List.flatten_nil, List.append_nil,
            List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
            List.sum_nil]
          have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
            have : 1 ≤ k := by omega
            push_cast [this]
            ring
          rw [hk1]
          ring
    | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The channel balance is a balanced weight of the repaired domain.** -/
lemma balanced_wCell (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync) :
    Balanced (methodsFix N w K) (wCell (Q := Q) (Γ := Γ) x w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wCell_bodiesFix x hx hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    rcases hx with rfl | rfl <;>
      simp [initChainsFix, headChainFix, wCell, cellBal] <;> ring

lemma sum_map_wCell (x : SyncKind) (as : List (TMAct Q Γ)) :
    (as.map fun a => wCell (Q := Q) (Γ := Γ) x w K (Sum.inl a)).sum =
      (as.countP (isStart x) : ℤ) - (as.countP (isCall x) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      by_cases h₁ : isStart x a = true <;> by_cases h₂ : isCall x a = true <;>
        simp [wCell, h₁, h₂] <;> ring

/-- The initial task network of the repaired problem is the single task `sI`. -/
lemma weight_tnIFix (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ) :
    weight ω ((problemFix N w K).tnI) = ω (Sum.inr (TMTask.sI : TMTask Q Γ)) := by
  show weight ω (TaskNetwork.seq [Sum.inr (TMTask.sI : TMTask Q Γ)]) = _
  rw [TaskNetwork.seq, weight_grid]
  simp

/-- **The cell counters of the repaired construction answer exactly as often as the tape
asks.**  In every refinement of the initial task network of the repaired problem the number of
`start x` actions minus the number of `call x` actions is the balance of the initial task
`sI` — which, for an input that fits into the time bound, is zero
(`HTN.TMEnc.countP_start_eq_countP_call_fix`).  For the printed construction the same
quantity is positive, which is why the printed problem has no solution
(`HTN.TMEnc.not_solvable`). -/
theorem countP_start_sub_call_fix (x : SyncKind) (hx : x = SyncKind.check ∨ x = SyncKind.sync)
    {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    (as.countP (isStart x) : ℤ) - (as.countP (isCall x) : ℤ) =
      checkersCountFixed K (K + 1) -
        ((K : ℤ) + 1) * (((1 + max w.length 1 + (K - w.length)) + K * (1 + K) : ℕ) : ℤ) := by
  have hw := weight_of_netYield (balanced_wCell (N := N) (w := w) (K := K) x hx) h
  rw [sum_map_wCell, weight_tnIFix] at hw
  simpa [wCell, cellBal] using hw

/-- **The two cell channels of the repaired construction balance.**  Every refinement of the
initial task network of the repaired problem contains exactly as many `start x` as `call x`
actions, for both cell channels `x`.

This is the identity that the printed construction violates
(`HTN.TMEnc.countP_startCheck_sub_callCheck` together with `HTN.TMEnc.not_solvable`), and it is
a necessary condition for a plan to be a solution
(`HTN.TMEnc.countP_sync_eq_of_isSolutionPlan'`): the `K + 1` repaired cell counters answer
`(K+1)³` synchronisation requests, exactly one for each of the `K + 1` requests of each of the
`(K+1)²` cells of the witness `W = #w₀#w₁…#w_K`. -/
theorem countP_start_eq_countP_call_fix (x : SyncKind)
    (hx : x = SyncKind.check ∨ x = SyncKind.sync) (hw0 : w ≠ []) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isStart x) = as.countP (isCall x) := by
  have hbal := countP_start_sub_call_fix (N := N) (w := w) (K := K) x hx h
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  have hA : (1 + max w.length 1 + (K - w.length)) + K * (1 + K) = (K + 1) ^ 2 := by
    have hmax : max w.length 1 = w.length := by omega
    rw [hmax]
    ring_nf
    omega
  rw [hA, checkersCountFixed_eq] at hbal
  have hcast : (((K + 1) ^ 2 : ℕ) : ℤ) = ((K : ℤ) + 1) ^ 2 := by push_cast; ring
  have hk1 : ((K + 1 : ℕ) : ℤ) = (K : ℤ) + 1 := by push_cast; ring
  rw [hcast, hk1] at hbal
  have hzero : ((as.countP (isStart x) : ℤ)) = (as.countP (isCall x) : ℤ) := by nlinarith [hbal]
  exact_mod_cast hzero

end TMEnc

end HTN
