import HtnComplexity.TMEnc.CorrectFix
/-!
# The head counter of the repaired encoding forces the head to come home

The head counter of the encoding of Theorem 4.3.7 answers exactly `K² + 3K + 1` requests
(`HTN.TMEnc.countP_startHead_eqFix`), while the `(K+1)²` cells of the witness issue only
`(K+1)² = K² + 2K + 1` of them.  The missing `K` requests are the ones the *transitions* issue:
a transition of the machine performs `moveExtra m ∈ {0, 1, 2}` additional `acquire head` tasks,
one for a `stay` move and two for a `left` move, and none for a `right` move — this is how the
construction realises the movement of the head.

Consequently a machine **all of whose transitions move the head to the right** issues no extra
request at all, and its encoded problem is unsolvable: the head counter can never be started
often enough.  This file proves that.

* `HTN.TMEnc.RightMoving` — every transition of the machine moves the head to the right;
* `HTN.TMEnc.countP_callHead_eq_sq_fix` — for such a machine every plan of the repaired problem
  contains exactly `(K+1)²` actions `call head`;
* `HTN.TMEnc.not_solvable_of_rightMoving_fix` — hence the repaired problem is **unsolvable**;
* `HTN.TMEnc.not_encodingCompleteFix` — since a machine can accept without performing any
  transition at all (its initial state may already be accepting), the completeness statement
  `HTN.TMEnc.EncodingCompleteFix` is **false** as it stands, and so is
  `HTN.EncodingCorrectFix` (`HTN.TMEnc.not_encodingCorrectFix`).

This is not a second defect of the same kind as the one of
`HtnComplexity/TMEnc/TMEncCheck.lean` — that one makes the problem unsolvable for *every* machine
— but the manifestation of an assumption that the source makes tacitly: the machine is assumed
to run for exactly `K` steps and to return its head to the first cell before it accepts, so that
the displacements of the `K` transitions sum to `0` and the transitions eat exactly the `K`
missing steps of the head counter.  The predicate `HTN.TMEnc.HomingRun` of this file records
that assumption, and `HTN.TMEnc.EncodingCompleteFixHoming` is the completeness statement
relative to it.  See `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Machines that only move to the right -/

/-- Every transition of the machine moves the head to the right.  Such a machine never issues an
extra request to the head counter of the encoding. -/
def RightMoving (N : NTM Q Γ) : Prop :=
  ∀ (q : Q) (c : Γ) (x : Q × Γ × Move), x ∈ N.step q c → x.2.2 = Move.right

/-! ### How many requests the tape issues

The weight is the one of `HTN.TMEnc.assertCount` except at the task `acquire head`, which
carries the single request of a produced cell; the transitions carry none, which is exactly
where `HTN.TMEnc.RightMoving` is used. -/

/-- How many `call head` actions the full expansion of a compound task performs, for a machine
all of whose transitions move to the right. -/
def callHeadCount (w : List Γ) (K : ℕ) : TMTask Q Γ → ℕ
  | .acquire x => if x = SyncKind.head then 1 else 0
  | .produce => 1
  | .produceSym _ => 1
  | .tapeProduce => 1 + K
  | .produceInit => 1 + max w.length 1 + (K - w.length)
  | .produceWord i => max (w.length - i) 1
  | .cSeq t k => k * callHeadCount w K t
  | .cPar t k => k * callHeadCount w K t
  | .sI => (1 + max w.length 1 + (K - w.length)) + K * (1 + K)
  | _ => 0

/-- The weight counting the requests to the head counter. -/
def wCallHead (w : List Γ) (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isCall SyncKind.head a then 1 else 0
  | Sum.inr t => (callHeadCount w K t : ℤ)

lemma sum_wCallHead_bodiesFix (hright : RightMoving N) {t : TMTask Q Γ}
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesFix N w K t) :
    (ls.flatten.map (wCallHead w K)).sum = wCallHead w K (Sum.inr t) := by
  cases t with
  | acquire y =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      by_cases hy : y = SyncKind.head <;>
        simp [wCallHead, callHeadCount, isCall, hy]
  | release y =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount, isCall]
  | produce =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wCallHead, callHeadCount, isCall]
  | produceSym c =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount, isCall]
  | tapeProduce =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount]
  | waitCell =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount]
  | waitN i =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount]
  | chk =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wCallHead, callHeadCount, isCall]
  | headCell =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount, isCall]
  | noHeadCell =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount, isCall]
  | heads =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wCallHead, callHeadCount]
  | transition =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, hmv, rfl⟩ := hls
      have hm : mv = Move.right := hright q c (q', c', mv) hmv
      subst hm
      simp [wCallHead, callHeadCount, isCall, moveExtra]
  | transitionAndCheck =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wCallHead, callHeadCount, isCall]
  | checkers i =>
      by_cases hi : i = 1
      · subst hi
        rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
        subst hls
        simp [checkerBodyFix, wCallHead, callHeadCount]
      · rw [bodiesFix_eq_of_ne (by simp [hi])] at hls
        simp only [bodies] at hls
        split_ifs at hls <;> simp_all [wCallHead, callHeadCount]
  | produceInit =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_zero, mul_one]
      push_cast
      ring
  | produceWord i =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies] at hls
      split_ifs at hls with hlt
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 + max (w.length - (i + 1)) 1 = max (w.length - i) 1 := by omega
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 = max (w.length - i) 1 := by omega
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | done =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wCallHead, callHeadCount, isCall]
  | cSeq u k =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wCallHead, callHeadCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wCallHead, callHeadCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : k / 2 * callHeadCount w K u + k / 2 * callHeadCount w K u =
            k * callHeadCount w K u := by
          have hrw : k / 2 * callHeadCount w K u + k / 2 * callHeadCount w K u =
              (2 * (k / 2)) * callHeadCount w K u := by ring
          rw [hrw, show 2 * (k / 2) = k by omega]
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : callHeadCount w K u + (k - 1) * callHeadCount w K u =
            k * callHeadCount w K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wCallHead, callHeadCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wCallHead, callHeadCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : k / 2 * callHeadCount w K u + k / 2 * callHeadCount w K u =
            k * callHeadCount w K u := by
          have hrw : k / 2 * callHeadCount w K u + k / 2 * callHeadCount w K u =
              (2 * (k / 2)) * callHeadCount w K u := by ring
          rw [hrw, show 2 * (k / 2) = k by omega]
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : callHeadCount w K u + (k - 1) * callHeadCount w K u =
            k * callHeadCount w K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wCallHead, callHeadCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI =>
      rw [bodiesFix_eq_of_ne (by simp)] at hls
      simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The request weight is balanced** for a right-moving machine. -/
lemma balanced_wCallHead (hright : RightMoving N) :
    Balanced (methodsFix N w K) (wCallHead (Q := Q) w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wCallHead_bodiesFix hright hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNetFix K) = _
    rw [initNetFix, weight_gridTail]
    simp [initChainsFix, headChainFix, wCallHead, callHeadCount]

lemma sum_map_wCallHead (as : List (TMAct Q Γ)) :
    (as.map fun a => wCallHead (Q := Q) w K (Sum.inl a)).sum =
      (as.countP (isCall SyncKind.head) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isCall SyncKind.head a = true
      · simp [wCallHead, h]; ring
      · simp [wCallHead, h]

/-- **A right-moving machine issues one request per produced cell.**  Every plan of the repaired
problem contains exactly `1 + max |w| 1 + (K - |w|) + K(K+1)` actions `call head`. -/
theorem countP_callHead_eq_fix (hright : RightMoving N) {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall SyncKind.head) = (1 + max w.length 1 + (K - w.length)) + K * (1 + K) := by
  have hw := weight_of_netYield (balanced_wCallHead (w := w) (K := K) hright) h
  rw [sum_map_wCallHead, weight_tnIFix] at hw
  simp only [wCallHead, callHeadCount] at hw
  exact_mod_cast hw

/-- **A right-moving machine issues exactly `(K+1)²` requests**, one per cell of the witness. -/
theorem countP_callHead_eq_sq_fix (hright : RightMoving N) (hw0 : w ≠ []) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)}
    (h : (domainFix N w K).NetYield ((problemFix N w K).tnI) as) :
    as.countP (isCall SyncKind.head) = (K + 1) ^ 2 := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  rw [countP_callHead_eq_fix hright h, show max w.length 1 = w.length by omega]
  ring_nf
  omega

/-! ### The encoded problem of a right-moving machine is unsolvable -/

/-- **The repaired problem of a right-moving machine has no solution plan.**  The head counter
has to be started `K² + 3K + 1` times, but only `(K+1)² = K² + 2K + 1` requests are ever
issued. -/
theorem not_isSolutionPlanFix_of_rightMoving (hright : RightMoving N) (hw0 : w ≠ [])
    (hwK : w.length ≤ K) (hK : 1 ≤ K) (as : List (TMAct Q Γ)) :
    ¬ (problemFix N w K).IsSolutionPlan as := by
  intro h
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  have hlow := countP_callHead_eq_of_isSolutionPlanFix hK h
  rw [countP_callHead_eq_sq_fix hright hw0 hwK hy] at hlow
  nlinarith [hlow, hK]

/-- **The repaired problem of a right-moving machine is unsolvable.** -/
theorem not_solvable_of_rightMoving_fix (hright : RightMoving N) (hw0 : w ≠ [])
    (hwK : w.length ≤ K) (hK : 1 ≤ K) : ¬ (problemFix N w K).Solvable := by
  intro h
  obtain ⟨as, hplan⟩ := Problem.solvable_iff_exists_solutionPlan.1 h
  exact not_isSolutionPlanFix_of_rightMoving hright hw0 hwK hK as hplan

/-- **The repaired construction is not complete as it stands.**  A right-moving machine whose
initial state is accepting accepts its input in zero steps, yet its encoded problem is
unsolvable. -/
theorem not_encodingCompleteFix_of_rightMoving (hright : RightMoving N) (hw0 : w ≠ [])
    (hwK : w.length ≤ K) (hK : 1 ≤ K) (hacc : N.AcceptsWithin w K) :
    ¬ EncodingCompleteFix N w K := fun h =>
  not_solvable_of_rightMoving_fix hright hw0 hwK hK (h hacc)

/-! ### A concrete counterexample

The machine `HTN.TMEnc.idleMachine` has no transition at all and accepts immediately.  It
witnesses that the completeness statement `HTN.TMEnc.EncodingCompleteFix`, and with it the
simulation correctness `HTN.EncodingCorrectFix` of the repaired construction, is false without
further assumptions on the machine. -/

/-- A machine without transitions whose initial state is accepting. -/
def idleMachine : NTM Unit Bool where
  step := fun _ _ => ∅
  init := ()
  accept := Set.univ
  blank := false

lemma rightMoving_idleMachine : RightMoving idleMachine := by
  rintro q c x hx
  exact absurd hx (Set.notMem_empty x)

lemma acceptsWithin_idleMachine (w : List Bool) (K : ℕ) : idleMachine.AcceptsWithin w K :=
  ⟨0, Nat.zero_le _, idleMachine.initConfig w, rfl, Set.mem_univ _⟩

/-- **`HTN.TMEnc.EncodingCompleteFix` is false.**  For the machine without transitions, which
accepts every input immediately, the repaired encoded problem is unsolvable. -/
theorem not_encodingCompleteFix {w : List Bool} {K : ℕ} (hw0 : w ≠ []) (hwK : w.length ≤ K)
    (hK : 1 ≤ K) : ¬ EncodingCompleteFix idleMachine w K :=
  not_encodingCompleteFix_of_rightMoving rightMoving_idleMachine hw0 hwK hK
    (acceptsWithin_idleMachine w K)

/-- **`HTN.EncodingCorrectFix` is false.**  The simulation correctness of the repaired
construction fails for the machine without transitions. -/
theorem not_encodingCorrectFix {p : Polynomial ℕ} :
    ¬ EncodingCorrectFix idleMachine p := by
  intro h
  have hK : 1 ≤ 2 ^ p.eval [true].length := Nat.one_le_two_pow
  exact not_solvable_of_rightMoving_fix rightMoving_idleMachine (w := [true])
    (by simp) (by simpa using hK) hK
    ((h [true]).2 (acceptsWithin_idleMachine [true] _))

/-! ### The assumption the source makes

The counterexample above is not a defect of the *repair* but of the statement: the encoding
simulates runs of **exactly `K` steps whose head returns to the first cell**, because the `K`
transitions have to eat exactly the `K` steps by which the head counter exceeds the number of
tape cells, and a transition eats `1 - δ` steps where `δ ∈ {-1, 0, 1}` is the displacement of
the head.  The following predicate records that assumption. -/

/-- A **homing run**: an accepting run of exactly `K` steps that ends with the head on the first
cell.  This is the shape of run the construction of Theorem 4.3.7 encodes; the source assumes
w.l.o.g. that an accepting machine has one. -/
def HomingRun (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  ∃ hist : ℕ → Config Q Γ, IsHistory N w K hist ∧ (hist K).head = 0

/-- **Completeness of the repaired encoding, relative to the assumption of the source**: a
homing accepting run of exactly `K` steps can be written out as a solution of the repaired
problem.  This is the statement that replaces `HTN.TMEnc.EncodingCompleteFix`, which is false
(`HTN.TMEnc.not_encodingCompleteFix`). -/
def EncodingCompleteFixHoming (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  HomingRun N w K → (problemFix N w K).Solvable

/-- A homing run is in particular an accepting run within `K` steps. -/
theorem acceptsWithin_of_homingRun (h : HomingRun N w K) : N.AcceptsWithin w K := by
  obtain ⟨hist, hhist, -⟩ := h
  exact (N.acceptsWithin_iff_exists_history w K).2 ⟨K, le_rfl, hist, hhist⟩

/-- The idle machine has no homing run for `K ≥ 1`: it cannot make a single step. -/
theorem not_homingRun_idleMachine {w : List Bool} {K : ℕ} (hK : 1 ≤ K) :
    ¬ HomingRun idleMachine w K := by
  rintro ⟨hist, hhist, -⟩
  obtain ⟨q', c', m, hmem, -⟩ := hhist.step 0 hK
  exact absurd hmem (Set.notMem_empty _)

end TMEnc

end HTN
