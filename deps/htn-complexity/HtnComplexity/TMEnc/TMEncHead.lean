import HtnComplexity.TMEnc.TMEncSim
/-!
# The budget of the head counter

The head counter of the Turing-machine encoding is the process

`retract_head ; respond_head ; head ; C^K noHead ; C^K heads`   with
`head → (start_head, assert_head, respond_head)`,
`noHead → (start_head, retract_head, respond_head)`,
`heads → (noHead, head, C^K noHead)`,

and it *answers* one `acquire head` of the tape-producing process per cell it runs through.  The
requests come from two places: every produced tape cell asks once, and a transition of the
machine that does not move the head to the right asks one (`stay`) or two (`left`) extra times,
which is how the construction realises the movement of the head.

This file computes the **budget** of that process: every refinement of the initial task network
contains exactly `K² + 3K + 1` actions `start head`
(`HTN.TMEnc.countP_startHead_eq`), so — by the handshake counting theorem of
`HtnComplexity/TMEnc/TMEncCount.lean` — every *solution plan* contains `K² + 3K + 1` or
`K² + 3K + 2` actions `call head`, of which `(K+1)²` come from the produced cells.  Hence

**`HTN.TMEnc.countP_extra_acquireHead`** — the transitions of a solution plan eat up exactly `K`
or `K + 1` steps of the head counter.

That is precisely the budget the construction needs: the machine performs `K` transitions, one
per pair of consecutive tapes, and each of them eats `1 - δ ∈ {0, 1, 2}` steps where `δ` is the
displacement of the head; since the head returns to the first cell at the end of the run
(the source assumes this w.l.o.g.), the displacements sum to `0` and the eaten steps to `K`,
plus the one of the final transition that does not move the head.

It is also the computation that shows why the trailing count of the `heads` cycle must be `K` and not
the `K + 2` printed in the source: with `C^{K+2}` the same computation gives `K² + 5K + 1`
answers, so a solution plan would have to eat up `3K` or `3K + 1` steps — more than the `2K`
that `K` transitions can ever eat.  See `NOTES.md`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### How many answers the head counter gives -/

/-- How many `start head` actions the full expansion of a compound task performs. -/
def startHeadCount (K : ℕ) : TMTask Q Γ → ℕ
  | .release x => if x = SyncKind.head then 1 else 0
  | .headCell => 1
  | .noHeadCell => 1
  | .heads => K + 2
  | .cSeq t k => k * startHeadCount K t
  | .cPar t k => k * startHeadCount K t
  | .sI => 1 + K + K * (K + 2)
  | _ => 0

/-- The weight counting the answers of the head counter. -/
def wStartHead (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isStart SyncKind.head a then 1 else 0
  | Sum.inr t => (startHeadCount K t : ℤ)

lemma sum_wStartHead_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wStartHead K)).sum = wStartHead K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount, isStart]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      cases y <;> simp [wStartHead, startHeadCount, isStart]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wStartHead, startHeadCount, isStart]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount, isStart]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wStartHead, startHeadCount, isStart]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount, isStart]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount, isStart]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wStartHead, startHeadCount, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mul_one]
      push_cast
      ring
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wStartHead, startHeadCount, isStart, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wStartHead, startHeadCount, isStart]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wStartHead, startHeadCount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wStartHead, startHeadCount]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wStartHead, startHeadCount]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wStartHead, startHeadCount, isStart]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHead, startHeadCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHead, startHeadCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * startHeadCount K u + k / 2 * startHeadCount K u =
            k * startHeadCount K u := by
          have hrw : k / 2 * startHeadCount K u + k / 2 * startHeadCount K u =
              (2 * (k / 2)) * startHeadCount K u := by ring
          rw [hrw, hk2]
        simp only [wStartHead, startHeadCount, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : startHeadCount K u + (k - 1) * startHeadCount K u = k * startHeadCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wStartHead, startHeadCount, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHead, startHeadCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wStartHead, startHeadCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * startHeadCount K u + k / 2 * startHeadCount K u =
            k * startHeadCount K u := by
          have hrw : k / 2 * startHeadCount K u + k / 2 * startHeadCount K u =
              (2 * (k / 2)) * startHeadCount K u := by ring
          rw [hrw, hk2]
        simp only [wStartHead, startHeadCount, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : startHeadCount K u + (k - 1) * startHeadCount K u = k * startHeadCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wStartHead, startHeadCount, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The answer weight of the head counter is balanced.** -/
lemma balanced_wStartHead : Balanced (methods N w K) (wStartHead (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wStartHead_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wStartHead, startHeadCount, isStart]
    ring

lemma sum_map_wStartHead (as : List (TMAct Q Γ)) :
    (as.map fun a => wStartHead (Q := Q) (Γ := Γ) K (Sum.inl a)).sum =
      (as.countP (isStart SyncKind.head) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isStart SyncKind.head a = true
      · simp [wStartHead, h]; ring
      · simp [wStartHead, h]

/-- **The head counter answers exactly `K² + 3K + 1` times.**  Every refinement of the initial
task network contains that many `start head` actions: one for the first cell of the first tape,
`K` for the remaining cells of the first tape, and `K + 2` for each of the `K` cycles `heads`
(one tape of `K + 1` cells plus the one step that the transition of that tape eats up). -/
theorem countP_startHead_eq {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP (isStart SyncKind.head) = 1 + K + K * (K + 2) := by
  have hw := weight_of_netYield (balanced_wStartHead (N := N) (w := w) (K := K)) h
  rw [sum_map_wStartHead, weight_tnI] at hw
  simp only [wStartHead, startHeadCount] at hw
  exact_mod_cast hw

/-- **The head counter of a solution plan is exhausted.**  Every solution plan asks for
`K² + 3K + 1` or `K² + 3K + 2` steps of the head counter — as many as it answers, up to the one
answer of the prologue `retract_head ; respond_head`. -/
theorem countP_callHead_eq_of_isSolutionPlan {as : List (TMAct Q Γ)}
    (h : (problem N w K).IsSolutionPlan as) :
    1 + K + K * (K + 2) ≤ as.countP (isCall SyncKind.head) ∧
      as.countP (isCall SyncKind.head) ≤ 1 + K + K * (K + 2) + 1 := by
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨-, -, h₃, h₄⟩ := countP_sync_eq_of_isSolutionPlan SyncKind.head h
  rw [countP_startHead_eq hy] at h₃ h₄
  simpa using ⟨h₃, h₄⟩

/-- **The transitions of a solution plan eat up exactly `K` or `K + 1` steps of the head
counter.**  A solution plan performs `(K+1)²` write actions, each of which is accompanied by one
`acquire head`; the remaining requests for the head counter are the ones the transition methods
add in order to keep the head in place or to move it to the left. -/
theorem countP_extra_acquireHead {as : List (TMAct Q Γ)} (hw0 : w ≠ []) (hwK : w.length ≤ K)
    (h : (problem N w K).IsSolutionPlan as) :
    as.countP isAssert + K ≤ as.countP (isCall SyncKind.head) ∧
      as.countP (isCall SyncKind.head) ≤ as.countP isAssert + K + 1 := by
  obtain ⟨hy, -, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨h₁, h₂⟩ := countP_callHead_eq_of_isSolutionPlan h
  rw [countP_assert_eq_sq hw0 hwK hy]
  constructor
  · calc (K + 1) ^ 2 + K ≤ 1 + K + K * (K + 2) := by ring_nf; omega
      _ ≤ _ := h₁
  · calc as.countP (isCall SyncKind.head) ≤ 1 + K + K * (K + 2) + 1 := h₂
      _ ≤ (K + 1) ^ 2 + K + 1 := by ring_nf; omega

end TMEnc

end HTN
