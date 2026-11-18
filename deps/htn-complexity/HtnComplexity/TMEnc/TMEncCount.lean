import HtnComplexity.TMEnc.TMEncSem
import HtnPlanning.Core.Weight
/-!
# The handshake counting theorem for the Turing-machine encoding

The processes of the encoding of `HtnComplexity/TMEnc/TMEncoding.lean` synchronise through the
three channels of `HTN.TMEnc.SyncKind`.  This file proves that in **every solution plan** of the
encoded problem, and for each channel `x`, the four synchronisation actions occur equally
often:

`#call x = #wait x = #start x = #respond x`  (`HTN.TMEnc.countP_sync_eq_of_isSolutionPlan`).

Two independent ingredients are combined.

* *The hierarchy.*  A task asking for a step (`acquire x = call x ; wait x`) contributes one
  `call x` and one `wait x`, a task answering one (`release x = start x ; respond x`, and the
  two cells `head`/`noHead` of the head counter, which answer inline) contributes one `start x`
  and one `respond x`, and no other method body mentions these actions at all.  So the two
  integer weights `HTN.TMEnc.wAcquire` and `HTN.TMEnc.wRelease` are *balanced*
  (`HTN.TMEnc.balanced_wAcquire`, `HTN.TMEnc.balanced_wRelease`) and therefore, by
  `HTN.weight_of_netYield`, they vanish on every plan: `#call = #wait` and `#start = #respond`.
* *The state.*  A `start x` needs the semaphore `x_step`, which only a `call x` raises, and a
  `wait x` needs `x_stepped`, which only a `respond x` raises
  (`HtnComplexity/TMEnc/TMEncSem.lean`), so `#start ≤ #call` and `#wait ≤ #respond`.

Chaining the two inequalities around the two equalities squeezes all four counts together: no
process can run ahead of the others.  This is the lock-step property that the simulation
argument of Theorem 4.3.7 rests on; it is the counterpart, for this construction, of
`HTN.ToAc.exists_countP_handshake_eq_of_isSolutionPlan`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The two weights -/

/-- The weight counting the actions of a task *asking* for a step of the channel `x`: `+1` for
`call x`, `-1` for `wait x`, `0` for everything else. -/
def wAcquire (x : SyncKind) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => (if isCall x a = true then 1 else 0) - (if isWait x a = true then 1 else 0)
  | Sum.inr _ => 0

@[simp] lemma wAcquire_inr (x : SyncKind) (t : TMTask Q Γ) :
    wAcquire x (Sum.inr t) = 0 := rfl

/-! ### The weights are balanced

The one asymmetry of the construction is the *prologue* of the head counter: the initial task
network starts with `retract_head ; respond_head`, an answer on the channel `head` that no
`start_head` precedes — it is what sets the head counter going.  The weight `wRelease head` is
therefore balanced only after charging the initial task `sI` with `-1`; the auxiliary count
`HTN.TMEnc.sICount` does that, also for the counting tasks `C^k_{sI}` that the (unreachable)
methods of the domain allow. -/

/-- How often the initial task `sI` occurs in the body of a compound task. -/
def sICount : TMTask Q Γ → ℕ
  | .cSeq u k => k * sICount u
  | .cPar u k => k * sICount u
  | .sI => 1
  | _ => 0

/-- The weight counting the actions of a task *answering* a step of the channel `x`: `+1` for
`start x`, `-1` for `respond x`, `0` for every other action; a compound task is charged with the
answer of the prologue of the head counter for every occurrence of the initial task `sI` it
expands into. -/
def wReleaseOn (x : SyncKind) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => (if isStart x a = true then 1 else 0) - (if isRespond x a = true then 1 else 0)
  | Sum.inr t => -(sICount t : ℤ) * (if x = SyncKind.head then 1 else 0)

/-- **The weight of a method body of the encoding is the weight of the task it decomposes.**
The weight is assumed to vanish on all actions except the four of a channel, to be balanced on
the two pairs `call`/`wait` and `start`/`respond`, and to charge a compound task with `-d` per
occurrence of `sI`. -/
lemma sum_weight_bodies (d : ℤ) (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ)
    (hcomp : ∀ t : TMTask Q Γ, ω (Sum.inr t) = -(sICount t : ℤ) * d)
    (hacq : ∀ y : SyncKind,
      ω (Sum.inl (TMAct.call y)) + ω (Sum.inl (TMAct.wait y)) = 0)
    (hrel : ∀ y : SyncKind,
      ω (Sum.inl (TMAct.start y)) + ω (Sum.inl (TMAct.respond y)) = 0)
    (hother : (∀ (c : Option Γ), ω (Sum.inl (TMAct.assert c)) = 0) ∧
      (∀ f : TMFact Q Γ, ω (Sum.inl (TMAct.check f)) = 0) ∧
      ω (Sum.inl (TMAct.assertHead : TMAct Q Γ)) = 0 ∧
      ω (Sum.inl (TMAct.retractHead : TMAct Q Γ)) = 0 ∧
      ∀ (q : Q) (c : Option Γ) (q' : Q) (c' : Option Γ),
        ω (Sum.inl (TMAct.step q c q' c')) = 0)
    {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map ω).sum = ω (Sum.inr t) := by
  obtain ⟨hassert, hcheck, hassertHead, hretractHead, hstep⟩ := hother
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      have := hacq y
      simp only [hcomp, sICount, Nat.cast_zero, neg_zero, zero_mul]
      simpa using this
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      have := hrel y
      simp only [hcomp, sICount, Nat.cast_zero, neg_zero, zero_mul]
      simpa using this
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [hcomp, sICount, hassert]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount, hassert]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [hcomp, sICount, hcheck]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      have := hrel SyncKind.head
      simp only [hcomp, sICount, Nat.cast_zero, neg_zero, zero_mul, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, hassertHead]
      omega
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      have := hrel SyncKind.head
      simp only [hcomp, sICount, Nat.cast_zero, neg_zero, zero_mul, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, hretractHead]
      omega
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [hcomp, sICount, hstep, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl
      · simp [hcomp, sICount]
      · simp [hcomp, sICount, hcheck]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [sICount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls
      subst hls
      simp [hcomp, sICount]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [sICount]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [hcomp, sICount, hcheck]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0
        simp only [Set.mem_singleton_iff] at hls
        subst hls
        simp [hcomp, sICount]
      · subst h1
        simp only [Set.mem_singleton_iff] at hls
        subst hls
        simp [hcomp, sICount]
      · simp only [Set.mem_singleton_iff] at hls
        subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * sICount u + k / 2 * sICount u = k * sICount u := by
          have hrw : k / 2 * sICount u + k / 2 * sICount u = (2 * (k / 2)) * sICount u := by
            ring
          rw [hrw, hk2]
        simp only [hcomp, sICount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hcast : ((k / 2 * sICount u : ℕ) : ℤ) + ((k / 2 * sICount u : ℕ) : ℤ) =
            ((k * sICount u : ℕ) : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
        rw [← hcast]
        ring
      · simp only [Set.mem_singleton_iff] at hls
        subst hls
        have hk : sICount u + (k - 1) * sICount u = k * sICount u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [hcomp, sICount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        have hcast : ((sICount u : ℕ) : ℤ) + (((k - 1) * sICount u : ℕ) : ℤ) =
            ((k * sICount u : ℕ) : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
        rw [← hcast]
        ring
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0
        simp only [Set.mem_singleton_iff] at hls
        subst hls
        simp [hcomp, sICount]
      · subst h1
        simp only [Set.mem_singleton_iff] at hls
        subst hls
        simp [hcomp, sICount]
      · simp only [Set.mem_singleton_iff] at hls
        subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * sICount u + k / 2 * sICount u = k * sICount u := by
          have hrw : k / 2 * sICount u + k / 2 * sICount u = (2 * (k / 2)) * sICount u := by
            ring
          rw [hrw, hk2]
        simp only [hcomp, sICount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hcast : ((k / 2 * sICount u : ℕ) : ℤ) + ((k / 2 * sICount u : ℕ) : ℤ) =
            ((k * sICount u : ℕ) : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
        rw [← hcast]
        ring
      · simp only [Set.mem_singleton_iff] at hls
        subst hls
        have hk : sICount u + (k - 1) * sICount u = k * sICount u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [hcomp, sICount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        have hcast : ((sICount u : ℕ) : ℤ) + (((k - 1) * sICount u : ℕ) : ℤ) =
            ((k * sICount u : ℕ) : ℤ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
        rw [← hcast]
        ring
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The weight of the initial method** — the one that starts the three parallel processes.
It is the weight of its one bare answer `respond_head`, all its other tasks being compound
tasks not expanding into `sI`. -/
lemma sum_weight_initChains (d : ℤ) (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ)
    (hcomp : ∀ t : TMTask Q Γ, ω (Sum.inr t) = -(sICount t : ℤ) * d)
    (hretractHead : ω (Sum.inl (TMAct.retractHead : TMAct Q Γ)) = 0) :
    (((initChains K : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) ++
      [[Sum.inr (TMTask.done : TMTask Q Γ)]]).flatten.map ω).sum =
      ω (Sum.inl (TMAct.respond SyncKind.head)) := by
  simp [initChains, hcomp, sICount, hretractHead]

/-- **The asking weight is balanced**: every `call x` of a plan is matched by a `wait x`. -/
lemma balanced_wAcquire (x : SyncKind) :
    Balanced (methods N w K) (wAcquire (Q := Q) (Γ := Γ) x) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    refine sum_weight_bodies 0 _ (fun t => by simp [wAcquire]) (fun y => ?_) (fun y => ?_)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ _ _ => rfl⟩ hls
    · by_cases hy : y = x
      · simp [wAcquire, isCall, isWait, hy]
      · simp [wAcquire, isCall, isWait, hy]
    · simp [wAcquire, isCall, isWait]
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail,
      sum_weight_initChains 0 _ (fun t => by simp [wAcquire]) rfl]
    simp [wAcquire, isCall, isWait]

/-- **The answering weight is balanced**, after charging the initial task with the one answer
of the prologue of the head counter. -/
lemma balanced_wRelease (x : SyncKind) :
    Balanced (methods N w K) (wReleaseOn (Q := Q) (Γ := Γ) x) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    refine sum_weight_bodies (if x = SyncKind.head then 1 else 0) _ (fun t => rfl)
      (fun y => by simp [wReleaseOn, isStart, isRespond]) (fun y => ?_)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, fun _ _ _ _ => rfl⟩ hls
    by_cases hy : y = x
    · simp [wReleaseOn, isStart, isRespond, hy]
    · simp [wReleaseOn, isStart, isRespond, hy]
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail,
      sum_weight_initChains (if x = SyncKind.head then 1 else 0) _ (fun t => rfl) rfl]
    by_cases hx : x = SyncKind.head
    · subst hx
      simp [wReleaseOn, isStart, isRespond, sICount]
    · simp [wReleaseOn, isStart, isRespond, hx, sICount, Ne.symm hx]

/-! ### Counting the actions of a plan -/

lemma sum_map_wAcquire (x : SyncKind) (as : List (TMAct Q Γ)) :
    (as.map fun a => wAcquire x (Sum.inl a)).sum =
      (as.countP (isCall x) : ℤ) - as.countP (isWait x) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      by_cases hc : isCall x a = true <;> by_cases hw : isWait x a = true <;>
        simp [wAcquire, hc, hw] <;> ring

lemma sum_map_wReleaseOn (x : SyncKind) (as : List (TMAct Q Γ)) :
    (as.map fun a => wReleaseOn x (Sum.inl a)).sum =
      (as.countP (isStart x) : ℤ) - as.countP (isRespond x) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons, List.countP_cons]
      by_cases hc : isStart x a = true <;> by_cases hw : isRespond x a = true <;>
        simp [wReleaseOn, hc, hw] <;> ring

/-- The initial task network of the encoded problem is the single task `sI`, so it weighs
nothing for the asking weight and `-1` on the channel `head` for the answering weight. -/
lemma weight_tnI (ω : TMAct Q Γ ⊕ TMTask Q Γ → ℤ) :
    weight ω ((problem N w K).tnI) = ω (Sum.inr (TMTask.sI : TMTask Q Γ)) := by
  show weight ω (TaskNetwork.seq [Sum.inr (TMTask.sI : TMTask Q Γ)]) = _
  rw [TaskNetwork.seq, weight_grid]
  simp

/-- **Every refinement of the initial task network asks for as many steps as it waits for
them.** -/
theorem countP_call_eq_countP_wait (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP (isCall x) = as.countP (isWait x) := by
  have hw := weight_of_netYield (balanced_wAcquire (N := N) (w := w) (K := K) x) h
  rw [sum_map_wAcquire, weight_tnI] at hw
  simp only [wAcquire] at hw
  omega

/-- **Every refinement of the initial task network answers exactly one step more than it
starts, on the channel of the head counter, and exactly as many as it starts on the other two
channels.**  The extra answer is the one of the prologue `retract_head ; respond_head`. -/
theorem countP_respond_eq_countP_start (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP (isRespond x) =
      as.countP (isStart x) + (if x = SyncKind.head then 1 else 0) := by
  have hw := weight_of_netYield (balanced_wRelease (N := N) (w := w) (K := K) x) h
  rw [sum_map_wReleaseOn, weight_tnI] at hw
  by_cases hx : x = SyncKind.head
  · subst hx
    simp only [wReleaseOn, sICount, Nat.cast_one] at hw
    norm_num at hw ⊢
    omega
  · simp only [wReleaseOn, sICount, if_neg hx, mul_zero] at hw
    simp only [if_neg hx]
    omega

/-! ### The lock-step theorem -/

/-- The initial state of the encoded problem contains no semaphore facts. -/
lemma stepF_not_mem_init (x : SyncKind) :
    (TMFact.stepF x : TMFact Q Γ) ∉ (problem N w K).init := by
  show (TMFact.stepF x : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

lemma steppedF_not_mem_init (x : SyncKind) :
    (TMFact.steppedF x : TMFact Q Γ) ∉ (problem N w K).init := by
  show (TMFact.steppedF x : TMFact Q Γ) ∉ ({TMFact.st N.init} : Set (TMFact Q Γ))
  simp

/-- **The handshake counting theorem.**  In every solution plan of the encoded problem the four
synchronisation actions of each of the channels `check` and `sync` occur equally often, and on
the channel `head` the same holds up to the single answer of the prologue: the parallel
processes of the encoding run in lock-step, none of them being able to overtake the others. -/
theorem countP_sync_eq_of_isSolutionPlan (x : SyncKind) {as : List (TMAct Q Γ)}
    (h : (problem N w K).IsSolutionPlan as) :
    as.countP (isCall x) = as.countP (isWait x) ∧
      as.countP (isRespond x) =
        as.countP (isStart x) + (if x = SyncKind.head then 1 else 0) ∧
      as.countP (isStart x) ≤ as.countP (isCall x) ∧
      as.countP (isCall x) ≤
        as.countP (isStart x) + (if x = SyncKind.head then 1 else 0) := by
  obtain ⟨hy, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  have h₁ : as.countP (isCall x) = as.countP (isWait x) := countP_call_eq_countP_wait x hy
  have h₂ : as.countP (isRespond x) =
      as.countP (isStart x) + (if x = SyncKind.head then 1 else 0) :=
    countP_respond_eq_countP_start x hy
  have h₃ : as.countP (isStart x) ≤ as.countP (isCall x) :=
    countP_start_le_countP_call x (stepF_not_mem_init x) happ
  have h₄ : as.countP (isWait x) ≤ as.countP (isRespond x) :=
    countP_wait_le_countP_respond x (steppedF_not_mem_init x) happ
  exact ⟨h₁, h₂, h₃, by omega⟩

/-- **The handshake counting theorem for the two cell-counter channels.**  On the channels
`check` and `sync` all four synchronisation actions of a solution plan occur equally often. -/
theorem countP_sync_eq_of_isSolutionPlan' (x : SyncKind) (hx : x ≠ SyncKind.head)
    {as : List (TMAct Q Γ)} (h : (problem N w K).IsSolutionPlan as) :
    as.countP (isCall x) = as.countP (isWait x) ∧
      as.countP (isWait x) = as.countP (isRespond x) ∧
      as.countP (isRespond x) = as.countP (isStart x) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := countP_sync_eq_of_isSolutionPlan x h
  simp only [if_neg hx, add_zero] at h₂ h₄
  exact ⟨h₁, by omega, by omega⟩

end TMEnc

end HTN
