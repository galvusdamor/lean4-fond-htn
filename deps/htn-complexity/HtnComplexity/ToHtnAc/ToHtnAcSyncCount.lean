import HtnComplexity.ToHtnAc.ToHtnAcChainClosed
import HtnComplexity.ToHtnAc.ToHtnAcSemaphore
import HtnComplexity.ToHtnAc.ToHtnAcBodies
import HtnComplexity.ToHtnAc.ToHtnAcSim
/-!
# Counting the synchronisation actions of the HTN-AC compilation

`HtnComplexity/ToHtnAc/ToHtnAcSemaphore.lean` bounds the number of `accept_X` actions of an
executable plan by the number of its `ask_X` actions.  To exploit that bound one has to know how
many synchronisation actions each gadget contributes, which is what this file computes.

A *handshake predicate* (`HTN.ToAc.HandshakePred`) is a predicate on actions that is false on
everything except `lock`, `unlock` and the four handshake actions; the four predicates
`isAsk`, `isAccept`, `isDone`, `isWait` of `HtnComplexity/ToHtnAc/ToHtnAcSemaphore.lean` are of that
kind.  For such a predicate:

* `HTN.ToAc.countP_yieldSeq_SEL`, `HTN.ToAc.countP_yieldSeq_EQ` — the state-guessing and
  state-comparing gadgets contribute nothing;
* `HTN.ToAc.countP_yieldSeq_STATE1` — `STATE_n^1` contributes exactly one `done_W` and one
  `accept_R` (from the innermost body of `STATE_0^3`);
* `HTN.ToAc.countP_yieldSeq_MEM` — **a memory cell contributes exactly `accept_W`, `done_W`,
  `accept_R`, `done_R`**;
* `HTN.ToAc.countP_yieldSeq_WRITE`, `HTN.ToAc.countP_yieldSeq_READ` — a `WRITE` contributes
  `ask_W` and `wait_W`, a `READ` contributes `ask_R` and `wait_R`.

Combining this with the semaphore bound gives `HTN.ToAc.card_mem_le_countP_ask_write`: **an
executable plan of the compiled problem contains at least as many `ask_W` actions as it refines
memory cells.**  In other words, no memory cell can be filled without a `WRITE` task of some
proof step asking for it — which is exactly the part of the correctness argument that the
semaphores are there to provide.

The same book-keeping performed on a proof step (`HTN.ToAc.countP_yieldSeq_TUPLE`: a `TUPLE` run
issues `r ≤ 2` read handshakes and `w ≤ bound` write handshakes, the numbers not depending on
the predicate) turns the inequality into an *equality*:

* `HTN.ToAc.countP_handshake_eq_card_mem` — **in an executable plan the memory cells, the
  executed `WRITE`s and the executed `READ`s are equinumerous**: with `m₁` memory cells the plan
  performs exactly `m₁` of each of `ask_W`, `wait_W`, `ask_R`, `wait_R`.  Each of the two
  semaphore inequalities is used once in each direction, squeezing the counts;
* `HTN.ToAc.card_mem_even` — hence the number of memory cells is even, since every proof step
  reads either two of them or none, and `HTN.ToAc.card_mem_le_two_mul_card_tuple` — at most two
  memory cells per proof step;
* `HTN.ToAc.countP_lock_eq_card_tuple` — each proof step takes and releases the lock exactly
  once, so the number of `lock` (and of `unlock`) actions is the number of proof steps;
* `HTN.ToAc.exists_countP_handshake_eq_of_isSolutionPlan` — the statement for a solution plan:
  it performs exactly `m` of each of the eight handshake actions, for one even `m ≤ bound`.
-/

namespace HTN

namespace ToAc

variable {F A C I : Type} {D : Domain F A C I} {vars : List F} {bound : ℕ}

open TaskNetwork Domain

/-! ### Splitting refinements of a chain -/

section General

universe u v w x

variable {F' : Type u} {A' : Type v} {C' : Type w} {I' : Type x} {E : Domain F' A' C' I'}

lemma yieldSeq_cons_split {x : A' ⊕ C'} {xs : List (A' ⊕ C')} {as : List A'}
    (h : E.YieldSeq (x :: xs) as) :
    ∃ a₁ a₂, as = a₁ ++ a₂ ∧ E.YieldSeq [x] a₁ ∧ E.YieldSeq xs a₂ :=
  Domain.YieldSeq.split (xs := [x]) (by simpa using h)

@[simp] lemma yieldSeq_singleton_inl_iff {a : A'} {as : List A'} :
    E.YieldSeq [Sum.inl a] as ↔ as = [a] := by
  rw [yieldSeq_inl_cons_iff]
  simp

lemma yieldSeq_singleton_inr_iff {c : C'} {as : List A'} :
    E.YieldSeq [Sum.inr c] as ↔ ∃ bs, E.SeqBody c bs ∧ E.YieldSeq bs as := by
  rw [yieldSeq_inr_cons_iff]
  simp

end General

/-! ### Handshake predicates -/

/-- A predicate on the compiled actions that only recognises `lock`, `unlock` and the four
handshake actions `ask_X`, `accept_X`, `done_X`, `wait_X`. -/
structure HandshakePred (p : AcAct F A C → Bool) : Prop where
  /-- `p` does not hold of `setV`. -/
  setV : ∀ v i, ¬ p (.setV v i)
  /-- `p` does not hold of `delV`. -/
  delV : ∀ v i, ¬ p (.delV v i)
  /-- `p` does not hold of `prePV`. -/
  prePV : ∀ v i j, ¬ p (.prePV v i j)
  /-- `p` does not hold of `preNV`. -/
  preNV : ∀ v i j, ¬ p (.preNV v i j)
  /-- `p` does not hold of `setC`. -/
  setC : ∀ t, ¬ p (.setC t)
  /-- `p` does not hold of `preC`. -/
  preC : ∀ t, ¬ p (.preC t)
  /-- `p` does not hold of `op2`. -/
  op2 : ∀ o, ¬ p (.op2 o)

lemma handshakePred_isAsk (x : RW) : HandshakePred (isAsk x : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isAsk]

lemma handshakePred_isAccept (x : RW) : HandshakePred (isAccept x : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isAccept]

lemma handshakePred_isDone (x : RW) : HandshakePred (isDone x : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isDone]

lemma handshakePred_isWait (x : RW) : HandshakePred (isWait x : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isWait]

lemma handshakePred_isLock : HandshakePred (isLock : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isLock]

lemma handshakePred_isUnlock : HandshakePred (isUnlock : AcAct F A C → Bool) := by
  constructor <;> intros <;> simp [isUnlock]

/-! ### Counting in the individual gadgets -/

variable {p : AcAct F A C → Bool}

lemma countP_yieldSeq_SELn (hp : HandshakePred p) : ∀ (n : ℕ) (i : Fin 5)
    (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.SELn n i)] as → as.countP p = 0 := by
  intro n
  induction n with
  | zero =>
      intro i as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_SELn_zero_iff] at hb
      subst hb
      simp_all
  | succ n ih =>
      intro i as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_SELn_succ_iff] at hb
      obtain ⟨v, -, rfl | rfl⟩ := hb <;>
        · obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := yieldSeq_cons_split hy
          rw [yieldSeq_singleton_inl_iff] at h₁
          subst h₁
          have := ih i a₂ (by simpa using h₂)
          simp [this, hp.setV, hp.delV]

lemma countP_yieldSeq_SEL (hp : HandshakePred p) {i : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.SEL i)] as) : as.countP p = 0 := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_SEL_iff] at hb
  subst hb
  exact countP_yieldSeq_SELn hp _ i as hy

lemma countP_yieldSeq_EQn (hp : HandshakePred p) : ∀ (n : ℕ) (i j : Fin 5)
    (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQn n i j)] as → as.countP p = 0 := by
  intro n
  induction n with
  | zero =>
      intro i j as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_EQn_zero_iff] at hb
      subst hb
      simp_all
  | succ n ih =>
      intro i j as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_EQn_succ_iff] at hb
      obtain ⟨v, -, rfl | rfl⟩ := hb <;>
        · obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := yieldSeq_cons_split hy
          rw [yieldSeq_singleton_inl_iff] at h₁
          subst h₁
          have := ih i j a₂ (by simpa using h₂)
          simp [this, hp.prePV, hp.preNV]

lemma countP_yieldSeq_EQ (hp : HandshakePred p) {i j : Fin 5} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.EQ i j)] as) : as.countP p = 0 := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_EQ_iff] at hb
  subst hb
  exact countP_yieldSeq_EQn hp _ i j as hy

/-- The handshake actions of a `STATE_n^3` refinement: the innermost body of `STATE_0^3`
contributes one `done_W` and one `accept_R`. -/
lemma countP_yieldSeq_STATE3 (hp : HandshakePred p) : ∀ (n : ℕ) (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE3 n)] as →
      as.countP p =
        ([AcAct.doneA RW.write, AcAct.accept RW.read] : List (AcAct F A C)).countP p := by
  intro n
  induction n with
  | zero =>
      intro as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_STATE3_zero_iff] at hb
      obtain ⟨t, rfl⟩ := hb
      obtain ⟨a₁, r₁, rfl, h₁, hy1⟩ := yieldSeq_cons_split hy
      obtain ⟨a₂, r₂, rfl, h₂, hy2⟩ := yieldSeq_cons_split hy1
      obtain ⟨a₃, r₃, rfl, h₃, hy3⟩ := yieldSeq_cons_split hy2
      obtain ⟨a₄, r₄, rfl, h₄, hy4⟩ := yieldSeq_cons_split hy3
      rw [yieldSeq_singleton_inl_iff] at h₁ h₂ h₃ h₄
      rw [yieldSeq_nil_iff] at hy4
      subst h₁; subst h₂; subst h₃; subst h₄; subst hy4
      simp [List.countP_cons, hp.preC, hp.setC]
  | succ n ih =>
      intro as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_STATE3_succ_iff] at hb
      obtain ⟨v, -, rfl | rfl⟩ := hb <;>
        · obtain ⟨a₁, r₁, rfl, h₁, hy⟩ := yieldSeq_cons_split hy
          obtain ⟨a₂, r₂, rfl, h₂, hy1⟩ := yieldSeq_cons_split hy
          obtain ⟨a₃, r₃, rfl, h₃, hy2⟩ := yieldSeq_cons_split hy1
          rw [yieldSeq_singleton_inl_iff] at h₁ h₃
          rw [yieldSeq_nil_iff] at hy2
          subst h₁; subst h₃; subst hy2
          have := ih a₂ h₂
          simp [List.countP_append, List.countP_cons, this, hp.prePV, hp.preNV, hp.setV,
            hp.delV]

/-- The handshake actions of a `STATE_n^1` refinement. -/
lemma countP_yieldSeq_STATE1 (hp : HandshakePred p) : ∀ (n : ℕ) (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq [Sum.inr (AcTask.STATE1 n)] as →
      as.countP p =
        ([AcAct.doneA RW.write, AcAct.accept RW.read] : List (AcAct F A C)).countP p := by
  intro n
  induction n with
  | zero =>
      intro as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_STATE1_zero_iff] at hb
      subst hb
      exact countP_yieldSeq_STATE3 hp _ as hy
  | succ n ih =>
      intro as h
      obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
      rw [seqBody_STATE1_succ_iff] at hb
      obtain ⟨v, -, rfl | rfl⟩ := hb <;>
        · obtain ⟨a₁, r₁, rfl, h₁, hy⟩ := yieldSeq_cons_split hy
          obtain ⟨a₂, r₂, rfl, h₂, hy1⟩ := yieldSeq_cons_split hy
          obtain ⟨a₃, r₃, rfl, h₃, hy2⟩ := yieldSeq_cons_split hy1
          rw [yieldSeq_singleton_inl_iff] at h₁ h₃
          rw [yieldSeq_nil_iff] at hy2
          subst h₁; subst h₃; subst hy2
          have := ih a₂ h₂
          simp [List.countP_append, List.countP_cons, this, hp.prePV, hp.preNV, hp.setV,
            hp.delV]

/-- **A memory cell performs exactly one `accept_W`, one `done_W`, one `accept_R` and one
`done_R`.** -/
theorem countP_yieldSeq_MEM (hp : HandshakePred p) {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.MEM] as) :
    as.countP p = ([AcAct.accept RW.write, AcAct.doneA RW.write, AcAct.accept RW.read,
      AcAct.doneA RW.read] : List (AcAct F A C)).countP p := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_MEM_iff] at hb
  subst hb
  obtain ⟨a₁, r₁, rfl, h₁, hy1⟩ := yieldSeq_cons_split hy
  obtain ⟨a₂, r₂, rfl, h₂, hy2⟩ := yieldSeq_cons_split hy1
  obtain ⟨a₃, r₃, rfl, h₃, hy3⟩ := yieldSeq_cons_split hy2
  rw [yieldSeq_singleton_inl_iff] at h₁ h₃
  rw [yieldSeq_nil_iff] at hy3
  subst h₁; subst h₃; subst hy3
  have := countP_yieldSeq_STATE1 hp _ a₂ h₂
  simp only [List.countP_append, List.countP_cons, List.countP_nil, this]
  omega

/-- A `WRITE` task refines exactly into `ask_W`, `wait_W`. -/
theorem countP_yieldSeq_WRITE {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.WRITE] as) :
    as = [AcAct.ask RW.write, AcAct.waitA RW.write] := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_WRITE_iff] at hb
  subst hb
  obtain ⟨a₁, r₁, rfl, h₁, hy1⟩ := yieldSeq_cons_split hy
  obtain ⟨a₂, r₂, rfl, h₂, hy2⟩ := yieldSeq_cons_split hy1
  rw [yieldSeq_singleton_inl_iff] at h₁ h₂
  rw [yieldSeq_nil_iff] at hy2
  subst h₁; subst h₂; subst hy2
  rfl

/-- A `READ` task refines exactly into `ask_R`, `wait_R`. -/
theorem countP_yieldSeq_READ {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.READ] as) :
    as = [AcAct.ask RW.read, AcAct.waitA RW.read] := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_READ_iff] at hb
  subst hb
  obtain ⟨a₁, r₁, rfl, h₁, hy1⟩ := yieldSeq_cons_split hy
  obtain ⟨a₂, r₂, rfl, h₂, hy2⟩ := yieldSeq_cons_split hy1
  rw [yieldSeq_singleton_inl_iff] at h₁ h₂
  rw [yieldSeq_nil_iff] at hy2
  subst h₁; subst h₂; subst hy2
  rfl

/-! ### Counting in a run of the counting task `𝔠̄^k_WRITE` -/

/-- `countP` of a list of `w` copies of the same block. -/
lemma countP_flatten_replicate {α : Type*} (w : ℕ) (l : List α) (p : α → Bool) :
    ((List.replicate w l).flatten).countP p = w * l.countP p := by
  induction w with
  | zero => simp
  | succ w ih =>
      rw [List.replicate_succ, List.flatten_cons, List.countP_append, ih]
      ring

/-- A sequence of `w` `WRITE` tasks refines exactly into `w` copies of `ask_W ; wait_W`. -/
lemma yieldSeq_replicate_WRITE : ∀ (w : ℕ) (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq (List.replicate w (Sum.inr AcTask.WRITE)) as →
      as = (List.replicate w
        ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten := by
  intro w
  induction w with
  | zero => intro as h; rw [List.replicate_zero, yieldSeq_nil_iff] at h; simp [h]
  | succ w ih =>
      intro as h
      rw [List.replicate_succ] at h
      obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := yieldSeq_cons_split h
      rw [countP_yieldSeq_WRITE h₁, ih a₂ h₂, List.replicate_succ, List.flatten_cons]

/-- A sequence of `r` `READ` tasks refines exactly into `r` copies of `ask_R ; wait_R`. -/
lemma yieldSeq_replicate_READ : ∀ (r : ℕ) (as : List (AcAct F A C)),
    (domain D vars bound).YieldSeq (List.replicate r (Sum.inr AcTask.READ)) as →
      as = (List.replicate r
        ([AcAct.ask RW.read, AcAct.waitA RW.read] : List (AcAct F A C))).flatten := by
  intro r
  induction r with
  | zero => intro as h; rw [List.replicate_zero, yieldSeq_nil_iff] at h; simp [h]
  | succ r ih =>
      intro as h
      rw [List.replicate_succ] at h
      obtain ⟨a₁, a₂, rfl, h₁, h₂⟩ := yieldSeq_cons_split h
      rw [countP_yieldSeq_READ h₁, ih a₂ h₂, List.replicate_succ, List.flatten_cons]

/-- **A run of the counting task `𝔠̄^k_WRITE` is `w` copies of `ask_W ; wait_W` for some
`w ≤ k`.** -/
lemma yieldSeq_cnt_WRITE {k : ℕ} {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr (AcTask.cnt AcTask.WRITE k)] as) :
    ∃ w ≤ k, as = (List.replicate w
      ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C))).flatten := by
  obtain ⟨w, hw, hy⟩ := (yieldSeq_cnt_iff k).1 h
  exact ⟨w, hw, yieldSeq_replicate_WRITE w as hy⟩

/-! ### Counting in a proof step -/

/-- **A `TUPLE` run takes the lock once, performs an even number `r ≤ 2` of read handshakes and
`w ≤ bound` write handshakes, and releases the lock** (and does nothing else that a handshake
predicate can see).  The numbers `r` and `w` do not depend on the predicate, which is what makes
them comparable across the four semaphores. -/
theorem countP_yieldSeq_TUPLE {as : List (AcAct F A C)}
    (h : (domain D vars bound).YieldSeq [Sum.inr AcTask.TUPLE] as) :
    ∃ r w, r ≤ 2 ∧ r % 2 = 0 ∧ w ≤ bound ∧ ∀ q : AcAct F A C → Bool, HandshakePred q →
      as.countP q = ([AcAct.lock, AcAct.unlock] : List (AcAct F A C)).countP q
        + (r * ([AcAct.ask RW.read, AcAct.waitA RW.read] : List (AcAct F A C)).countP q
          + w * ([AcAct.ask RW.write, AcAct.waitA RW.write] : List (AcAct F A C)).countP q) := by
  obtain ⟨bs, hb, hy⟩ := yieldSeq_singleton_inr_iff.1 h
  rw [seqBody_TUPLE_iff] at hb
  rcases hb with ⟨c, x, y, -, rfl⟩ | ⟨o, rfl⟩
  · obtain ⟨b₁, s₁, rfl, h₁, y₁⟩ := yieldSeq_cons_split hy
    obtain ⟨b₂, s₂, rfl, h₂, y₂⟩ := yieldSeq_cons_split y₁
    obtain ⟨b₃, s₃, rfl, h₃, y₃⟩ := yieldSeq_cons_split y₂
    obtain ⟨b₄, s₄, rfl, h₄, y₄⟩ := yieldSeq_cons_split y₃
    obtain ⟨b₅, s₅, rfl, h₅, y₅⟩ := yieldSeq_cons_split y₄
    obtain ⟨b₆, s₆, rfl, h₆, y₆⟩ := yieldSeq_cons_split y₅
    obtain ⟨b₇, s₇, rfl, h₇, y₇⟩ := yieldSeq_cons_split y₆
    obtain ⟨b₈, s₈, rfl, h₈, y₈⟩ := yieldSeq_cons_split y₇
    obtain ⟨b₉, s₉, rfl, h₉, y₉⟩ := yieldSeq_cons_split y₈
    obtain ⟨b₁₀, s₁₀, rfl, h₁₀, y₁₀⟩ := yieldSeq_cons_split y₉
    obtain ⟨b₁₁, s₁₁, rfl, h₁₁, y₁₁⟩ := yieldSeq_cons_split y₁₀
    obtain ⟨b₁₂, s₁₂, rfl, h₁₂, y₁₂⟩ := yieldSeq_cons_split y₁₁
    obtain ⟨b₁₃, s₁₃, rfl, h₁₃, y₁₃⟩ := yieldSeq_cons_split y₁₂
    obtain ⟨b₁₄, s₁₄, rfl, h₁₄, y₁₄⟩ := yieldSeq_cons_split y₁₃
    obtain ⟨b₁₅, s₁₅, rfl, h₁₅, y₁₅⟩ := yieldSeq_cons_split y₁₄
    rw [yieldSeq_nil_iff] at y₁₅
    rw [yieldSeq_singleton_inl_iff] at h₁ h₈ h₁₂ h₁₃ h₁₅
    subst h₁; subst h₈; subst h₁₂; subst h₁₃; subst h₁₅; subst y₁₅
    have hr₅ := countP_yieldSeq_READ h₅
    have hr₉ := countP_yieldSeq_READ h₉
    subst hr₅; subst hr₉
    obtain ⟨w, hw, rfl⟩ := yieldSeq_cnt_WRITE h₁₄
    refine ⟨2, w, le_refl 2, rfl, hw, fun q hq => ?_⟩
    have e₂ := countP_yieldSeq_SEL hq h₂
    have e₃ := countP_yieldSeq_SEL hq h₃
    have e₄ := countP_yieldSeq_SEL hq h₄
    have e₆ := countP_yieldSeq_EQ hq h₆
    have e₇ := countP_yieldSeq_EQ hq h₇
    have e₁₀ := countP_yieldSeq_EQ hq h₁₀
    have e₁₁ := countP_yieldSeq_EQ hq h₁₁
    simp only [List.countP_append, List.countP_cons, List.countP_nil, e₂, e₃, e₄, e₆, e₇, e₁₀,
      e₁₁, countP_flatten_replicate, hq.preC, hq.setC, Bool.false_eq_true,
      if_false, Nat.zero_add, Nat.add_zero]
    ring
  · obtain ⟨b₁, s₁, rfl, h₁, y₁⟩ := yieldSeq_cons_split hy
    obtain ⟨b₂, s₂, rfl, h₂, y₂⟩ := yieldSeq_cons_split y₁
    obtain ⟨b₃, s₃, rfl, h₃, y₃⟩ := yieldSeq_cons_split y₂
    obtain ⟨b₄, s₄, rfl, h₄, y₄⟩ := yieldSeq_cons_split y₃
    obtain ⟨b₅, s₅, rfl, h₅, y₅⟩ := yieldSeq_cons_split y₄
    obtain ⟨b₆, s₆, rfl, h₆, y₆⟩ := yieldSeq_cons_split y₅
    obtain ⟨b₇, s₇, rfl, h₇, y₇⟩ := yieldSeq_cons_split y₆
    obtain ⟨b₈, s₈, rfl, h₈, y₈⟩ := yieldSeq_cons_split y₇
    obtain ⟨b₉, s₉, rfl, h₉, y₉⟩ := yieldSeq_cons_split y₈
    obtain ⟨b₁₀, s₁₀, rfl, h₁₀, y₁₀⟩ := yieldSeq_cons_split y₉
    rw [yieldSeq_nil_iff] at y₁₀
    rw [yieldSeq_singleton_inl_iff] at h₁ h₆ h₈ h₁₀
    subst h₁; subst h₆; subst h₈; subst h₁₀; subst y₁₀
    obtain ⟨w, hw, rfl⟩ := yieldSeq_cnt_WRITE h₉
    refine ⟨0, w, Nat.zero_le _, rfl, hw, fun q hq => ?_⟩
    have e₂ := countP_yieldSeq_SEL hq h₂
    have e₃ := countP_yieldSeq_SEL hq h₃
    have e₄ := countP_yieldSeq_SEL hq h₄
    have e₅ := countP_yieldSeq_EQ hq h₅
    have e₇ := countP_yieldSeq_EQ hq h₇
    simp only [List.countP_append, List.countP_cons, List.countP_nil, e₂, e₃, e₄, e₅, e₇,
      countP_flatten_replicate, hq.op2, hq.setC, Bool.false_eq_true,
      if_false, Nat.zero_add, Nat.add_zero]
    ring

/-! ### Counting in the parallel memory cells -/

/-- `m` parallel memory cells perform `m` times the handshake actions of one cell. -/
theorem countP_gridYield_replicate_MEM (hp : HandshakePred p) : ∀ (m : ℕ)
    (as : List (AcAct F A C)),
    (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.MEM]) as →
      as.countP p = m * ([AcAct.accept RW.write, AcAct.doneA RW.write, AcAct.accept RW.read,
        AcAct.doneA RW.read] : List (AcAct F A C)).countP p := by
  intro m
  induction m with
  | zero =>
      intro as h
      rw [gridYield_replicate_zero] at h
      subst h
      simp
  | succ m ih =>
      intro as h
      obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := (gridYield_replicate_succ isSeqTask_MEM).1 h
      rw [hint.countP p, countP_yieldSeq_MEM hp h₁, ih as₂ h₂]
      ring

/-- The number of `accept_W` actions of a refinement of `m` parallel memory cells is `m`. -/
theorem countP_isAccept_write_gridYield_MEM {m : ℕ} {as : List (AcAct F A C)}
    (h : (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.MEM]) as) :
    as.countP (isAccept RW.write) = m := by
  rw [countP_gridYield_replicate_MEM (handshakePred_isAccept RW.write) m as h]
  simp [isAccept]

/-- A refinement of parallel memory cells contains no `ask_W` action. -/
theorem countP_isAsk_write_gridYield_MEM {m : ℕ} {as : List (AcAct F A C)}
    (h : (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.MEM]) as) :
    as.countP (isAsk RW.write) = 0 := by
  rw [countP_gridYield_replicate_MEM (handshakePred_isAsk RW.write) m as h]
  simp [isAsk]

/-! ### Counting in the parallel proof steps -/

/-- `m` parallel proof steps take the lock `m` times and perform `r` read handshakes and `w`
write handshakes, for numbers `r ≤ 2 * m` (even) and `w ≤ bound * m` that do not depend on the
handshake predicate. -/
theorem countP_gridYield_replicate_TUPLE : ∀ (m : ℕ) (as : List (AcAct F A C)),
    (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.TUPLE]) as →
      ∃ r w, r ≤ 2 * m ∧ r % 2 = 0 ∧ w ≤ bound * m ∧ ∀ q : AcAct F A C → Bool, HandshakePred q →
        as.countP q = m * ([AcAct.lock, AcAct.unlock] : List (AcAct F A C)).countP q
          + (r * ([AcAct.ask RW.read, AcAct.waitA RW.read] : List (AcAct F A C)).countP q
            + w * ([AcAct.ask RW.write, AcAct.waitA RW.write] :
                List (AcAct F A C)).countP q) := by
  intro m
  induction m with
  | zero =>
      intro as h
      rw [gridYield_replicate_zero] at h
      subst h
      exact ⟨0, 0, le_refl 0, rfl, le_refl 0, by simp⟩
  | succ m ih =>
      intro as h
      obtain ⟨as₁, as₂, h₁, h₂, hint⟩ := (gridYield_replicate_succ isSeqTask_TUPLE).1 h
      obtain ⟨r₁, w₁, hr₁, hp₁, hw₁, e₁⟩ := countP_yieldSeq_TUPLE h₁
      obtain ⟨r₂, w₂, hr₂, hp₂, hw₂, e₂⟩ := ih as₂ h₂
      refine ⟨r₁ + r₂, w₁ + w₂, by omega, by omega,
        by rw [Nat.mul_succ, Nat.add_comm (bound * m) bound]; exact Nat.add_le_add hw₁ hw₂,
        fun q hq => ?_⟩
      rw [hint.countP q, e₁ q hq, e₂ q hq]
      ring

/-! ### The consequence of the semaphore invariant -/

section Instance

variable {Q : Instance F A C I} {tI0 : C}

/-- **No memory cell can be filled without a `WRITE` asking for it.**  If an executable action
sequence of the compiled problem interleaves a refinement of `m` parallel memory cells with
anything else, then it contains at least `m` occurrences of `ask_W`. -/
theorem card_mem_le_countP_ask_write {m : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.MEM]) as₁)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init) :
    m ≤ as.countP (isAsk RW.write) := by
  have hcount : as.countP (isAccept RW.write) = m + as₂.countP (isAccept RW.write) := by
    rw [hint.countP, countP_isAccept_write_gridYield_MEM hmem]
  have hsem := countP_accept_le_countP_ask (D' := D) (Q := Q) (tI0 := tI0) RW.write happ
  omega

/-- **In an executable plan, the memory cells, the `WRITE` tasks and the `READ` tasks are in
exact correspondence.**  If an executable action sequence of the compiled problem interleaves a
refinement of `m₁` parallel memory cells with a refinement of `m₂` parallel proof steps, then
the number of `ask_W`, `wait_W`, `ask_R` and `wait_R` actions it contains is exactly `m₁`: each
memory cell is filled by exactly one `WRITE` and read by exactly one `READ`. -/
theorem countP_handshake_eq_card_mem {m₁ m₂ : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init) :
    as.countP (isAsk RW.write) = m₁ ∧ as.countP (isWait RW.write) = m₁ ∧
      as.countP (isAsk RW.read) = m₁ ∧ as.countP (isWait RW.read) = m₁ := by
  obtain ⟨r, w, -, -, -, e⟩ := countP_gridYield_replicate_TUPLE m₂ as₂ htup
  have key : ∀ q : AcAct F A C → Bool, HandshakePred q → as.countP q =
      m₁ * ([AcAct.accept RW.write, AcAct.doneA RW.write, AcAct.accept RW.read,
          AcAct.doneA RW.read] : List (AcAct F A C)).countP q
        + (m₂ * ([AcAct.lock, AcAct.unlock] : List (AcAct F A C)).countP q
          + (r * ([AcAct.ask RW.read, AcAct.waitA RW.read] : List (AcAct F A C)).countP q
            + w * ([AcAct.ask RW.write, AcAct.waitA RW.write] :
              List (AcAct F A C)).countP q)) := by
    intro q hq
    rw [hint.countP q, countP_gridYield_replicate_MEM hq m₁ as₁ hmem, e q hq]
  have hAW : as.countP (isAsk RW.write) = w := by
    rw [key _ (handshakePred_isAsk RW.write)]; simp [isAsk]
  have hWW : as.countP (isWait RW.write) = w := by
    rw [key _ (handshakePred_isWait RW.write)]; simp [isWait]
  have hAR : as.countP (isAsk RW.read) = r := by
    rw [key _ (handshakePred_isAsk RW.read)]; simp [isAsk]
  have hWR : as.countP (isWait RW.read) = r := by
    rw [key _ (handshakePred_isWait RW.read)]; simp [isWait]
  have hCW : as.countP (isAccept RW.write) = m₁ := by
    rw [key _ (handshakePred_isAccept RW.write)]; simp [isAccept]
  have hDW : as.countP (isDone RW.write) = m₁ := by
    rw [key _ (handshakePred_isDone RW.write)]; simp [isDone]
  have hCR : as.countP (isAccept RW.read) = m₁ := by
    rw [key _ (handshakePred_isAccept RW.read)]; simp [isAccept]
  have hDR : as.countP (isDone RW.read) = m₁ := by
    rw [key _ (handshakePred_isDone RW.read)]; simp [isDone]
  have s₁ := countP_accept_le_countP_ask (D' := D) (Q := Q) (tI0 := tI0) RW.write happ
  have s₂ := countP_wait_le_countP_done (D' := D) (Q := Q) (tI0 := tI0) RW.write happ
  have s₃ := countP_accept_le_countP_ask (D' := D) (Q := Q) (tI0 := tI0) RW.read happ
  have s₄ := countP_wait_le_countP_done (D' := D) (Q := Q) (tI0 := tI0) RW.read happ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **Each proof step locks and unlocks the memory exactly once**, and the memory cells never
touch the lock, so a refinement of `m₁` memory cells interleaved with `m₂` proof steps contains
exactly `m₂` `lock` and `m₂` `unlock` actions.  (No executability assumption is needed.) -/
theorem countP_lock_eq_card_tuple {m₁ m₂ : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as) :
    as.countP isLock = m₂ ∧ as.countP isUnlock = m₂ := by
  obtain ⟨r, w, -, -, -, e⟩ := countP_gridYield_replicate_TUPLE m₂ as₂ htup
  constructor
  · rw [hint.countP, countP_gridYield_replicate_MEM handshakePred_isLock m₁ as₁ hmem,
      e _ handshakePred_isLock]
    simp [isLock]
  · rw [hint.countP, countP_gridYield_replicate_MEM handshakePred_isUnlock m₁ as₁ hmem,
      e _ handshakePred_isUnlock]
    simp [isUnlock]

/-- The read requests of an interleaving of memory cells with `m₂` proof steps all come from the
proof steps, so there is an even number of at most `2 * m₂` of them. -/
lemma exists_countP_isAsk_read_eq {m₁ m₂ : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as) :
    ∃ r ≤ 2 * m₂, r % 2 = 0 ∧ as.countP (isAsk RW.read) = r := by
  obtain ⟨r, w, hr, hpar, -, e⟩ := countP_gridYield_replicate_TUPLE m₂ as₂ htup
  refine ⟨r, hr, hpar, ?_⟩
  rw [hint.countP, countP_gridYield_replicate_MEM (handshakePred_isAsk RW.read) m₁ as₁ hmem,
    e _ (handshakePred_isAsk RW.read)]
  simp [isAsk]

/-- **An executable plan of the compiled problem fills an even number of memory cells.**  Each
proof step either reads two memory cells (the method for a compound proof tuple) or none (the
method for a base tuple), so the number of read requests is even; by
`HTN.ToAc.countP_handshake_eq_card_mem` that number is the number of memory cells. -/
theorem card_mem_even {m₁ m₂ : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init) :
    m₁ % 2 = 0 := by
  obtain ⟨r, -, hpar, hAR⟩ := exists_countP_isAsk_read_eq hmem htup hint
  have hm := (countP_handshake_eq_card_mem (Q := Q) (tI0 := tI0) hmem htup hint happ).2.2.1
  omega

/-- **An executable plan of the compiled problem fills at most two memory cells per proof
step.**  Together with `HTN.ToAc.card_mem_le_countP_ask_write` this pins the size of the memory
an executable plan can use to the number of proof steps it performs. -/
theorem card_mem_le_two_mul_card_tuple {m₁ m₂ : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m₁ [Sum.inr AcTask.MEM]) as₁)
    (htup : (domain D vars bound).GridYield (List.replicate m₂ [Sum.inr AcTask.TUPLE]) as₂)
    (hint : Interleave as₁ as₂ as)
    (happ : (problem D Q vars bound tI0).SeqApplicable as (problem D Q vars bound tI0).init) :
    m₁ ≤ 2 * m₂ := by
  obtain ⟨r, hr, -, hAR⟩ := exists_countP_isAsk_read_eq hmem htup hint
  have hm := (countP_handshake_eq_card_mem (Q := Q) (tI0 := tI0) hmem htup hint happ).2.2.1
  omega

/-- The same exact correspondence for a solution plan of the compiled problem: a plan refines
some even number `m ≤ bound` of memory cells, and then performs exactly `m` `ask_W`, `wait_W`,
`ask_R`, `wait_R`, `accept_W`, `done_W`, `accept_R` and `done_R` actions. -/
theorem exists_countP_handshake_eq_of_isSolutionPlan {as : List (AcAct F A C)}
    (h : (problem D Q vars bound tI0).IsSolutionPlan as) :
    ∃ m ≤ bound, m % 2 = 0 ∧ as.countP (isAsk RW.write) = m ∧ as.countP (isWait RW.write) = m ∧
      as.countP (isAsk RW.read) = m ∧ as.countP (isWait RW.read) = m ∧
      as.countP (isAccept RW.write) = m ∧ as.countP (isDone RW.write) = m ∧
      as.countP (isAccept RW.read) = m ∧ as.countP (isDone RW.read) = m := by
  obtain ⟨hnet, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  obtain ⟨m₁, m₂, as₁, as₂, hm₁, -, hmem, htup, hint⟩ :=
    (netYield_tnI_iff (Q := Q) (tI0 := tI0)).1 hnet
  obtain ⟨e₁, e₂, e₃, e₄⟩ := countP_handshake_eq_card_mem (Q := Q) (tI0 := tI0) hmem htup hint
    happ
  obtain ⟨r, w, -, -, -, e⟩ := countP_gridYield_replicate_TUPLE m₂ as₂ htup
  have key : ∀ q : AcAct F A C → Bool, HandshakePred q → as.countP q =
      m₁ * ([AcAct.accept RW.write, AcAct.doneA RW.write, AcAct.accept RW.read,
          AcAct.doneA RW.read] : List (AcAct F A C)).countP q
        + (m₂ * ([AcAct.lock, AcAct.unlock] : List (AcAct F A C)).countP q
          + (r * ([AcAct.ask RW.read, AcAct.waitA RW.read] : List (AcAct F A C)).countP q
            + w * ([AcAct.ask RW.write, AcAct.waitA RW.write] :
              List (AcAct F A C)).countP q)) := by
    intro q hq
    rw [hint.countP q, countP_gridYield_replicate_MEM hq m₁ as₁ hmem, e q hq]
  refine ⟨m₁, hm₁, card_mem_even (Q := Q) (tI0 := tI0) hmem htup hint happ,
    e₁, e₂, e₃, e₄, ?_, ?_, ?_, ?_⟩
  · rw [key _ (handshakePred_isAccept RW.write)]; simp [isAccept]
  · rw [key _ (handshakePred_isDone RW.write)]; simp [isDone]
  · rw [key _ (handshakePred_isAccept RW.read)]; simp [isAccept]
  · rw [key _ (handshakePred_isDone RW.read)]; simp [isDone]

/-- The same statement for a solution plan of the compiled problem. -/
theorem card_mem_le_countP_ask_write_of_isSolutionPlan {m : ℕ} {as as₁ as₂ : List (AcAct F A C)}
    (hmem : (domain D vars bound).GridYield (List.replicate m [Sum.inr AcTask.MEM]) as₁)
    (hint : Interleave as₁ as₂ as)
    (h : (problem D Q vars bound tI0).IsSolutionPlan as) :
    m ≤ as.countP (isAsk RW.write) :=
  card_mem_le_countP_ask_write (Q := Q) (tI0 := tI0) hmem hint h.classical.1

end Instance

end ToAc

end HTN
