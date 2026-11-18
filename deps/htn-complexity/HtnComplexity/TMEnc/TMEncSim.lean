import HtnComplexity.TMEnc.TMEncTrace
import HtnComplexity.TMEnc.Correct
/-!
# Simulation correctness of the Turing-machine encoding

The encoding of `HtnComplexity/TMEnc/TMEncoding.lean` is *simulation correct* if the encoded
problem is solvable exactly when the machine accepts; this is the property
`HTN.EncodingCorrect` used (as an explicit hypothesis) in
`HtnCompilability/TMEnc/NonCompilability.lean`.

This file **packages** that property and proves the parts of it that are available.

## Packaging

* `HTN.TMEnc.EncodingSound` — a solution plan of the encoded problem witnesses an accepting run
  of the machine within `K` steps;
* `HTN.TMEnc.EncodingComplete` — the converse;
* `HTN.encodingCorrect_of_sound_complete` — the two halves, at the exponential time bound,
  give `HTN.EncodingCorrect`.

## Proved consequences of solvability

The following are *necessary conditions* on a plan of the encoded problem; each is the
counterpart of one of the claims that the informal correctness argument of Theorem 4.3.7 makes
about a solution.

* `HTN.TMEnc.exists_accepting_run_of_isSolutionPlan` (in
  `HtnComplexity/TMEnc/TMEncTrace.lean`) — the fact `st q` travels along a genuine run of the
  machine and reaches an accepting state;
* `HTN.TMEnc.countP_assert_eq` and `HTN.TMEnc.countP_assert_eq_sq` — **every plan writes
  exactly `(K+1)²` tape symbols**, i.e. the witness `W = #w₀#w₁…#w_K` consists of `K + 1`
  tapes of `K + 1` cells each;
* `HTN.TMEnc.countP_call_eq_countP_wait`, `HTN.TMEnc.countP_respond_eq_countP_start`,
  `HTN.TMEnc.countP_sync_eq_of_isSolutionPlan` (in `HtnComplexity/TMEnc/TMEncCount.lean`) — the
  processes of the construction run in lock step;
* `HTN.TMEnc.countP_assertHead_eq` — **every plan places the head exactly `K + 1` times**, once
  on each tape of the witness;
* `HTN.TMEnc.countP_examine_eq` — **every plan performs exactly `K(K+1)` cell examinations**:
  each of the `K + 1` cell counters, for each of the `K` tape-to-tape transitions, either
  applies a machine transition or tests that the head is absent;
* `HTN.TMEnc.symUnique_transitionSeq` — at every point of a plan at most one tape symbol
  holds, so the fact `sym c` really is *the* content of the cell currently produced;
* `HTN.TMEnc.headUnique_of_plan` — at every point of a plan the complementary facts `head` and
  `noHead` do not both hold.

What is **not** proved is the identification of the plan with a *history* of the machine: that
needs, on top of the above, the tape-level argument in which the `K + 1` cell counters force
the symbol read by a transition to be the one written `K + 1` cells earlier.  Consequently
`HTN.TMEnc.EncodingSound` and `HTN.TMEnc.EncodingComplete` are not proved here.

In fact `HTN.TMEnc.EncodingComplete` is **false** for the construction as printed in the source:
`HtnComplexity/TMEnc/TMEncCheck.lean` proves that the encoded problem has no solution plan at all,
because the cell counters offer more synchronisation steps than the tape has cells.  See that
file and `NOTES.md` for the counting argument and for what has to be repaired.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The two halves of simulation correctness -/

/-- **Soundness of the encoding**: a solution of the encoded problem witnesses an accepting run
of the machine of at most `K` steps. -/
def EncodingSound (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  (problem N w K).Solvable → N.AcceptsWithin w K

/-- **Completeness of the encoding**: an accepting run of at most `K` steps can be written out
as a solution of the encoded problem. -/
def EncodingComplete (N : NTM Q Γ) (w : List Γ) (K : ℕ) : Prop :=
  N.AcceptsWithin w K → (problem N w K).Solvable

end TMEnc

/-- **Simulation correctness is exactly soundness plus completeness** at the exponential time
bound. -/
theorem encodingCorrect_iff_sound_complete {Q Γ : Type} (N : TM.NTM Q Γ) (p : Polynomial ℕ) :
    EncodingCorrect N p ↔
      ∀ w : List Γ, TMEnc.EncodingSound N w (2 ^ p.eval w.length) ∧
        TMEnc.EncodingComplete N w (2 ^ p.eval w.length) := by
  constructor
  · intro h w
    exact ⟨(h w).1, (h w).2⟩
  · intro h w
    exact ⟨(h w).1, (h w).2⟩

/-- The two halves of simulation correctness give `HTN.EncodingCorrect`. -/
theorem encodingCorrect_of_sound_complete {Q Γ : Type} {N : TM.NTM Q Γ} {p : Polynomial ℕ}
    (hs : ∀ w : List Γ, TMEnc.EncodingSound N w (2 ^ p.eval w.length))
    (hc : ∀ w : List Γ, TMEnc.EncodingComplete N w (2 ^ p.eval w.length)) :
    EncodingCorrect N p :=
  (encodingCorrect_iff_sound_complete N p).2 fun w => ⟨hs w, hc w⟩

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### The length of the witness

Every plan of the encoded problem performs exactly `(K+1)²` write actions `assert c`: the
witness `W = #w₀#w₁…#w_K` is made of `K + 1` tapes of `K + 1` cells.  Like the other counting
statements about the encoding this is proved by an additive invariant of decomposition
(`HTN.Balanced`), not along the plan. -/

/-- The write actions. -/
def isAssert : TMAct Q Γ → Bool
  | .assert _ => true
  | _ => false

/-- How many write actions the full expansion of a compound task performs. -/
def assertCount (w : List Γ) (K : ℕ) : TMTask Q Γ → ℕ
  | .produce => 1
  | .produceSym _ => 1
  | .tapeProduce => 1 + K
  | .produceInit => 1 + max w.length 1 + (K - w.length)
  | .produceWord i => max (w.length - i) 1
  | .cSeq t k => k * assertCount w K t
  | .cPar t k => k * assertCount w K t
  | .sI => (1 + max w.length 1 + (K - w.length)) + K * (1 + K)
  | _ => 0

/-- The weight counting the write actions. -/
def wAssert (w : List Γ) (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isAssert a then 1 else 0
  | Sum.inr t => (assertCount w K t : ℤ)

lemma sum_wAssert_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wAssert w K)).sum = wAssert w K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount, isAssert]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount, isAssert]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wAssert, assertCount, isAssert]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount, isAssert]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wAssert, assertCount, isAssert]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount, isAssert]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount, isAssert]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wAssert, assertCount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wAssert, assertCount, isAssert, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wAssert, assertCount, isAssert]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wAssert, assertCount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.sub_zero, mul_one]
      push_cast
      ring
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls with hlt
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 + max (w.length - (i + 1)) 1 = max (w.length - i) 1 := by omega
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : 1 = max (w.length - i) 1 := by omega
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wAssert, assertCount, isAssert]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAssert, assertCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAssert, assertCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * assertCount w K u + k / 2 * assertCount w K u =
            k * assertCount w K u := by
          have hrw : k / 2 * assertCount w K u + k / 2 * assertCount w K u =
              (2 * (k / 2)) * assertCount w K u := by ring
          rw [hrw, hk2]
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : assertCount w K u + (k - 1) * assertCount w K u = k * assertCount w K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAssert, assertCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wAssert, assertCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * assertCount w K u + k / 2 * assertCount w K u =
            k * assertCount w K u := by
          have hrw : k / 2 * assertCount w K u + k / 2 * assertCount w K u =
              (2 * (k / 2)) * assertCount w K u := by ring
          rw [hrw, hk2]
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : assertCount w K u + (k - 1) * assertCount w K u = k * assertCount w K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wAssert, assertCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The write weight is balanced.** -/
lemma balanced_wAssert : Balanced (methods N w K) (wAssert (Q := Q) w K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wAssert_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wAssert, assertCount, isAssert]

lemma sum_map_wAssert (as : List (TMAct Q Γ)) :
    (as.map fun a => wAssert (Q := Q) w K (Sum.inl a)).sum = (as.countP isAssert : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isAssert a = true
      · simp [wAssert, h]; ring
      · simp [wAssert, h]

/-- **Every plan of the encoded problem writes exactly `1 + max |w| 1 + (K - |w|) + K(K+1)`
tape symbols.** -/
theorem countP_assert_eq {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP isAssert = (1 + max w.length 1 + (K - w.length)) + K * (1 + K) := by
  have hw := weight_of_netYield (balanced_wAssert (N := N) (w := w) (K := K)) h
  rw [sum_map_wAssert, weight_tnI] at hw
  simp only [wAssert, assertCount] at hw
  exact_mod_cast hw

/-- **The witness has `(K+1)²` cells.**  For a nonempty input that fits into the time bound,
every plan of the encoded problem performs exactly `(K+1)²` write actions: the witness
`W = #w₀#w₁…#w_K` consists of `K + 1` tapes of `K + 1` cells each. -/
theorem countP_assert_eq_sq (hw0 : w ≠ []) (hwK : w.length ≤ K) {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP isAssert = (K + 1) ^ 2 := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw0
  rw [countP_assert_eq h]
  have : max w.length 1 = w.length := by omega
  rw [this]
  ring_nf
  omega

/-! ### At most one tape symbol at a time

The fact `sym c` is the content of the tape cell the encoding is currently producing.  At most
one of these facts holds at any point of a plan: the writes `assert c` delete every other
symbol, and the transitions `step^{q,c}_{q',c'}` replace the symbol they read. -/

/-- At most one symbol fact holds. -/
def SymUnique (s : Set (TMFact Q Γ)) : Prop :=
  ∀ c d : Option Γ, TMFact.sym c ∈ s → TMFact.sym d ∈ s → c = d

/-- **One action preserves the uniqueness of the symbol.** -/
lemma symUnique_transition {a : TMAct Q Γ} {s : Set (TMFact Q Γ)}
    (ha : (actionModel (Q := Q) (Γ := Γ)).Applicable a s) (hs : SymUnique s) :
    SymUnique ((actionModel (Q := Q) (Γ := Γ)).transition a s) := by
  cases a with
  | assert e =>
      intro c d hc hd
      have key : ∀ x : Option Γ, (TMFact.sym x : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transition (TMAct.assert e) s → x = e := by
        intro x hx
        rcases hx with ⟨hmem, hnd⟩ | hadd
        · by_contra hne
          exact hnd ⟨x, rfl, hne⟩
        · have : (TMFact.sym x : TMFact Q Γ) ∈ ({TMFact.sym e} : Set (TMFact Q Γ)) := hadd
          simpa using this
      rw [key c hc, key d hd]
  | step q e q' e' =>
      have hsym : (TMFact.sym e : TMFact Q Γ) ∈ s := ha (by
        show (TMFact.sym e : TMFact Q Γ) ∈
          ({TMFact.head, TMFact.sym e, TMFact.st q} : Set (TMFact Q Γ))
        simp)
      intro c d hc hd
      have key : ∀ x : Option Γ, (TMFact.sym x : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transition (TMAct.step q e q' e') s → x = e' := by
        intro x hx
        rcases hx with ⟨hmem, hnd⟩ | hadd
        · exfalso
          have : x = e := hs x e hmem hsym
          subst this
          exact hnd (by
            show (TMFact.sym x : TMFact Q Γ) ∈
              ({TMFact.sym x, TMFact.st q} : Set (TMFact Q Γ))
            simp)
        · have : (TMFact.sym x : TMFact Q Γ) ∈
              ({TMFact.sym e', TMFact.st q'} : Set (TMFact Q Γ)) := hadd
          simpa using this
      rw [key c hc, key d hd]
  | _ =>
      intro c d hc hd
      refine hs c d ?_ ?_ <;>
        [rcases hc with ⟨h, -⟩ | h; rcases hd with ⟨h, -⟩ | h] <;>
        first
          | exact h
          | (exfalso; revert h; simp [actionModel, TMEnc.add])

/-- **A whole executable action sequence preserves the uniqueness of the symbol.** -/
lemma symUnique_transitionSeq : ∀ (as : List (TMAct Q Γ)) (s : Set (TMFact Q Γ)),
    (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s → SymUnique s →
      SymUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as s) := by
  intro as
  induction as with
  | nil => intro s _ hs; exact hs
  | cons a as ih =>
      intro s happ hs
      obtain ⟨ha, hrest⟩ := happ
      exact ih _ hrest (symUnique_transition ha hs)

/-- The initial state of the encoded problem holds no symbol at all. -/
lemma symUnique_init : SymUnique ((problem N w K).init : Set (TMFact Q Γ)) := by
  intro c d hc _
  exact absurd hc (by simp [problem, Domain.mkProblem, instance_])

/-- **At every point of a plan at most one tape symbol holds.** -/
theorem symUnique_of_seqApplicable {as : List (TMAct Q Γ)}
    (h : (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as ((problem N w K).init)) :
    SymUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as ((problem N w K).init)) :=
  symUnique_transitionSeq as _ h symUnique_init

/-! ### The head is placed exactly once per tape

The head counter of the construction runs through the `(K+1)²` cells of the witness and asserts
the fact `head` in exactly one cell of each of the `K + 1` tapes.  Accordingly every plan
performs exactly `K + 1` actions `assert_head`. -/

/-- The action `assert_head`. -/
def isAssertHead : TMAct Q Γ → Bool
  | .assertHead => true
  | _ => false

/-- How many head placements the full expansion of a compound task performs. -/
def headCount (K : ℕ) : TMTask Q Γ → ℕ
  | .headCell => 1
  | .heads => 1
  | .cSeq t k => k * headCount K t
  | .cPar t k => k * headCount K t
  | .sI => 1 + K
  | _ => 0

/-- The weight counting the head placements. -/
def wHead (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isAssertHead a then 1 else 0
  | Sum.inr t => (headCount K t : ℤ)

lemma sum_wHead_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wHead K)).sum = wHead K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount, isAssertHead]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount, isAssertHead]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wHead, headCount, isAssertHead]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount, isAssertHead]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wHead, headCount, isAssertHead]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount, isAssertHead]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount, isAssertHead]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wHead, headCount, isAssertHead, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wHead, headCount, isAssertHead]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wHead, headCount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wHead, headCount]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wHead, headCount]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wHead, headCount, isAssertHead]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wHead, headCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wHead, headCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * headCount K u + k / 2 * headCount K u = k * headCount K u := by
          have hrw : k / 2 * headCount K u + k / 2 * headCount K u =
              (2 * (k / 2)) * headCount K u := by ring
          rw [hrw, hk2]
        simp only [wHead, headCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : headCount K u + (k - 1) * headCount K u = k * headCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wHead, headCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wHead, headCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wHead, headCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * headCount K u + k / 2 * headCount K u = k * headCount K u := by
          have hrw : k / 2 * headCount K u + k / 2 * headCount K u =
              (2 * (k / 2)) * headCount K u := by ring
          rw [hrw, hk2]
        simp only [wHead, headCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : headCount K u + (k - 1) * headCount K u = k * headCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wHead, headCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The head-placement weight is balanced.** -/
lemma balanced_wHead : Balanced (methods N w K) (wHead (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wHead_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wHead, headCount, isAssertHead]

lemma sum_map_wHead (as : List (TMAct Q Γ)) :
    (as.map fun a => wHead (Q := Q) (Γ := Γ) K (Sum.inl a)).sum =
      (as.countP isAssertHead : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isAssertHead a = true
      · simp [wHead, h]; ring
      · simp [wHead, h]

/-- **Every plan places the head exactly `K + 1` times** — once on each of the `K + 1` tapes of
the witness. -/
theorem countP_assertHead_eq {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP isAssertHead = K + 1 := by
  have hw := weight_of_netYield (balanced_wHead (N := N) (w := w) (K := K)) h
  rw [sum_map_wHead, weight_tnI] at hw
  simp only [wHead, headCount] at hw
  have hw' : as.countP isAssertHead = 1 + K := by exact_mod_cast hw
  omega

/-! ### The head flag is consistent

`head` and `noHead` are complementary and only the actions `assert_head` and `retract_head`
change them; at every point of a plan at most one of the two holds. -/

/-- At most one of `head`, `noHead` holds. -/
def HeadUnique (s : Set (TMFact Q Γ)) : Prop :=
  ¬ ((TMFact.head : TMFact Q Γ) ∈ s ∧ (TMFact.noHead : TMFact Q Γ) ∈ s)

lemma headUnique_transition {a : TMAct Q Γ} {s : Set (TMFact Q Γ)} (hs : HeadUnique s) :
    HeadUnique ((actionModel (Q := Q) (Γ := Γ)).transition a s) := by
  cases a with
  | assertHead =>
      rintro ⟨-, hn⟩
      rcases hn with ⟨-, hnd⟩ | hn
      · exact hnd (show (TMFact.noHead : TMFact Q Γ) ∈
          ({TMFact.noHead} : Set (TMFact Q Γ)) from rfl)
      · exact absurd (show (TMFact.noHead : TMFact Q Γ) ∈
          ({TMFact.head} : Set (TMFact Q Γ)) from hn) (by simp)
  | retractHead =>
      rintro ⟨hh, -⟩
      rcases hh with ⟨-, hnd⟩ | hh
      · exact hnd (show (TMFact.head : TMFact Q Γ) ∈
          ({TMFact.head} : Set (TMFact Q Γ)) from rfl)
      · exact absurd (show (TMFact.head : TMFact Q Γ) ∈
          ({TMFact.noHead} : Set (TMFact Q Γ)) from hh) (by simp)
  | _ =>
      rintro ⟨hh, hn⟩
      refine hs ⟨?_, ?_⟩
      · rcases hh with ⟨h, -⟩ | h
        · exact h
        · exact absurd h (by simp [actionModel, TMEnc.add])
      · rcases hn with ⟨h, -⟩ | h
        · exact h
        · exact absurd h (by simp [actionModel, TMEnc.add])

lemma headUnique_transitionSeq : ∀ (as : List (TMAct Q Γ)) (s : Set (TMFact Q Γ)),
    HeadUnique s → HeadUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as s) := by
  intro as
  induction as with
  | nil => intro s hs; exact hs
  | cons a as ih => intro s hs; exact ih _ (headUnique_transition hs)

lemma headUnique_init : HeadUnique ((problem N w K).init : Set (TMFact Q Γ)) := by
  rintro ⟨hh, -⟩
  exact absurd hh (by simp [problem, Domain.mkProblem, instance_])

/-- **At every point of a plan the head flag is consistent.** -/
theorem headUnique_of_plan (as : List (TMAct Q Γ)) :
    HeadUnique ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as ((problem N w K).init)) :=
  headUnique_transitionSeq as _ headUnique_init

/-! ### Each cell counter examines its cell once per tape transition

The `K + 1` cell counters run through the tapes together with the head counter.  For each of
the `K` transitions from a tape to the next, each of the `K + 1` counters performs one
`transitionAndCheck`, and this is either a machine transition `step^{q,c}_{q',c'}` — the head
is at the cell — or the test `check_{noHead}` — it is not.  So every plan performs exactly
`K(K+1)` actions of these two kinds together. -/

/-- A machine transition, or the test that the head is absent. -/
def isStepOrNoHead : TMAct Q Γ → Bool
  | .step _ _ _ _ => true
  | .check .noHead => true
  | _ => false

/-- How many cell examinations the full expansion of a compound task performs. -/
def examineCount (K : ℕ) : TMTask Q Γ → ℕ
  | .transition => 1
  | .transitionAndCheck => 1
  | .checkers i => i * K
  | .cSeq t k => k * examineCount K t
  | .cPar t k => k * examineCount K t
  | .sI => (K + 1) * K
  | _ => 0

/-- The weight counting the cell examinations. -/
def wExamine (K : ℕ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isStepOrNoHead a then 1 else 0
  | Sum.inr t => (examineCount K t : ℤ)

lemma sum_wExamine_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) :
    (ls.flatten.map (wExamine K)).sum = wExamine K (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wExamine, examineCount, isStepOrNoHead, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wExamine, examineCount, isStepOrNoHead]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (i / 2) = i := by omega
        have hk : i / 2 * K + i / 2 * K = i * K := by
          have hrw : i / 2 * K + i / 2 * K = (2 * (i / 2)) * K := by ring
          rw [hrw, hk2]
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, mul_zero, add_zero]
        have hcast := congrArg (fun n : ℕ => (n : ℤ)) hk
        push_cast at hcast ⊢
        linarith
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : (i - 1) * K + 1 * K = i * K := by
          obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, mul_zero, add_zero]
        have hcast := congrArg (fun n : ℕ => (n : ℤ)) hk
        push_cast at hcast ⊢
        linarith
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wExamine, examineCount]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wExamine, examineCount]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      simp [wExamine, examineCount, isStepOrNoHead]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * examineCount K u + k / 2 * examineCount K u =
            k * examineCount K u := by
          have hrw : k / 2 * examineCount K u + k / 2 * examineCount K u =
              (2 * (k / 2)) * examineCount K u := by ring
          rw [hrw, hk2]
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : examineCount K u + (k - 1) * examineCount K u = k * examineCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wExamine, examineCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * examineCount K u + k / 2 * examineCount K u =
            k * examineCount K u := by
          have hrw : k / 2 * examineCount K u + k / 2 * examineCount K u =
              (2 * (k / 2)) * examineCount K u := by ring
          rw [hrw, hk2]
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : examineCount K u + (k - 1) * examineCount K u = k * examineCount K u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wExamine, examineCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **The examination weight is balanced.** -/
lemma balanced_wExamine : Balanced (methods N w K) (wExamine (Q := Q) (Γ := Γ) K) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wExamine_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wExamine, examineCount, isStepOrNoHead]

lemma sum_map_wExamine (as : List (TMAct Q Γ)) :
    (as.map fun a => wExamine (Q := Q) (Γ := Γ) K (Sum.inl a)).sum =
      (as.countP isStepOrNoHead : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isStepOrNoHead a = true
      · simp [wExamine, h]; ring
      · simp [wExamine, h]

/-- **Every plan examines the cells exactly `K(K+1)` times**: each of the `K + 1` cell counters
performs, for each of the `K` tape-to-tape transitions, either a machine transition (the head
is at its cell) or the test `check_{noHead}` (it is not). -/
theorem countP_examine_eq {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP isStepOrNoHead = (K + 1) * K := by
  have hw := weight_of_netYield (balanced_wExamine (N := N) (w := w) (K := K)) h
  rw [sum_map_wExamine, weight_tnI] at hw
  simp only [wExamine, examineCount] at hw
  exact_mod_cast hw

end TMEnc

end HTN
