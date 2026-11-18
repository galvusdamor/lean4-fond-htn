import HtnComplexity.TMEnc.TMEncFixPlanAnalysis
/-!
# The refinements of one cell counter, analysed

`HtnComplexity/TMEnc/TMEncFixSchedule.lean` builds the run of one cell counter cell by cell.
This file proves the converse — the shape of **every** refinement of a cell counter — which the
soundness half of the simulation argument needs:

* `HTN.TMEnc.chainYield_waitN_forward` — a delay is a sequence of waiting cycles;
* `HTN.TMEnc.chainYield_chk_forward` — a `chk` gadget is `HTN.TMEnc.chkRun`, for one symbol:
  it tests the same symbol at the beginning and at the end of a block of `K + 1` cells;
* `HTN.TMEnc.chainYield_transitionAndCheck_iff` — a decision of a counter is either a transition
  of the machine or the test that the head is elsewhere (`HTN.TMEnc.StepDecision`);
* `HTN.TMEnc.chainYield_checkers_one_iff` — **one cell counter is exactly**
  `release check ; (decision ; chk)^K ; release sync` (`HTN.TMEnc.counterBody`);
* `HTN.TMEnc.chainYield_counterChain_iff` — with the leading and trailing delays
  (`HTN.TMEnc.counterRun`).
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork Domain

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-- A delay of `n` cells is `n` waiting cycles. -/
lemma chainYield_waitN_forward {n : ℕ} {as : List (TMAct Q Γ)}
    (h : (domainBod N w K).ChainYield [Sum.inr (TMTask.waitN n)] as) :
    as = roundStream n fun _ => waitCellActs Q Γ := by
  obtain ⟨ass, hlen, hall, rfl⟩ := chainYield_waitN_iff.1 h
  rw [flatten_eq_roundStream hlen]
  refine roundStream_congr fun r hr => ?_
  have hmem : ass.getD r [] ∈ ass := by
    have hr' : r < ass.length := by omega
    rw [show ass.getD r [] = ass[r] from List.getD_eq_getElem _ _ hr']
    exact List.getElem_mem _
  exact chainYield_waitCell_iff.1 (hall _ hmem)

/-- **A `chk` gadget has exactly the refinements `HTN.TMEnc.chkRun`**, one per symbol. -/
lemma chainYield_chk_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.chk] as ↔
      ∃ c : Option Γ, as = chkRun Q Γ K c := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ∃ c : Option Γ, ls =
        [[Sum.inl (TMAct.check (TMFact.sym c)), Sum.inr (TMTask.release SyncKind.sync),
          Sum.inr (TMTask.waitN K), Sum.inr (TMTask.release SyncKind.check),
          Sum.inl (TMAct.check (TMFact.sym c))]] := by
      simpa [bodiesFix, bodies] using hls
    obtain ⟨c, rfl⟩ := hls'
    refine ⟨c, ?_⟩
    rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
    obtain ⟨as₁, rfl, h₁⟩ := hy
    rw [show [(Sum.inr (TMTask.release SyncKind.sync) : TMAct Q Γ ⊕ TMTask Q Γ),
        Sum.inr (TMTask.waitN K), Sum.inr (TMTask.release SyncKind.check),
        Sum.inl (TMAct.check (TMFact.sym c))] =
      [(Sum.inr (TMTask.release SyncKind.sync) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        ([Sum.inr (TMTask.waitN K)] ++
          ([Sum.inr (TMTask.release SyncKind.check)] ++
            [Sum.inl (TMAct.check (TMFact.sym c))])) from rfl,
      chainYield_append_iff] at h₁
    obtain ⟨u₁, v₁, rfl, hu₁, hv₁⟩ := h₁
    rw [chainYield_append_iff] at hv₁
    obtain ⟨u₂, v₂, rfl, hu₂, hv₂⟩ := hv₁
    rw [chainYield_append_iff] at hv₂
    obtain ⟨u₃, v₃, rfl, hu₃, hv₃⟩ := hv₂
    rw [chainYield_release_iff] at hu₁ hu₃
    rw [chainYield_waitN_forward hu₂, hu₁, hu₃]
    obtain ⟨v₄, rfl, hv₄⟩ := chainYield_cons_inl_iff.1 hv₃
    rw [chainYield_nil_iff] at hv₄
    subst hv₄
    rfl
  · rintro ⟨c, rfl⟩
    exact chainYield_chk

/-- One decision of a cell counter: a transition of the machine, or the test that the head is
somewhere else. -/
def StepDecision (N : NTM Q Γ) (w : List Γ) (K : ℕ) (p : List (TMAct Q Γ)) : Prop :=
  (domainBod N w K).ChainYield [Sum.inr TMTask.transition] p ∨ p = [TMAct.check TMFact.noHead]

/-- **A step of a counter is a decision followed by a `chk` gadget.** -/
lemma chainYield_transitionAndCheck_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.transitionAndCheck] as ↔
      ∃ (p : List (TMAct Q Γ)) (c : Option Γ), StepDecision N w K p ∧ as = p ++ chkRun Q Γ K c := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = [[Sum.inr TMTask.transition, Sum.inr TMTask.chk]] ∨
        ls = [[Sum.inl (TMAct.check TMFact.noHead), Sum.inr TMTask.chk]] := by
      simpa [bodiesFix, bodies] using hls
    rcases hls' with rfl | rfl
    · rw [gridYield_singleton_iff, show [(Sum.inr TMTask.transition : TMAct Q Γ ⊕ TMTask Q Γ),
          Sum.inr TMTask.chk] = [(Sum.inr TMTask.transition : TMAct Q Γ ⊕ TMTask Q Γ)] ++
          [Sum.inr TMTask.chk] from rfl, chainYield_append_iff] at hy
      obtain ⟨p, q, rfl, hp, hq⟩ := hy
      obtain ⟨c, rfl⟩ := chainYield_chk_iff.1 hq
      exact ⟨p, c, Or.inl hp, rfl⟩
    · rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
      obtain ⟨q, rfl, hq⟩ := hy
      obtain ⟨c, rfl⟩ := chainYield_chk_iff.1 hq
      exact ⟨[TMAct.check TMFact.noHead], c, Or.inr rfl, rfl⟩
  · rintro ⟨p, c, hp, rfl⟩
    exact chainYield_transitionAndCheck hp

/-- **The body of one cell counter**: it answers the request on the `check` channel of the cell
at which it starts, then takes its `K` decisions — each followed by the `chk` gadget that
compares the symbol of the current cell with the one `K + 1` cells later — and finally answers
the request on the `sync` channel of the last cell. -/
def counterBody (Q Γ : Type) (K : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) :
    List (TMAct Q Γ) :=
  relCheckActs Q Γ ++ ((roundStream K fun t => P t ++ chkRun Q Γ K (c t)) ++ relSyncActs Q Γ)

/-- **One cell counter has exactly the refinements `HTN.TMEnc.counterBody`.** -/
theorem chainYield_checkers_one_iff {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr (TMTask.checkers 1)] as ↔
      ∃ (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ),
        (∀ t < K, StepDecision N w K (P t)) ∧ as = counterBody Q Γ K P c := by
  classical
  have hchain : [(Sum.inr (TMTask.release SyncKind.check) : TMAct Q Γ ⊕ TMTask Q Γ),
      Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K), Sum.inr (TMTask.release SyncKind.sync)] =
    [(Sum.inr (TMTask.release SyncKind.check) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
      ([Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K)] ++
        [Sum.inr (TMTask.release SyncKind.sync)]) := rfl
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ls = checkerBodyFix (Q := Q) (Γ := Γ) K := by
      rw [bodiesFix_checkers_one, Set.mem_singleton_iff] at hls
      exact hls
    subst hls'
    rw [show checkerBodyFix (Q := Q) (Γ := Γ) K =
      [[Sum.inr (TMTask.release SyncKind.check),
        Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K),
        Sum.inr (TMTask.release SyncKind.sync)]] from rfl, gridYield_singleton_iff, hchain,
      chainYield_append_iff] at hy
    obtain ⟨u, v, rfl, hu, hv⟩ := hy
    rw [chainYield_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
    rw [chainYield_release_iff] at hu hv₂
    obtain ⟨seg, hall, rfl⟩ := chainYield_cSeq_rounds_iff.1 hv₁
    have hex : ∀ t : ℕ, ∃ pc : List (TMAct Q Γ) × Option Γ, t < K →
        (StepDecision N w K pc.1 ∧ seg t = pc.1 ++ chkRun Q Γ K pc.2) := by
      intro t
      by_cases ht : t < K
      · obtain ⟨p, c, hp, hseg⟩ := chainYield_transitionAndCheck_iff.1 (hall t ht)
        exact ⟨(p, c), fun _ => ⟨hp, hseg⟩⟩
      · exact ⟨([TMAct.check TMFact.noHead], none), fun ht' => absurd ht' ht⟩
    choose pc hpc using hex
    refine ⟨fun t => (pc t).1, fun t => (pc t).2, fun t ht => (hpc t ht).1, ?_⟩
    rw [hu, hv₂]
    simp only [counterBody, relCheckActs, relSyncActs]
    congr 2
    exact roundStream_congr fun t ht => (hpc t ht).2
  · rintro ⟨P, c, hP, rfl⟩
    rw [chainYield_singleton_bod_iff]
    refine ⟨checkerBodyFix (Q := Q) (Γ := Γ) K, by rw [bodiesFix_checkers_one]; rfl, ?_⟩
    rw [show checkerBodyFix (Q := Q) (Γ := Γ) K =
      [[Sum.inr (TMTask.release SyncKind.check),
        Sum.inr (TMTask.cSeq TMTask.transitionAndCheck K),
        Sum.inr (TMTask.release SyncKind.sync)]] from rfl, gridYield_singleton_iff, hchain]
    refine chainYield_app (chainYield_release_iff.2 rfl)
      (chainYield_app (chainYield_cSeq_rounds ?_) (chainYield_release_iff.2 rfl))
    intro t ht
    exact chainYield_transitionAndCheck_iff.2 ⟨P t, c t, hP t ht, rfl⟩

/-- **The run of one cell counter**: the leading delay, the body, and the trailing delay. -/
def counterRun (Q Γ : Type) (K d e : ℕ) (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ) :
    List (TMAct Q Γ) :=
  (roundStream d fun _ => waitCellActs Q Γ) ++
    (counterBody Q Γ K P c ++ roundStream e fun _ => waitCellActs Q Γ)

/-- **A cell counter with delays `(d, e)` has exactly the refinements
`HTN.TMEnc.counterRun`.** -/
theorem chainYield_counterChain_iff {d e : ℕ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield (counterChain Q Γ d e) as ↔
      ∃ (P : ℕ → List (TMAct Q Γ)) (c : ℕ → Option Γ),
        (∀ t < K, StepDecision N w K (P t)) ∧ as = counterRun Q Γ K d e P c := by
  have hchain : counterChain Q Γ d e =
      [(Sum.inr (TMTask.waitN d) : TMAct Q Γ ⊕ TMTask Q Γ)] ++
        ([Sum.inr (TMTask.checkers 1)] ++ [Sum.inr (TMTask.waitN e)]) := rfl
  rw [hchain, chainYield_append_iff]
  constructor
  · rintro ⟨u, v, rfl, hu, hv⟩
    rw [chainYield_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
    obtain ⟨P, c, hP, rfl⟩ := chainYield_checkers_one_iff.1 hv₁
    exact ⟨P, c, hP, by rw [chainYield_waitN_forward hu, chainYield_waitN_forward hv₂]; rfl⟩
  · rintro ⟨P, c, hP, rfl⟩
    refine ⟨_, _, rfl, chainYield_waitN_waits, chainYield_append_iff.2 ?_⟩
    exact ⟨_, _, rfl, chainYield_checkers_one_iff.2 ⟨P, c, hP, rfl⟩, chainYield_waitN_waits⟩

/-! ### The structure of a solution plan, with the counters made explicit -/

/-- Every cell counter of a plan runs the explicit `HTN.TMEnc.counterRun`. -/
lemma counterRuns_explicit {ps : List (ℕ × ℕ)} {ass : List (List (TMAct Q Γ))}
    (h : CounterRuns N w K ps ass) :
    List.Forall₂ (fun (p : ℕ × ℕ) (l : List (TMAct Q Γ)) => ∃ P c,
      (∀ t < K, StepDecision N w K (P t)) ∧ l = counterRun Q Γ K p.1 p.2 P c) ps ass :=
  h.imp fun _ _ hp => chainYield_counterChain_iff.1 hp

/-- **The syntactic normal form of a solution plan of the repaired encoding.**  This is
`HTN.TMEnc.isSolutionPlanFix_structure` with the runs of the cell counters written out: the plan
interleaves the rigid stream of units of the head counter, `K + 1` cell counters with delays
`(j, K - j)` each of which answers one `check` and one `sync` request per cell and takes `K`
decisions, and the `(K+1)²` cells of a space-time diagram; it ends with one accepting test. -/
theorem isSolutionPlanFix_normalForm (hw : 1 ≤ w.length) (hwK : w.length ≤ K)
    {as : List (TMAct Q Γ)} (h : (problemFix N w K).IsSolutionPlan as) :
    ∃ (sym : ℕ → Option Γ) (ps : List (ℕ × ℕ)) (ass : List (List (TMAct Q Γ)))
      (ac bs as₁ : List (TMAct Q Γ)) (f : Q),
      (∀ j ≤ K, sym j = tapeInitSym N w j) ∧
      (∀ i ≤ K, sym (i * (K + 1)) = none) ∧
      ps.Perm ((List.range (K + 1)).map fun j => (j, K - j)) ∧
      List.Forall₂ (fun (p : ℕ × ℕ) (l : List (TMAct Q Γ)) => ∃ P c,
        (∀ t < K, StepDecision N w K (P t)) ∧ l = counterRun Q Γ K p.1 p.2 P c) ps ass ∧
      InterleaveList ass ac ∧
      Interleave ac (roundStream ((K + 1) * (K + 1)) fun n => cellRun Q Γ K (sym n)) bs ∧
      Interleave (headStream Q Γ K) bs as₁ ∧
      f ∈ N.accept ∧ as = as₁ ++ [TMAct.check (TMFact.st f)] ∧
      (problemFix N w K).SeqApplicable (as₁ ++ [TMAct.check (TMFact.st f)])
        (problemFix N w K).init := by
  obtain ⟨sym, ps, ass, ac, bs, as₁, f, hinit, hsep, hperm, hruns, hil, hint', hint, hf, rfl,
    happ⟩ := isSolutionPlanFix_structure hw hwK h
  exact ⟨sym, ps, ass, ac, bs, as₁, f, hinit, hsep, hperm, counterRuns_explicit hruns, hil,
    hint', hint, hf, rfl, happ⟩

/-! ### The decisions of a counter are transitions of the machine -/

/-- A chain of `k` requests on the channel `x` refines only into `k` requests. -/
lemma chainYield_replicate_acquire_iff {x : SyncKind} {k : ℕ} {as : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield (List.replicate k (Sum.inr (TMTask.acquire x))) as ↔
      as = roundStream k fun _ => acquireActs Q Γ x := by
  induction k generalizing as with
  | zero => simp
  | succ k ih =>
      have hsplit : (roundStream (k + 1) fun _ => acquireActs Q Γ x) =
          acquireActs Q Γ x ++ roundStream k fun _ => acquireActs Q Γ x := by
        have h := roundStream_add 1 k fun _ => acquireActs Q Γ x
        rw [show 1 + k = k + 1 by omega] at h
        rw [h, roundStream_one]
      rw [show List.replicate (k + 1) (Sum.inr (TMTask.acquire x) : TMAct Q Γ ⊕ TMTask Q Γ) =
        [Sum.inr (TMTask.acquire x)] ++ List.replicate k (Sum.inr (TMTask.acquire x)) from rfl,
        chainYield_append_iff, hsplit]
      constructor
      · rintro ⟨u, v, rfl, hu, hv⟩
        rw [chainYield_acquire_iff.1 hu, ih.1 hv]
      · rintro rfl
        exact ⟨_, _, rfl, chainYield_acquire_iff.2 rfl, ih.2 rfl⟩

/-- **A decision that is not the test `check noHead` is a transition of the machine**: it
performs the action `step q c q' c'` for a transition `(q', c', m) ∈ δ(q, c)` of `N` and then
issues the `moveExtra m` extra requests to the head counter that realise the head movement. -/
theorem chainYield_transition_iff {p : List (TMAct Q Γ)} :
    (domainBod N w K).ChainYield [Sum.inr TMTask.transition] p ↔
      ∃ (q q' : Q) (c c' : Γ) (m : Move), (q', c', m) ∈ N.step q c ∧
        p = TMAct.step q (some c) q' (some c') ::
          roundStream (moveExtra m) fun _ => acquireActs Q Γ SyncKind.head := by
  constructor
  · intro h
    rw [chainYield_singleton_bod_iff] at h
    obtain ⟨ls, hls, hy⟩ := h
    have hls' : ∃ (q q' : Q) (c c' : Γ) (m : Move), (q', c', m) ∈ N.step q c ∧
        ls = [Sum.inl (TMAct.step q (some c) q' (some c')) ::
          List.replicate (moveExtra m) (Sum.inr (TMTask.acquire SyncKind.head))] := by
      simpa [bodiesFix, bodies] using hls
    obtain ⟨q, q', c, c', m, hstep, rfl⟩ := hls'
    rw [gridYield_singleton_iff, chainYield_cons_inl_iff] at hy
    obtain ⟨p', rfl, hp'⟩ := hy
    exact ⟨q, q', c, c', m, hstep, by rw [chainYield_replicate_acquire_iff.1 hp']⟩
  · rintro ⟨q, q', c, c', m, hstep, rfl⟩
    rw [chainYield_singleton_bod_iff]
    refine ⟨[Sum.inl (TMAct.step q (some c) q' (some c')) ::
      List.replicate (moveExtra m) (Sum.inr (TMTask.acquire SyncKind.head))], ?_,
      gridYield_singleton_iff.2 (chainYield_cons_inl_iff.2 ⟨_, rfl,
        chainYield_replicate_acquire_iff.2 rfl⟩)⟩
    have : [Sum.inl (TMAct.step q (some c) q' (some c')) ::
        List.replicate (moveExtra m) (Sum.inr (TMTask.acquire SyncKind.head))] ∈
        bodies N w K (TMTask.transition : TMTask Q Γ) := ⟨q, q', c, c', m, hstep, rfl⟩
    simpa [bodiesFix] using this

/-- **Every decision of a cell counter is a transition of the machine or the test that the head
is elsewhere.**  This is `HTN.TMEnc.StepDecision` written out. -/
theorem stepDecision_iff {p : List (TMAct Q Γ)} :
    StepDecision N w K p ↔
      (∃ (q q' : Q) (c c' : Γ) (m : Move), (q', c', m) ∈ N.step q c ∧
        p = TMAct.step q (some c) q' (some c') ::
          roundStream (moveExtra m) fun _ => acquireActs Q Γ SyncKind.head) ∨
      p = [TMAct.check TMFact.noHead] := by
  rw [StepDecision, chainYield_transition_iff]

end TMEnc

end HTN
