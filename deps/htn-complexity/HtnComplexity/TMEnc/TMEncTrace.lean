import HtnComplexity.TMEnc.TMEncCount
/-!
# The Turing-machine encoding simulates a run of the machine

This file proves the *machine-state* half of the simulation argument for the encoding of
`HtnComplexity/TMEnc/TMEncoding.lean`: a plan of the encoded problem drives the fact `st q` — the
state of the machine — along a genuine run of the machine, and it must reach an accepting state.

* `HTN.TMEnc.LegalAct` — an action is legal if, being a transition action
  `step^{q,c}_{q',c'}`, it belongs to the transition relation of the machine; every action of
  every plan is legal (`HTN.TMEnc.legal_of_mem_netYield`), because the only method body
  containing transition actions is the one of the task `transition`;
* `HTN.TMEnc.StateIs` — exactly one machine state holds in the planning state; this is an
  invariant, and it moves along the machine's transition relation
  (`HTN.TMEnc.exists_stateIs_of_seqApplicable`);
* `HTN.TMEnc.countP_acceptCheck_eq_one` — every plan contains **exactly one** accepting test
  `check_{st(f)}`, the one of the task `done`, again by an additive invariant of decomposition;
* `HTN.TMEnc.exists_accepting_run_of_isSolutionPlan` — **the theorem**: if the encoded problem
  has a solution plan, then the machine has a run from its initial state to an accepting state.

This is the state-level part of the soundness direction of Theorem 4.3.7; what it does not yet
contain is the *tape* part — that the symbols the transitions read are the ones the witness
holds — which is what the `K + 1` cell counters of the construction enforce, and which needs the
lock-step analysis begun in `HtnComplexity/TMEnc/TMEncCount.lean`.
-/

namespace HTN

namespace TMEnc

open TM TaskNetwork

variable {Q Γ : Type} {N : NTM Q Γ} {w : List Γ} {K : ℕ}

/-! ### Legal actions -/

/-- An action is *legal* for the machine `N` if, in case it is a transition action, it performs
a transition of `N`. -/
def LegalAct (N : NTM Q Γ) : TMAct Q Γ → Prop
  | .step q c q' c' => ∃ (b b' : Γ) (mv : Move), c = some b ∧ c' = some b' ∧
      (q', b', mv) ∈ N.step q b
  | _ => True

/-- Reduce a membership `Sum.inl a ∈ (explicit list of chains).flatten` to the finitely many
possibilities for `a` and close the resulting legality goals. -/
local macro "legal_tac" h:ident : tactic =>
  `(tactic| (simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.mem_append, List.not_mem_nil, List.mem_replicate,
      or_false, false_or, reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at $h:ident <;>
      (try casesm* _ ∧ _, _ ∨ _) <;> subst_vars <;> trivial))

lemma legalAct_of_mem_bodies {t : TMTask Q Γ}
    {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodies N w K t)
    {a : TMAct Q Γ} (ha : Sum.inl a ∈ ls.flatten) : LegalAct N a := by
  cases t with
  | acquire y => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | release y => simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      legal_tac ha
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      legal_tac ha
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, hstep, rfl⟩ := hls
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons,
        List.mem_replicate, reduceCtorEq, Sum.inl.injEq, and_false, or_false] at ha
      subst ha
      exact ⟨c, c', mv, rfl, rfl, hstep⟩
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> legal_tac ha
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;>
        [skip; skip; skip; skip] <;>
        simp only [Set.mem_singleton_iff] at hls <;>
        (try subst hls) <;> legal_tac ha
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls; legal_tac ha
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp only [Set.mem_singleton_iff] at hls <;> subst hls <;> legal_tac ha
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, -, rfl⟩ := hls
      legal_tac ha
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp only [Set.mem_singleton_iff] at hls <;> subst hls <;> legal_tac ha
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp only [Set.mem_singleton_iff] at hls <;> subst hls <;> legal_tac ha
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

/-- **Every action of every plan of the encoded problem is legal.** -/
theorem legal_of_mem_netYield {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) : ∀ a ∈ as, LegalAct N a := by
  refine forall_mem_of_netYield (P := LegalAct N) ?_ ?_ h
  · rintro ⟨c, tn⟩ hm t ht a hα
    rcases hm with ⟨ls, hls, hsub⟩ | hm
    · simp only at hls hsub
      subst hsub
      have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) ht
      rw [show (TaskNetwork.grid ls).α t = Sum.inl a from hα] at hmem
      exact legalAct_of_mem_bodies hls hmem
    · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have hmem := TaskNetwork.gridTail_α_mem_flatten (ls := initChains K)
        (tl := [Sum.inr (TMTask.done : TMTask Q Γ)]) ht
      rw [show (TaskNetwork.gridTail (initChains K)
        [Sum.inr (TMTask.done : TMTask Q Γ)]).α t = Sum.inl a from hα] at hmem
      simp only [initChains, List.flatten_cons, List.flatten_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
        Sum.inl.injEq] at hmem
      rcases hmem with rfl | rfl <;> trivial
  · intro t ht a hα
    have hmem := TaskNetwork.grid_α_mem_flatten (ls := [[Sum.inr (TMTask.sI : TMTask Q Γ)]])
      (show t ∈ (TaskNetwork.grid [[Sum.inr (TMTask.sI : TMTask Q Γ)]]).T from ht)
    rw [show (TaskNetwork.grid [[Sum.inr (TMTask.sI : TMTask Q Γ)]]).α t = Sum.inl a from hα]
      at hmem
    simp at hmem

/-! ### The machine state of a planning state -/

/-- The planning state holds exactly the machine state `q`. -/
def StateIs (q : Q) (s : Set (TMFact Q Γ)) : Prop := ∀ p : Q, TMFact.st p ∈ s ↔ p = q

/-- One step of the machine, forgetting the tape: the machine can go from `q` to `q'` reading
some symbol. -/
def StateStep (N : NTM Q Γ) (q q' : Q) : Prop :=
  ∃ (b b' : Γ) (mv : Move), (q', b', mv) ∈ N.step q b

/-- **One action moves the machine state along the transition relation of the machine** (or
leaves it alone). -/
lemma exists_stateIs_transition {a : TMAct Q Γ} {s : Set (TMFact Q Γ)} {q : Q}
    (hq : StateIs q s) (ha : (actionModel (Q := Q) (Γ := Γ)).Applicable a s)
    (hlegal : LegalAct N a) :
    ∃ q', StateIs q' ((actionModel (Q := Q) (Γ := Γ)).transition a s) ∧
      (q' = q ∨ StateStep N q q') := by
  cases a with
  | step p c p' c' =>
      obtain ⟨b, b', mv, rfl, rfl, hstep⟩ := hlegal
      have hp : p = q := (hq p).1 (ha (by simp [actionModel, TMEnc.prec]))
      subst hp
      refine ⟨p', fun r => ?_, Or.inr ⟨b, b', mv, hstep⟩⟩
      have hdel : ((TMFact.st r : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).del (TMAct.step p (some b) p' (some b'))) ↔ r = p := by
        simp [actionModel, TMEnc.del]
      have hadd : ((TMFact.st r : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).add (TMAct.step p (some b) p' (some b'))) ↔ r = p' := by
        simp [actionModel, TMEnc.add]
      simp only [ActionModel.transition, Set.mem_union, Set.mem_diff, hdel, hadd]
      constructor
      · rintro (⟨hr, hne⟩ | hr)
        · exact absurd ((hq r).1 hr) hne
        · exact hr
      · rintro rfl
        exact Or.inr rfl
  | _ =>
      refine ⟨q, fun r => ?_, Or.inl rfl⟩
      simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
      constructor
      · rintro (⟨hr, -⟩ | hr)
        · exact (hq r).1 hr
        · simp [actionModel, TMEnc.add] at hr
      · rintro rfl
        exact Or.inl ⟨(hq r).2 rfl, by simp [actionModel, TMEnc.del]⟩

/-- **A whole executable action sequence moves the machine state along a run.** -/
theorem exists_stateIs_of_seqApplicable :
    ∀ (as : List (TMAct Q Γ)) (s : Set (TMFact Q Γ)) (q : Q), (∀ a ∈ as, LegalAct N a) →
      (actionModel (Q := Q) (Γ := Γ)).SeqApplicable as s → StateIs q s →
        ∃ q', StateIs q' ((actionModel (Q := Q) (Γ := Γ)).transitionSeq as s) ∧
          Relation.ReflTransGen (StateStep N) q q' := by
  intro as
  induction as with
  | nil => intro s q _ _ hq; exact ⟨q, hq, Relation.ReflTransGen.refl⟩
  | cons a as ih =>
      intro s q hlegal happ hq
      obtain ⟨ha, hrest⟩ := happ
      obtain ⟨q₁, hq₁, hstep⟩ :=
        exists_stateIs_transition hq ha (hlegal a (by simp))
      obtain ⟨q', hq', hreach⟩ :=
        ih _ q₁ (fun b hb => hlegal b (by simp [hb])) hrest hq₁
      refine ⟨q', hq', ?_⟩
      rcases hstep with rfl | hs
      · exact hreach
      · exact Relation.ReflTransGen.head hs hreach

/-! ### Every plan performs the accepting test exactly once -/

open scoped Classical in
/-- The accepting test `check_{st(f)}` for an accepting state `f`. -/
noncomputable def isAcceptCheck (N : NTM Q Γ) : TMAct Q Γ → Bool
  | .check (.st f) => decide (f ∈ N.accept)
  | _ => false

/-- How often the task `done` occurs in the body of a compound task. -/
def doneCount : TMTask Q Γ → ℕ
  | .cSeq u k => k * doneCount u
  | .cPar u k => k * doneCount u
  | .done => 1
  | .sI => 1
  | _ => 0

open scoped Classical in
/-- The weight counting the accepting tests. -/
noncomputable def wDone (N : NTM Q Γ) : TMAct Q Γ ⊕ TMTask Q Γ → ℤ
  | Sum.inl a => if isAcceptCheck N a = true then 1 else 0
  | Sum.inr t => (doneCount t : ℤ)

open scoped Classical in
lemma sum_wDone_bodies {t : TMTask Q Γ} {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))}
    (hls : ls ∈ bodies N w K t) : (ls.flatten.map (wDone N)).sum = wDone N (Sum.inr t) := by
  cases t with
  | acquire y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount, isAcceptCheck]
  | release y =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount, isAcceptCheck]
  | produce =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wDone, doneCount, isAcceptCheck]
  | produceSym c =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount, isAcceptCheck]
  | tapeProduce =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount]
  | waitCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount]
  | waitN i =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount]
  | chk =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨c, rfl⟩ := hls
      simp [wDone, doneCount, isAcceptCheck]
  | headCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount, isAcceptCheck]
  | noHeadCell =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount, isAcceptCheck]
  | heads =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount]
  | transition =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨q, q', c, c', mv, -, rfl⟩ := hls
      simp [wDone, doneCount, isAcceptCheck, List.map_replicate, List.sum_replicate]
  | transitionAndCheck =>
      simp only [bodies, Set.mem_insert_iff, Set.mem_singleton_iff] at hls
      rcases hls with rfl | rfl <;> simp [wDone, doneCount, isAcceptCheck]
  | checkers i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wDone, doneCount]
  | produceInit =>
      simp only [bodies, Set.mem_singleton_iff] at hls; subst hls
      simp [wDone, doneCount]
  | produceWord i =>
      simp only [bodies] at hls
      split_ifs at hls <;> simp_all [wDone, doneCount]
  | done =>
      simp only [bodies, Set.mem_setOf_eq] at hls
      obtain ⟨f, hf, rfl⟩ := hls
      simp [wDone, doneCount, isAcceptCheck, hf]
  | cSeq u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wDone, doneCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wDone, doneCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * doneCount u + k / 2 * doneCount u = k * doneCount u := by
          have hrw : k / 2 * doneCount u + k / 2 * doneCount u = (2 * (k / 2)) * doneCount u := by
            ring
          rw [hrw, hk2]
        simp only [wDone, doneCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : doneCount u + (k - 1) * doneCount u = k * doneCount u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wDone, doneCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | cPar u k =>
      simp only [bodies] at hls
      split_ifs at hls with h0 h1 he
      · subst h0; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wDone, doneCount]
      · subst h1; simp only [Set.mem_singleton_iff] at hls; subst hls
        simp [wDone, doneCount]
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk2 : 2 * (k / 2) = k := by omega
        have hk : k / 2 * doneCount u + k / 2 * doneCount u = k * doneCount u := by
          have hrw : k / 2 * doneCount u + k / 2 * doneCount u = (2 * (k / 2)) * doneCount u := by
            ring
          rw [hrw, hk2]
        simp only [wDone, doneCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
      · simp only [Set.mem_singleton_iff] at hls; subst hls
        have hk : doneCount u + (k - 1) * doneCount u = k * doneCount u := by
          obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        simp only [wDone, doneCount, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hk
  | sI => simp only [bodies, Set.mem_empty_iff_false] at hls

open scoped Classical in
/-- **The accepting-test weight is balanced.** -/
lemma balanced_wDone : Balanced (methods N w K) (wDone N) := by
  rintro ⟨c, tn⟩ hm
  rcases hm with ⟨ls, hls, hsub⟩ | hm
  · simp only at hls hsub
    subst hsub
    rw [weight_grid]
    exact sum_wDone_bodies hls
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    show weight _ (initNet K) = _
    rw [initNet, weight_gridTail]
    simp [initChains, wDone, doneCount, isAcceptCheck]

open scoped Classical in
lemma sum_map_wDone (as : List (TMAct Q Γ)) :
    (as.map fun a => wDone N (Sum.inl a)).sum = (as.countP (isAcceptCheck N) : ℤ) := by
  induction as with
  | nil => simp
  | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      by_cases h : isAcceptCheck N a = true
      · simp [wDone, h]; ring
      · simp [wDone, h]

open scoped Classical in
/-- **Every plan of the encoded problem performs exactly one accepting test.**  It is the one of
the task `done`, which the initial task network schedules after everything else. -/
theorem countP_acceptCheck_eq_one {as : List (TMAct Q Γ)}
    (h : (domain N w K).NetYield ((problem N w K).tnI) as) :
    as.countP (isAcceptCheck N) = 1 := by
  have hw := weight_of_netYield (balanced_wDone (N := N) (w := w) (K := K)) h
  rw [sum_map_wDone, weight_tnI] at hw
  simp only [wDone, doneCount, Nat.cast_one] at hw
  exact_mod_cast hw

/-! ### The machine accepts -/

lemma stateIs_init : StateIs N.init ((problem N w K).init : Set (TMFact Q Γ)) := by
  intro p
  show (TMFact.st p : TMFact Q Γ) ∈ ({TMFact.st N.init} : Set (TMFact Q Γ)) ↔ p = N.init
  simp

open scoped Classical in
/-- **The soundness of the encoding at the level of the machine states.**  If the encoded
problem has a solution plan, then the machine `N` can go from its initial state to an accepting
state, each step being a transition of `N`.

This is the state-level half of the simulation statement of Theorem 4.3.7; the tape-level half —
that the symbols read along the way are the ones written on the witness tape — is what the cell
counters of the construction enforce. -/
theorem exists_accepting_run_of_isSolutionPlan {as : List (TMAct Q Γ)}
    (h : (problem N w K).IsSolutionPlan as) :
    ∃ f ∈ N.accept, Relation.ReflTransGen (StateStep N) N.init f := by
  obtain ⟨hy, happ, -⟩ := Problem.isSolutionPlan_iff.1 h
  have hlegal := legal_of_mem_netYield hy
  -- the plan contains the accepting test
  have hcount := countP_acceptCheck_eq_one hy
  have hex : ∃ a ∈ as, isAcceptCheck N a = true := by
    by_contra hcon
    push_neg at hcon
    have : as.countP (isAcceptCheck N) = 0 :=
      List.countP_eq_zero.2 fun a ha => by simpa using hcon a ha
    omega
  obtain ⟨a, hmem, hacc⟩ := hex
  obtain ⟨pre, post, rfl⟩ : ∃ pre post, as = pre ++ a :: post := by
    obtain ⟨pre, post, h⟩ := List.append_of_mem hmem
    exact ⟨pre, post, h⟩
  -- the state at that point
  rw [ActionModel.seqApplicable_append] at happ
  obtain ⟨happre, happost⟩ := happ
  obtain ⟨ha, -⟩ := happost
  obtain ⟨q, hq, hreach⟩ :=
    exists_stateIs_of_seqApplicable (N := N) pre ((problem N w K).init) N.init
      (fun b hb => hlegal b (by simp [hb])) happre stateIs_init
  -- the accepting test forces the machine state to be accepting
  match a, hacc with
  | .check (.st f), hacc =>
      have hf : f ∈ N.accept := by simpa [isAcceptCheck] using hacc
      have hst : (TMFact.st f : TMFact Q Γ) ∈
          (actionModel (Q := Q) (Γ := Γ)).transitionSeq pre ((problem N w K).init) :=
        ha (show (TMFact.st f : TMFact Q Γ) ∈ ({TMFact.st f} : Set (TMFact Q Γ)) from rfl)
      have : f = q := (hq f).1 hst
      subst this
      exact ⟨f, hf, hreach⟩

end TMEnc

end HTN
