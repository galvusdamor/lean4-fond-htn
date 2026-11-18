import HtnComplexity.Computable.AcFreeRow
/-!
# The verification phase of the vocabulary-free wrapper

The compound task `tPost` of `HtnComplexity/Computable/AcFreeWrap.lean` decomposes into the
chain of one **check** task `tChk v` and one **earn** task `tEarn v` per fact `v` of the
vocabulary.  This file computes what that phase does:

> `HTN.Syn.AcFree.solvable_post` — the problem consisting of the verification phase alone,
> started in the state `s`, is solvable exactly when
>
> * for every `v` of the vocabulary, either `¬v⁰` holds in `s`, or `v⁰` holds and `v` is
>   *licensed* — the state the acyclic construction guessed is contained in the initial state of
>   the source;
> * every goal fact either already holds in `s`, or is the receipt of a vocabulary fact that
>   holds in copy `2`.

The phase changes nothing except that it may add receipts, and every check is effect free, so
the proof is the totally ordered normal form of `HtnPlanning/Core/TONormalForm.lean` applied
to the sub-hierarchy under `tPost`, which is totally ordered.
-/

namespace HTN

namespace Syn

namespace AcFree

open Ac TaskNetwork

variable {V : List ℕ} {d₀ : DomDesc}

/-! ### The methods of the verification phase -/

/-- The methods of the wrapper, listed. -/
lemma mem_wrapMeths_iff {e : MethodDesc} :
    e ∈ wrapMeths V ↔ e = (tPost, gridDesc [postBody V]) ∨
      ∃ v ∈ V, e = (tChk v, gridDesc [[pAct (aChkN v)]]) ∨
        e = (tChk v, gridDesc [[pAct (aChkP v)]]) ∨
        e = (tEarn v, gridDesc [[pAct (aEarn v)]]) ∨
        e = (tEarn v, gridDesc [[pAct aSkip]]) := by
  constructor
  · intro he
    simp only [wrapMeths, List.mem_cons, List.mem_flatMap] at he
    rcases he with rfl | ⟨v, hv, hmem⟩
    · exact Or.inl rfl
    · simp only [List.not_mem_nil, or_false] at hmem
      exact Or.inr ⟨v, hv, hmem⟩
  · intro h
    simp only [wrapMeths, List.mem_cons, List.mem_flatMap]
    rcases h with rfl | ⟨v, hv, hmem⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hv, by simp only [List.not_mem_nil, or_false]; exact hmem⟩

/-- A method of the wrapped description whose head is not base shaped is one of the wrapper. -/
lemma mem_wrapMeths_of_not_baseTask (hshape : BaseShaped d₀) {e : MethodDesc}
    (he : e ∈ (wrapDom V d₀).methods) (hb : ¬ BaseTask e.1) : e ∈ wrapMeths V := by
  rcases List.mem_append.1 (by simpa using he) with h' | h'
  · exact absurd (hshape.heads e h') hb
  · exact h'

/-- **The body of the verification phase.** -/
theorem seqBody_tPost (hshape : BaseShaped d₀) {xs : List (ℕ ⊕ ℕ)} :
    (wrapDom V d₀).toDomain.SeqBody tPost xs ↔ xs = rowLabels (postBody V) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    have hb : ¬ BaseTask e.1 := by rw [hc]; exact not_baseTask_tPost
    rcases mem_wrapMeths_iff.1 (mem_wrapMeths_of_not_baseTask hshape he hb) with rfl | ⟨v, -, hv⟩
    · exact hasSeqBody_oneRow.1 hbody
    · exfalso
      rcases hv with rfl | rfl | rfl | rfl
      · exact tPost_ne_tChk v hc.symm
      · exact tPost_ne_tChk v hc.symm
      · exact tPost_ne_tEarn v hc.symm
      · exact tPost_ne_tEarn v hc.symm
  · rintro rfl
    refine ⟨(tPost, gridDesc [postBody V]), ?_, rfl, hasSeqBody_oneRow.2 rfl⟩
    simp [wrapDom, DomDesc.methods, wrapMeths]

/-- **The bodies of a check task.** -/
theorem seqBody_tChk (hshape : BaseShaped d₀) {v : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (wrapDom V d₀).toDomain.SeqBody (tChk v) xs ↔
      v ∈ V ∧ (xs = [Sum.inl (aChkN v)] ∨ xs = [Sum.inl (aChkP v)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    have hb : ¬ BaseTask e.1 := by rw [hc]; exact not_baseTask_tChk v
    rcases mem_wrapMeths_iff.1 (mem_wrapMeths_of_not_baseTask hshape he hb) with rfl | ⟨w, hw, hv⟩
    · exact absurd hc (tPost_ne_tChk v)
    · rcases hv with rfl | rfl | rfl | rfl
      · obtain rfl : w = v := tChk_injective hc
        exact ⟨hw, Or.inl (hasSeqBody_oneRow.1 hbody)⟩
      · obtain rfl : w = v := tChk_injective hc
        exact ⟨hw, Or.inr (hasSeqBody_oneRow.1 hbody)⟩
      · exact absurd hc (tChk_ne_tEarn v w).symm
      · exact absurd hc (tChk_ne_tEarn v w).symm
  · rintro ⟨hv, rfl | rfl⟩
    · refine ⟨(tChk v, gridDesc [[pAct (aChkN v)]]), ?_, rfl, hasSeqBody_oneRow.2 rfl⟩
      refine List.mem_append.2 (Or.inr (mem_wrapMeths_iff.2 (Or.inr ⟨v, hv, Or.inl rfl⟩)))
    · refine ⟨(tChk v, gridDesc [[pAct (aChkP v)]]), ?_, rfl, hasSeqBody_oneRow.2 rfl⟩
      refine List.mem_append.2 (Or.inr (mem_wrapMeths_iff.2 (Or.inr ⟨v, hv, Or.inr (Or.inl rfl)⟩)))

/-- **The bodies of an earn task.** -/
theorem seqBody_tEarn (hshape : BaseShaped d₀) {v : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (wrapDom V d₀).toDomain.SeqBody (tEarn v) xs ↔
      v ∈ V ∧ (xs = [Sum.inl (aEarn v)] ∨ xs = [Sum.inl aSkip]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    have hb : ¬ BaseTask e.1 := by rw [hc]; exact not_baseTask_tEarn v
    rcases mem_wrapMeths_iff.1 (mem_wrapMeths_of_not_baseTask hshape he hb) with rfl | ⟨w, hw, hv⟩
    · exact absurd hc (tPost_ne_tEarn v)
    · rcases hv with rfl | rfl | rfl | rfl
      · exact absurd hc (tChk_ne_tEarn w v)
      · exact absurd hc (tChk_ne_tEarn w v)
      · obtain rfl : w = v := tEarn_injective hc
        exact ⟨hw, Or.inl (hasSeqBody_oneRow.1 hbody)⟩
      · obtain rfl : w = v := tEarn_injective hc
        exact ⟨hw, Or.inr (hasSeqBody_oneRow.1 hbody)⟩
  · rintro ⟨hv, rfl | rfl⟩
    · refine ⟨(tEarn v, gridDesc [[pAct (aEarn v)]]), ?_, rfl, hasSeqBody_oneRow.2 rfl⟩
      exact List.mem_append.2 (Or.inr (mem_wrapMeths_iff.2
        (Or.inr ⟨v, hv, Or.inr (Or.inr (Or.inl rfl))⟩)))
    · refine ⟨(tEarn v, gridDesc [[pAct aSkip]]), ?_, rfl, hasSeqBody_oneRow.2 rfl⟩
      exact List.mem_append.2 (Or.inr (mem_wrapMeths_iff.2
        (Or.inr ⟨v, hv, Or.inr (Or.inr (Or.inr rfl))⟩)))

/-! ### The actions of the verification phase -/

/-- The wrapper's action list, looked up at a check action. -/
lemma lookup_wrapActs_chkN {v : ℕ} (hv : v ∈ V) :
    (wrapActs V).lookup (aChkN v) = some ([fNeg v 0], [], []) := by
  have key : ∀ W : List ℕ, v ∈ W →
      ((W.flatMap fun w =>
        [(aChkN w, ([fNeg w 0], ([] : List ℕ), ([] : List ℕ))),
         (aChkP w, ([fPos w 0, fLic w], ([] : List ℕ), ([] : List ℕ))),
         (aEarn w, ([fPos w 2], [fRes w], ([] : List ℕ)))] : List ActionDesc)).lookup (aChkN v) =
        some ([fNeg v 0], ([] : List ℕ), ([] : List ℕ)) := by
    intro W hW
    induction W with
    | nil => simp at hW
    | cons w ws ih =>
        rw [List.flatMap_cons]
        by_cases hwv : w = v
        · subst hwv
          simp
        · have h1 : (aChkN v == aChkN w) = false :=
            beq_eq_false_iff_ne.2 fun hc => hwv (aChkN_injective hc).symm
          have h2 : (aChkN v == aChkP w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aChkP v w hc
          have h3 : (aChkN v == aEarn w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aEarn v w hc
          simp only [List.cons_append, List.nil_append, List.lookup_cons, h1, h2, h3]
          exact ih (by rcases List.mem_cons.1 hW with rfl | h; exacts [absurd rfl hwv, h])
  have hb : (aChkN v == aBoot) = false := beq_eq_false_iff_ne.2 fun hc => aBoot_ne_aChkN v hc.symm
  have hs : (aChkN v == aSkip) = false := beq_eq_false_iff_ne.2 fun hc => aSkip_ne_aChkN v hc.symm
  simp only [wrapActs, List.lookup_cons, hb, hs]
  exact key V hv

/-- The wrapper's action list, looked up at a check action. -/
lemma lookup_wrapActs_chkP {v : ℕ} (hv : v ∈ V) :
    (wrapActs V).lookup (aChkP v) = some ([fPos v 0, fLic v], [], []) := by
  have key : ∀ W : List ℕ, v ∈ W →
      ((W.flatMap fun w =>
        [(aChkN w, ([fNeg w 0], ([] : List ℕ), ([] : List ℕ))),
         (aChkP w, ([fPos w 0, fLic w], ([] : List ℕ), ([] : List ℕ))),
         (aEarn w, ([fPos w 2], [fRes w], ([] : List ℕ)))] : List ActionDesc)).lookup (aChkP v) =
        some ([fPos v 0, fLic v], ([] : List ℕ), ([] : List ℕ)) := by
    intro W hW
    induction W with
    | nil => simp at hW
    | cons w ws ih =>
        rw [List.flatMap_cons]
        by_cases hwv : w = v
        · subst hwv
          have h1 : (aChkP w == aChkN w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aChkP w w hc.symm
          simp [List.lookup_cons, h1]
        · have h1 : (aChkP v == aChkN w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aChkP w v hc.symm
          have h2 : (aChkP v == aChkP w) = false :=
            beq_eq_false_iff_ne.2 fun hc => hwv (aChkP_injective hc).symm
          have h3 : (aChkP v == aEarn w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkP_ne_aEarn v w hc
          simp only [List.cons_append, List.nil_append, List.lookup_cons, h1, h2, h3]
          exact ih (by rcases List.mem_cons.1 hW with rfl | h; exacts [absurd rfl hwv, h])
  have hb : (aChkP v == aBoot) = false := beq_eq_false_iff_ne.2 fun hc => aBoot_ne_aChkP v hc.symm
  have hs : (aChkP v == aSkip) = false := beq_eq_false_iff_ne.2 fun hc => aSkip_ne_aChkP v hc.symm
  simp only [wrapActs, List.lookup_cons, hb, hs]
  exact key V hv

/-- The wrapper's action list, looked up at an earn action. -/
lemma lookup_wrapActs_earn {v : ℕ} (hv : v ∈ V) :
    (wrapActs V).lookup (aEarn v) = some ([fPos v 2], [fRes v], []) := by
  have key : ∀ W : List ℕ, v ∈ W →
      ((W.flatMap fun w =>
        [(aChkN w, ([fNeg w 0], ([] : List ℕ), ([] : List ℕ))),
         (aChkP w, ([fPos w 0, fLic w], ([] : List ℕ), ([] : List ℕ))),
         (aEarn w, ([fPos w 2], [fRes w], ([] : List ℕ)))] : List ActionDesc)).lookup (aEarn v) =
        some ([fPos v 2], [fRes v], ([] : List ℕ)) := by
    intro W hW
    induction W with
    | nil => simp at hW
    | cons w ws ih =>
        rw [List.flatMap_cons]
        by_cases hwv : w = v
        · subst hwv
          have h1 : (aEarn w == aChkN w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aEarn w w hc.symm
          have h2 : (aEarn w == aChkP w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkP_ne_aEarn w w hc.symm
          simp [List.lookup_cons, h1, h2]
        · have h1 : (aEarn v == aChkN w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkN_ne_aEarn w v hc.symm
          have h2 : (aEarn v == aChkP w) = false :=
            beq_eq_false_iff_ne.2 fun hc => aChkP_ne_aEarn w v hc.symm
          have h3 : (aEarn v == aEarn w) = false :=
            beq_eq_false_iff_ne.2 fun hc => hwv (aEarn_injective hc).symm
          simp only [List.cons_append, List.nil_append, List.lookup_cons, h1, h2, h3]
          exact ih (by rcases List.mem_cons.1 hW with rfl | h; exacts [absurd rfl hwv, h])
  have hb : (aEarn v == aBoot) = false := beq_eq_false_iff_ne.2 fun hc => aBoot_ne_aEarn v hc.symm
  have hs : (aEarn v == aSkip) = false := beq_eq_false_iff_ne.2 fun hc => aSkip_ne_aEarn v hc.symm
  simp only [wrapActs, List.lookup_cons, hb, hs]
  exact key V hv

/-- The wrapper's action list, looked up at the boot action. -/
lemma lookup_wrapActs_boot :
    (wrapActs V).lookup aBoot =
      some ([], fKey0 :: V.flatMap fun v => (List.range 5).map (fNeg v), V.map fRes) := by
  simp [wrapActs]

/-- The wrapper's action list, looked up at the no-op action. -/
lemma lookup_wrapActs_skip : (wrapActs V).lookup aSkip = some ([], [], []) := by
  have hb : (aSkip == aBoot) = false := beq_eq_false_iff_ne.2 fun hc => aBoot_ne_aSkip hc.symm
  simp [wrapActs, List.lookup_cons, hb]

/-- The wrapped description looks a wrapper action up in the wrapper. -/
lemma lookup_wrapDom_new (hshape : BaseShaped d₀) {a : ℕ} (ha : ¬ BaseAct a) :
    (wrapDom V d₀).actions.lookup a = (wrapActs V).lookup a := by
  have hnone : d₀.actions.lookup a = none := by
    have key : ∀ l : List ActionDesc, (∀ e ∈ l, BaseAct e.1) → l.lookup a = none := by
      intro l hl
      induction l with
      | nil => rfl
      | cons p ps ih =>
          rw [show p = (p.1, p.2) from rfl, List.lookup_cons]
          have hne : (a == p.1) = false :=
            beq_eq_false_iff_ne.2 fun hc => ha (hc ▸ hl p (by simp))
          rw [hne]
          exact ih fun e he => hl e (by simp [he])
    exact key _ hshape.acts
  rw [wrapDom_actions, List.lookup_append, hnone]
  rfl

variable (V d₀)

/-- The precondition of a check action. -/
lemma prec_chkN (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).prec (aChkN v) = {fNeg v 0} := by
  rw [DomDesc.prec, lookup_wrapDom_new hshape (not_baseAct_aChkN v), lookup_wrapActs_chkN hv]
  ext f; simp

/-- A check action has no effect. -/
lemma add_chkN (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).add (aChkN v) = ∅ := by
  rw [DomDesc.add, lookup_wrapDom_new hshape (not_baseAct_aChkN v), lookup_wrapActs_chkN hv]
  ext f; simp

/-- A check action has no effect. -/
lemma del_chkN (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).del (aChkN v) = ∅ := by
  rw [DomDesc.del, lookup_wrapDom_new hshape (not_baseAct_aChkN v), lookup_wrapActs_chkN hv]
  ext f; simp

/-- The precondition of a check action. -/
lemma prec_chkP (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).prec (aChkP v) = {fPos v 0, fLic v} := by
  rw [DomDesc.prec, lookup_wrapDom_new hshape (not_baseAct_aChkP v), lookup_wrapActs_chkP hv]
  ext f; simp

/-- A check action has no effect. -/
lemma add_chkP (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).add (aChkP v) = ∅ := by
  rw [DomDesc.add, lookup_wrapDom_new hshape (not_baseAct_aChkP v), lookup_wrapActs_chkP hv]
  ext f; simp

/-- A check action has no effect. -/
lemma del_chkP (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).del (aChkP v) = ∅ := by
  rw [DomDesc.del, lookup_wrapDom_new hshape (not_baseAct_aChkP v), lookup_wrapActs_chkP hv]
  ext f; simp

/-- The precondition of an earn action. -/
lemma prec_earn (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).prec (aEarn v) = {fPos v 2} := by
  rw [DomDesc.prec, lookup_wrapDom_new hshape (not_baseAct_aEarn v), lookup_wrapActs_earn hv]
  ext f; simp

/-- An earn action adds the receipt. -/
lemma add_earn (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).add (aEarn v) = {fRes v} := by
  rw [DomDesc.add, lookup_wrapDom_new hshape (not_baseAct_aEarn v), lookup_wrapActs_earn hv]
  ext f; simp

/-- An earn action deletes nothing. -/
lemma del_earn (hshape : BaseShaped d₀) {v : ℕ} (hv : v ∈ V) :
    (wrapDom V d₀).del (aEarn v) = ∅ := by
  rw [DomDesc.del, lookup_wrapDom_new hshape (not_baseAct_aEarn v), lookup_wrapActs_earn hv]
  ext f; simp

/-- The no-op action has no precondition. -/
lemma prec_skip (hshape : BaseShaped d₀) : (wrapDom V d₀).prec aSkip = ∅ := by
  rw [DomDesc.prec, lookup_wrapDom_new hshape not_baseAct_aSkip, lookup_wrapActs_skip]
  ext f; simp

/-- The no-op action has no effect. -/
lemma add_skip (hshape : BaseShaped d₀) : (wrapDom V d₀).add aSkip = ∅ := by
  rw [DomDesc.add, lookup_wrapDom_new hshape not_baseAct_aSkip, lookup_wrapActs_skip]
  ext f; simp

/-- The no-op action has no effect. -/
lemma del_skip (hshape : BaseShaped d₀) : (wrapDom V d₀).del aSkip = ∅ := by
  rw [DomDesc.del, lookup_wrapDom_new hshape not_baseAct_aSkip, lookup_wrapActs_skip]
  ext f; simp

/-- The precondition of the boot action is empty. -/
lemma prec_boot (hshape : BaseShaped d₀) : (wrapDom V d₀).prec aBoot = ∅ := by
  rw [DomDesc.prec, lookup_wrapDom_new hshape not_baseAct_aBoot, lookup_wrapActs_boot]
  ext f; simp

/-- The boot action establishes the initial state of the acyclic construction. -/
lemma add_boot (hshape : BaseShaped d₀) :
    (wrapDom V d₀).add aBoot = {f | f = fKey0 ∨ ∃ v ∈ V, ∃ i < 5, f = fNeg v i} := by
  rw [DomDesc.add, lookup_wrapDom_new hshape not_baseAct_aBoot, lookup_wrapActs_boot]
  ext f
  simp only [Option.elim, Set.mem_setOf_eq, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_range]
  constructor
  · rintro (rfl | ⟨v, hv, i, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hv, i, hi, rfl⟩
  · rintro (rfl | ⟨v, hv, i, hi, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨v, hv, i, hi, rfl⟩

/-- The boot action deletes the receipts of the vocabulary. -/
lemma del_boot (hshape : BaseShaped d₀) :
    (wrapDom V d₀).del aBoot = {f | ∃ v ∈ V, f = fRes v} := by
  rw [DomDesc.del, lookup_wrapDom_new hshape not_baseAct_aBoot, lookup_wrapActs_boot]
  ext f
  simp only [Option.elim, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-! ### The refinements of the verification phase -/

variable {V d₀}

/-- The refinements of a single check task. -/
theorem yieldSeq_tChk (hshape : BaseShaped d₀) {v : ℕ} {as : List ℕ} :
    (wrapDom V d₀).toDomain.YieldSeq [Sum.inr (tChk v)] as ↔
      v ∈ V ∧ (as = [aChkN v] ∨ as = [aChkP v]) := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      obtain ⟨hv, hbs⟩ := (seqBody_tChk hshape).1 hm
      rcases hbs with rfl | rfl <;>
      · rw [List.append_nil] at h
        cases h with
        | prim h' =>
          cases h'
          simp [hv]
  · rintro ⟨hv, rfl | rfl⟩
    · refine Domain.YieldSeq.comp ((seqBody_tChk hshape).2 ⟨hv, Or.inl rfl⟩) ?_
      simp
    · refine Domain.YieldSeq.comp ((seqBody_tChk hshape).2 ⟨hv, Or.inr rfl⟩) ?_
      simp

/-- The refinements of a single earn task. -/
theorem yieldSeq_tEarn (hshape : BaseShaped d₀) {v : ℕ} {as : List ℕ} :
    (wrapDom V d₀).toDomain.YieldSeq [Sum.inr (tEarn v)] as ↔
      v ∈ V ∧ (as = [aEarn v] ∨ as = [aSkip]) := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      obtain ⟨hv, hbs⟩ := (seqBody_tEarn hshape).1 hm
      rcases hbs with rfl | rfl <;>
      · rw [List.append_nil] at h
        cases h with
        | prim h' =>
          cases h'
          simp [hv]
  · rintro ⟨hv, rfl | rfl⟩
    · refine Domain.YieldSeq.comp ((seqBody_tEarn hshape).2 ⟨hv, Or.inl rfl⟩) ?_
      simp
    · refine Domain.YieldSeq.comp ((seqBody_tEarn hshape).2 ⟨hv, Or.inr rfl⟩) ?_
      simp

/-- The refinements of a chain of check tasks. -/
theorem yieldSeq_chkChain (hshape : BaseShaped d₀) {W : List ℕ} (hW : ∀ v ∈ W, v ∈ V)
    {as : List ℕ} :
    (wrapDom V d₀).toDomain.YieldSeq (W.map fun v => Sum.inr (tChk v)) as ↔
      List.Forall₂ (fun v a => a = aChkN v ∨ a = aChkP v) W as := by
  induction W generalizing as with
  | nil =>
      constructor
      · intro h; cases h; exact List.Forall₂.nil
      · intro h; cases h; exact Domain.YieldSeq.nil
  | cons v W ih =>
      have hWv : v ∈ V := hW v (by simp)
      have hW' : ∀ w ∈ W, w ∈ V := fun w hw => hW w (by simp [hw])
      constructor
      · intro h
        rw [List.map_cons, show ((Sum.inr (tChk v) : ℕ ⊕ ℕ) :: W.map fun w => Sum.inr (tChk w)) =
          [Sum.inr (tChk v)] ++ W.map (fun w => Sum.inr (tChk w)) from rfl] at h
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
        obtain ⟨-, hcase⟩ := (yieldSeq_tChk hshape).1 h₁
        rcases hcase with rfl | rfl
        · exact List.Forall₂.cons (Or.inl rfl) ((ih hW').1 h₂)
        · exact List.Forall₂.cons (Or.inr rfl) ((ih hW').1 h₂)
      · intro h
        obtain ⟨a, as', ha, hrest, rfl⟩ :
            ∃ a as', (a = aChkN v ∨ a = aChkP v) ∧
              List.Forall₂ (fun v a => a = aChkN v ∨ a = aChkP v) W as' ∧ as = a :: as' := by
          cases h with
          | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
        rw [List.map_cons, show ((Sum.inr (tChk v) : ℕ ⊕ ℕ) :: W.map fun w => Sum.inr (tChk w)) =
          [Sum.inr (tChk v)] ++ W.map (fun w => Sum.inr (tChk w)) from rfl,
          show (a :: as') = [a] ++ as' from rfl]
        exact Domain.YieldSeq.append ((yieldSeq_tChk hshape).2
          ⟨hWv, by rcases ha with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]⟩) ((ih hW').2 hrest)

/-- The refinements of a chain of earn tasks. -/
theorem yieldSeq_earnChain (hshape : BaseShaped d₀) {W : List ℕ} (hW : ∀ v ∈ W, v ∈ V)
    {as : List ℕ} :
    (wrapDom V d₀).toDomain.YieldSeq (W.map fun v => Sum.inr (tEarn v)) as ↔
      List.Forall₂ (fun v a => a = aEarn v ∨ a = aSkip) W as := by
  induction W generalizing as with
  | nil =>
      constructor
      · intro h; cases h; exact List.Forall₂.nil
      · intro h; cases h; exact Domain.YieldSeq.nil
  | cons v W ih =>
      have hWv : v ∈ V := hW v (by simp)
      have hW' : ∀ w ∈ W, w ∈ V := fun w hw => hW w (by simp [hw])
      constructor
      · intro h
        rw [List.map_cons, show ((Sum.inr (tEarn v) : ℕ ⊕ ℕ) :: W.map fun w => Sum.inr (tEarn w)) =
          [Sum.inr (tEarn v)] ++ W.map (fun w => Sum.inr (tEarn w)) from rfl] at h
        obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
        obtain ⟨-, hcase⟩ := (yieldSeq_tEarn hshape).1 h₁
        rcases hcase with rfl | rfl
        · exact List.Forall₂.cons (Or.inl rfl) ((ih hW').1 h₂)
        · exact List.Forall₂.cons (Or.inr rfl) ((ih hW').1 h₂)
      · intro h
        obtain ⟨a, as', ha, hrest, rfl⟩ :
            ∃ a as', (a = aEarn v ∨ a = aSkip) ∧
              List.Forall₂ (fun v a => a = aEarn v ∨ a = aSkip) W as' ∧ as = a :: as' := by
          cases h with
          | cons h1 h2 => exact ⟨_, _, h1, h2, rfl⟩
        rw [List.map_cons, show ((Sum.inr (tEarn v) : ℕ ⊕ ℕ) :: W.map fun w => Sum.inr (tEarn w)) =
          [Sum.inr (tEarn v)] ++ W.map (fun w => Sum.inr (tEarn w)) from rfl,
          show (a :: as') = [a] ++ as' from rfl]
        exact Domain.YieldSeq.append ((yieldSeq_tEarn hshape).2
          ⟨hWv, by rcases ha with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]⟩) ((ih hW').2 hrest)

/-- The body of the verification phase, as a task sequence. -/
lemma rowLabels_postBody :
    rowLabels (postBody V) =
      (V.map fun v => Sum.inr (tChk v)) ++ (V.map fun v => Sum.inr (tEarn v)) := by
  simp [rowLabels, postBody, pTsk, List.map_map, Function.comp_def]

/-- **The refinements of the verification phase**: one chosen check and one chosen earn action
per fact of the vocabulary. -/
theorem yieldSeq_tPost (hshape : BaseShaped d₀) {as : List ℕ} :
    (wrapDom V d₀).toDomain.YieldSeq [Sum.inr tPost] as ↔
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧
        List.Forall₂ (fun v a => a = aChkN v ∨ a = aChkP v) V as₁ ∧
        List.Forall₂ (fun v a => a = aEarn v ∨ a = aSkip) V as₂ := by
  constructor
  · intro h
    cases h with
    | comp hm h =>
      have hbs := (seqBody_tPost hshape).1 hm
      subst hbs
      rw [List.append_nil, rowLabels_postBody] at h
      obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := h.split
      exact ⟨as₁, as₂, rfl, (yieldSeq_chkChain hshape (fun _ hv => hv)).1 h₁,
        (yieldSeq_earnChain hshape (fun _ hv => hv)).1 h₂⟩
  · rintro ⟨as₁, as₂, rfl, h₁, h₂⟩
    refine Domain.YieldSeq.comp ((seqBody_tPost hshape).2 rfl) ?_
    rw [List.append_nil, rowLabels_postBody]
    exact Domain.YieldSeq.append ((yieldSeq_chkChain hshape (fun _ hv => hv)).2 h₁)
      ((yieldSeq_earnChain hshape (fun _ hv => hv)).2 h₂)

end AcFree

end Syn

end HTN
