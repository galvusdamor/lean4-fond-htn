import HtnComplexity.Computable.TrStrips
/-!
# Correctness of the stack-machine compilation

The compiled description of `HtnComplexity/Computable/TrStrips.lean` simulates the bounded
stack machine of `HtnComplexity/Computable/StackMachine.lean` step by step, and this file
proves it:

* `HTN.Syn.exists_plan_of_run` — every run of the machine, together with an executable action
  sequence, becomes a plan of the compiled description;
* `HTN.Syn.run_of_plan`, `HTN.Syn.run_of_start_plan` — and conversely: every plan of the
  compiled description that reaches `done` is a run of the machine;
* `HTN.Syn.solvable_trStrips_iff` — **the compiled description is solvable exactly when the
  source description is**, for a totally ordered tail-recursive domain description and a rooted
  instance description.

The reverse direction is an invariant argument: a state reachable in the compiled problem is
either `startCfg` (the initial compound task has not been started), or `cfg s st` for a source
state `s` and a non-empty stack `st`, or `endCfg s` — and in the last shape no action of the
compiled description is applicable any more, so the plan is frozen (`transitionSeq_endCfg`).
-/

namespace HTN

namespace Syn

variable {d : DomDesc}

/-! ### Residues of the three shapes of a state -/

theorem mod_of_mem_cfg {s : Set ℕ} {st : List (ℕ × ℕ)} {x : ℕ} (h : x ∈ cfg s st) :
    x % 6 = 0 ∨ x % 6 = 1 ∨ x % 6 = 2 := by
  rcases h with h | h
  · exact Or.inl (mod_zero_of_mem_stSet h)
  · exact Or.inr (mod_of_mem_ctlSet h)

theorem mod_of_mem_startCfg {s : Set ℕ} {c x : ℕ} (h : x ∈ startCfg s c) :
    x % 6 = 0 ∨ x % 6 = 3 := by
  rw [startCfg_eq] at h
  rcases h with h | h
  · exact Or.inl (mod_zero_of_mem_stSet h)
  · simp only [Set.mem_singleton_iff] at h
    exact Or.inr (h ▸ encCall_mod c)

theorem mod_of_mem_endCfg {s : Set ℕ} {x : ℕ} (h : x ∈ endCfg s) : x % 6 = 0 ∨ x % 6 = 4 := by
  rw [endCfg_eq] at h
  rcases h with h | h
  · exact Or.inl (mod_zero_of_mem_stSet h)
  · simp only [Set.mem_singleton_iff] at h
    exact Or.inr (h ▸ encDone_mod)

/-! ### Actions the description does not mention -/

theorem transition_unlisted {n : ℕ} (hn : ¬ n < (cacts d).length) (X : Set ℕ) :
    (trStripsDom d).toDomain.transition n X = X := by
  have hmem : n ∉ (trStripsDom d).actNames := by
    rw [actNames_trStripsDom]
    simpa using hn
  obtain ⟨-, hadd, hdel⟩ := DomDesc.unmentioned hmem
  show (X \ (trStripsDom d).del n) ∪ (trStripsDom d).add n = X
  rw [show (trStripsDom d).del n = (∅ : Set ℕ) from hdel,
    show (trStripsDom d).add n = (∅ : Set ℕ) from hadd]
  simp

/-! ### Every action is guarded by a control fact -/

/-- Every listed action of the compiled description has a fact of residue `1`, `3` or `5` in
its precondition — an active frame, the initial call, or the unsatisfiable fact. -/
theorem exists_prec_control {n : ℕ} (hn : n < (cacts d).length) :
    ∃ f ∈ (trStripsDom d).prec n, f % 6 = 1 ∨ f % 6 = 3 ∨ f % 6 = 5 := by
  rcases hget : (cacts d).getI n with ⟨k, i, m, j, m'⟩
  by_cases hbad : specOf d ((cacts d).getI n) = badSpec
  · exact ⟨encBot, by rw [prec_of_badSpec hn hbad]; rfl, Or.inr (Or.inr encBot_mod)⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hm : m < d.methods.length := by
      by_contra hm
      exact hbad (specOf_beg_invalid hget hm)
    exact ⟨encCall (d.hd m), by rw [prec_beg hn hget hm]; exact Or.inr rfl,
      Or.inr (Or.inl (encCall_mod _))⟩
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨a, ha⟩ : ∃ a, (d.bd m)[j]? = some (Sum.inl a) := by
      by_contra hcon
      push_neg at hcon
      exact hbad (specOf_exec_invalid hget hcon)
    exact ⟨encCur i m j, by rw [prec_exec hn hget ha]; exact Or.inr rfl,
      Or.inl (encCur_mod _ _ _)⟩
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨hval, hlast, hm', hi⟩ := push_valid_of_ne_bad hget hbad
    exact ⟨encCur i m j, by rw [prec_push hn hget hval rfl hlast hm' hi]; exact Or.inr rfl,
      Or.inl (encCur_mod _ _ _)⟩
  by_cases hk3 : k = 3
  · subst hk3
    obtain ⟨hval, hlast, hm'⟩ := tail_valid_of_ne_bad hget hbad
    exact ⟨encCur i m j, by rw [prec_tail hn hget hval rfl hlast hm']; exact Or.inr rfl,
      Or.inl (encCur_mod _ _ _)⟩
  by_cases hk4 : k = 4
  · subst hk4
    have hi : 0 < i := by
      by_contra hi
      exact hbad (specOf_ret_invalid hget hi)
    refine ⟨encCur i m (d.bd m).length, ?_, Or.inl (encCur_mod _ _ _)⟩
    rw [prec_ret hn hget hi]
    exact Or.inr (Set.mem_insert _ _)
  by_cases hk5 : k = 5
  · subst hk5
    exact ⟨encCur 0 m (d.bd m).length, by rw [prec_fin hn hget]; exact Or.inr rfl,
      Or.inl (encCur_mod _ _ _)⟩
  · exact absurd (by rw [hget]; exact specOf_other (by omega)) hbad

/-! ### Nothing happens after `done` -/

theorem transitionSeq_endCfg (s : Set ℕ) :
    ∀ bs : List ℕ, (trStripsDom d).toDomain.SeqApplicable bs (endCfg s) →
      (trStripsDom d).toDomain.transitionSeq bs (endCfg s) = endCfg s := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons b bs ih =>
    intro happ
    obtain ⟨happ1, happ2⟩ := happ
    by_cases hb : b < (cacts d).length
    · exfalso
      obtain ⟨f, hf, hres⟩ := exists_prec_control (d := d) hb
      have hmem : f ∈ endCfg s := happ1 hf
      rcases mod_of_mem_endCfg hmem with h | h <;> omega
    · rw [ActionModel.transitionSeq_cons, transition_unlisted hb] at *
      exact ih happ2

/-! ### The first step: starting the initial compound task -/

/-- In the initial state of the compiled problem the only applicable actions are those that
start the initial compound task with one of its methods. -/
theorem start_step {n : ℕ} (hn : n < (cacts d).length) {s : Set ℕ} {c : ℕ}
    (happ : (trStripsDom d).toDomain.Applicable n (startCfg s c)) :
    ∃ m, m < d.methods.length ∧ d.hd m = c ∧
      (trStripsDom d).toDomain.transition n (startCfg s c) = cfg s [(m, 0)] := by
  rcases hget : (cacts d).getI n with ⟨k, i, m, j, m'⟩
  by_cases hbad : specOf d ((cacts d).getI n) = badSpec
  · exact absurd (encBot_mem_of_applicable_bad hn hbad happ) (encBot_notMem_startCfg s c)
  have hcur : ∀ i₀ m₀ j₀ : ℕ, encCur i₀ m₀ j₀ ∈ startCfg s c → False := by
    intro i₀ m₀ j₀ hmem
    rcases mod_of_mem_startCfg hmem with h | h <;> rw [encCur_mod] at h <;> omega
  by_cases hk0 : k = 0
  · subst hk0
    have hm : m < d.methods.length := by
      by_contra hm
      exact hbad (specOf_beg_invalid hget hm)
    have hmem : encCall (d.hd m) ∈ startCfg s c := by
      refine happ ?_
      show encCall (d.hd m) ∈ (trStripsDom d).prec n
      rw [prec_beg hn hget hm]
      exact Or.inr rfl
    have hc : d.hd m = c := by
      rw [startCfg_eq] at hmem
      rcases hmem with hmem | hmem
      · exact absurd (mod_zero_of_mem_stSet hmem) (by simp)
      · simpa using hmem
    refine ⟨m, hm, hc, ?_⟩
    rw [startCfg_eq, transition_gen (del_beg hn hget hm) (add_beg hn hget hm)
      (mod_ne_zero_startCfg _) (mod_ne_zero_cur _ _ _) s {encCall c} (mod_ne_zero_startCfg c),
      hc, ctl_step_beg, cfg_eq]
    simp
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨a, ha⟩ : ∃ a, (d.bd m)[j]? = some (Sum.inl a) := by
      by_contra hcon
      push_neg at hcon
      exact hbad (specOf_exec_invalid hget hcon)
    refine absurd (happ ?_) (hcur i m j)
    show encCur i m j ∈ (trStripsDom d).prec n
    rw [prec_exec hn hget ha]
    exact Or.inr rfl
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨hval, hlast, hm', hi⟩ := push_valid_of_ne_bad hget hbad
    refine absurd (happ ?_) (hcur i m j)
    show encCur i m j ∈ (trStripsDom d).prec n
    rw [prec_push hn hget hval rfl hlast hm' hi]
    exact Or.inr rfl
  by_cases hk3 : k = 3
  · subst hk3
    obtain ⟨hval, hlast, hm'⟩ := tail_valid_of_ne_bad hget hbad
    refine absurd (happ ?_) (hcur i m j)
    show encCur i m j ∈ (trStripsDom d).prec n
    rw [prec_tail hn hget hval rfl hlast hm']
    exact Or.inr rfl
  by_cases hk4 : k = 4
  · subst hk4
    have hi : 0 < i := by
      by_contra hi
      exact hbad (specOf_ret_invalid hget hi)
    refine absurd (happ ?_) (hcur i m (d.bd m).length)
    show encCur i m (d.bd m).length ∈ (trStripsDom d).prec n
    rw [prec_ret hn hget hi]
    exact Or.inr (Set.mem_insert _ _)
  by_cases hk5 : k = 5
  · subst hk5
    refine absurd (happ ?_) (hcur 0 m (d.bd m).length)
    show encCur 0 m (d.bd m).length ∈ (trStripsDom d).prec n
    rw [prec_fin hn hget]
    exact Or.inr rfl
  · exact absurd (by rw [hget]; exact specOf_other (by omega)) hbad

/-! ### The steps of the machine -/

/-- **Every step of the compiled problem is a step of the machine.**  Either the compiled action
performs a step of the machine — emitting a source action or none — or it is the action that
finishes the plan, and then the stack is a single exhausted frame. -/
theorem step_of_applicable {n : ℕ} (hn : n < (cacts d).length) {s : Set ℕ} {st : List (ℕ × ℕ)}
    (hst : st ≠ []) (happ : (trStripsDom d).toDomain.Applicable n (cfg s st)) :
    (∃ (w : List ℕ) (st' : List (ℕ × ℕ)), d.toDomain.SeqApplicable w s ∧
        (trStripsDom d).toDomain.transition n (cfg s st) =
          cfg (d.toDomain.transitionSeq w s) st' ∧
        st' ≠ [] ∧
        ∀ as, Run d d.methods.length st' as → Run d d.methods.length st (w ++ as)) ∨
      ((trStripsDom d).toDomain.transition n (cfg s st) = endCfg s ∧
        Run d d.methods.length st []) := by
  have hCctl : ∀ x ∈ ctlSet st, x % 6 ≠ 0 := fun x hx => mod_ne_zero_of_mem_ctlSet hx
  rcases hget : (cacts d).getI n with ⟨k, i, m, j, m'⟩
  by_cases hbad : specOf d ((cacts d).getI n) = badSpec
  · exact absurd (encBot_mem_of_applicable_bad hn hbad happ) (encBot_notMem_cfg s st)
  by_cases hk0 : k = 0
  · subst hk0
    exfalso
    have hm : m < d.methods.length := by
      by_contra hm
      exact hbad (specOf_beg_invalid hget hm)
    have hmem : encCall (d.hd m) ∈ cfg s st := by
      refine happ ?_
      show encCall (d.hd m) ∈ (trStripsDom d).prec n
      rw [prec_beg hn hget hm]
      exact Or.inr rfl
    rcases mod_of_mem_cfg hmem with h | h | h <;> rw [encCall_mod] at h <;> omega
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨a, ha⟩ : ∃ a, (d.bd m)[j]? = some (Sum.inl a) := by
      by_contra hcon
      push_neg at hcon
      exact hbad (specOf_exec_invalid hget hcon)
    rw [cfg_eq] at happ
    obtain ⟨hpre, hctl⟩ :=
      (applicable_gen (prec_exec hn hget ha) (mod_ne_zero_cur i m j) s (ctlSet st) hCctl).1 happ
    obtain ⟨rest, rfl, hlen⟩ := encCur_mem_ctlSet_iff.1 (hctl rfl)
    refine Or.inl ⟨[a], (m, j + 1) :: rest, ⟨hpre, trivial⟩, ?_, by simp, ?_⟩
    · rw [cfg_eq, transition_gen (del_exec hn hget ha) (add_exec hn hget ha)
        (mod_ne_zero_cur i m j) (mod_ne_zero_cur i m (j + 1)) s (ctlSet ((m, j) :: rest)) hCctl,
        ctl_step_cur i m j m (j + 1) hlen, cfg_eq]
      rfl
    · intro as hrun
      exact Run.exec ha hrun
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨hval, hlast, hm', hi⟩ := push_valid_of_ne_bad hget hbad
    rw [cfg_eq] at happ
    obtain ⟨-, hctl⟩ :=
      (applicable_gen (prec_push hn hget hval rfl hlast hm' hi) (mod_ne_zero_cur i m j) s
        (ctlSet st) hCctl).1 happ
    obtain ⟨rest, rfl, hlen⟩ := encCur_mem_ctlSet_iff.1 (hctl rfl)
    refine Or.inl ⟨[], (m', 0) :: (m, j + 1) :: rest, trivial, ?_, by simp, ?_⟩
    · rw [cfg_eq, transition_gen (del_push hn hget hval rfl hlast hm' hi)
        (add_push hn hget hval rfl hlast hm' hi) (mod_ne_zero_cur i m j)
        (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) s (ctlSet ((m, j) :: rest)) hCctl,
        ctl_step_push i m j m' hlen, cfg_eq]
      simp
    · intro as hrun
      refine Run.push hval hlast hm' rfl (by omega) ?_
      simpa using hrun
  by_cases hk3 : k = 3
  · subst hk3
    obtain ⟨hval, hlast, hm'⟩ := tail_valid_of_ne_bad hget hbad
    rw [cfg_eq] at happ
    obtain ⟨-, hctl⟩ :=
      (applicable_gen (prec_tail hn hget hval rfl hlast hm') (mod_ne_zero_cur i m j) s
        (ctlSet st) hCctl).1 happ
    obtain ⟨rest, rfl, hlen⟩ := encCur_mem_ctlSet_iff.1 (hctl rfl)
    refine Or.inl ⟨[], (m', 0) :: rest, trivial, ?_, by simp, ?_⟩
    · rw [cfg_eq, transition_gen (del_tail hn hget hval rfl hlast hm')
        (add_tail hn hget hval rfl hlast hm') (mod_ne_zero_cur i m j) (mod_ne_zero_cur i m' 0) s
        (ctlSet ((m, j) :: rest)) hCctl, ctl_step_cur i m j m' 0 hlen, cfg_eq]
      simp
    · intro as hrun
      exact Run.tailCall hval hlast hm' rfl (by simpa using hrun)
  by_cases hk4 : k = 4
  · subst hk4
    have hi : 0 < i := by
      by_contra hi
      exact hbad (specOf_ret_invalid hget hi)
    rw [cfg_eq] at happ
    obtain ⟨-, hctl⟩ :=
      (applicable_gen (prec_ret hn hget hi) (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) s
        (ctlSet st) hCctl).1 happ
    obtain ⟨rest, rfl, hlen⟩ :=
      encCur_mem_ctlSet_iff.1 (hctl (Set.mem_insert _ _))
    have hsav : encSav (i - 1) m' j ∈ savSet rest := by
      have hmem := hctl (Set.mem_insert_of_mem _ rfl)
      rw [ctlSet_cons] at hmem
      rcases Set.mem_insert_iff.1 hmem with h | h
      · exact absurd (congrArg (· % 6) h) (by simp)
      · exact h
    obtain ⟨tl, hrest, htl⟩ := encSav_mem_savSet_top hsav (by omega)
    subst hrest
    refine Or.inl ⟨[], (m', j) :: tl, trivial, ?_, by simp, ?_⟩
    · have hi1 : i = tl.length + 1 := by simpa using hlen.symm
      subst hi1
      rw [cfg_eq, transition_gen (del_ret hn hget hi) (add_ret hn hget hi)
        (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) (mod_ne_zero_cur _ _ _) s
        (ctlSet ((m, (d.bd m).length) :: (m', j) :: tl)) hCctl]
      simp only [Nat.add_sub_cancel]
      rw [ctl_step_ret m (d.bd m).length m' j, cfg_eq]
      simp
    · intro as hrun
      simpa using Run.ret (le_refl (d.bd m).length) hrun
  by_cases hk5 : k = 5
  · subst hk5
    rw [cfg_eq] at happ
    obtain ⟨-, hctl⟩ :=
      (applicable_gen (prec_fin hn hget) (mod_ne_zero_cur _ _ _) s (ctlSet st) hCctl).1 happ
    obtain ⟨rest, rfl, hlen⟩ := encCur_mem_ctlSet_iff.1 (hctl rfl)
    have hrest : rest = [] := List.eq_nil_of_length_eq_zero hlen
    subst hrest
    refine Or.inr ⟨?_, ?_⟩
    · rw [cfg_eq, transition_gen (del_fin hn hget) (add_fin hn hget) (mod_ne_zero_cur _ _ _)
        mod_ne_zero_endCfg s (ctlSet [(m, (d.bd m).length)]) hCctl,
        ctl_step_fin m (d.bd m).length, endCfg_eq]
      simp
    · exact Run.ret (le_refl _) Run.nil
  · exact absurd (by rw [hget]; exact specOf_other (by omega)) hbad

/-! ### From a plan of the compiled description to a run of the machine -/

theorem eq_nil_of_run_nil {D : ℕ} {as : List ℕ} (h : Run d D [] as) : as = [] := by
  cases h
  rfl

/-- **A plan of the compiled description that reaches `done` is a run of the machine.** -/
theorem run_of_plan : ∀ (bs : List ℕ) (s : Set ℕ) (st : List (ℕ × ℕ)), st ≠ [] →
    (trStripsDom d).toDomain.SeqApplicable bs (cfg s st) →
    encDone ∈ (trStripsDom d).toDomain.transitionSeq bs (cfg s st) →
    ∃ as, Run d d.methods.length st as ∧ d.toDomain.SeqApplicable as s ∧
      (trStripsDom d).toDomain.transitionSeq bs (cfg s st) =
        endCfg (d.toDomain.transitionSeq as s) := by
  intro bs
  induction bs with
  | nil =>
    intro s st _ _ hdone
    exact absurd hdone (encDone_notMem_cfg s st)
  | cons b bs ih =>
    intro s st hst happ hdone
    obtain ⟨happ1, happ2⟩ := happ
    by_cases hb : b < (cacts d).length
    · rcases step_of_applicable hb hst happ1 with ⟨w, st', hw, htr, hne, hrun⟩ | ⟨htr, hrunnil⟩
      · rw [ActionModel.transitionSeq_cons, htr] at hdone ⊢
        rw [htr] at happ2
        obtain ⟨as, hras, hasapp, heq⟩ := ih _ st' hne happ2 hdone
        refine ⟨w ++ as, hrun as hras, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_append]
          exact ⟨hw, hasapp⟩
        · rw [heq, ActionModel.transitionSeq_append]
      · rw [ActionModel.transitionSeq_cons, htr] at hdone ⊢
        rw [htr] at happ2
        exact ⟨[], hrunnil, trivial, transitionSeq_endCfg s bs happ2⟩
    · rw [ActionModel.transitionSeq_cons, transition_unlisted hb] at hdone ⊢
      rw [transition_unlisted hb] at happ2
      exact ih s st hst happ2 hdone

/-- **A plan of the compiled description, from its initial state.** -/
theorem run_of_start_plan : ∀ (bs : List ℕ) (s : Set ℕ) (c : ℕ),
    (trStripsDom d).toDomain.SeqApplicable bs (startCfg s c) →
    encDone ∈ (trStripsDom d).toDomain.transitionSeq bs (startCfg s c) →
    ∃ m as, m < d.methods.length ∧ d.hd m = c ∧ Run d d.methods.length [(m, 0)] as ∧
      d.toDomain.SeqApplicable as s ∧
      (trStripsDom d).toDomain.transitionSeq bs (startCfg s c) =
        endCfg (d.toDomain.transitionSeq as s) := by
  intro bs
  induction bs with
  | nil =>
    intro s c _ hdone
    exact absurd hdone (encDone_notMem_startCfg s c)
  | cons b bs ih =>
    intro s c happ hdone
    obtain ⟨happ1, happ2⟩ := happ
    by_cases hb : b < (cacts d).length
    · obtain ⟨m, hm, hc, htr⟩ := start_step hb happ1
      rw [ActionModel.transitionSeq_cons, htr] at hdone ⊢
      rw [htr] at happ2
      obtain ⟨as, hras, hasapp, heq⟩ := run_of_plan bs s [(m, 0)] (by simp) happ2 hdone
      exact ⟨m, as, hm, hc, hras, hasapp, heq⟩
    · rw [ActionModel.transitionSeq_cons, transition_unlisted hb] at hdone ⊢
      rw [transition_unlisted hb] at happ2
      exact ih s c happ2 hdone

/-! ### From a run of the machine to a plan of the compiled description -/

/-- The frames of a stack are listed methods, at a position of their body. -/
def StackWF (d : DomDesc) (st : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ st, p.1 < d.methods.length ∧ p.2 ≤ (d.bd p.1).length

theorem StackWF.head {st : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : StackWF d (p :: st)) :
    p.1 < d.methods.length ∧ p.2 ≤ (d.bd p.1).length := h p (by simp)

theorem StackWF.tail {st : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : StackWF d (p :: st)) : StackWF d st :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem lt_size_of_le_length_bd {m j : ℕ} (h : j ≤ (d.bd m).length) : j < d.size + 2 := by
  have := DomDesc.length_bd_le d m
  omega

/-- **Every run of the machine is a plan of the compiled description.** -/
theorem exists_plan_of_run {st : List (ℕ × ℕ)} {as : List ℕ}
    (hrun : Run d d.methods.length st as) :
    st ≠ [] → StackWF d st → st.length ≤ d.methods.length → ∀ s : Set ℕ,
      d.toDomain.SeqApplicable as s →
        ∃ bs, (trStripsDom d).toDomain.SeqApplicable bs (cfg s st) ∧
          (trStripsDom d).toDomain.transitionSeq bs (cfg s st) =
            endCfg (d.toDomain.transitionSeq as s) := by
  induction hrun with
  | nil => intro hne; exact absurd rfl hne
  | @ret m j rest as hj h ih =>
    intro _ hwf hlen s happ
    obtain ⟨hm, hjle⟩ := hwf.head
    have hjeq : j = (d.bd m).length := by simp only at hjle hj; omega
    subst hjeq
    rcases rest with _ | ⟨⟨m', j'⟩, tl⟩
    · -- the last frame: finish
      have hasnil : as = [] := eq_nil_of_run_nil h
      subst hasnil
      have hx : (5, 0, m, 0, 0) ∈ cacts d :=
        mem_cacts (by norm_num) (by omega) hm (by omega) (by omega)
      refine ⟨[nameOf d (5, 0, m, 0, 0)], ⟨?_, trivial⟩, ?_⟩
      · rw [cfg_eq]
        refine (applicable_gen (prec_fin (nameOf_lt hx) (getI_nameOf hx))
          (mod_ne_zero_cur _ _ _) s _ (fun x hx => mod_ne_zero_of_mem_ctlSet hx)).2
          ⟨Set.empty_subset _, ?_⟩
        exact Set.singleton_subset_iff.2 (encCur_mem_ctlSet_iff.2 ⟨[], rfl, rfl⟩)
      · rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_nil, cfg_eq,
          transition_gen (del_fin (nameOf_lt hx) (getI_nameOf hx))
            (add_fin (nameOf_lt hx) (getI_nameOf hx)) (mod_ne_zero_cur _ _ _)
            mod_ne_zero_endCfg s (ctlSet [(m, (d.bd m).length)])
            (fun x hx => mod_ne_zero_of_mem_ctlSet hx),
          ctl_step_fin m (d.bd m).length, endCfg_eq]
        simp
    · -- return to the frame below
      have hi : tl.length + 1 < d.methods.length := by
        simp only [List.length_cons] at hlen
        omega
      obtain ⟨hm', hj'⟩ := hwf.tail.head
      have hx : (4, tl.length + 1, m, j', m') ∈ cacts d :=
        mem_cacts (by norm_num) hi hm
          (lt_size_of_le_length_bd (show j' ≤ (d.bd m').length from hj')) hm'
      have hn := nameOf_lt hx
      have hget := getI_nameOf hx
      have hsub : ({encCur (tl.length + 1) m (d.bd m).length,
          encSav (tl.length + 1 - 1) m' j'} : Set ℕ) ⊆
            ctlSet ((m, (d.bd m).length) :: (m', j') :: tl) := by
        simp only [Nat.add_sub_cancel]
        refine Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 ?_⟩
        · exact encCur_mem_ctlSet_iff.2 ⟨(m', j') :: tl, rfl, by simp⟩
        · exact Set.mem_insert_of_mem _ (by rw [savSet_cons]; exact Set.mem_insert _ _)
      have htr : (trStripsDom d).toDomain.transition (nameOf d (4, tl.length + 1, m, j', m'))
          (cfg s ((m, (d.bd m).length) :: (m', j') :: tl)) = cfg s ((m', j') :: tl) := by
        rw [cfg_eq, transition_gen (del_ret hn hget (by omega)) (add_ret hn hget (by omega))
          (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) (mod_ne_zero_cur _ _ _) s
          (ctlSet ((m, (d.bd m).length) :: (m', j') :: tl))
          (fun x hx => mod_ne_zero_of_mem_ctlSet hx)]
        simp only [Nat.add_sub_cancel]
        rw [ctl_step_ret m (d.bd m).length m' j', cfg_eq]
        simp
      obtain ⟨bs, hbs, hbseq⟩ := ih (by simp) hwf.tail
        (by simp only [List.length_cons] at hlen ⊢; omega) s happ
      refine ⟨nameOf d (4, tl.length + 1, m, j', m') :: bs, ⟨?_, ?_⟩, ?_⟩
      · rw [cfg_eq]
        refine (applicable_gen (prec_ret hn hget (by omega))
          (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) s _
          (fun x hx => mod_ne_zero_of_mem_ctlSet hx)).2 ⟨Set.empty_subset _, ?_⟩
        exact hsub
      · rw [htr]; exact hbs
      · rw [ActionModel.transitionSeq_cons, htr]; exact hbseq
  | @exec m j a rest as ha h ih =>
    intro _ hwf hlen s happ
    obtain ⟨happ1, happ2⟩ := happ
    obtain ⟨hm, -⟩ := hwf.head
    have hjlt : j < (d.bd m).length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at ha
      exact absurd ha (by simp)
    have hi : rest.length < d.methods.length := by
      simp only [List.length_cons] at hlen
      omega
    have hx : (1, rest.length, m, j, 0) ∈ cacts d :=
      mem_cacts (by norm_num) hi hm
        (lt_size_of_le_length_bd (show j ≤ (d.bd m).length from le_of_lt hjlt)) (by omega)
    have hn := nameOf_lt hx
    have hget := getI_nameOf hx
    have htr : (trStripsDom d).toDomain.transition (nameOf d (1, rest.length, m, j, 0))
        (cfg s ((m, j) :: rest)) =
          cfg (d.toDomain.transition a s) ((m, j + 1) :: rest) := by
      rw [cfg_eq, transition_gen (del_exec hn hget ha) (add_exec hn hget ha)
        (mod_ne_zero_cur _ _ _) (mod_ne_zero_cur _ _ _) s (ctlSet ((m, j) :: rest))
        (fun x hx => mod_ne_zero_of_mem_ctlSet hx),
        ctl_step_cur rest.length m j m (j + 1) rfl, cfg_eq]
      rfl
    have hwf' : StackWF d ((m, j + 1) :: rest) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hm, by simp only; omega⟩
      · exact hwf.tail p hp
    obtain ⟨bs, hbs, hbseq⟩ := ih (by simp) hwf' (by simpa using hlen) _ happ2
    refine ⟨nameOf d (1, rest.length, m, j, 0) :: bs, ⟨?_, ?_⟩, ?_⟩
    · rw [cfg_eq]
      refine (applicable_gen (prec_exec hn hget ha) (mod_ne_zero_cur _ _ _) s _
        (fun x hx => mod_ne_zero_of_mem_ctlSet hx)).2 ⟨happ1, ?_⟩
      exact Set.singleton_subset_iff.2 (encCur_mem_ctlSet_iff.2 ⟨rest, rfl, rfl⟩)
    · rw [htr]; exact hbs
    · rw [ActionModel.transitionSeq_cons, htr]; exact hbseq
  | @push m j c m' rest as ha hlast hm' hc hdepth h ih =>
    intro _ hwf hlen s happ
    obtain ⟨hm, -⟩ := hwf.head
    have hi : rest.length < d.methods.length := by omega
    have hx : (2, rest.length, m, j, m') ∈ cacts d :=
      mem_cacts (by norm_num) hi hm
        (lt_size_of_le_length_bd (show j ≤ (d.bd m).length by omega)) hm'
    have hn := nameOf_lt hx
    have hget := getI_nameOf hx
    have hi1 : rest.length + 1 < d.methods.length := by omega
    have htr : (trStripsDom d).toDomain.transition (nameOf d (2, rest.length, m, j, m'))
        (cfg s ((m, j) :: rest)) = cfg s ((m', 0) :: (m, j + 1) :: rest) := by
      rw [cfg_eq, transition_gen (del_push hn hget ha hc hlast hm' hi1)
        (add_push hn hget ha hc hlast hm' hi1) (mod_ne_zero_cur _ _ _)
        (mod_ne_zero_pair_cur_sav _ _ _ _ _ _) s (ctlSet ((m, j) :: rest))
        (fun x hx => mod_ne_zero_of_mem_ctlSet hx),
        ctl_step_push rest.length m j m' rfl, cfg_eq]
      simp
    have hwf' : StackWF d ((m', 0) :: (m, j + 1) :: rest) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hm', by simp⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨hm, by simp only; omega⟩
        · exact hwf.tail p hp
    obtain ⟨bs, hbs, hbseq⟩ := ih (by simp) hwf' (by simp only [List.length_cons]; omega) s happ
    refine ⟨nameOf d (2, rest.length, m, j, m') :: bs, ⟨?_, ?_⟩, ?_⟩
    · rw [cfg_eq]
      refine (applicable_gen (prec_push hn hget ha hc hlast hm' hi1) (mod_ne_zero_cur _ _ _) s _
        (fun x hx => mod_ne_zero_of_mem_ctlSet hx)).2 ⟨Set.empty_subset _, ?_⟩
      exact Set.singleton_subset_iff.2 (encCur_mem_ctlSet_iff.2 ⟨rest, rfl, rfl⟩)
    · rw [htr]; exact hbs
    · rw [ActionModel.transitionSeq_cons, htr]; exact hbseq
  | @tailCall m j c m' rest as ha hlast hm' hc h ih =>
    intro _ hwf hlen s happ
    obtain ⟨hm, -⟩ := hwf.head
    have hi : rest.length < d.methods.length := by
      simp only [List.length_cons] at hlen
      omega
    have hx : (3, rest.length, m, j, m') ∈ cacts d :=
      mem_cacts (by norm_num) hi hm
        (lt_size_of_le_length_bd (show j ≤ (d.bd m).length by omega)) hm'
    have hn := nameOf_lt hx
    have hget := getI_nameOf hx
    have htr : (trStripsDom d).toDomain.transition (nameOf d (3, rest.length, m, j, m'))
        (cfg s ((m, j) :: rest)) = cfg s ((m', 0) :: rest) := by
      rw [cfg_eq, transition_gen (del_tail hn hget ha hc hlast hm')
        (add_tail hn hget ha hc hlast hm') (mod_ne_zero_cur _ _ _) (mod_ne_zero_cur _ _ _) s
        (ctlSet ((m, j) :: rest)) (fun x hx => mod_ne_zero_of_mem_ctlSet hx),
        ctl_step_cur rest.length m j m' 0 rfl, cfg_eq]
      simp
    have hwf' : StackWF d ((m', 0) :: rest) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hm', by simp⟩
      · exact hwf.tail p hp
    obtain ⟨bs, hbs, hbseq⟩ := ih (by simp) hwf' (by simpa using hlen) s happ
    refine ⟨nameOf d (3, rest.length, m, j, m') :: bs, ⟨?_, ?_⟩, ?_⟩
    · rw [cfg_eq]
      refine (applicable_gen (prec_tail hn hget ha hc hlast hm') (mod_ne_zero_cur _ _ _) s _
        (fun x hx => mod_ne_zero_of_mem_ctlSet hx)).2 ⟨Set.empty_subset _, ?_⟩
      exact Set.singleton_subset_iff.2 (encCur_mem_ctlSet_iff.2 ⟨rest, rfl, rfl⟩)
    · rw [htr]; exact hbs
    · rw [ActionModel.transitionSeq_cons, htr]; exact hbseq

/-! ### Solvability of the compiled description -/

/-- The initial state of the compiled instance description. -/
theorem trStripsInst_init (q : InstDesc) :
    {f | f ∈ (trStripsInst q).initList} = startCfg {v | v ∈ q.initList} (rootName q) := by
  rw [startCfg_eq]
  show {f | f ∈ q.initList.map encSt ++ [encCall (rootName q)]} = _
  rw [setOf_mem_append, setOf_mem_map_encSt, setOf_mem_singleton]

/-- The goal of the compiled instance description. -/
theorem trStripsInst_goal (q : InstDesc) :
    {f | f ∈ (trStripsInst q).goalList} = stSet {v | v ∈ q.goalList} ∪ {encDone} := by
  show {f | f ∈ q.goalList.map encSt ++ [encDone]} = _
  rw [setOf_mem_append, setOf_mem_map_encSt, setOf_mem_singleton]

theorem subset_of_stSet_subset_endCfg {G s' : Set ℕ} (h : stSet G ⊆ endCfg s') : G ⊆ s' := by
  intro v hv
  rcases h ⟨v, hv, rfl⟩ with hmem | hmem
  · exact absurd (congrArg (· % 6) hmem) (by simp)
  · simpa using hmem

/-- **The compiled description is solvable exactly when the source description is.**

The source domain description is totally ordered and tail recursive, the source instance
description is *rooted* — its initial task network is a single compound task. -/
theorem solvable_trStrips_iff {d : DomDesc} {q : InstDesc} (hTO : d.MethodsTO)
    (hTR : d.IsTailRec) (hroot : q.IsRooted) :
    Solvable (trStripsDom d) (trStripsInst q) ↔ Solvable d q := by
  obtain ⟨rk, hrk⟩ := hTR
  obtain ⟨t₀, hT, hα⟩ := InstDesc.rootName_spec hroot
  have hseq : (problem d q).tnI.IsSeqNet [t₀] [Sum.inr (rootName q)] := by
    have h := TaskNetwork.isSeqNet_singleton (problem_wf d q).tnI hT
    have hα' : (problem d q).tnI.α t₀ = Sum.inr (rootName q) := hα
    rwa [hα'] at h
  have hTOm : (problem d q).IsTO_M := (isTO_problem hTO hroot.isTO).2
  -- the source side: a refinement of the initial compound task
  have hsrc : Solvable d q ↔ ∃ as : List ℕ, d.toDomain.YieldSeq [Sum.inr (rootName q)] as ∧
      d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf d q) hTOm hseq
  -- the target side: a classical plan
  have htgt : Solvable (trStripsDom d) (trStripsInst q) ↔
      ∃ bs : List ℕ, (trStripsDom d).toDomain.SeqApplicable bs
          (startCfg {v | v ∈ q.initList} (rootName q)) ∧
        stSet {v | v ∈ q.goalList} ∪ {encDone} ⊆ (trStripsDom d).toDomain.transitionSeq bs
          (startCfg {v | v ∈ q.initList} (rootName q)) := by
    have h := solvable_strips_iff (trActions d) (trStripsInst q).initList
      (trStripsInst q).goalList
    rw [show stripsInst (trStripsInst q).initList (trStripsInst q).goalList = trStripsInst q from
      rfl] at h
    rw [show stripsDom (trActions d) = trStripsDom d from rfl] at h
    rw [h, trStripsInst_init q, trStripsInst_goal q]
  rw [hsrc, htgt]
  constructor
  · rintro ⟨bs, happ, hgoal⟩
    have hdone : encDone ∈ (trStripsDom d).toDomain.transitionSeq bs
        (startCfg {v | v ∈ q.initList} (rootName q)) := hgoal (Or.inr rfl)
    obtain ⟨m, as, hm, hc, hrun, hasapp, heq⟩ := run_of_start_plan bs _ _ happ hdone
    refine ⟨as, (yieldSeq_singleton_iff_run hTO hrk).2 ⟨m, hm, hc, hrun⟩, hasapp, ?_⟩
    refine subset_of_stSet_subset_endCfg ?_
    rw [← heq]
    exact fun x hx => hgoal (Or.inl hx)
  · rintro ⟨as, hy, hasapp, hgoal⟩
    obtain ⟨m, hm, hc, hrun⟩ := (yieldSeq_singleton_iff_run hTO hrk).1 hy
    have hx : (0, 0, m, 0, 0) ∈ cacts d :=
      mem_cacts (by norm_num) (by omega) hm (by omega) (by omega)
    have hn := nameOf_lt hx
    have hget := getI_nameOf hx
    have hwf : StackWF d [(m, 0)] := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hm, by simp⟩
      · simp at hp
    obtain ⟨bs, hbs, hbseq⟩ :=
      exists_plan_of_run hrun (by simp) hwf
        (by simp only [List.length_cons, List.length_nil]; omega) {v | v ∈ q.initList} hasapp
    have htr : (trStripsDom d).toDomain.transition (nameOf d (0, 0, m, 0, 0))
        (startCfg {v | v ∈ q.initList} (rootName q)) = cfg {v | v ∈ q.initList} [(m, 0)] := by
      rw [startCfg_eq, transition_gen (del_beg hn hget hm) (add_beg hn hget hm)
        (mod_ne_zero_startCfg _) (mod_ne_zero_cur _ _ _) _ {encCall (rootName q)}
        (mod_ne_zero_startCfg _), hc, ctl_step_beg, cfg_eq]
      simp
    refine ⟨nameOf d (0, 0, m, 0, 0) :: bs, ⟨?_, ?_⟩, ?_⟩
    · rw [startCfg_eq]
      refine (applicable_gen (prec_beg hn hget hm) (mod_ne_zero_startCfg _) _
        {encCall (rootName q)} (mod_ne_zero_startCfg _)).2 ⟨Set.empty_subset _, ?_⟩
      rw [hc]
    · rw [htr]; exact hbs
    · rw [ActionModel.transitionSeq_cons, htr, hbseq, endCfg_eq]
      exact Set.union_subset_union_left _ (Set.image_mono hgoal)

end Syn

end HTN
