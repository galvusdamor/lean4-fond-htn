import HtnComplexity.Space.ThrStep
/-!
# Regular HTN with an initial task network is the thread system

    HTN.Space.Thr.solvable_iff_tsolv :
      Solvable P.d q ↔ TSolv P {f | f ∈ q.initList} {f | f ∈ q.goalList}

for a regular domain description and an instance whose initial task network is isomorphic to
the canonical network of the initial thread configuration.

A thread configuration `c` *represents* a search node `n` of the progression search iff the
states agree and `toTN P c.th` is isomorphic to the task network of `n`.  Every step of the
thread system is simulated by at most one progression step (`HTN.Space.Thr.sound_step`), and
every progression step by one or two steps of the thread system
(`HTN.Space.Thr.complete_step`); both directions keep the invariant `HTN.Space.Thr.Inv`.
-/

namespace HTN

namespace Space

namespace Thr

open Syn

variable {P : Par}

/-! ### The invariant -/

variable (P) in
/-- **The invariant of the thread system**: a running thread runs a listed method and has
executed primitive subtasks only, and a thread that has started has idle predecessors. -/
structure Inv (c : Cfg) : Prop where
  run : ∀ j < P.k, ∀ μ D, c.th j = .run μ D → μ < P.d.methods.length ∧ D ⊆ prims P.d μ
  pre : ∀ j < P.k, c.th j ≠ .pend → ∀ i < P.k, P.O i j → Idle P c.th i

theorem inv_init (s₀ : Set ℕ) : Inv P (initCfg s₀) where
  run j _ μ D h := by simp [initCfg] at h
  pre j _ h := absurd rfl h

theorem idle_update_of_ne {th : ℕ → TSt} {j i : ℕ} {s : TSt} (h : i ≠ j) :
    Idle P (Function.update th j s) i ↔ Idle P th i := by
  unfold Idle
  rw [Function.update_of_ne h]

/-- A body all of whose subtasks have been executed has no compound subtask. -/
theorem closed_of_idle {th : ℕ → TSt} {j μ : ℕ} {D : Finset ℕ} (hs : th j = .run μ D)
    (hD : D ⊆ prims P.d μ) (hidle : Idle P th j) : closed P.d μ = .fin := by
  unfold Idle at hidle
  rw [hs, thTasks_run_eq_empty] at hidle
  unfold closed
  rw [tail_eq_none fun z hz => (mem_prims.1 (hD (hidle z hz))).2]

/-- Idle threads stay idle. -/
theorem idle_of_step {c : Cfg} (hinv : Inv P c) {c' : Cfg} (h : TStep P c c') {i : ℕ} (hi : i < P.k)
    (hidle : Idle P c.th i) : Idle P c'.th i := by
  cases h with
  | @expandP j μ hj hs hl hμ hpre =>
    by_cases hij : i = j
    · subst hij; unfold Idle at hidle; rw [hs] at hidle; simp [thTasks] at hidle
    · exact (idle_update_of_ne hij).2 hidle
  | @expandC j μ hj hs hμ =>
    by_cases hij : i = j
    · subst hij; unfold Idle at hidle; rw [hs] at hidle; simp [thTasks] at hidle
    · exact (idle_update_of_ne hij).2 hidle
  | @exec j μ x a D hj hs hx hxD hpre hl happ =>
    by_cases hij : i = j
    · subst hij
      unfold Idle at hidle
      rw [hs] at hidle
      exact absurd (mem_thTasks_run.2 ⟨x, (mem_prims.1 hx).1, hxD, rfl⟩)
        (by rw [hidle]; simp)
    · exact (idle_update_of_ne hij).2 hidle
  | @close j μ D hj hs hD =>
    by_cases hij : i = j
    · subst hij
      have := closed_of_idle hs (hinv.run i hi μ D hs).2 hidle
      show thTasks P.d (Function.update c.th i (closed P.d μ) i) i = ∅
      rw [Function.update_self, this]
      rfl
    · exact (idle_update_of_ne hij).2 hidle
  | @execP j a hj hs hl hpre happ =>
    by_cases hij : i = j
    · subst hij; unfold Idle at hidle; rw [hs] at hidle; simp [thTasks] at hidle
    · exact (idle_update_of_ne hij).2 hidle

/-- **The invariant is preserved.** -/
theorem inv_step (hP : Good P) {c : Cfg} (hinv : Inv P c) {c' : Cfg} (h : TStep P c c') : Inv P c' := by
  -- the thread that moves, and what happens to it
  obtain ⟨j, s, hj, hth, hs_run, hs_pre⟩ : ∃ j s, j < P.k ∧ c'.th = Function.update c.th j s ∧
      (∀ μ D, s = .run μ D → μ < P.d.methods.length ∧ D ⊆ prims P.d μ) ∧
      (s ≠ .pend → ∀ i < P.k, P.O i j → Idle P c.th i) := by
    cases h with
    | @expandP j μ hj hs hl hμ hpre =>
      exact ⟨j, _, hj, rfl, fun μ' D h => by cases h; exact ⟨hμ, by simp⟩, fun _ => hpre⟩
    | @expandC j μ hj hs hμ =>
      exact ⟨j, _, hj, rfl, fun μ' D h => by cases h; exact ⟨hμ, by simp⟩,
        fun _ => hinv.pre j hj (by rw [hs]; simp)⟩
    | @exec j μ x a D hj hs hx hxD hpre hl happ =>
      refine ⟨j, _, hj, rfl, fun μ' D' h => ?_, fun _ => hinv.pre j hj (by rw [hs]; simp)⟩
      cases h
      obtain ⟨hμ, hD⟩ := hinv.run j hj μ D hs
      exact ⟨hμ, Finset.insert_subset hx hD⟩
    | @close j μ D hj hs hD =>
      refine ⟨j, _, hj, rfl, fun μ' D' h => ?_, fun _ => hinv.pre j hj (by rw [hs]; simp)⟩
      unfold closed at h
      split at h <;> simp at h
    | @execP j a hj hs hl hpre happ =>
      exact ⟨j, _, hj, rfl, fun μ' D h => by simp at h, fun _ => hpre⟩
  constructor
  · intro l hl μ D hs
    rw [hth] at hs
    by_cases hlj : l = j
    · subst hlj
      rw [Function.update_self] at hs
      exact hs_run μ D hs
    · rw [Function.update_of_ne hlj] at hs
      exact hinv.run l hl μ D hs
  · intro l hl hnp i hi hO
    rw [hth]
    by_cases hlj : l = j
    · subst hlj
      rw [hth, Function.update_self] at hnp
      have hil : i ≠ l := fun h => hP.irrefl i (h ▸ hO)
      exact (idle_update_of_ne hil).2 (hs_pre hnp i hi hO)
    · rw [hth, Function.update_of_ne hlj] at hnp
      have := idle_of_step hinv h hi (hinv.pre l hl hnp i hi hO)
      rwa [hth] at this

theorem inv_reach (hP : Good P) {c c' : Cfg} (hinv : Inv P c)
    (h : Relation.ReflTransGen (TStep P) c c') : Inv P c' := by
  induction h with
  | refl => exact hinv
  | tail _ hstep ih => exact inv_step hP ih hstep

/-! ### Transport along an isomorphism -/

theorem unc_map {tn₁ tn₂ : TaskNetwork ℕ ℕ ℕ} {σ : ℕ → ℕ}
    (hbij : Set.BijOn σ (tn₁.T : Set ℕ) (tn₂.T : Set ℕ))
    (hord : ∀ x ∈ tn₁.T, ∀ y ∈ tn₁.T, (tn₁.ord x y ↔ tn₂.ord (σ x) (σ y)))
    {a : ℕ} (ha : tn₁.Unconstrained a) : tn₂.Unconstrained (σ a) := by
  refine ⟨by simpa using hbij.mapsTo (by simpa using ha.1), ?_⟩
  intro t ht hord'
  obtain ⟨b, hb, rfl⟩ := hbij.surjOn (by simpa using ht)
  exact ha.2 b (by simpa using hb) ((hord b (by simpa using hb) a ha.1).2 hord')

theorem unc_unmap {tn₁ tn₂ : TaskNetwork ℕ ℕ ℕ} {σ : ℕ → ℕ}
    (hbij : Set.BijOn σ (tn₁.T : Set ℕ) (tn₂.T : Set ℕ))
    (hord : ∀ x ∈ tn₁.T, ∀ y ∈ tn₁.T, (tn₁.ord x y ↔ tn₂.ord (σ x) (σ y)))
    {a : ℕ} (haT : a ∈ tn₁.T) (ha : tn₂.Unconstrained (σ a)) : tn₁.Unconstrained a := by
  refine ⟨haT, fun b hb hba => ha.2 (σ b) ?_ ((hord b hb a haT).1 hba)⟩
  simpa using hbij.mapsTo (by simpa using hb)

/-- A fresh copy of a described network, avoiding a given finite set. -/
theorem exists_fresh_copy (T₀ : Finset ℕ) (t : TnDesc) :
    ∃ u : TaskNetwork ℕ ℕ ℕ, u.WF ∧ u.Iso t.toTaskNetwork ∧ Disjoint T₀ u.T := by
  refine ⟨(TnDesc.shift (T₀.sup id + 1) t).toTaskNetwork, TnDesc.toTaskNetwork_wf _,
    TnDesc.shift_iso _ _, ?_⟩
  rw [Finset.disjoint_left]
  intro x hx hxu
  simp only [TnDesc.toTaskNetwork_T, List.mem_toFinset] at hxu
  obtain ⟨y, -, rfl⟩ := TnDesc.mem_shift_ids.1 hxu
  have h2 : T₀.sup id + 1 + y ≤ T₀.sup id := Finset.le_sup (f := id) hx
  omega

theorem copy_disjoint {th : ℕ → TSt} {j μ : ℕ} (hth : th j = .pend ∨ ∃ c, th j = .cur c) :
    Disjoint (toTN P th).T (copy P j μ).T := by
  rw [Finset.disjoint_left]
  intro a ha hac
  obtain ⟨x, -, rfl⟩ := mem_copy.1 hac
  have := mem_tasks_thread (P := P) (j := j) ha (by simp)
  rcases hth with h | ⟨c, h⟩ <;> rw [h] at this <;> simp [thTasks, tid_inj] at this


/-! ### Labels and closing -/

theorem toTN_α_tid (th : ℕ → TSt) (j y : ℕ) :
    (toTN P th).α (tid j y) = thLabel P.d P.lab (th j) j y := by
  rw [toTN_α, th_tid th]
  simp

theorem exists_compound_of_tail {d : DomDesc} {μ cc : ℕ} (h : tail d μ = some cc) :
    ∃ z ∈ (body d μ).ids, (body d μ).label z = Sum.inr cc := by
  unfold tail at h
  rcases hh : (body d μ).compoundNames with _ | ⟨c', l⟩
  · rw [hh] at h
    simp at h
  · rw [hh] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact TnDesc.mem_compoundNames.1 (by rw [hh]; simp)

/-- **Closing a body changes the canonical network only up to isomorphism.** -/
theorem close_iso (hP : Good P) {th : ℕ → TSt} {j μ : ℕ} {D : Finset ℕ} (hj : j < P.k)
    (hs : th j = .run μ D) (hμ : μ < P.d.methods.length) (hD : D ⊆ prims P.d μ)
    (hD' : prims P.d μ ⊆ D) :
    (toTN P (Function.update th j (closed P.d μ))).Iso (toTN P th) := by
  rcases ht : tail P.d μ with _ | cc
  · have hcl : closed P.d μ = .fin := by unfold closed; rw [ht]
    rw [hcl]
    refine toTN_close_none hs fun x hx => hD' (mem_prims.2 ⟨hx, ?_⟩)
    rcases hl : (body P.d μ).label x with a | c''
    · rfl
    · rw [tail_eq_some hP.reg hμ hx hl] at ht
      simp at ht
  · have hcl : closed P.d μ = .cur cc := by unfold closed; rw [ht]
    rw [hcl]
    obtain ⟨z, hz, hl⟩ := exists_compound_of_tail ht
    have hzD : z ∉ D := fun h => by
      have := (mem_prims.1 (hD h)).2
      rw [hl] at this
      simp at this
    have hall : ∀ x ∈ (body P.d μ).ids, x ≠ z → x ∈ D := by
      intro x hx hxz
      refine hD' (mem_prims.2 ⟨hx, ?_⟩)
      rcases hl' : (body P.d μ).label x with a | c''
      · rfl
      · exact absurd (compound_unique hP.reg hμ hx hl' hz hl) hxz
    obtain ⟨h1, h2, h3⟩ := close_iso_some hj hs hz hzD hall hl
    exact ⟨closeMap j z, h1, h2, h3⟩

/-! ### Soundness -/

/-- **Every step of the thread system is simulated by at most one progression step.** -/
theorem sound_step (hP : Good P) {q : InstDesc} {c c' : Cfg} (hinv : Inv P c)
    (h : TStep P c c') {n : SearchNode ℕ ℕ ℕ ℕ} (hst : n.state = c.st)
    (hiso : (toTN P c.th).Iso n.net) (hwf : n.net.WF) :
    ∃ n', Relation.ReflTransGen (problem P.d q).Step n n' ∧ n'.state = c'.st ∧
      (toTN P c'.th).Iso n'.net := by
  obtain ⟨σ, hσbij, hσord, hσα⟩ := hiso
  -- the two expansions
  have hdec : ∀ {j μ : ℕ}, j < P.k → (c.th j = .pend ∨ ∃ cc, c.th j = .cur cc) →
      μ < P.d.methods.length → (∀ i < P.k, P.O i j → Idle P c.th i) →
      (toTN P c.th).α (tid j 0) = Sum.inr (head P.d μ) →
      ∃ n', Relation.ReflTransGen (problem P.d q).Step n n' ∧ n'.state = c.st ∧
        (toTN P (Function.update c.th j (.run μ ∅))).Iso n'.net := by
    intro j μ hj hth hμ hpre hlab
    have hunc := unc_single hj hth hpre
    have hunc' := unc_map hσbij hσord hunc
    obtain ⟨u, huwf, huiso, hdisj⟩ := exists_fresh_copy n.net.T (body P.d μ)
    obtain ⟨ρ, hρbij, hρord, hρα⟩ := (copy_iso (P := P) j μ).trans huiso.symm
    refine ⟨⟨n.state, decomposeWith n.net (σ (tid j 0)) u, n.plan⟩, ?_, hst, ?_⟩
    · refine Relation.ReflTransGen.single ?_
      refine Problem.Step.decomp (s := n.state) (π := n.plan) (m := (mth P.d μ).toMethod) hunc'
        ⟨⟨mth P.d μ, mth_mem hμ, rfl⟩, hunc'.1, ?_, u, huwf, huiso, hdisj, rfl⟩
      rw [← hσα _ hunc.1, hlab]
      rfl
    · exact (toTN_expand hj hth hpre).trans (decomposeWith_iso_congr (toTN_wf hP _) hwf
        (copy_wf j μ) huwf (copy_disjoint hth) hdisj hunc.1 hσbij hσord hσα hρbij hρord hρα)
  -- the two executions
  have hprog : ∀ {a : ℕ} {a' : ℕ}, (toTN P c.th).Unconstrained a →
      (toTN P c.th).α a = Sum.inl a' → P.d.prec a' ⊆ c.st →
      ∃ n', Relation.ReflTransGen (problem P.d q).Step n n' ∧
        n'.state = (c.st \ P.d.del a') ∪ P.d.add a' ∧ ((toTN P c.th).progress a).Iso n'.net := by
    intro a a' hunc hlab happ
    have hunc' := unc_map hσbij hσord hunc
    refine ⟨⟨(problem P.d q).transition a' n.state, n.net.progress (σ a), n.plan ++ [a']⟩,
      Relation.ReflTransGen.single ?_, ?_, TaskNetwork.iso_progress hσbij hσord hσα hunc.1⟩
    · refine Problem.Step.prog (s := n.state) (π := n.plan) hunc' ?_ ?_
      · rw [← hσα _ hunc.1, hlab]
      · show P.d.prec a' ⊆ n.state
        rw [hst]; exact happ
    · show (n.state \ P.d.del a') ∪ P.d.add a' = _
      rw [hst]
  cases h with
  | @expandP j μ hj hs hl hμ hpre =>
    exact hdec hj (Or.inl hs) hμ hpre (by rw [toTN_α_tid, hs]; exact hl)
  | @expandC j μ hj hs hμ =>
    exact hdec hj (Or.inr ⟨_, hs⟩) hμ (hinv.pre j hj (by rw [hs]; simp))
      (by rw [toTN_α_tid, hs]; rfl)
  | @exec j μ x a D hj hs hx hxD hpre hl happ =>
    have hunc := unc_exec hj hs (mem_prims.1 hx).1 hxD hpre (hinv.pre j hj (by rw [hs]; simp))
    obtain ⟨n', h1, h2, h3⟩ := hprog hunc (by rw [toTN_α_tid, hs]; exact hl) happ
    exact ⟨n', h1, h2, (toTN_exec hs).trans h3⟩
  | @close j μ D hj hs hD =>
    obtain ⟨hμ, hD'⟩ := hinv.run j hj μ D hs
    exact ⟨n, Relation.ReflTransGen.refl, hst,
      (close_iso hP hj hs hμ hD' hD).trans ⟨σ, hσbij, hσord, hσα⟩⟩
  | @execP j a hj hs hl hpre happ =>
    have hunc := unc_single hj (Or.inl hs) hpre
    obtain ⟨n', h1, h2, h3⟩ := hprog hunc (by rw [toTN_α_tid, hs]; exact hl) happ
    exact ⟨n', h1, h2, (toTN_execP hs).trans h3⟩


/-! ### Completeness -/

/-- **Every progression step is simulated by one or two steps of the thread system.** -/
theorem complete_step (hP : Good P) {q : InstDesc} {c : Cfg} (hinv : Inv P c)
    {n n' : SearchNode ℕ ℕ ℕ ℕ} (hstep : (problem P.d q).Step n n') (hst : n.state = c.st)
    (hiso : (toTN P c.th).Iso n.net) (hwf : n.net.WF) :
    ∃ c', Relation.ReflTransGen (TStep P) c c' ∧ n'.state = c'.st ∧
      (toTN P c'.th).Iso n'.net := by
  obtain ⟨σ, hσbij, hσord, hσα⟩ := hiso
  -- the predecessors of an unconstrained task are idle
  have hidle : ∀ {j y : ℕ}, (toTN P c.th).Unconstrained (tid j y) →
      ∀ i < P.k, P.O i j → Idle P c.th i := by
    intro j y hunc i hi hO
    unfold Idle
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    have hbT : b ∈ tasks P c.th := mem_tasks_of hi hb
    have hb1 : b.unpair.1 = i := mem_thTasks_fst hb
    have hne : i ≠ j := fun h => hP.irrefl i (by rw [← h] at hO; exact hO)
    exact hunc.2 b hbT ⟨hbT, hunc.1, Or.inr ⟨by rw [hb1]; simpa using hne,
      by rw [hb1]; simpa using hO⟩⟩
  -- a task of a running body whose body-predecessor is still there is constrained
  have hbody : ∀ {j μ x z : ℕ} {D : Finset ℕ}, c.th j = .run μ D →
      (toTN P c.th).Unconstrained (tid j (z + 1)) → (body P.d μ).ordOf x z →
      j < P.k → x ∈ D := by
    intro j μ x z D hs hunc hord hj
    by_contra hxD
    have hbT : tid j (x + 1) ∈ tasks P c.th :=
      mem_tasks_of hj (by rw [hs]; exact mem_thTasks_run.2 ⟨x, hord.1, hxD, rfl⟩)
    refine hunc.2 _ hbT ⟨hbT, hunc.1, Or.inl ⟨by simp, μ, D, by rw [th_tid c.th]; exact hs,
      by simp, by simp, by simpa using hord⟩⟩
  cases hstep with
  | @prog s tn π t a' hu hα happ =>
    simp only at hst hσbij hσord hσα hwf ⊢
    obtain ⟨a, haT, rfl⟩ := hσbij.surjOn (by simpa using hu.1)
    have haT' : a ∈ (toTN P c.th).T := by simpa using haT
    obtain ⟨j, y, rfl⟩ : ∃ j y, a = tid j y := ⟨a.unpair.1, a.unpair.2, (Nat.pair_unpair a).symm⟩
    have hunc := unc_unmap hσbij hσord haT' hu
    have hlab : (toTN P c.th).α (tid j y) = Sum.inl a' := by rw [hσα _ haT']; exact hα
    rw [toTN_α_tid] at hlab
    have happ' : P.d.prec a' ⊆ c.st := by rw [← hst]; exact happ
    have hk : j < P.k := by simpa using (mem_tasks.1 haT').1
    have hmem : tid j y ∈ thTasks P.d (c.th j) j := by simpa using (mem_tasks.1 haT').2
    have hiso' := TaskNetwork.iso_progress hσbij hσord hσα haT'
    rcases hth : c.th j with _ | cc | ⟨μ, D⟩ | _ <;> rw [hth] at hmem hlab
    · -- a pending primitive initial task
      obtain rfl : y = 0 := by simpa [thTasks, tid_inj] using hmem
      refine ⟨_, Relation.ReflTransGen.single (TStep.execP hk hth hlab (hidle hunc) happ'), ?_,
        (toTN_execP hth).trans hiso'⟩
      show (s \ P.d.del a') ∪ P.d.add a' = _
      rw [hst]
    · obtain rfl : y = 0 := by simpa [thTasks, tid_inj] using hmem
      simp [thLabel] at hlab
    · obtain ⟨x, hx, hxD, hxy⟩ := mem_thTasks_run.1 hmem
      obtain rfl : y = x + 1 := (tid_inj.1 hxy).2
      have hl : (body P.d μ).label x = Sum.inl a' := hlab
      have hxp : x ∈ prims P.d μ := mem_prims.2 ⟨hx, by rw [hl]; rfl⟩
      refine ⟨_, Relation.ReflTransGen.single (TStep.exec hk hth hxp hxD
        (fun z hz => hbody hth hunc hz hk) hl happ'), ?_, (toTN_exec hth).trans hiso'⟩
      show (s \ P.d.del a') ∪ P.d.add a' = _
      rw [hst]
    · simp [thTasks] at hmem
  | @decomp s tn tn₂ π t m hu hdstep =>
    simp only at hst hσbij hσord hσα hwf ⊢
    obtain ⟨hmM, htT, hαt, u, huwf, huiso, hdisj, rfl⟩ := hdstep
    obtain ⟨e, he, rfl⟩ := hmM
    obtain ⟨μ, hμ, rfl⟩ := exists_mth_eq he
    obtain ⟨a, haT, rfl⟩ := hσbij.surjOn (by simpa using htT)
    have haT' : a ∈ (toTN P c.th).T := by simpa using haT
    obtain ⟨j, y, rfl⟩ : ∃ j y, a = tid j y := ⟨a.unpair.1, a.unpair.2, (Nat.pair_unpair a).symm⟩
    have hunc := unc_unmap hσbij hσord haT' hu
    have hlab : (toTN P c.th).α (tid j y) = Sum.inr (head P.d μ) := by
      rw [hσα _ haT']; exact hαt
    rw [toTN_α_tid] at hlab
    have hk : j < P.k := by simpa using (mem_tasks.1 haT').1
    have hmem : tid j y ∈ thTasks P.d (c.th j) j := by simpa using (mem_tasks.1 haT').2
    obtain ⟨ρ, hρbij, hρord, hρα⟩ := (copy_iso (P := P) j μ).trans huiso.symm
    rcases hth : c.th j with _ | cc | ⟨μ', D⟩ | _ <;> rw [hth] at hmem hlab
    · -- a pending compound initial task
      obtain rfl : y = 0 := by simpa [thTasks, tid_inj] using hmem
      have hpre := hidle hunc
      refine ⟨_, Relation.ReflTransGen.single (TStep.expandP hk hth hlab hμ hpre), hst, ?_⟩
      exact (toTN_expand hk (Or.inl hth) hpre).trans (decomposeWith_iso_congr (toTN_wf hP _) hwf
        (copy_wf j μ) huwf (copy_disjoint (Or.inl hth)) hdisj haT' hσbij hσord hσα hρbij hρord
        hρα)
    · -- the current compound task of a thread
      obtain rfl : y = 0 := by simpa [thTasks, tid_inj] using hmem
      have hcc : cc = head P.d μ := by simpa [thLabel] using hlab
      subst hcc
      have hpre := hinv.pre j hk (by rw [hth]; simp)
      refine ⟨_, Relation.ReflTransGen.single (TStep.expandC hk hth hμ), hst, ?_⟩
      exact (toTN_expand hk (Or.inr ⟨_, hth⟩) hpre).trans (decomposeWith_iso_congr
        (toTN_wf hP _) hwf (copy_wf j μ) huwf (copy_disjoint (Or.inr ⟨_, hth⟩)) hdisj haT' hσbij
        hσord hσα hρbij hρord hρα)
    · -- the compound subtask of a finished body: close it, then decompose
      obtain ⟨z, hz, hzD, hzy⟩ := mem_thTasks_run.1 hmem
      obtain rfl : y = z + 1 := (tid_inj.1 hzy).2
      have hlz : (body P.d μ').label z = Sum.inr (head P.d μ) := hlab
      obtain ⟨hμ', hDp⟩ := hinv.run j hk μ' D hth
      have hD' : prims P.d μ' ⊆ D := by
        intro x hx
        have hxz : x ≠ z := by
          rintro rfl
          have := (mem_prims.1 hx).2
          rw [hlz] at this
          simp at this
        exact hbody hth hunc (ordOf_of_compound hP.reg hμ' hz hlz (mem_prims.1 hx).1 hxz) hk
      have hcl : closed P.d μ' = .cur (head P.d μ) := by
        unfold closed
        rw [tail_eq_some hP.reg hμ' hz hlz]
      have hstep1 := TStep.close (P := P) hk hth hD'
      rw [hcl] at hstep1
      have hth1 : Function.update c.th j (.cur (head P.d μ)) j = .cur (head P.d μ) :=
        Function.update_self _ _ _
      have hstep2 := TStep.expandC (P := P) (c := ⟨c.st, Function.update c.th j
        (.cur (head P.d μ))⟩) hk hth1 hμ
      have hpre1 : ∀ i < P.k, P.O i j → Idle P (Function.update c.th j (.cur (head P.d μ))) i := by
        intro i hi hO
        have hij : i ≠ j := fun h => hP.irrefl i (by rw [← h] at hO; exact hO)
        exact (idle_update_of_ne hij).2 (hinv.pre j hk (by rw [hth]; simp) i hi hO)
      have hall : ∀ x ∈ (body P.d μ').ids, x ≠ z → x ∈ D := by
        intro x hx hxz
        refine hD' (mem_prims.2 ⟨hx, ?_⟩)
        rcases hl' : (body P.d μ').label x with a | c''
        · rfl
        · exact absurd (compound_unique hP.reg hμ' hx hl' hz hlz) hxz
      obtain ⟨h1, h2, h3⟩ := close_iso_some hk hth hz hzD hall hlz
      have hbij1 := hσbij.comp h1
      have hord1 : ∀ x ∈ (toTN P (Function.update c.th j (.cur (head P.d μ)))).T,
          ∀ y ∈ (toTN P (Function.update c.th j (.cur (head P.d μ)))).T,
          ((toTN P (Function.update c.th j (.cur (head P.d μ)))).ord x y ↔
            tn.ord ((σ ∘ closeMap j z) x) ((σ ∘ closeMap j z) y)) := fun x hx y hy =>
        (h2 x hx y hy).trans (hσord _ (by simpa using h1.mapsTo (by simpa using hx)) _
          (by simpa using h1.mapsTo (by simpa using hy)))
      have hα1 : ∀ x ∈ (toTN P (Function.update c.th j (.cur (head P.d μ)))).T,
          (toTN P (Function.update c.th j (.cur (head P.d μ)))).α x =
            tn.α ((σ ∘ closeMap j z) x) := fun x hx =>
        (h3 x hx).trans (hσα _ (by simpa using h1.mapsTo (by simpa using hx)))
      have ht0 : tid j 0 ∈ (toTN P (Function.update c.th j (.cur (head P.d μ)))).T :=
        tasks_update.2 (Or.inl ⟨by simp, hk, by simp [thTasks]⟩)
      have hcong := decomposeWith_iso_congr (toTN_wf hP _) hwf (copy_wf (P := P) j μ) huwf
        (copy_disjoint (Or.inr ⟨_, hth1⟩)) hdisj ht0 hbij1 hord1 hα1 hρbij hρord hρα
      have hσ1 : (σ ∘ closeMap j z) (tid j 0) = σ (tid j (z + 1)) := by
        simp [Function.comp, closeMap_self]
      rw [hσ1] at hcong
      exact ⟨_, Relation.ReflTransGen.single hstep1 |>.tail hstep2, hst,
        (toTN_expand hk (Or.inr ⟨_, hth1⟩) hpre1).trans hcong⟩
    · simp [thTasks] at hmem

/-! ### The main theorem -/

theorem idle_of_tasks_empty {th : ℕ → TSt} (h : tasks P th = ∅) : ∀ j < P.k, Idle P th j := by
  intro j hj
  unfold Idle
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a ha
  have := mem_tasks_of hj ha
  rw [h] at this
  simp at this

theorem tasks_empty_of_idle {th : ℕ → TSt} (h : ∀ j < P.k, Idle P th j) : tasks P th = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a ha
  obtain ⟨hk, hmem⟩ := mem_tasks.1 ha
  have := h _ hk
  unfold Idle at this
  rw [this] at hmem
  simp at hmem

/-- **Regular HTN with an initial task network is the thread system.** -/
theorem solvable_iff_tsolv (hP : Good P) {q : InstDesc}
    (hiso : q.tnI.toTaskNetwork.Iso (toTN P (fun _ => .pend))) :
    Solvable P.d q ↔ TSolv P {f | f ∈ q.initList} {f | f ∈ q.goalList} := by
  rw [Solvable, Problem.solvable_iff_exists_goalNode (problem_wf P.d q)]
  constructor
  · rintro ⟨n, hr, hgT, hgs⟩
    have key : ∀ n : SearchNode ℕ ℕ ℕ ℕ, (problem P.d q).ReachableNode n → ∃ c : Cfg,
        Relation.ReflTransGen (TStep P) (initCfg {f | f ∈ q.initList}) c ∧ Inv P c ∧
        n.state = c.st ∧ (toTN P c.th).Iso n.net := by
      intro n hn
      induction hn with
      | refl => exact ⟨_, Relation.ReflTransGen.refl, inv_init _, rfl, hiso.symm⟩
      | @tail b b' hr hstep ih =>
        obtain ⟨c, hc, hinv, hst, hiso'⟩ := ih
        obtain ⟨c', hc', hst', hiso''⟩ := complete_step hP hinv hstep hst hiso'
          (Problem.ReachableNode.wf (problem_wf P.d q) hr)
        exact ⟨c', hc.trans hc', inv_reach hP hinv hc', hst', hiso''⟩
    obtain ⟨c, hc, -, hst, hiso'⟩ := key n hr
    refine ⟨c, hc, idle_of_tasks_empty ?_, ?_⟩
    · have hcard := hiso'.card_eq
      rw [hgT] at hcard
      exact Finset.card_eq_zero.1 (by simpa using hcard)
    · rw [← hst]; exact hgs
  · rintro ⟨c, hc, hidle, hgoal⟩
    have key : ∀ c : Cfg, Relation.ReflTransGen (TStep P) (initCfg {f | f ∈ q.initList}) c →
        ∃ n : SearchNode ℕ ℕ ℕ ℕ, (problem P.d q).ReachableNode n ∧ Inv P c ∧
          n.state = c.st ∧ (toTN P c.th).Iso n.net := by
      intro c hc
      induction hc with
      | refl => exact ⟨_, Problem.ReachableNode.refl _, inv_init _, rfl, hiso.symm⟩
      | @tail b b' hr hstep ih =>
        obtain ⟨n, hn, hinv, hst, hiso'⟩ := ih
        obtain ⟨n', hn', hst', hiso''⟩ := sound_step (q := q) hP hinv hstep hst hiso'
          (Problem.ReachableNode.wf (problem_wf P.d q) hn)
        exact ⟨n', hn.trans hn', inv_step hP hinv hstep, hst', hiso''⟩
    obtain ⟨n, hn, -, hst, hiso'⟩ := key c hc
    refine ⟨n, hn, ?_, ?_⟩
    · have hcard := hiso'.card_eq
      have h0 : (toTN P c.th).T = ∅ := tasks_empty_of_idle hidle
      rw [h0] at hcard
      exact Finset.card_eq_zero.1 (by simpa using hcard.symm)
    · intro f hf
      rw [hst]
      exact hgoal hf

end Thr

end Space

end HTN
