import HtnComplexity.AcVerify.PathBasics
/-!
# Completeness of path witnesses: every solvable problem has one

`HTN.Syn.AcVer.exists_pathOK_of_solvable` — if the described problem `(d, q)` is solvable, it has
a path witness (`HTN.Syn.AcVer.PathOK`).

The proof follows a decomposition sequence `tnI →* tn` of a solution and records, for every task
of the current network, its path in the decomposition tree (`f t`), together with the list `E` of
empty leaves produced so far (methods with an empty subtask network).  The invariant
`HTN.Syn.AcVer.Inv` says that the recorded paths are well formed, that the order of the current
network is the order inherited along the paths, and that the recorded tree is consistent and
complete.  At the end the solution network is primitive, and its executable linearisation, with
the empty leaves appended, is the witness.
-/

namespace HTN

namespace Syn

namespace AcVer

variable {d : DomDesc} {q : InstDesc}

/-! ### Small facts about paths -/

theorem lastLabel_snoc (p : List PStep) (x : PStep) :
    lastLabel d q (p ++ [x]) = stepLabel d q x := by
  simp [lastLabel]

theorem lastLabel_eq_of_getLast? {p : List PStep} {x : PStep} (h : p.getLast? = some x) :
    lastLabel d q p = stepLabel d q x := by
  simp [lastLabel, h]

theorem leafAct_eq (p : List PStep) :
    leafAct d q p = Sum.elim id (fun _ => 0) (lastLabel d q p) := by
  unfold leafAct
  cases lastLabel d q p <;> rfl

theorem netOf_zero : netOf d q 0 = q.tnI := by simp [netOf]

theorem netOf_succ (k : ℕ) : netOf d q (k + 1) = (methodAt d (k + 1)).2 := by simp [netOf]

theorem methodAt_succ {k : ℕ} (hk : k < d.methods.length) :
    methodAt d (k + 1) = d.methods[k] := by
  simp [methodAt, List.getElem?_eq_getElem hk]

/-- A node path is not empty. -/
theorem NodeOK.ne_nil {p : List PStep} (h : NodeOK d q p) : p ≠ [] := by
  obtain ⟨⟨i, s, rfl⟩, -, -⟩ := h
  simp

/-- A node path ending in `x` can be extended by any step linked to `x` that names a task. -/
theorem NodeOK.snoc {p : List PStep} (h : NodeOK d q p) {y : PStep}
    (hl : ∀ x ∈ p.getLast?, Link d q x y) (hy : StepIn d q y) : NodeOK d q (p ++ [y]) := by
  obtain ⟨⟨i, s, rfl⟩, hc, hin⟩ := h
  refine ⟨⟨i, s ++ [y], by simp⟩, ?_, ?_⟩
  · exact List.IsChain.append hc (List.isChain_singleton y) (by simpa using hl)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hin x hx
    · simp only [List.mem_singleton] at hx
      exact hx ▸ hy

/-- An empty-leaf entry is not a node path. -/
theorem nodeOK_ne_eps {p e : List PStep} (hp : NodeOK d q p) (he : EntryOK d q (e, true)) :
    p ≠ e := by
  rintro rfl
  simp only [EntryOK, if_true] at he
  obtain ⟨p', y, hpy, -, -, -, hnil⟩ := he
  have : StepIn d q y := hp.2.2 y (by rw [hpy]; simp)
  rw [StepIn, hnil] at this
  simp at this

/-- The two shapes of a decomposition `P ++ x :: y :: s` of a path `f ++ [z]`. -/
theorem split_snoc {P s f : List PStep} {x y z : PStep} (h : P ++ x :: y :: s = f ++ [z]) :
    (s = [] ∧ y = z ∧ P ++ [x] = f) ∨ (∃ s₀, s = s₀ ++ [z] ∧ f = P ++ x :: y :: s₀) := by
  rcases List.eq_nil_or_concat s with rfl | ⟨s₀, w, rfl⟩
  · left
    have h' : (P ++ [x]) ++ [y] = f ++ [z] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨rfl, h2, h1⟩
  · right
    have h' : (P ++ x :: y :: s₀) ++ [w] = f ++ [z] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at h2
    exact ⟨s₀, by subst h2; simp, h1.symm⟩

/-! ### The invariant -/

/-- The paths recorded so far: those of the tasks of the current network and the empty leaves. -/
def Mem (tn : TaskNetwork ℕ ℕ ℕ) (f : ℕ → List PStep) (E : List (List PStep))
    (p : List PStep) : Prop :=
  (∃ t ∈ tn.T, p = f t) ∨ p ∈ E

/-- **The invariant of the completeness proof.** -/
structure Inv (d : DomDesc) (q : InstDesc) (tn : TaskNetwork ℕ ℕ ℕ) (f : ℕ → List PStep)
    (E : List (List PStep)) : Prop where
  wf : tn.WF
  node : ∀ t ∈ tn.T, NodeOK d q (f t)
  lbl : ∀ t ∈ tn.T, tn.α t = lastLabel d q (f t)
  inj : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, f t = f t' → t = t'
  ord : ∀ t ∈ tn.T, ∀ t' ∈ tn.T, tn.ord t t' ↔ DivOrd d q (f t) (f t')
  eps : ∀ e ∈ E, EntryOK d q (e, true)
  eps0 : ∀ e ∈ E, ∃ p k, e = p ++ [(k, 0)]
  nodup : E.Nodup
  div : ∀ p p', Mem tn f E p → Mem tn f E p' → p ≠ p' → ∃ x y, DivAt p p' x y ∧ x.1 = y.1
  roots : ∀ i ∈ q.tnI.ids, ∃ p, Mem tn f E p ∧ ∃ s, p = (0, i) :: s
  children : ∀ p, Mem tn f E p → ∀ (P : List PStep) (x y : PStep) (s : List PStep),
    p = P ++ x :: y :: s → ∀ j ∈ (netOf d q y.1).ids,
      ∃ p', Mem tn f E p' ∧ ∃ s', p' = P ++ x :: (y.1, j) :: s'

/-! ### The initial network -/

theorem divAt_single {i i' : ℕ} {x y : PStep} :
    DivAt [((0 : ℕ), i)] [((0 : ℕ), i')] x y ↔ x = (0, i) ∧ y = (0, i') ∧ i ≠ i' := by
  constructor
  · rintro ⟨P, su, sv, hu, hv, hxy⟩
    rcases P with _ | ⟨z, P⟩
    · simp only [List.nil_append, List.cons.injEq] at hu hv
      refine ⟨hu.1.symm, hv.1.symm, ?_⟩
      rintro rfl
      exact hxy (hu.1.symm.trans hv.1)
    · simp only [List.cons_append, List.cons.injEq] at hu
      simp at hu
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨[], [], [], rfl, rfl, by simpa using h⟩

theorem inv_init : Inv d q q.tnI.toTaskNetwork (fun i => [(0, i)]) [] where
  wf := TnDesc.toTaskNetwork_wf _
  node := by
    intro t ht
    refine ⟨⟨t, [], rfl⟩, List.isChain_singleton _, ?_⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simpa [StepIn, netOf_zero] using ht
  lbl := by
    intro t _
    simp [lastLabel, stepLabel, netOf_zero]
  inj := by
    intro t _ t' _ h
    simpa using h
  ord := by
    intro t _ t' _
    simp only [TnDesc.toTaskNetwork_ord]
    constructor
    · intro h
      have hne : t ≠ t' := by
        rintro rfl
        exact h.2.2.2 h.2.2.1
      exact ⟨(0, t), (0, t'), divAt_single.2 ⟨rfl, rfl, hne⟩, rfl, by
        simpa [netOf_zero, TnDesc.ordOf] using h⟩
    · rintro ⟨x, y, hd, -, ho⟩
      obtain ⟨rfl, rfl, -⟩ := divAt_single.1 hd
      simpa [netOf_zero, TnDesc.ordOf] using ho
  eps := by simp
  eps0 := by simp
  nodup := List.nodup_nil
  div := by
    rintro p p' (⟨t, -, rfl⟩ | h) (⟨t', -, rfl⟩ | h') hne
    · have : t ≠ t' := by rintro rfl; exact hne rfl
      exact ⟨(0, t), (0, t'), divAt_single.2 ⟨rfl, rfl, this⟩, rfl⟩
    all_goals simp_all
  roots := by
    intro i hi
    exact ⟨[(0, i)], Or.inl ⟨i, by simpa using hi, rfl⟩, [], rfl⟩
  children := by
    rintro p (⟨t, -, rfl⟩ | h) P x y s hp
    · rcases P with _ | ⟨z, P⟩ <;> simp at hp
    · simp at h

/-! ### One decomposition step -/

section Step

variable {tn tn' : TaskNetwork ℕ ℕ ℕ} {f : ℕ → List PStep} {E : List (List PStep)}

theorem Inv.mem_ne_ne {hI : Inv d q tn f E} {t : ℕ} (ht : t ∈ tn.T) {p : List PStep}
    (hp : Mem tn f E p) (hne : p ≠ f t) :
    ∃ x y, DivAt p (f t) x y ∧ x.1 = y.1 :=
  hI.div p (f t) hp (Or.inl ⟨t, ht, rfl⟩) hne

/-- **The invariant survives a decomposition step**, and the new paths are at most one step
longer than the path of the decomposed task (with at most one new empty leaf). -/
theorem Inv.stepB (hI : Inv d q tn f E) {t : ℕ} {m : Method ℕ ℕ ℕ} {tn₂ : TaskNetwork ℕ ℕ ℕ}
    (hstep : DecompStep (problem d q).methods tn t m tn₂) :
    ∃ f₂ E₂, Inv d q tn₂ f₂ E₂ ∧
      (∀ u ∈ tn₂.T, (u ∈ tn.T ∧ f₂ u = f u) ∨ (f₂ u).length = (f t).length + 1) ∧
      (∀ p ∈ E₂, p ∈ E ∨ p.length = (f t).length + 1) ∧ E₂.length ≤ E.length + 1 := by
  have hwf₂ : tn₂.WF := hstep.wf hI.wf
  obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn', hwf', ⟨σ, hbij, hσord, hσα⟩, hdisj, rfl⟩ := hstep
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  set e := d.methods[i] with he_def
  set k := i + 1 with hk
  have hmk : methodAt d k = e := methodAt_succ hi
  have hnk : netOf d q k = e.2 := by rw [hk, netOf_succ, hmk]
  -- the task `t`
  have hnode_t := hI.node t ht
  have hlink : ∀ j, ∀ x ∈ (f t).getLast?, Link d q x (k, j) := by
    intro j x hx
    refine ⟨by omega, by simpa [hk] using hi, ?_⟩
    rw [← lastLabel_eq_of_getLast? hx, ← hI.lbl t ht, hαt, hmk]
    rfl
  -- the copy
  have hσmaps : ∀ u ∈ tn'.T, σ u ∈ e.2.ids := fun u hu => by
    have := hbij.mapsTo hu
    simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using this
  have hσinj : ∀ u ∈ tn'.T, ∀ u' ∈ tn'.T, σ u = σ u' → u = u' :=
    fun u hu u' hu' h => hbij.injOn hu hu' h
  have hσsurj : ∀ j ∈ e.2.ids, ∃ u ∈ tn'.T, σ u = j := by
    intro j hj
    have : j ∈ ((e.toMethod).subtasks.T : Set ℕ) := by
      simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hj
    obtain ⟨u, hu, rfl⟩ := hbij.surjOn this
    exact ⟨u, hu, rfl⟩
  have hdisj' : ∀ u ∈ tn'.T, u ∉ tn.T := fun u hu hu' =>
    Finset.disjoint_left.1 hdisj hu' hu
  -- the new data
  let g : ℕ → List PStep := fun u => f t ++ [(k, σ u)]
  let f₂ : ℕ → List PStep := fun u => if u ∈ tn'.T then g u else f u
  let E₂ : List (List PStep) := if e.2.ids = [] then E ++ [f t ++ [(k, 0)]] else E
  -- old members other than `f t` diverge from `f t`
  have hold : ∀ p, Mem tn f E p → p ≠ f t → ∃ x y, DivAt p (f t) x y ∧ x.1 = y.1 :=
    fun p hp hne => hI.div p (f t) hp (Or.inl ⟨t, ht, rfl⟩) hne
  have hfne : ∀ u ∈ tn.T, u ≠ t → f u ≠ f t := fun u hu hne h => hne (hI.inj u hu t ht h)
  have hEne : ∀ p ∈ E, p ≠ f t := fun p hp h =>
    nodeOK_ne_eps hnode_t (hI.eps p hp) h.symm
  -- membership after the step
  have hmem₂ : ∀ p, Mem (decomposeWith tn t tn') f₂ E₂ p →
      (Mem tn f E p ∧ p ≠ f t) ∨ ∃ j, p = f t ++ [(k, j)] := by
    rintro p (⟨u, hu, rfl⟩ | hp)
    · simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu
      by_cases hu' : u ∈ tn'.T
      · right; exact ⟨σ u, by simp [f₂, g, hu']⟩
      · left
        have hu2 : u ≠ t ∧ u ∈ tn.T := hu.resolve_right hu'
        simp only [f₂, hu', if_false]
        exact ⟨Or.inl ⟨u, hu2.2, rfl⟩, hfne u hu2.2 hu2.1⟩
    · simp only [E₂] at hp
      split_ifs at hp with hids
      · rcases List.mem_append.1 hp with hp | hp
        · exact Or.inl ⟨Or.inr hp, hEne p hp⟩
        · simp only [List.mem_singleton] at hp
          exact Or.inr ⟨0, hp⟩
      · exact Or.inl ⟨Or.inr hp, hEne p hp⟩
  have hmem_old : ∀ p, Mem tn f E p → p ≠ f t → Mem (decomposeWith tn t tn') f₂ E₂ p := by
    rintro p (⟨u, hu, rfl⟩ | hp) hne
    · have hut : u ≠ t := by rintro rfl; exact hne rfl
      refine Or.inl ⟨u, ?_, ?_⟩
      · simp only [decomposeWith, Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨hut, hu⟩
      · simp [f₂, hdisj' u |>.mt (not_not.2 hu)]
    · refine Or.inr ?_
      simp only [E₂]
      split_ifs
      · exact List.mem_append_left _ hp
      · exact hp
  have hmem_new : ∀ u ∈ tn'.T, Mem (decomposeWith tn t tn') f₂ E₂ (g u) := by
    intro u hu
    refine Or.inl ⟨u, ?_, by simp [f₂, hu]⟩
    simp only [decomposeWith, Finset.mem_union]
    exact Or.inr hu
  have hmem_eps : e.2.ids = [] → Mem (decomposeWith tn t tn') f₂ E₂ (f t ++ [(k, 0)]) := by
    intro hids
    refine Or.inr ?_
    simp [E₂, hids]
  -- every extension of `f t` by a step of the method is recorded (if the method has tasks),
  -- and `f t` itself has a recorded extension
  have hext : ∃ y, Mem (decomposeWith tn t tn') f₂ E₂ (f t ++ [y]) := by
    by_cases hids : e.2.ids = []
    · exact ⟨_, hmem_eps hids⟩
    · obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ hids
      obtain ⟨u, hu, -⟩ := hσsurj j hj
      exact ⟨_, hmem_new u hu⟩
  have hchild : ∀ j ∈ e.2.ids, Mem (decomposeWith tn t tn') f₂ E₂ (f t ++ [(k, j)]) := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := hσsurj j hj
    exact hmem_new u hu
  -- an old member with the right shape, possibly replaced by an extension of `f t`
  have hrepl : ∀ p, Mem tn f E p → ∀ (P : List PStep) (x : PStep) (s : List PStep),
      p = P ++ x :: s → ∃ p', Mem (decomposeWith tn t tn') f₂ E₂ p' ∧ ∃ s', p' = P ++ x :: s' := by
    intro p hp P x s hps
    by_cases hpt : p = f t
    · obtain ⟨y, hy⟩ := hext
      exact ⟨_, hy, s ++ [y], by rw [← hpt, hps]; simp⟩
    · exact ⟨p, hmem_old p hp hpt, s, hps⟩
  refine ⟨f₂, E₂, ?_, ?_, ?_, ?_⟩
  rotate_left
  · intro u hu
    by_cases hu' : u ∈ tn'.T
    · right; simp [f₂, g, hu']
    · left
      simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu
      exact ⟨(hu.resolve_right hu').2, by simp [f₂, hu']⟩
  · intro p hp
    simp only [E₂] at hp
    split_ifs at hp
    · rcases List.mem_append.1 hp with h | h
      · exact Or.inl h
      · simp only [List.mem_singleton] at h
        subst h
        right; simp
    · exact Or.inl hp
  · simp only [E₂]
    split_ifs <;> simp
  refine
    { wf := hwf₂
      node := ?_
      lbl := ?_
      inj := ?_
      ord := ?_
      eps := ?_
      eps0 := ?_
      nodup := ?_
      div := ?_
      roots := ?_
      children := ?_ }
  · -- node
    intro u hu
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu
    by_cases hu' : u ∈ tn'.T
    · simp only [f₂, hu', if_true, g]
      refine hnode_t.snoc (hlink _) ?_
      simp only [StepIn, hnk]
      exact hσmaps u hu'
    · simp only [f₂, hu', if_false]
      exact hI.node u (hu.resolve_right hu').2
  · -- lbl
    intro u hu
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu
    by_cases hu' : u ∈ tn'.T
    · simp only [decomposeWith, f₂, hu', if_true, g, lastLabel_snoc]
      rw [hσα u hu']
      simp [stepLabel, hnk, MethodDesc.toMethod]
    · simp only [decomposeWith, f₂, hu', if_false]
      exact hI.lbl u (hu.resolve_right hu').2
  · -- inj
    intro u hu u' hu' h
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu hu'
    by_cases h1 : u ∈ tn'.T <;> by_cases h2 : u' ∈ tn'.T <;>
      simp only [f₂, g, h1, h2, if_true, if_false] at h
    · simp only [List.append_cancel_left_eq, List.cons.injEq, Prod.mk.injEq, true_and,
        and_true] at h
      exact hσinj u h1 u' h2 h
    · have hu2 := hu'.resolve_right h2
      obtain ⟨x, y, hd, -⟩ := hold _ (Or.inl ⟨u', hu2.2, rfl⟩) (hfne u' hu2.2 hu2.1)
      exact absurd ⟨_, h⟩ (not_prefix_of_divAt (divAt_symm hd))
    · have hu2 := hu.resolve_right h1
      obtain ⟨x, y, hd, -⟩ := hold _ (Or.inl ⟨u, hu2.2, rfl⟩) (hfne u hu2.2 hu2.1)
      exact absurd ⟨_, h.symm⟩ (not_prefix_of_divAt (divAt_symm hd))
    · exact hI.inj u (hu.resolve_right h1).2 u' (hu'.resolve_right h2).2 h
  · -- ord
    intro u hu u' hu'
    simp only [decomposeWith, Finset.mem_union, Finset.mem_erase] at hu hu'
    have hnT : ∀ v, v ∈ tn'.T → v ∉ tn.T := hdisj'
    have hL := @TaskNetwork.WF.mem_left _ _ _ _ hI.wf
    have hR := @TaskNetwork.WF.mem_right _ _ _ _ hI.wf
    have hL' := @TaskNetwork.WF.mem_left _ _ _ _ hwf'
    have hR' := @TaskNetwork.WF.mem_right _ _ _ _ hwf'
    by_cases h1 : u ∈ tn'.T <;> by_cases h2 : u' ∈ tn'.T
    · -- both new
      simp only [decomposeWith, f₂, g, if_pos h1, if_pos h2]
      have e1 : (tn'.ord u u' ∨ tn.ord u t ∧ u' ∈ tn'.T ∨ tn.ord t u' ∧ u ∈ tn'.T ∨
          tn.ord u u' ∧ u ≠ t ∧ u' ≠ t) ↔ tn'.ord u u' := by
        constructor
        · rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
          · exact h
          · exact absurd (hL h) (hnT u h1)
          · exact absurd (hR h) (hnT u' h2)
          · exact absurd (hL h) (hnT u h1)
        · exact Or.inl
      rw [e1, hσord u h1 u' h2]
      by_cases huu : u = u'
      · subst huu
        constructor
        · intro h
          exact absurd h ((TnDesc.toTaskNetwork_wf _).irrefl _)
        · rintro ⟨x, y, hd, -, -⟩
          obtain ⟨P, su, sv, hu1, hv1, hxy⟩ := hd
          exact absurd (by
            have := hu1.symm.trans hv1
            simp only [List.append_cancel_left_eq, List.cons.injEq] at this
            exact this.1) hxy
      · have hne : σ u ≠ σ u' := fun h => huu (hσinj u h1 u' h2 h)
        have hd : DivAt (f t ++ [(k, σ u)]) (f t ++ [(k, σ u')]) (k, σ u) (k, σ u') :=
          divAt_snoc (f t) (by simpa using hne) [] []
        constructor
        · intro h
          refine ⟨_, _, hd, rfl, ?_⟩
          rw [hnk]
          simpa [MethodDesc.toMethod] using h
        · rintro ⟨x, y, hd', -, ho⟩
          obtain ⟨rfl, rfl⟩ := divAt_unique hd hd'
          rw [hnk] at ho
          simpa [MethodDesc.toMethod] using ho
    · -- new, old
      have hu2 := hu'.resolve_right h2
      simp only [decomposeWith, f₂, g, if_pos h1, if_neg h2]
      have e1 : (tn'.ord u u' ∨ tn.ord u t ∧ u' ∈ tn'.T ∨ tn.ord t u' ∧ u ∈ tn'.T ∨
          tn.ord u u' ∧ u ≠ t ∧ u' ≠ t) ↔ tn.ord t u' := by
        constructor
        · rintro (h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
          · exact absurd (hR' h) h2
          · exact absurd h h2
          · exact h
          · exact absurd (hL h) (hnT u h1)
        · intro h; exact Or.inr (Or.inr (Or.inl ⟨h, h1⟩))
      rw [e1, hI.ord t ht u' hu2.2]
      obtain ⟨x, y, hd, -⟩ := hold _ (Or.inl ⟨u', hu2.2, rfl⟩) (hfne u' hu2.2 hu2.1)
      have := divOrd_append_iff (d := d) (q := q) (divAt_symm hd) [(k, σ u)] []
      simp only [List.append_nil] at this
      exact this.symm
    · -- old, new
      have hu2 := hu.resolve_right h1
      simp only [decomposeWith, f₂, g, if_neg h1, if_pos h2]
      have e1 : (tn'.ord u u' ∨ tn.ord u t ∧ u' ∈ tn'.T ∨ tn.ord t u' ∧ u ∈ tn'.T ∨
          tn.ord u u' ∧ u ≠ t ∧ u' ≠ t) ↔ tn.ord u t := by
        constructor
        · rintro (h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd (hL' h) h1
          · exact h
          · exact absurd h h1
          · exact absurd (hR h) (hnT u' h2)
        · intro h; exact Or.inr (Or.inl ⟨h, h2⟩)
      rw [e1, hI.ord u hu2.2 t ht]
      obtain ⟨x, y, hd, -⟩ := hold _ (Or.inl ⟨u, hu2.2, rfl⟩) (hfne u hu2.2 hu2.1)
      have := divOrd_append_iff (d := d) (q := q) hd [] [(k, σ u')]
      simp only [List.append_nil] at this
      exact this.symm
    · -- both old
      have hu2 := hu.resolve_right h1
      have hu2' := hu'.resolve_right h2
      simp only [decomposeWith, f₂, if_neg h1, if_neg h2]
      have e1 : (tn'.ord u u' ∨ tn.ord u t ∧ u' ∈ tn'.T ∨ tn.ord t u' ∧ u ∈ tn'.T ∨
          tn.ord u u' ∧ u ≠ t ∧ u' ≠ t) ↔ tn.ord u u' := by
        constructor
        · rintro (h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd (hL' h) h1
          · exact absurd h h2
          · exact absurd h h1
          · exact h
        · intro h; exact Or.inr (Or.inr (Or.inr ⟨h, hu2.1, hu2'.1⟩))
      rw [e1]
      exact hI.ord u hu2.2 u' hu2'.2
  · -- eps
    intro p hp
    simp only [E₂] at hp
    split_ifs at hp with hids
    · rcases List.mem_append.1 hp with hp | hp
      · exact hI.eps p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only [EntryOK, if_true]
        refine ⟨f t, (k, 0), rfl, hnode_t.ne_nil, hnode_t, ?_, by rw [hnk]; exact hids⟩
        exact List.IsChain.append hnode_t.2.1 (List.isChain_singleton _) (by
          simpa using hlink 0)
    · exact hI.eps p hp
  · -- eps0
    intro p hp
    simp only [E₂] at hp
    split_ifs at hp with hids
    · rcases List.mem_append.1 hp with hp | hp
      · exact hI.eps0 p hp
      · simp only [List.mem_singleton] at hp
        exact ⟨f t, k, hp⟩
    · exact hI.eps0 p hp
  · -- nodup
    simp only [E₂]
    split_ifs
    · refine List.nodup_append.2 ⟨hI.nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb hab
      obtain ⟨x, y, hd, -⟩ := hold _ (Or.inr ha) (hEne _ ha)
      exact not_prefix_of_divAt (divAt_symm hd) ⟨_, rfl⟩
    · exact hI.nodup
  · -- div
    intro p p' hp hp' hne
    rcases hmem₂ p hp with ⟨hp1, hpt⟩ | ⟨j, rfl⟩ <;>
      rcases hmem₂ p' hp' with ⟨hp1', hpt'⟩ | ⟨j', rfl⟩
    · exact hI.div p p' hp1 hp1' hne
    · obtain ⟨x, y, hd, hxy⟩ := hold p hp1 hpt
      exact ⟨x, y, divAt_append_right hd _, hxy⟩
    · obtain ⟨x, y, hd, hxy⟩ := hold p' hp1' hpt'
      exact ⟨y, x, divAt_append_left (divAt_symm hd) _, hxy.symm⟩
    · have hjj : (k, j) ≠ (k, j') := fun h => hne (by rw [h])
      exact ⟨_, _, divAt_snoc (f t) hjj [] [], rfl⟩
  · -- roots
    intro i hi
    obtain ⟨p, hp, s, hps⟩ := hI.roots i hi
    obtain ⟨p', hp', s', hps'⟩ := hrepl p hp [] (0, i) s (by simpa using hps)
    exact ⟨p', hp', s', by simpa using hps'⟩
  · -- children
    intro p hp P x y s hps j hj
    rcases hmem₂ p hp with ⟨hp1, -⟩ | ⟨j₀, rfl⟩
    · obtain ⟨p', hp', s', hps'⟩ := hI.children p hp1 P x y s hps j hj
      obtain ⟨p'', h1, s'', h2⟩ := hrepl p' hp' (P ++ [x]) (y.1, j) s' (by simp [hps'])
      exact ⟨p'', h1, s'', by simp [h2]⟩
    · rcases split_snoc hps.symm with ⟨rfl, rfl, hPx⟩ | ⟨s₀, rfl, hft⟩
      · refine ⟨_, hchild j (by simpa [hnk] using hj), [], ?_⟩
        rw [← hPx]
        simp
      · obtain ⟨p', hp', s', hps'⟩ :=
          hI.children (f t) (Or.inl ⟨t, ht, rfl⟩) P x y s₀ hft j hj
        obtain ⟨p'', h1, s'', h2⟩ := hrepl p' hp' (P ++ [x]) (y.1, j) s' (by simp [hps'])
        exact ⟨p'', h1, s'', by simp [h2]⟩

/-- **The invariant survives a decomposition step.** -/
theorem Inv.step (hI : Inv d q tn f E) {t : ℕ} {m : Method ℕ ℕ ℕ} {tn₂ : TaskNetwork ℕ ℕ ℕ}
    (hstep : DecompStep (problem d q).methods tn t m tn₂) :
    ∃ f₂ E₂, Inv d q tn₂ f₂ E₂ :=
  (hI.stepB hstep).imp fun _ ⟨E₂, h, _⟩ => ⟨E₂, h⟩

end Step

/-! ### The witness -/

/-- The invariant holds along every decomposition sequence from the initial task network. -/
theorem exists_inv_of_decomposesTo {tn : TaskNetwork ℕ ℕ ℕ}
    (h : (problem d q).DecomposesTo (problem d q).tnI tn) : ∃ f E, Inv d q tn f E := by
  induction h with
  | refl => exact ⟨_, _, inv_init⟩
  | tail _ hstep ih =>
    obtain ⟨f, E, hI⟩ := ih
    obtain ⟨t, m, hs⟩ := hstep
    exact hI.step hs

/-- The witness built from a primitive network with an executable linearisation `l`. -/
def witnessOf (f : ℕ → List PStep) (E : List (List PStep)) (l : List ℕ) : List Entry :=
  l.map (fun t => (f t, false)) ++ E.map (fun e => (e, true))

theorem actsOf_witnessOf {tn : TaskNetwork ℕ ℕ ℕ} {f : ℕ → List PStep}
    {E : List (List PStep)} (hI : Inv d q tn f E) {l : List ℕ} {as : List ℕ}
    (hl : ∀ t ∈ l, t ∈ tn.T) (has : tn.IsActionSeq l as) :
    actsOf d q (witnessOf f E l) = as := by
  have h1 : actsOf d q (witnessOf f E l) = l.map (fun t => leafAct d q (f t)) := by
    rw [actsOf, witnessOf, List.filter_append, List.filter_map, List.filter_map, List.map_append]
    simp [Function.comp_def]
  have h2 : l.map (fun t => leafAct d q (f t)) =
      (l.map tn.α).map (Sum.elim id (fun _ => 0)) := by
    rw [List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply, leafAct_eq, hI.lbl t (hl t ht)]
  rw [h1, h2, has, List.map_map]
  simp [Function.comp_def]

/-- **The witness of a primitive executable network carrying the invariant**, with every dummy
step normalised to `(k, 0)`. -/
theorem pathOK_witnessOf {tn : TaskNetwork ℕ ℕ ℕ} {f : ℕ → List PStep} {E : List (List PStep)}
    (hI : Inv d q tn f E) (hprim : tn.IsPrimitive) {l : List ℕ} {as : List ℕ}
    (hlin : tn.IsLinearization l) (has : tn.IsActionSeq l as)
    (happ : (problem d q).SeqApplicable as (problem d q).init)
    (hgoal : (problem d q).GoalState ((problem d q).transitionSeq as (problem d q).init)) :
    PathOK d q (witnessOf f E l) ∧
      ∀ u ∈ witnessOf f E l, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)] := by
  obtain ⟨hnd, hmem, hpw⟩ := hlin
  have hl : ∀ t ∈ l, t ∈ tn.T := fun t ht => (hmem t).1 ht
  have hmemW : ∀ p, Mem tn f E p ↔ ∃ u ∈ witnessOf f E l, u.1 = p := by
    intro p
    constructor
    · rintro (⟨t, ht, rfl⟩ | hp)
      · refine ⟨(f t, false), ?_, rfl⟩
        simp only [witnessOf, List.mem_append, List.mem_map]
        exact Or.inl ⟨t, (hmem t).2 ht, rfl⟩
      · exact ⟨(p, true), by simp [witnessOf, hp], rfl⟩
    · rintro ⟨u, hu, rfl⟩
      simp only [witnessOf, List.mem_append, List.mem_map] at hu
      rcases hu with ⟨t, ht, rfl⟩ | ⟨e, he, rfl⟩
      · exact Or.inl ⟨t, hl t ht, rfl⟩
      · exact Or.inr he
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- entries
    intro u hu
    simp only [witnessOf, List.mem_append, List.mem_map] at hu
    rcases hu with ⟨t, ht, rfl⟩ | ⟨e, he, rfl⟩
    · simp only [EntryOK, Bool.false_eq_true, if_false]
      refine ⟨hI.node t (hl t ht), ?_⟩
      obtain ⟨a, ha⟩ := hprim t (hl t ht)
      exact ⟨a, by rw [← hI.lbl t (hl t ht), ha]⟩
    · exact hI.eps e he
  · -- pairs
    have hpair_mem : ∀ p p', Mem tn f E p → Mem tn f E p' → p ≠ p' →
        ∃ x y, DivAt p p' x y ∧ x.1 = y.1 := hI.div
    refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine (hnd.and hpw).imp_of_mem ?_
      rintro t t' ht ht' ⟨hne, hno⟩
      have htT := hl t ht
      have htT' := hl t' ht'
      have hfne : f t ≠ f t' := fun h => hne (hI.inj t htT t' htT' h)
      obtain ⟨x, y, hd, hxy⟩ :=
        hpair_mem _ _ (Or.inl ⟨t, htT, rfl⟩) (Or.inl ⟨t', htT', rfl⟩) hfne
      refine ⟨x, y, hd, hxy, fun _ _ ho => hno ?_⟩
      rw [hI.ord t' htT' t htT]
      exact ⟨y, x, divAt_symm hd, hxy.symm, by rw [← hxy]; exact ho⟩
    · rw [List.pairwise_map]
      refine hI.nodup.imp_of_mem ?_
      intro e e' he he' hne
      obtain ⟨x, y, hd, hxy⟩ := hpair_mem _ _ (Or.inr he) (Or.inr he') hne
      exact ⟨x, y, hd, hxy, by simp⟩
    · simp only [List.mem_map]
      rintro _ ⟨t, ht, rfl⟩ _ ⟨e, he, rfl⟩
      have hne : f t ≠ e := nodeOK_ne_eps (hI.node t (hl t ht)) (hI.eps e he)
      obtain ⟨x, y, hd, hxy⟩ := hpair_mem _ _ (Or.inl ⟨t, hl t ht, rfl⟩) (Or.inr he) hne
      exact ⟨x, y, hd, hxy, by simp⟩
  · -- roots
    intro i hi
    obtain ⟨p, hp, s, rfl⟩ := hI.roots i hi
    obtain ⟨u, hu, hup⟩ := (hmemW _).1 hp
    exact ⟨u, hu, s, hup⟩
  · -- children
    intro u hu P x y s hps j hj
    have hp : Mem tn f E u.1 := (hmemW _).2 ⟨u, hu, rfl⟩
    obtain ⟨p', hp', s', rfl⟩ := hI.children u.1 hp P x y s hps j hj
    obtain ⟨v, hv, hvp⟩ := (hmemW _).1 hp'
    exact ⟨v, hv, s', hvp⟩
  · -- exec
    rw [ExecOK, actsOf_witnessOf hI hl has]
    exact ⟨happ, hgoal⟩
  · -- dummies
    intro u hu hf
    simp only [witnessOf, List.mem_append, List.mem_map] at hu
    rcases hu with ⟨t, -, rfl⟩ | ⟨e, he, rfl⟩
    · simp at hf
    · exact hI.eps0 e he

/-- **Completeness, with every dummy step normalised to `(k, 0)`.** -/
theorem exists_pathOK0_of_solvable (h : Solvable d q) :
    ∃ W, PathOK d q W ∧ ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)] := by
  obtain ⟨tn, hreach, hprim, l, as, hlin, has, happ, hgoal⟩ := h
  obtain ⟨f, E, hI⟩ := exists_inv_of_decomposesTo hreach
  exact ⟨_, pathOK_witnessOf hI hprim hlin has happ hgoal⟩

/-- **Completeness: a solvable described problem has a path witness.** -/
theorem exists_pathOK_of_solvable (h : Solvable d q) : ∃ W, PathOK d q W :=
  (exists_pathOK0_of_solvable h).imp fun _ h => h.1

end AcVer

end Syn

end HTN
