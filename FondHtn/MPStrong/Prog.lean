import FondHtn.MethodPoliciesStrong
import FondHtn.IsoLemmas
import HtnPlanning.Core.DecompCommute
/-!
# Strong method-based solvability by progression (gap G8 of the catalogue)

The AND/OR characterisation `FOND.Problem.MPAndOr` of strong method-based solvability [CB22]
allows a policy to decompose *any* compound task, as in [CB22, Defs. 5–6].  The algorithms of
[CB22] (Alg. 2 and the bounded graph search) and the progression bounds of Alford et al. /
Bercher et al. only consider **progression**: only tasks without predecessors are executed *or
decomposed*.  The paper never states that this restriction is harmless (gap G8).

* `FOND.Problem.MPProg` / `MPProgH` — the progression game (ungraded / graded): the empty network
  wins; an unconstrained applicable primitive task with all outcomes winning; or the
  decomposition of an **unconstrained** compound task leading to a winning network.
* **`FOND.Problem.MPProgH.delay`** — the key lemma: decomposing *any* task first and then winning
  the progression game can be replaced by winning the progression game directly.  If the
  decomposed task `t` is constrained, every move available after the decomposition acts on an old
  task that is already unconstrained before it (an inserted task inherits the predecessors of
  `t`; a successor of `t` is preceded by a predecessor of `t`, by transitivity), and that move
  commutes with the decomposition of `t` (`HTN.decomposeWith_comm`,
  `HTN.progress_decomposeWith_comm`; a fresh copy is chosen for the commuted decomposition and
  the game is invariant under isomorphism).
* **`FOND.Problem.mpAndOr_iff_mpProg`** — for well-formed problems and networks
  `MPAndOr tn s ↔ MPProg tn s`, hence (`FOND.Problem.mpStrongSolvable_iff_mpProg`)
  strong method-based solvability is the progression game from `(tn_I, s_I)`.
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

variable (P : Problem F A C I) [DecidableEq I]

/-- **The progression game** (ungraded): only unconstrained tasks are executed or decomposed. -/
inductive MPProg : TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : MPProg tn s
  /-- Execute an unconstrained applicable primitive task; all outcomes must be solvable. -/
  | prim {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MPProg (tn.progress t) s') : MPProg tn s
  /-- Decompose an unconstrained compound task. -/
  | decomp {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hd : DecompStep P.methods tn t m tn') (h : MPProg tn' s) :
      MPProg tn s

/-- The progression game, graded by the height of the winning strategy. -/
inductive MPProgH : ℕ → TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : MPProgH n tn s
  /-- Execute an unconstrained applicable primitive task. -/
  | prim {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MPProgH n (tn.progress t) s') : MPProgH (n + 1) tn s
  /-- Decompose an unconstrained compound task. -/
  | decomp {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hu : tn.Unconstrained t) (hd : DecompStep P.methods tn t m tn') (h : MPProgH n tn' s) :
      MPProgH (n + 1) tn s

variable {P}

lemma MPProgH.toProg {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : P.MPProgH n tn s) :
    P.MPProg tn s := by
  induction h with
  | empty h => exact .empty h
  | prim hu hα happ _ ih => exact .prim hu hα happ ih
  | decomp hu hd _ ih => exact .decomp hu hd ih

lemma MPProgH.mono {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : P.MPProgH n tn s) :
    ∀ {n'}, n ≤ n' → P.MPProgH n' tn s := by
  induction h with
  | empty h => exact fun _ => .empty h
  | prim hu hα happ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim hu hα happ fun s' hs' => ih s' hs' (by omega)
  | decomp hu hd _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .decomp hu hd (ih (by omega))

lemma MPProg.toH (hA : ∀ a, (P.δ a).WF) {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPProg tn s) : ∃ n, P.MPProgH n tn s := by
  classical
  induction h with
  | empty h => exact ⟨0, .empty h⟩
  | @prim tn s t a hu hα happ _ ih =>
    let g : Set F → ℕ := fun s' => if h : s' ∈ (P.δ a).outcomes s then (ih s' h).choose else 0
    obtain ⟨N, hN⟩ := ((Action.outcomes_finite (hA a) s).image g).bddAbove
    refine ⟨N + 1, .prim hu hα happ fun s' hs' => ?_⟩
    have hg : g s' = (ih s' hs').choose := dif_pos hs'
    exact (ih s' hs').choose_spec.mono (hg ▸ hN ⟨s', hs', rfl⟩)
  | decomp hu hd _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .decomp hu hd hn⟩

/-- Progression moves are moves of the unrestricted game. -/
lemma MPProg.toAndOr {tn : TaskNetwork I A C} {s : Set F} (h : P.MPProg tn s) :
    P.MPAndOr tn s := by
  induction h with
  | empty h => exact .empty h
  | prim hu hα happ _ ih => exact .prim hu hα happ ih
  | decomp _ hd _ ih => exact .decomp hd ih

/-! ### Invariance under isomorphism -/

/-- The graded progression game is invariant under isomorphism. -/
theorem MPProgH.isoVia [Infinite I] {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPProgH n tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.MPProgH n tn' s := by
  induction h with
  | empty he => exact fun _ _ hσ => .empty (hσ.empty he)
  | prim hu hα happ _ ih =>
    intro tn' σ hw hw' hσ
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ fun s' hs' =>
      ih s' hs' (progress_wf hw hu) (progress_wf hw' (hσ.unconstrained hu)) (hσ.progress hu.1)
  | decomp hu hd _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp (hσ.unconstrained hu) hd' (ih (hd.wf hw) (hd'.wf hw') hρ)

/-- The progression game is invariant under isomorphism. -/
theorem MPProg.isoVia [Infinite I] {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPProg tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.MPProg tn' s := by
  induction h with
  | empty he => exact fun _ _ hσ => .empty (hσ.empty he)
  | prim hu hα happ _ ih =>
    intro tn' σ hw hw' hσ
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ fun s' hs' =>
      ih s' hs' (progress_wf hw hu) (progress_wf hw' (hσ.unconstrained hu)) (hσ.progress hu.1)
  | decomp hu hd _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp (hσ.unconstrained hu) hd' (ih (hd.wf hw) (hd'.wf hw') hρ)

/-! ### Delaying a decomposition -/

/-- If the task `t` decomposed into `u` is constrained in `tn`, every task that is unconstrained
after the decomposition is an old task, unconstrained already in `tn`. -/
lemma unconstrained_of_decomposeWith {tn u : TaskNetwork I A C} {t t₀ t' : I} (hwf : tn.WF)
    (ht₀ : t₀ ∈ tn.T) (ht₀t : tn.ord t₀ t)
    (hu' : (decomposeWith tn t u).Unconstrained t') :
    t' ∈ tn.T ∧ t' ≠ t ∧ t' ∉ u.T ∧ tn.Unconstrained t' ∧
      (decomposeWith tn t u).α t' = tn.α t' := by
  have ht₀ne : t₀ ≠ t := fun e => hwf.irrefl t (e ▸ ht₀t)
  have ht₀mem : t₀ ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₀, ht₀ne⟩)
  have ht'u : t' ∉ u.T := fun h =>
    hu'.2 t₀ ht₀mem (decomposeWith_ord_iff.2 (Or.inr (Or.inl ⟨ht₀t, h⟩)))
  have ht'T : t' ∈ tn.T ∧ t' ≠ t := by
    rcases mem_decomposeWith_T.1 hu'.1 with h | h
    · exact h
    · exact absurd h ht'u
  refine ⟨ht'T.1, ht'T.2, ht'u, ⟨ht'T.1, fun y hy hyt' => ?_⟩, ?_⟩
  · by_cases hyt : y = t
    · subst hyt
      have h₀ : tn.ord t₀ t' := hwf.trans ht₀t hyt'
      exact hu'.2 t₀ ht₀mem (decomposeWith_ord_iff.2 (Or.inr (Or.inr (Or.inr ⟨h₀, ht₀ne,
        ht'T.2⟩))))
    · exact hu'.2 y (mem_decomposeWith_T.2 (Or.inl ⟨hy, hyt⟩))
        (decomposeWith_ord_iff.2 (Or.inr (Or.inr (Or.inr ⟨hyt', hyt, ht'T.2⟩))))
  · simp [decomposeWith, ht'u]

/-- **Delaying a decomposition never hurts** (the key lemma of gap G8): if `tn →_{t,m} tn'` (for
an arbitrary, possibly constrained, task `t`) and the progression game is won from `tn'` within
`n` rounds, it is won from `tn` within `n + 1` rounds. -/
theorem MPProgH.delay [Infinite I] (n : ℕ) :
    ∀ {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}, tn.WF →
      DecompStep P.methods tn t m tn' → P.MPProgH n tn' s → P.MPProgH (n + 1) tn s := by
  induction n with
  | zero =>
    intro tn tn' s t m hwf hd h
    by_cases hu : tn.Unconstrained t
    · exact .decomp hu hd h
    obtain ⟨-, ht, -, u, -, -, hdisj, rfl⟩ := hd
    have : ∃ t₀ ∈ tn.T, tn.ord t₀ t := by
      by_contra hc
      push_neg at hc
      exact hu ⟨ht, hc⟩
    obtain ⟨t₀, ht₀, ht₀t⟩ := this
    have ht₀ne : t₀ ≠ t := fun e => hwf.irrefl t (e ▸ ht₀t)
    have hmem : t₀ ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₀, ht₀ne⟩)
    have he : (decomposeWith tn t u).T = ∅ := by cases h with | empty h => exact h
    rw [he] at hmem
    simp at hmem
  | succ k ih =>
    intro tn tn' s t m hwf hd h
    by_cases hu : tn.Unconstrained t
    · exact .decomp hu hd h
    have hd₀ := hd
    obtain ⟨hmM, ht, hαt, u, hwu, huiso, hdisj, rfl⟩ := hd
    have : ∃ t₀ ∈ tn.T, tn.ord t₀ t := by
      by_contra hc
      push_neg at hc
      exact hu ⟨ht, hc⟩
    obtain ⟨t₀, ht₀, ht₀t⟩ := this
    have ht₀ne : t₀ ≠ t := fun e => hwf.irrefl t (e ▸ ht₀t)
    cases h with
    | empty he =>
      have hmem : t₀ ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₀, ht₀ne⟩)
      rw [he] at hmem
      simp at hmem
    | @prim _ _ _ t' a hu' hα happ hall =>
      obtain ⟨ht'T, ht't, ht'u, hut', hαeq⟩ := unconstrained_of_decomposeWith hwf ht₀ ht₀t hu'
      refine .prim hut' (hαeq.symm.trans hα) happ fun s' hs' => ?_
      have hd' : DecompStep P.methods (tn.progress t') t m (decomposeWith (tn.progress t') t u) :=
        ⟨hmM, mem_progress_T.2 ⟨fun e => ht't e.symm, ht⟩, hαt, u, hwu, huiso,
          Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj, rfl⟩
      have := hall s' hs'
      rw [progress_decomposeWith_comm hwu ht't ht'u] at this
      exact ih (progress_wf hwf hut') hd' this
    | @decomp _ _ tn'' _ t' m' hu' hd'' h'' =>
      obtain ⟨ht'T, ht't, ht'u, hut', hαeq⟩ := unconstrained_of_decomposeWith hwf ht₀ ht₀t hu'
      obtain ⟨hm'M, -, hα', v, hwv, hviso, hvdisj, rfl⟩ := hd''
      obtain ⟨v₂, hwv₂, hv₂iso, hv₂disj⟩ := exists_fresh_iso_copy v hwv (tn.T ∪ u.T)
      have hdv₂ : Disjoint tn.T v₂.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hv₂disj
      have huv₂ : Disjoint u.T v₂.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_right hv₂disj
      -- decompose `t'` first
      set tn₁ := decomposeWith tn t' v₂ with htn₁
      have hd₁ : DecompStep P.methods tn t' m' tn₁ :=
        ⟨hm'M, ht'T, hαeq.symm.trans hα', v₂, hwv₂, hv₂iso.trans hviso, hdv₂, rfl⟩
      have hwf₁ : tn₁.WF := hd₁.wf hwf
      have htv₂ : t ∉ v₂.T := fun h => Finset.disjoint_left.1 hdv₂ ht h
      have hdisj₁ : Disjoint tn₁.T u.T := by
        rw [Finset.disjoint_left]
        intro y hy hyu
        rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact Finset.disjoint_left.1 hdisj hy hyu
        · exact Finset.disjoint_left.1 huv₂ hyu hy
      have hd₂ : DecompStep P.methods tn₁ t m (decomposeWith tn₁ t u) :=
        ⟨hmM, mem_decomposeWith_T.2 (Or.inl ⟨ht, fun e => ht't e.symm⟩),
          by simp [htn₁, decomposeWith, htv₂, hαt], u, hwu, huiso, hdisj₁, rfl⟩
      -- the two orders give the same network
      have hcomm : decomposeWith tn₁ t u = decomposeWith (decomposeWith tn t u) t' v₂ :=
        (decomposeWith_comm hwu hwv₂ (fun e => ht't e.symm) ht ht'T hdisj hdv₂ huv₂).symm
      -- and it is isomorphic to the network `tn''` that is won
      have hwf' : (decomposeWith tn t u).WF := decomposeWith_wf hwf hwu hdisj
      have hdisj' : Disjoint (decomposeWith tn t u).T v₂.T := by
        rw [Finset.disjoint_left]
        intro y hy hyv
        rcases mem_decomposeWith_T.1 hy with ⟨hy, -⟩ | hy
        · exact Finset.disjoint_left.1 hdv₂ hy hyv
        · exact Finset.disjoint_left.1 huv₂ hy hyv
      obtain ⟨ρ, hρbij, hρord, hρα⟩ := hv₂iso.symm
      have hiso : (decomposeWith (decomposeWith tn t u) t' v).Iso
          (decomposeWith (decomposeWith tn t u) (id t') v₂) :=
        decomposeWith_iso_congr hwf' hwf' hwv hwv₂ hvdisj hdisj' hu'.1 (Set.bijOn_id _)
          (by simp) (by simp) hρbij hρord hρα
      obtain ⟨τ, hτ⟩ := hiso
      have hX : P.MPProgH k (decomposeWith tn₁ t u) s := by
        rw [hcomm]
        exact h''.isoVia (decomposeWith_wf hwf' hwv hvdisj)
          (decomposeWith_wf hwf' hwv₂ hdisj') hτ
      exact .decomp hut' hd₁ (ih hwf₁ hd₂ hX)

/-- **Gap G8**: the unrestricted game, graded, is won by progression within the same number of
rounds. -/
theorem MPAndOrH.toProgH [Infinite I] {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPAndOrH n tn s) (hwf : tn.WF) : P.MPProgH n tn s := by
  induction h with
  | empty h => exact .empty h
  | prim hu hα happ _ ih => exact .prim hu hα happ fun s' hs' => ih s' hs' (progress_wf hwf hu)
  | decomp hd _ ih => exact MPProgH.delay _ hwf hd (ih (hd.wf hwf))

/-- **Gap G8: progression suffices.**  For well-formed actions and a well-formed network, the
unrestricted AND/OR game of [CB22] and the progression game agree. -/
theorem mpAndOr_iff_mpProg [Infinite I] (hA : ∀ a, (P.δ a).WF) {tn : TaskNetwork I A C}
    {s : Set F} (hwf : tn.WF) : P.MPAndOr tn s ↔ P.MPProg tn s := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.toH hA
    exact (hn.toProgH hwf).toProg
  · exact MPProg.toAndOr

/-- **Strong method-based solvability [CB22] is the progression game** from `(tn_I, s_I)`. -/
theorem mpStrongSolvable_iff_mpProg [Infinite I] (hP : P.WF) :
    P.MPStrongSolvable ↔ P.MPProg P.tnI P.init :=
  (mpStrongSolvable_iff_mpAndOr hP).trans (mpAndOr_iff_mpProg hP.actions hP.tnI)

end Problem

end FOND
