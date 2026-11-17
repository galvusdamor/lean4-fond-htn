import FondHtn.MPStrong.Prog
import FondHtn.MP.Fair
/-!
# Fair strong cyclic method-based policies as a fixpoint game

The fair reading of strong cyclic solutions ([CB22, Def. 7] read as Cimatti et al.:
`FOND.Problem.IsMPStrongCyclicFairSolution` — a well-defined policy from whose every reachable
node a goal node is reachable) is characterised by the nested fixpoint
`νW. μZ. goal ∨ (∃ move. all successors in W ∧ some successor in Z)`, adapted to method-based
policies:

* `FOND.Problem.FAttrH prog X n tn s` — the (graded) **attractor** of the empty networks with
  respect to a set `X` of nodes: `(tn, s)` is a goal; or some unconstrained applicable primitive
  task has all outcomes in `X` and some outcome in the attractor; or some decomposition leads to
  a node in `X` and in the attractor.  For `prog = true` only unconstrained tasks may be
  decomposed (progression); for `prog = false` any compound task, as in [CB22, Defs. 5–6].
* `FOND.Problem.FairWin prog tn s` — `(tn, s)` lies in a set `X` of well-formed nodes, closed
  under isomorphism, every node of which is in the attractor of `X` (a post-fixpoint, i.e. the
  greatest fixpoint `νW` contains `(tn, s)`).

Results:

* **`FOND.Problem.fairWin_of_fair`**, **`FOND.Problem.fair_of_fairWin`** — fair strong cyclic
  solvability is `FairWin false tn_I s_I` (for well-formed problems, infinite id type).  A
  winning policy is read off the minimal attractor ranks on canonical representatives of
  isomorphism classes, as in `FOND.Problem.andOrPolicy`.
* **`FOND.Problem.FAttrH.delay`** — the delay lemma of gap G8 for the attractor: decomposing a
  task first never helps, provided the set `D` is closed under *pre*-decomposition.
* **`FOND.Problem.fairWin_prog_of_fairWin`** — **G8 holds for the fair reading**: a solution of
  the unrestricted game yields one of the progression game (with `D` the closure of `X` under
  pre-decomposition sequences).
* **`FOND.Problem.mpStrongCyclicFairSolvable_iff_prog`** — fair strong cyclic solvability is the
  progression game `FairWin true tn_I s_I`.
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} (P : Problem F A C I) [DecidableEq I]

/-- A set of nodes. -/
abbrev NSet (F A C I : Type) := TaskNetwork I A C → Set F → Prop

/-- Well-formed networks only, closed under isomorphism. -/
def NGood (X : NSet F A C I) : Prop :=
  (∀ tn s, X tn s → tn.WF) ∧
    ∀ tn tn' s (σ : I → I), X tn s → tn'.WF → IsoVia σ tn tn' → X tn' s

/-- **The attractor** of the goal nodes with respect to `X` (graded). -/
inductive FAttrH (prog : Bool) (X : NSet F A C I) : ℕ → TaskNetwork I A C → Set F → Prop
  /-- A goal node. -/
  | goal {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : FAttrH prog X n tn s
  /-- Execute an unconstrained primitive task: all outcomes in `X`, one in the attractor. -/
  | prim {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A}
      (hu : tn.Unconstrained t) (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, X (tn.progress t) s') {s₀ : Set F}
      (hs₀ : s₀ ∈ (P.δ a).outcomes s) (h : FAttrH prog X n (tn.progress t) s₀) :
      FAttrH prog X (n + 1) tn s
  /-- Decompose a compound task (unconstrained, for progression). -/
  | decomp {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hu : prog = true → tn.Unconstrained t) (hd : DecompStep P.methods tn t m tn')
      (hX : X tn' s) (h : FAttrH prog X n tn' s) : FAttrH prog X (n + 1) tn s

/-- **The fair game**: `(tn, s)` lies in a self-supporting, isomorphism-closed set of
well-formed nodes. -/
def FairWin (prog : Bool) (tn : TaskNetwork I A C) (s : Set F) : Prop :=
  ∃ X : NSet F A C I, NGood X ∧ X tn s ∧ ∀ tn s, X tn s → ∃ n, P.FAttrH prog X n tn s

variable {P}

lemma FAttrH.mono {prog : Bool} {X : NSet F A C I} {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.FAttrH prog X n tn s) : ∀ {n'}, n ≤ n' → P.FAttrH prog X n' tn s := by
  induction h with
  | goal h => exact fun _ => .goal h
  | prim hu hα happ hall hs₀ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim hu hα happ hall hs₀ (ih (by omega))
  | decomp hu hd hX _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .decomp hu hd hX (ih (by omega))

lemma FAttrH.toGeneral {X : NSet F A C I} {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.FAttrH true X n tn s) : P.FAttrH false X n tn s := by
  induction h with
  | goal h => exact .goal h
  | prim hu hα happ hall hs₀ _ ih => exact .prim hu hα happ hall hs₀ ih
  | decomp _ hd hX _ ih => exact .decomp (by simp) hd hX ih

lemma FAttrH.empty_of_zero {prog : Bool} {X : NSet F A C I} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.FAttrH prog X 0 tn s) : tn.T = ∅ := by
  cases h with
  | goal h => exact h

/-- The attractor of an isomorphism-closed set is invariant under isomorphism. -/
theorem FAttrH.isoVia [Infinite I] {prog : Bool} {X : NSet F A C I} (hX : NGood X) {n : ℕ}
    {tn : TaskNetwork I A C} {s : Set F} (h : P.FAttrH prog X n tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.FAttrH prog X n tn' s := by
  induction h with
  | goal he => exact fun _ _ hσ => .goal (hσ.empty he)
  | prim hu hα happ hall hs₀ _ ih =>
    intro tn' σ hw hw' hσ
    have hw₁ := progress_wf hw hu
    have hw₁' := progress_wf hw' (hσ.unconstrained hu)
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ
      (fun s' hs' => hX.2 _ _ _ _ (hall s' hs') hw₁' (hσ.progress hu.1)) hs₀
      (ih hw₁ hw₁' (hσ.progress hu.1))
  | decomp hu hd hXt _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp (fun hp => hσ.unconstrained (hu hp)) hd'
      (hX.2 _ _ _ _ hXt (hd'.wf hw') hρ) (ih (hd.wf hw) (hd'.wf hw') hρ)

theorem FAttrH.iff_of_isoVia [Infinite I] {prog : Bool} {X : NSet F A C I} (hX : NGood X)
    {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {σ : I → I} (hw : tn.WF) (hw' : tn'.WF)
    (hσ : IsoVia σ tn tn') : P.FAttrH prog X n tn s ↔ P.FAttrH prog X n tn' s := by
  obtain ⟨τ, hτ, -⟩ := hσ.exists_inv
  exact ⟨fun h => h.isoVia hX hw hw' hσ, fun h => h.isoVia hX hw' hw hτ⟩

/-! ## From fair policies to the game -/

/-- **A fair strong cyclic solution wins the unrestricted fair game.** -/
theorem fairWin_of_fair [Infinite I] (hP : P.tnI.WF) (h : P.MPStrongCyclicFairSolvable) :
    P.FairWin false P.tnI P.init := by
  obtain ⟨π, -, hfair⟩ := h
  let X : NSet F A C I := fun tn s =>
    tn.WF ∧ ∃ (y : MPNode F A C I) (σ : I → I), P.MPReach π y ∧ y.state = s ∧ IsoVia σ y.net tn
  have hXg : NGood X := by
    refine ⟨fun _ _ h => h.1, fun tn tn' s σ h hw' hσ => ?_⟩
    obtain ⟨-, y, τ, hy, hys, hτ⟩ := h
    exact ⟨hw', y, σ ∘ τ, hy, hys, hτ.comp hσ⟩
  have hreachX : ∀ y, P.MPReach π y → X y.net y.state := fun y hy =>
    ⟨mpReach_wf hP hy, y, id, hy, rfl, IsoVia.refl _⟩
  -- reachable nodes are in the attractor
  have hattr : ∀ y z, Relation.ReflTransGen (P.MPStep π) y z → z.IsGoal → P.MPReach π y →
      ∃ n, P.FAttrH false X n y.net y.state := by
    intro y z hyz hz
    induction hyz using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => ⟨0, .goal hz⟩
    | @head y y₁ hs _ ih =>
      intro hy
      obtain ⟨n, hn⟩ := ih (hy.tail hs)
      cases hs with
      | @prim t a s' hi hu hα happ hs' =>
        exact ⟨n + 1, .prim hu hα happ (fun s'' hs'' => hreachX _
          (hy.tail (MPStep.prim hi hu hα happ hs''))) hs' hn⟩
      | @decomp t m tn' hi hd =>
        exact ⟨n + 1, .decomp (by simp) hd (hreachX _ (hy.tail (MPStep.decomp hi hd))) hn⟩
  refine ⟨X, hXg, hreachX _ .refl, fun tn s hX => ?_⟩
  obtain ⟨hw, y, σ, hy, rfl, hσ⟩ := hX
  obtain ⟨z, hyz, hz⟩ := hfair y hy
  obtain ⟨n, hn⟩ := hattr y z hyz hz hy
  exact ⟨n, hn.isoVia hXg (mpReach_wf hP hy) hw hσ⟩

/-! ## From the game to a fair policy -/

section Policy

variable (P)

/-- An instruction realising attractor rank `k + 1` at `(tn, s)`. -/
def FGood (X : NSet F A C I) (k : ℕ) (tn : TaskNetwork I A C) (s : Set F)
    (i : I × Option (Method I A C)) : Prop :=
  (i.2 = none ∧ ∃ a, tn.Unconstrained i.1 ∧ tn.α i.1 = Sum.inl a ∧ (P.δ a).Applicable s ∧
      (∀ s' ∈ (P.δ a).outcomes s, X (tn.progress i.1) s') ∧
      ∃ s₀ ∈ (P.δ a).outcomes s, P.FAttrH false X k (tn.progress i.1) s₀) ∨
    ∃ m tn', i.2 = some m ∧ DecompStep P.methods tn i.1 m tn' ∧ X tn' s ∧
      P.FAttrH false X k tn' s

/-- The policy is defined at well-formed canonical representatives in `X` of minimal rank
`k + 1`. -/
def FCond [Nonempty I] (X : NSet F A C I) (tn : TaskNetwork I A C) (s : Set F) : Prop :=
  tn.WF ∧ canon tn = tn ∧ ∃ k i, (∀ j, P.FAttrH false X j tn s → k + 1 ≤ j) ∧ P.FGood X k tn s i

open Classical in
/-- **The policy read off the fair game.** -/
noncomputable def fairPolicy [Nonempty I] (X : NSet F A C I) : MPPolicy F A C I := fun tn s =>
  if h : P.FCond X tn s then some h.2.2.choose_spec.choose else none

variable {P}

lemma fairPolicy_spec [Nonempty I] {X : NSet F A C I} {tn : TaskNetwork I A C} {s : Set F}
    {i : I × Option (Method I A C)} (h : P.fairPolicy X tn s = some i) :
    tn.WF ∧ canon tn = tn ∧ ∃ k, (∀ j, P.FAttrH false X j tn s → k + 1 ≤ j) ∧
      P.FGood X k tn s i := by
  unfold fairPolicy at h
  split_ifs at h with hc
  cases h
  exact ⟨hc.1, hc.2.1, _, hc.2.2.choose_spec.choose_spec⟩

lemma fairPolicy_wellDefined [Nonempty I] {X : NSet F A C I} :
    (P.fairPolicy X).WellDefined := by
  intro tn tn' s h h' hiso
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 h'
  obtain ⟨hw, hc, -⟩ := fairPolicy_spec hi
  obtain ⟨hw', hc', -⟩ := fairPolicy_spec hi'
  rw [← hc, ← hc']
  exact canon_eq hiso ⟨fun _ => hw', fun _ => hw⟩

/-- **Steps of the policy stay in `X`.** -/
theorem fairPolicy_step_mem [Infinite I] {X : NSet F A C I} (hX : NGood X)
    {x y : MPNode F A C I} (hx : x.net.WF) (hs : P.MPStep (P.fairPolicy X) x y) :
    X y.net y.state := by
  cases hs with
  | @prim t a s' hi hu hα happ hs' =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    obtain ⟨hw₀, -, k, -, hgood⟩ := fairPolicy_spec hπ
    rcases hgood with ⟨-, a', hu₀, hα₀, -, hall, -⟩ | ⟨m, tn', hm, -⟩
    · obtain rfl : a' = a := Sum.inl_injective (hα₀.symm.trans ((hσ.α_eq ht₀).symm.trans hα))
      exact hX.2 _ _ _ _ (hall s' hs') (progress_wf hx hu) (hσ.progress ht₀)
    · simp at hm
  | @decomp t m u hi hd =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    obtain ⟨hw₀, -, k, -, hgood⟩ := fairPolicy_spec hπ
    rcases hgood with ⟨hm, -⟩ | ⟨m', tn', hm, hd₀, hXt, -⟩
    · simp at hm
    · obtain ⟨ρ, hρ⟩ := hd₀.iso_of_isoVia hd (Option.some_injective _ hm).symm hw₀ hx hσ
      exact hX.2 _ _ _ _ hXt (hd.wf hx) hρ

/-- **At a non-goal node of `X` the policy moves to a node of smaller rank.** -/
theorem fairPolicy_progress [Infinite I] {X : NSet F A C I} (hX : NGood X)
    {x : MPNode F A C I} (hxX : X x.net x.state) {n : ℕ}
    (hn : P.FAttrH false X n x.net x.state) (hne : x.net.T ≠ ∅) :
    ∃ y k, P.MPStep (P.fairPolicy X) x y ∧ (∀ j, P.FAttrH false X j x.net x.state → k + 1 ≤ j) ∧
      P.FAttrH false X k y.net y.state := by
  classical
  have hx := hX.1 _ _ hxX
  set r := canon x.net
  have hr := canon_rel x.net
  have hrw : r.WF := hr.2.2 hx
  obtain ⟨σ, hσ⟩ := hr.1
  replace hσ : IsoVia σ r x.net := hσ
  have hcr : canon r = r := canon_canon x.net
  obtain ⟨τ, hτ, -⟩ := hσ.exists_inv
  have hex : ∃ n, P.FAttrH false X n r x.state := ⟨n, hn.isoVia hX hx hrw hτ⟩
  set h := Nat.find hex
  have hh : P.FAttrH false X h r x.state := Nat.find_spec hex
  have hrne : r.T ≠ ∅ := fun he => hne (hσ.empty he)
  obtain ⟨k, hk⟩ : ∃ k, h = k + 1 := by
    rcases hh0 : h with _ | k
    · exact absurd (FAttrH.empty_of_zero (hh0 ▸ hh)) hrne
    · exact ⟨k, rfl⟩
  have hmin : ∀ j, P.FAttrH false X j x.net x.state → k + 1 ≤ j := fun j hj =>
    hk ▸ Nat.find_min' hex (hj.isoVia hX hx hrw hτ)
  have hgood₀ : ∃ i, P.FGood X k r x.state i := by
    have := hk ▸ hh
    cases this with
    | goal h => exact absurd h hrne
    | prim hu hα happ hall hs₀ h =>
      exact ⟨(_, none), Or.inl ⟨rfl, _, hu, hα, happ, hall, _, hs₀, h⟩⟩
    | decomp _ hd hXt h => exact ⟨(_, some _), Or.inr ⟨_, _, rfl, hd, hXt, h⟩⟩
  obtain ⟨i, hi⟩ := hgood₀
  have hcond : P.FCond X r x.state :=
    ⟨hrw, hcr, k, i, fun j hj => hk ▸ Nat.find_min' hex hj, hi⟩
  obtain ⟨i₀, hπ⟩ : ∃ i₀, P.fairPolicy X r x.state = some i₀ :=
    ⟨_, by unfold fairPolicy; exact dif_pos hcond⟩
  obtain ⟨-, -, k₀, hmin₀, hgood⟩ := fairPolicy_spec hπ
  have hkk : k₀ = k := by
    have h1 := hmin₀ _ (hk ▸ hh)
    have h2 : h ≤ k₀ + 1 := Nat.find_min' hex (by
      rcases hgood with ⟨-, a, hu, hα, happ, hall, s₀, hs₀, h⟩ | ⟨m, tn', -, hd, hXt, h⟩
      · exact .prim hu hα happ hall hs₀ h
      · exact .decomp (by simp) hd hXt h)
    omega
  subst hkk
  rcases hgood with ⟨h2, a, hu, hα, happ, -, s₀, hs₀, hk₀⟩ | ⟨m, tn', h2, hd, -, hk₀⟩
  · have hπ' : P.fairPolicy X r x.state = some (i₀.1, none) := by rw [hπ, ← h2]
    refine ⟨_, k₀, MPStep.prim ⟨r, σ, i₀.1, hσ, hu.1, hπ', rfl⟩ (hσ.unconstrained hu)
      ((hσ.α_eq hu.1).trans hα) happ hs₀, hmin, ?_⟩
    exact hk₀.isoVia hX (progress_wf hrw hu) (progress_wf hx (hσ.unconstrained hu))
      (hσ.progress hu.1)
  · have hπ' : P.fairPolicy X r x.state = some (i₀.1, some m) := by rw [hπ, ← h2]
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hrw hx hσ
    exact ⟨_, k₀, MPStep.decomp ⟨r, σ, i₀.1, hσ, hd.2.1, hπ', rfl⟩ hd', hmin,
      hk₀.isoVia hX (hd.wf hrw) (hd'.wf hx) hρ⟩

/-- **The fair game yields a fair strong cyclic solution.** -/
theorem fair_of_fairWin [Infinite I] (h : P.FairWin false P.tnI P.init) :
    P.MPStrongCyclicFairSolvable := by
  classical
  obtain ⟨X, hX, hX₀, hXa⟩ := h
  refine ⟨P.fairPolicy X, fairPolicy_wellDefined, ?_⟩
  have hreach : ∀ x, P.MPReach (P.fairPolicy X) x → X x.net x.state := by
    intro x hx
    induction hx with
    | refl => exact hX₀
    | tail _ hs ih => exact fairPolicy_step_mem hX (hX.1 _ _ ih) hs
  -- from every node of `X` a goal is reachable, by induction on the rank
  have key : ∀ N (x : MPNode F A C I), X x.net x.state → P.FAttrH false X N x.net x.state →
      ∃ z, Relation.ReflTransGen (P.MPStep (P.fairPolicy X)) x z ∧ z.IsGoal := by
    intro N
    induction N with
    | zero =>
      intro x _ h
      exact ⟨x, .refl, FAttrH.empty_of_zero h⟩
    | succ N ih =>
      intro x hxX h
      by_cases hne : x.net.T = ∅
      · exact ⟨x, .refl, hne⟩
      obtain ⟨y, k, hs, hmin, hk⟩ := fairPolicy_progress hX hxX h hne
      have hkN : k ≤ N := by have := hmin _ h; omega
      obtain ⟨z, hz, hgz⟩ := ih y (fairPolicy_step_mem hX (hX.1 _ _ hxX) hs) (hk.mono hkN)
      exact ⟨z, .head hs hz, hgz⟩
  intro x hx
  have hxX := hreach x hx
  obtain ⟨N, hN⟩ := hXa _ _ hxX
  exact key N x hxX hN

end Policy

/-! ## Delaying decompositions (gap G8 for the fair reading) -/

/-- `D` is closed under *pre*-decomposition: if `tn →_{t,m} tn'` and `(tn', s) ∈ D` then
`(tn, s) ∈ D`. -/
def PreClosed (D : NSet F A C I) : Prop :=
  ∀ tn tn' s t m, tn.WF → DecompStep P.methods tn t m tn' → D tn' s → D tn s

/-- **Delaying a decomposition in the progression attractor.** -/
theorem FAttrH.delay [Infinite I] {D : NSet F A C I} (hD : NGood D) (hpre : P.PreClosed D)
    (n : ℕ) :
    ∀ {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}, tn.WF →
      DecompStep P.methods tn t m tn' → D tn' s → P.FAttrH true D n tn' s →
        P.FAttrH true D (n + 1) tn s := by
  induction n with
  | zero =>
    intro tn tn' s t m hwf hd hDt h
    by_cases hu : tn.Unconstrained t
    · exact .decomp (fun _ => hu) hd hDt h
    obtain ⟨-, ht, -, u, -, -, hdisj, rfl⟩ := hd
    have : ∃ t₀ ∈ tn.T, tn.ord t₀ t := by
      by_contra hc
      push_neg at hc
      exact hu ⟨ht, hc⟩
    obtain ⟨t₀, ht₀, ht₀t⟩ := this
    have ht₀ne : t₀ ≠ t := fun e => hwf.irrefl t (e ▸ ht₀t)
    have hmem : t₀ ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₀, ht₀ne⟩)
    rw [FAttrH.empty_of_zero h] at hmem
    simp at hmem
  | succ k ih =>
    intro tn tn' s t m hwf hd hDt h
    by_cases hu : tn.Unconstrained t
    · exact .decomp (fun _ => hu) hd hDt h
    obtain ⟨hmM, ht, hαt, u, hwu, huiso, hdisj, rfl⟩ := hd
    have : ∃ t₀ ∈ tn.T, tn.ord t₀ t := by
      by_contra hc
      push_neg at hc
      exact hu ⟨ht, hc⟩
    obtain ⟨t₀, ht₀, ht₀t⟩ := this
    have ht₀ne : t₀ ≠ t := fun e => hwf.irrefl t (e ▸ ht₀t)
    cases h with
    | goal he =>
      have hmem : t₀ ∈ (decomposeWith tn t u).T := mem_decomposeWith_T.2 (Or.inl ⟨ht₀, ht₀ne⟩)
      rw [he] at hmem
      simp at hmem
    | @prim _ _ _ t' a hu' hα happ hall s₀ hs₀ h₀ =>
      obtain ⟨ht'T, ht't, ht'u, hut', hαeq⟩ :=
        unconstrained_of_decomposeWith hwf ht₀ ht₀t hu'
      have hd' : DecompStep P.methods (tn.progress t') t m
          (decomposeWith (tn.progress t') t u) :=
        ⟨hmM, mem_progress_T.2 ⟨fun e => ht't e.symm, ht⟩, hαt, u, hwu, huiso,
          Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj, rfl⟩
      have hcomm := progress_decomposeWith_comm (tn := tn) hwu ht't ht'u
      have hwp := progress_wf hwf hut'
      refine .prim hut' (hαeq.symm.trans hα) happ (fun s' hs' => ?_) hs₀ ?_
      · have := hall s' hs'
        rw [hcomm] at this
        exact hpre _ _ _ _ _ hwp hd' this
      · have hD₀ := hall s₀ hs₀
        rw [hcomm] at hD₀ h₀
        exact ih hwp hd' hD₀ h₀
    | @decomp _ _ tn'' _ t' m' hu' hd'' hDt'' h'' =>
      have hu'' := hu' rfl
      obtain ⟨ht'T, ht't, ht'u, hut', hαeq⟩ :=
        unconstrained_of_decomposeWith hwf ht₀ ht₀t hu''
      obtain ⟨hm'M, -, hα', v, hwv, hviso, hvdisj, rfl⟩ := hd''
      obtain ⟨v₂, hwv₂, hv₂iso, hv₂disj⟩ := exists_fresh_iso_copy v hwv (tn.T ∪ u.T)
      have hdv₂ : Disjoint tn.T v₂.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_left hv₂disj
      have huv₂ : Disjoint u.T v₂.T :=
        Finset.disjoint_of_subset_left Finset.subset_union_right hv₂disj
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
      have hcomm : decomposeWith tn₁ t u = decomposeWith (decomposeWith tn t u) t' v₂ :=
        (decomposeWith_comm hwu hwv₂ (fun e => ht't e.symm) ht ht'T hdisj hdv₂ huv₂).symm
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
        decomposeWith_iso_congr hwf' hwf' hwv hwv₂ hvdisj hdisj' hu''.1 (Set.bijOn_id _)
          (by simp) (by simp) hρbij hρord hρα
      obtain ⟨τ, hτ⟩ := hiso
      have hwX : (decomposeWith (decomposeWith tn t u) t' v₂).WF :=
        decomposeWith_wf hwf' hwv₂ hdisj'
      have hDX : D (decomposeWith tn₁ t u) s := by
        rw [hcomm]
        exact hD.2 _ _ _ _ hDt'' hwX hτ
      have hX : P.FAttrH true D k (decomposeWith tn₁ t u) s := by
        rw [hcomm]
        exact h''.isoVia hD (decomposeWith_wf hwf' hwv hvdisj) hwX hτ
      exact .decomp (fun _ => hut') hd₁ (hpre _ _ _ _ _ hwf₁ hd₂ hDX) (ih hwf₁ hd₂ hDX hX)

/-- The unrestricted attractor is contained in the progression attractor of any pre-closed,
isomorphism-closed superset. -/
theorem FAttrH.toProg [Infinite I] {X D : NSet F A C I} (hD : NGood D) (hpre : P.PreClosed D)
    (hXD : ∀ tn s, X tn s → D tn s) {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.FAttrH false X n tn s) (hwf : tn.WF) : P.FAttrH true D n tn s := by
  induction h with
  | goal h => exact .goal h
  | prim hu hα happ hall hs₀ _ ih =>
    exact .prim hu hα happ (fun s' hs' => hXD _ _ (hall s' hs')) hs₀ (ih (progress_wf hwf hu))
  | decomp _ hd hXt _ ih => exact FAttrH.delay hD hpre _ hwf hd (hXD _ _ hXt) (ih (hd.wf hwf))

/-- **Gap G8 for the fair reading: progression suffices.** -/
theorem fairWin_prog_of_fairWin [Infinite I] {tn : TaskNetwork I A C} {s : Set F}
    (h : P.FairWin false tn s) : P.FairWin true tn s := by
  obtain ⟨X, hX, hXtn, hXa⟩ := h
  let D : NSet F A C I := fun tn s =>
    tn.WF ∧ ∃ n tn'', DecomposesToN P.methods n tn tn'' ∧ X tn'' s
  have hD : NGood D := by
    refine ⟨fun _ _ h => h.1, fun tn tn' s σ h hw' hσ => ?_⟩
    obtain ⟨hw, n, tn'', hn, hX''⟩ := h
    obtain ⟨tn₂, hn₂, ρ, hρ⟩ := hn.iso hw hw' ⟨σ, hσ⟩
    exact ⟨hw', n, tn₂, hn₂, hX.2 _ _ _ _ hX'' (hn₂.wf hw') hρ⟩
  have hpre : P.PreClosed D := by
    intro tn tn' s t m hw hd h
    obtain ⟨-, n, tn'', hn, hX''⟩ := h
    exact ⟨hw, n + 1, tn'', DecomposesToN.head ⟨t, m, hd⟩ hn, hX''⟩
  have hXD : ∀ tn s, X tn s → D tn s := fun tn s h =>
    ⟨hX.1 _ _ h, 0, tn, DecomposesToN.refl _, h⟩
  refine ⟨D, hD, hXD _ _ hXtn, fun tn s hDt => ?_⟩
  obtain ⟨hw, n, tn'', hn, hX''⟩ := hDt
  clear hXtn
  induction hn with
  | refl tn =>
    obtain ⟨k, hk⟩ := hXa _ _ hX''
    exact ⟨k, hk.toProg hD hpre hXD hw⟩
  | @head tn tn₁ tn₂ n hstep hrest ih =>
    obtain ⟨t, m, hd⟩ := hstep
    obtain ⟨k, hk⟩ := ih (hd.wf hw) hX''
    exact ⟨k + 1, FAttrH.delay hD hpre _ hw hd ⟨hd.wf hw, n, tn₂, hrest, hX''⟩ hk⟩

theorem FairWin.toGeneral {tn : TaskNetwork I A C} {s : Set F} (h : P.FairWin true tn s) :
    P.FairWin false tn s := by
  obtain ⟨X, hX, hXtn, hXa⟩ := h
  exact ⟨X, hX, hXtn, fun tn s h => let ⟨n, hn⟩ := hXa tn s h; ⟨n, hn.toGeneral⟩⟩

/-- **Fair strong cyclic solvability is the progression fair game.** -/
theorem mpStrongCyclicFairSolvable_iff_prog [Infinite I] (hP : P.tnI.WF) :
    P.MPStrongCyclicFairSolvable ↔ P.FairWin true P.tnI P.init :=
  ⟨fun h => fairWin_prog_of_fairWin (fairWin_of_fair hP h),
    fun h => fair_of_fairWin h.toGeneral⟩

end Problem

end FOND
