import FondHtn.IsoLemmas
/-!
# Strong method-based policies as an AND/OR game

**Theorem** (`FOND.Problem.mpStrongSolvable_iff_mpAndOr`).  For a well-formed problem over an
infinite type of task ids, a strong solution in the sense of [CB22, Def. 7] exists iff
`(tn_I, s_I)` is won in the AND/OR game `FOND.Problem.MPAndOr`.

* `⟹` (`mpAndOr_of_mpStrongSolvable`): finiteness and acyclicity of `[L]` bound the length of
  every execution (pigeonhole on isomorphism classes); induction on that bound.
* `⟸` (`mpStrongSolvable_of_mpAndOr`): the game is graded by the height of a winning strategy
  (`MPAndOrH`).  The policy `andOrPolicy` is defined only on one canonical representative of every
  isomorphism class of well-formed task networks (`canon`), and there gives an instruction that
  realises the minimal height.  Every step strictly decreases the height (acyclicity), a step is
  possible at every non-goal node (no bad terminal nodes), and every node has finitely many
  successor classes, so by induction on the height `[L]` is finite.
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

lemma Action.outcomes_finite {a : Action F} (h : a.WF) (s : Set F) : (a.outcomes s).Finite := by
  have : a.outcomes s = (fun e => Action.applyEff e s) '' a.effs := by
    ext s'; simp [Action.outcomes, eq_comm]
  rw [this]; exact h.2.image _

namespace Problem

/-! ## From strong policies to the AND/OR game -/

section PolicyToGame

variable (P : Problem F A C I) [DecidableEq I]

/-- There is an execution of length `n` starting at `x`. -/
def MPPathFrom (π : MPPolicy F A C I) (x : MPNode F A C I) (n : ℕ) : Prop :=
  ∃ f : ℕ → MPNode F A C I, f 0 = x ∧ ∀ i < n, P.MPStep π (f i) (f (i + 1))

variable {P}

lemma mpPathFrom_zero {π : MPPolicy F A C I} {x : MPNode F A C I} : P.MPPathFrom π x 0 :=
  ⟨fun _ => x, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

lemma not_mpPathFrom_of_step {π : MPPolicy F A C I} {x y : MPNode F A C I} {k : ℕ}
    (hs : P.MPStep π x y) (h : ¬ P.MPPathFrom π x (k + 1)) : ¬ P.MPPathFrom π y k := by
  rintro ⟨f, hf0, hf⟩
  apply h
  refine ⟨fun i => if i = 0 then x else f (i - 1), by simp, fun i hi => ?_⟩
  rcases i with _ | i
  · simpa [hf0] using hs
  · simpa using hf i (by omega)

theorem mpAndOr_of_noPath {π : MPPolicy F A C I}
    (hgoal : ∀ x, P.MPReach π x → P.MPTerminal π x → x.IsGoal) :
    ∀ k x, P.MPReach π x → ¬ P.MPPathFrom π x k → P.MPAndOr x.net x.state := by
  intro k
  induction k with
  | zero => intro x _ h; exact absurd mpPathFrom_zero h
  | succ k ih =>
    intro x hx hp
    by_cases ht : P.MPTerminal π x
    · exact .empty (hgoal x hx ht)
    · simp only [MPTerminal, not_forall, not_not] at ht
      obtain ⟨y, hy⟩ := ht
      cases hy with
      | prim hi hu hα happ _ =>
        refine .prim hu hα happ fun s'' hs'' => ?_
        have hst := MPStep.prim hi hu hα happ hs''
        exact ih _ (hx.tail hst) (not_mpPathFrom_of_step hst hp)
      | decomp hi hd =>
        have hst := MPStep.decomp hi hd
        exact .decomp hd (ih _ (hx.tail hst) (not_mpPathFrom_of_step hst hp))

/-- In a finite acyclic execution structure, executions have bounded length. -/
theorem exists_not_mpPathFrom [Nonempty I] {π : MPPolicy F A C I} (hfin : P.MPFinite π)
    (hacyc : P.MPAcyclic π) : ∃ N, ¬ P.MPPathFrom π P.mpInit N := by
  classical
  obtain ⟨S, hS, hcov⟩ := hfin
  refine ⟨hS.toFinset.card, ?_⟩
  rintro ⟨f, hf0, hf⟩
  set N := hS.toFinset.card
  have hreach : ∀ i ≤ N, P.MPReach π (f i) := by
    intro i hi
    induction i with
    | zero => rw [hf0]; exact .refl
    | succ i ih => exact (ih (by omega)).tail (hf i (by omega))
  have htrans : ∀ i j, i < j → j ≤ N → Relation.TransGen (P.MPStep π) (f i) (f j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact (ih h (by omega)).tail (hf j (by omega))
      · subst h; exact .single (hf i (by omega))
  let rep : ℕ → MPNode F A C I := fun i =>
    if h : i ≤ N then (hcov _ (hreach i h)).choose else f i
  have hrep : ∀ i ≤ N, rep i ∈ S ∧ (f i).Iso (rep i) := by
    intro i hi
    simp only [rep, dif_pos hi]
    exact (hcov _ (hreach i hi)).choose_spec
  obtain ⟨i, hi, j, hj, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (N + 1)) (t := hS.toFinset) (by rw [Finset.card_range]; omega) (f := rep)
    (fun i hi => by
      simpa using (hrep i (by simpa [Nat.lt_succ_iff] using hi)).1)
  simp only [Finset.mem_range] at hi hj
  have hj' : (rep i).Iso (f j) := by rw [heq]; exact (hrep j (by omega)).2.symm
  have hiso : (f i).Iso (f j) := (hrep i (by omega)).2.trans hj'
  rcases lt_or_gt_of_ne hne with h | h
  · exact hacyc _ _ (hreach i (by omega)) (htrans i j h (by omega)) hiso
  · exact hacyc _ _ (hreach j (by omega)) (htrans j i h (by omega)) hiso.symm

/-- **Strong solutions win the AND/OR game.** -/
theorem mpAndOr_of_mpStrongSolvable [Nonempty I] (h : P.MPStrongSolvable) :
    P.MPAndOr P.tnI P.init := by
  obtain ⟨π, -, hfin, hacyc, hgoal⟩ := h
  obtain ⟨N, hN⟩ := exists_not_mpPathFrom hfin hacyc
  exact mpAndOr_of_noPath hgoal N P.mpInit .refl hN

end PolicyToGame

/-! ## The graded game -/

section Graded

variable (P : Problem F A C I) [DecidableEq I]

/-- The AND/OR game, graded by the height of the winning strategy. -/
inductive MPAndOrH : ℕ → TaskNetwork I A C → Set F → Prop
  /-- The empty task network is solved. -/
  | empty {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : tn.T = ∅) : MPAndOrH n tn s
  /-- Execute an unconstrained applicable primitive task. -/
  | prim {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} {t : I} {a : A} (hu : tn.Unconstrained t)
      (hα : tn.α t = Sum.inl a) (happ : (P.δ a).Applicable s)
      (hall : ∀ s' ∈ (P.δ a).outcomes s, MPAndOrH n (tn.progress t) s') : MPAndOrH (n + 1) tn s
  /-- Decompose a compound task. -/
  | decomp {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F} {t : I} {m : Method I A C}
      (hd : DecompStep P.methods tn t m tn') (h : MPAndOrH n tn' s) : MPAndOrH (n + 1) tn s

variable {P}

lemma MPAndOrH.mono {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : P.MPAndOrH n tn s) :
    ∀ {n'}, n ≤ n' → P.MPAndOrH n' tn s := by
  induction h with
  | empty h => exact fun _ => .empty h
  | prim hu hα happ _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .prim hu hα happ fun s' hs' => ih s' hs' (by omega)
  | decomp hd _ ih =>
    intro n' hn
    obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
    exact .decomp hd (ih (by omega))

lemma MPAndOrH.empty_of_zero {tn : TaskNetwork I A C} {s : Set F} (h : P.MPAndOrH 0 tn s) :
    tn.T = ∅ := by
  cases h with
  | empty h => exact h

lemma MPAndOrH.toAndOr {n : ℕ} {tn : TaskNetwork I A C} {s : Set F} (h : P.MPAndOrH n tn s) :
    P.MPAndOr tn s := by
  induction h with
  | empty h => exact .empty h
  | prim hu hα happ _ ih => exact .prim hu hα happ ih
  | decomp hd _ ih => exact .decomp hd ih

lemma MPAndOr.toH (hA : ∀ a, (P.δ a).WF) {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPAndOr tn s) : ∃ n, P.MPAndOrH n tn s := by
  classical
  induction h with
  | empty h => exact ⟨0, .empty h⟩
  | @prim tn s t a hu hα happ _ ih =>
    let g : Set F → ℕ := fun s' => if h : s' ∈ (P.δ a).outcomes s then (ih s' h).choose else 0
    obtain ⟨N, hN⟩ := ((Action.outcomes_finite (hA a) s).image g).bddAbove
    refine ⟨N + 1, .prim hu hα happ fun s' hs' => ?_⟩
    have hg : g s' = (ih s' hs').choose := dif_pos hs'
    exact (ih s' hs').choose_spec.mono (hg ▸ hN ⟨s', hs', rfl⟩)
  | decomp hd _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .decomp hd hn⟩

lemma mpAndOr_iff_exists_H (hA : ∀ a, (P.δ a).WF) {tn : TaskNetwork I A C} {s : Set F} :
    P.MPAndOr tn s ↔ ∃ n, P.MPAndOrH n tn s :=
  ⟨MPAndOr.toH hA, fun ⟨_, h⟩ => h.toAndOr⟩

/-- The graded game is invariant under isomorphism. -/
theorem MPAndOrH.isoVia [Infinite I] {n : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPAndOrH n tn s) :
    ∀ {tn' : TaskNetwork I A C} {σ : I → I}, tn.WF → tn'.WF → IsoVia σ tn tn' →
      P.MPAndOrH n tn' s := by
  induction h with
  | empty he => exact fun _ _ hσ => .empty (hσ.empty he)
  | prim hu hα happ _ ih =>
    intro tn' σ hw hw' hσ
    exact .prim (hσ.unconstrained hu) ((hσ.α_eq hu.1).trans hα) happ fun s' hs' =>
      ih s' hs' (progress_wf hw hu) (progress_wf hw' (hσ.unconstrained hu)) (hσ.progress hu.1)
  | decomp hd _ ih =>
    intro tn' σ hw hw' hσ
    obtain ⟨u', hd', ρ, hρ⟩ := hd.isoVia hw hw' hσ
    exact .decomp hd' (ih (hd.wf hw) (hd'.wf hw') hρ)

theorem MPAndOrH.iff_of_isoVia [Infinite I] {n : ℕ} {tn tn' : TaskNetwork I A C} {s : Set F}
    {σ : I → I} (hw : tn.WF) (hw' : tn'.WF) (hσ : IsoVia σ tn tn') :
    P.MPAndOrH n tn s ↔ P.MPAndOrH n tn' s := by
  obtain ⟨τ, hτ, -⟩ := hσ.exists_inv
  exact ⟨fun h => h.isoVia hw hw' hσ, fun h => h.isoVia hw' hw hτ⟩

end Graded

/-! ## The policy -/

section Policy

variable [DecidableEq I]

/-- Isomorphism together with agreement on well-formedness: an equivalence relation. -/
def isoWFSetoid [Nonempty I] : Setoid (TaskNetwork I A C) where
  r tn tn' := tn.Iso tn' ∧ (tn.WF ↔ tn'.WF)
  iseqv := ⟨fun tn => ⟨HTN.TaskNetwork.Iso.refl tn, Iff.rfl⟩,
    fun h => ⟨h.1.symm, h.2.symm⟩, fun h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩⟩

/-- A canonical representative of the class of `tn`. -/
noncomputable def canon [Nonempty I] (tn : TaskNetwork I A C) : TaskNetwork I A C :=
  Quotient.out (Quotient.mk (isoWFSetoid (A := A) (C := C)) tn)

omit [DecidableEq I] in
lemma canon_rel [Nonempty I] (tn : TaskNetwork I A C) :
    (canon tn).Iso tn ∧ ((canon tn).WF ↔ tn.WF) :=
  Quotient.mk_out (s := isoWFSetoid) tn

omit [DecidableEq I] in
lemma canon_eq [Nonempty I] {tn tn' : TaskNetwork I A C} (h : tn.Iso tn')
    (hw : tn.WF ↔ tn'.WF) : canon tn = canon tn' :=
  congrArg Quotient.out (Quotient.sound (s := isoWFSetoid) ⟨h, hw⟩)

lemma canon_canon [Nonempty I] (tn : TaskNetwork I A C) : canon (canon tn) = canon tn :=
  canon_eq (canon_rel tn).1 (canon_rel tn).2

variable (P : Problem F A C I)

/-- An instruction realising height `k + 1` at `(tn, s)`. -/
def MPGood (k : ℕ) (tn : TaskNetwork I A C) (s : Set F) (i : I × Option (Method I A C)) :
    Prop :=
  (i.2 = none ∧ ∃ a, tn.Unconstrained i.1 ∧ tn.α i.1 = Sum.inl a ∧ (P.δ a).Applicable s ∧
      ∀ s' ∈ (P.δ a).outcomes s, P.MPAndOrH k (tn.progress i.1) s') ∨
    ∃ m tn', i.2 = some m ∧ DecompStep P.methods tn i.1 m tn' ∧ P.MPAndOrH k tn' s

/-- The policy is defined at `(tn, s)` iff `tn` is a well-formed canonical representative and
`(tn, s)` is won with minimal height `k + 1`. -/
def MPPolicyCond [Nonempty I] (tn : TaskNetwork I A C) (s : Set F) : Prop :=
  tn.WF ∧ canon tn = tn ∧ ∃ k i, (∀ j, P.MPAndOrH j tn s → k + 1 ≤ j) ∧ P.MPGood k tn s i

open Classical in
/-- **The policy read off the AND/OR game.** -/
noncomputable def andOrPolicy [Nonempty I] : MPPolicy F A C I := fun tn s =>
  if h : P.MPPolicyCond tn s then some h.2.2.choose_spec.choose else none

variable {P}

lemma MPGood.toH {k : ℕ} {tn : TaskNetwork I A C} {s : Set F} {i : I × Option (Method I A C)}
    (h : P.MPGood k tn s i) : P.MPAndOrH (k + 1) tn s := by
  rcases h with ⟨-, a, hu, hα, happ, hall⟩ | ⟨m, tn', -, hd, h⟩
  · exact .prim hu hα happ hall
  · exact .decomp hd h

lemma exists_mpGood {k : ℕ} {tn : TaskNetwork I A C} {s : Set F}
    (h : P.MPAndOrH (k + 1) tn s) (hne : tn.T ≠ ∅) : ∃ i, P.MPGood k tn s i := by
  cases h with
  | empty h => exact absurd h hne
  | prim hu hα happ hall => exact ⟨(_, none), Or.inl ⟨rfl, _, hu, hα, happ, hall⟩⟩
  | decomp hd h => exact ⟨(_, some _), Or.inr ⟨_, _, rfl, hd, h⟩⟩

lemma andOrPolicy_spec [Nonempty I] {tn : TaskNetwork I A C} {s : Set F}
    {i : I × Option (Method I A C)} (h : P.andOrPolicy tn s = some i) :
    tn.WF ∧ canon tn = tn ∧ ∃ k, (∀ j, P.MPAndOrH j tn s → k + 1 ≤ j) ∧ P.MPGood k tn s i := by
  unfold andOrPolicy at h
  split_ifs at h with hc
  cases h
  exact ⟨hc.1, hc.2.1, _, hc.2.2.choose_spec.choose_spec⟩

lemma andOrPolicy_wellDefined [Nonempty I] : (P.andOrPolicy).WellDefined := by
  intro tn tn' s h h' hiso
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.1 h'
  obtain ⟨hw, hc, -⟩ := andOrPolicy_spec hi
  obtain ⟨hw', hc', -⟩ := andOrPolicy_spec hi'
  rw [← hc, ← hc']
  exact canon_eq hiso ⟨fun _ => hw', fun _ => hw⟩

/-- Properties of an entry of the policy transported to an isomorphic node. -/
lemma andOrPolicy_entry [Infinite I] {tn₀ : TaskNetwork I A C} {x : MPNode F A C I}
    {σ : I → I} {i : I × Option (Method I A C)} (hπ : P.andOrPolicy tn₀ x.state = some i)
    (hσ : IsoVia σ tn₀ x.net) (hx : x.net.WF) :
    tn₀.WF ∧ ∃ k, (∀ j, P.MPAndOrH j x.net x.state → k + 1 ≤ j) ∧
      P.MPAndOrH (k + 1) x.net x.state ∧ P.MPGood k tn₀ x.state i := by
  obtain ⟨hw₀, -, k, hmin, hgood⟩ := andOrPolicy_spec hπ
  refine ⟨hw₀, k, fun j hj => hmin j ((MPAndOrH.iff_of_isoVia hw₀ hx hσ).2 hj),
    (MPAndOrH.iff_of_isoVia hw₀ hx hσ).1 hgood.toH, hgood⟩

/-- **Every step decreases the height.** -/
theorem andOrPolicy_step [Infinite I] {x y : MPNode F A C I} (hx : x.net.WF)
    (hs : P.MPStep P.andOrPolicy x y) :
    ∃ k, (∀ j, P.MPAndOrH j x.net x.state → k + 1 ≤ j) ∧ P.MPAndOrH (k + 1) x.net x.state ∧
      y.net.WF ∧ P.MPAndOrH k y.net y.state := by
  cases hs with
  | @prim t a s' hi hu hα happ hs' =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    obtain ⟨hw₀, k, hmin, hk, hgood⟩ := andOrPolicy_entry hπ hσ hx
    refine ⟨k, hmin, hk, progress_wf hx hu, ?_⟩
    rcases hgood with ⟨-, a', hu₀, hα₀, -, hall⟩ | ⟨m, tn', hm, -⟩
    · obtain rfl : a' = a := Sum.inl_injective (hα₀.symm.trans ((hσ.α_eq ht₀).symm.trans hα))
      exact (hall s' hs').isoVia (progress_wf hw₀ hu₀) (progress_wf hx hu) (hσ.progress ht₀)
    · simp at hm
  | @decomp t m u hi hd =>
    obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, rfl⟩ := hi
    obtain ⟨hw₀, k, hmin, hk, hgood⟩ := andOrPolicy_entry hπ hσ hx
    refine ⟨k, hmin, hk, hd.wf hx, ?_⟩
    rcases hgood with ⟨hm, -⟩ | ⟨m', tn', hm, hd₀, h⟩
    · simp at hm
    · obtain ⟨ρ, hρ⟩ := hd₀.iso_of_isoVia hd (Option.some_injective _ hm).symm hw₀ hx hσ
      exact h.isoVia (hd₀.wf hw₀) (hd.wf hx) hρ

/-- **No bad terminal nodes.** At a won node with a non-empty network the policy can move. -/
theorem andOrPolicy_progress [Infinite I] (hA : ∀ a, (P.δ a).WF) {x : MPNode F A C I}
    (hx : x.net.WF) {n : ℕ} (hn : P.MPAndOrH n x.net x.state) (hne : x.net.T ≠ ∅) :
    ∃ y, P.MPStep P.andOrPolicy x y := by
  classical
  set r := canon x.net
  have hr := canon_rel x.net
  have hrw : r.WF := hr.2.2 hx
  obtain ⟨σ, hσ⟩ := hr.1
  replace hσ : IsoVia σ r x.net := hσ
  have hcr : canon r = r := canon_canon x.net
  have hex : ∃ n, P.MPAndOrH n r x.state := ⟨n, (MPAndOrH.iff_of_isoVia hrw hx hσ).2 hn⟩
  set h := Nat.find hex
  have hh : P.MPAndOrH h r x.state := Nat.find_spec hex
  have hrne : r.T ≠ ∅ := fun he => hne (hσ.empty he)
  obtain ⟨k, hk⟩ : ∃ k, h = k + 1 := by
    rcases hh0 : h with _ | k
    · exact absurd (MPAndOrH.empty_of_zero (hh0 ▸ hh)) hrne
    · exact ⟨k, rfl⟩
  obtain ⟨i, hi⟩ := exists_mpGood (hk ▸ hh) hrne
  have hcond : P.MPPolicyCond r x.state :=
    ⟨hrw, hcr, k, i, fun j hj => hk ▸ Nat.find_min' hex hj, hi⟩
  obtain ⟨i₀, hπ⟩ : ∃ i₀, P.andOrPolicy r x.state = some i₀ :=
    ⟨_, by unfold andOrPolicy; exact dif_pos hcond⟩
  obtain ⟨-, -, k₀, -, hgood⟩ := andOrPolicy_spec hπ
  rcases hgood with ⟨h2, a, hu, hα, happ, -⟩ | ⟨m, tn', h2, hd, -⟩
  · have hπ' : P.andOrPolicy r x.state = some (i₀.1, none) := by rw [hπ, ← h2]
    obtain ⟨s', hs'⟩ := Action.outcomes_nonempty (hA a) x.state
    exact ⟨_, MPStep.prim ⟨r, σ, i₀.1, hσ, hu.1, hπ', rfl⟩ (hσ.unconstrained hu)
      ((hσ.α_eq hu.1).trans hα) happ hs'⟩
  · have hπ' : P.andOrPolicy r x.state = some (i₀.1, some m) := by rw [hπ, ← h2]
    obtain ⟨u', hd', -⟩ := hd.isoVia hrw hx hσ
    exact ⟨_, MPStep.decomp ⟨r, σ, i₀.1, hσ, hd.2.1, hπ', rfl⟩ hd'⟩

/-- Finitely many successor classes. -/
theorem andOrPolicy_succ [Infinite I] (hA : ∀ a, (P.δ a).WF) {x : MPNode F A C I}
    (hx : x.net.WF) :
    ∃ L : Set (MPNode F A C I), L.Finite ∧
      (∀ y ∈ L, y.net.WF ∧ ∃ k, (∀ j, P.MPAndOrH j x.net x.state → k + 1 ≤ j) ∧
        P.MPAndOrH k y.net y.state) ∧
      ∀ y, P.MPStep P.andOrPolicy x y → ∃ y' ∈ L, y.Iso y' := by
  classical
  by_cases hex : ∃ y, P.MPStep P.andOrPolicy x y
  swap
  · exact ⟨∅, Set.finite_empty, by simp, fun y hy => absurd ⟨y, hy⟩ hex⟩
  -- the (unique) entry of the policy used at `x`
  obtain ⟨tn₀, σ₀, t₀, mo, hσ₀, ht₀, hπ₀⟩ : ∃ tn₀ σ₀ t₀ mo, IsoVia σ₀ tn₀ x.net ∧ t₀ ∈ tn₀.T ∧
      P.andOrPolicy tn₀ x.state = some (t₀, mo) := by
    obtain ⟨y, hy⟩ := hex
    cases hy with
    | prim hi => obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, -⟩ := hi; exact ⟨_, _, _, _, hσ, ht₀, hπ⟩
    | decomp hi => obtain ⟨tn₀, σ, t₀, hσ, ht₀, hπ, -⟩ := hi; exact ⟨_, _, _, _, hσ, ht₀, hπ⟩
  obtain ⟨hw₀, k, hmin, -, hgood⟩ := andOrPolicy_entry hπ₀ hσ₀ hx
  -- every instruction at `x` comes from this entry
  have huniq : ∀ {tn₁ σ₁ t₁ mo₁}, IsoVia σ₁ tn₁ x.net → t₁ ∈ tn₁.T →
      P.andOrPolicy tn₁ x.state = some (t₁, mo₁) → tn₁ = tn₀ ∧ t₁ = t₀ ∧ mo₁ = mo := by
    intro tn₁ σ₁ t₁ mo₁ hσ₁ _ hπ₁
    have htn : tn₁ = tn₀ := andOrPolicy_wellDefined tn₁ tn₀ x.state (by rw [hπ₁]; rfl)
      (by rw [hπ₀]; rfl) (hσ₁.iso.trans hσ₀.iso.symm)
    subst htn
    rw [hπ₀] at hπ₁
    cases hπ₁
    exact ⟨rfl, rfl, rfl⟩
  rcases hgood with ⟨hmo, a₀, hu₀, hα₀, -, hall⟩ | ⟨m, tn', hmo, hd₀, hk⟩
  · obtain rfl : mo = none := hmo
    refine ⟨(fun s' => (⟨tn₀.progress t₀, s'⟩ : MPNode F A C I)) ''
      (P.δ a₀).outcomes x.state, (Action.outcomes_finite (hA a₀) _).image _, ?_, ?_⟩
    · rintro _ ⟨s', hs', rfl⟩
      exact ⟨progress_wf hw₀ hu₀, k, hmin, hall s' hs'⟩
    · intro y hy
      cases hy with
      | @prim t a s' hi hu hα happ hs' =>
        obtain ⟨tn₁, σ₁, t₁, hσ₁, ht₁, hπ₁, rfl⟩ := hi
        obtain ⟨rfl, rfl, -⟩ := huniq hσ₁ ht₁ hπ₁
        obtain rfl : a = a₀ := Sum.inl_injective (hα.symm.trans ((hσ₁.α_eq ht₁).trans hα₀))
        exact ⟨_, ⟨s', hs', rfl⟩, rfl, (hσ₁.progress ht₁).iso.symm⟩
      | decomp hi =>
        obtain ⟨tn₁, σ₁, t₁, hσ₁, ht₁, hπ₁, rfl⟩ := hi
        exact absurd (huniq hσ₁ ht₁ hπ₁).2.2 (by simp)
  · obtain rfl : mo = some m := hmo
    refine ⟨{⟨tn', x.state⟩}, Set.finite_singleton _, ?_, ?_⟩
    · rintro _ rfl
      exact ⟨hd₀.wf hw₀, k, hmin, hk⟩
    · intro y hy
      cases hy with
      | prim hi =>
        obtain ⟨tn₁, σ₁, t₁, hσ₁, ht₁, hπ₁, rfl⟩ := hi
        exact absurd (huniq hσ₁ ht₁ hπ₁).2.2 (by simp)
      | @decomp t m' u hi hd =>
        obtain ⟨tn₁, σ₁, t₁, hσ₁, ht₁, hπ₁, rfl⟩ := hi
        obtain ⟨rfl, rfl, hm⟩ := huniq hσ₁ ht₁ hπ₁
        exact ⟨_, rfl, rfl, (hd₀.iso_of_isoVia hd (Option.some_injective _ hm).symm hw₀ hx
          hσ₁).symm⟩

/-- Finitely many classes of nodes are reachable from a node won with height `k`. -/
theorem andOrPolicy_finite_from [Infinite I] (hA : ∀ a, (P.δ a).WF) :
    ∀ (k : ℕ) (x : MPNode F A C I), x.net.WF → P.MPAndOrH k x.net x.state →
      ∃ S : Set (MPNode F A C I), S.Finite ∧
        ∀ z, Relation.ReflTransGen (P.MPStep P.andOrPolicy) x z → ∃ w ∈ S, z.Iso w := by
  classical
  intro k
  induction k with
  | zero =>
    intro x _ hk
    have he := MPAndOrH.empty_of_zero hk
    refine ⟨{x}, Set.finite_singleton _, fun z hz => ⟨x, rfl, ?_⟩⟩
    rcases Relation.ReflTransGen.cases_head hz with rfl | ⟨y, hxy, -⟩
    · exact MPNode.Iso.refl _
    · exfalso
      cases hxy with
      | prim _ hu => exact absurd hu.1 (by simp [he])
      | decomp _ hd => exact absurd hd.2.1 (by simp [he])
  | succ k ih =>
    intro x hx hk
    obtain ⟨L, hLfin, hLprop, hLcov⟩ := andOrPolicy_succ hA hx
    have hL : ∀ y ∈ L, ∃ S : Set (MPNode F A C I), S.Finite ∧
        ∀ z, Relation.ReflTransGen (P.MPStep P.andOrPolicy) y z → ∃ w ∈ S, z.Iso w := by
      intro y hy
      obtain ⟨hyw, k₀, hmin, hk₀⟩ := hLprop y hy
      exact ih y hyw (hk₀.mono (by have := hmin _ hk; omega))
    let Sy : MPNode F A C I → Set (MPNode F A C I) := fun y =>
      if h : y ∈ L then (hL y h).choose else ∅
    refine ⟨insert x (⋃ y ∈ L, Sy y), (hLfin.biUnion fun y hy => ?_).insert x, fun z hz => ?_⟩
    · simp only [Sy, dif_pos hy]; exact (hL y hy).choose_spec.1
    · rcases Relation.ReflTransGen.cases_head hz with rfl | ⟨y, hxy, hyz⟩
      · exact ⟨x, Set.mem_insert _ _, MPNode.Iso.refl _⟩
      · obtain ⟨y', hy'L, hyy'⟩ := hLcov y hxy
        obtain ⟨z', hz', hzz'⟩ := MPStep.sim_star hyz (andOrPolicy_step hx hxy).choose_spec.2.2.1
          (hLprop y' hy'L).1 hyy'
        have hspec : ∃ w ∈ Sy y', z'.Iso w := by
          simp only [Sy, dif_pos hy'L]; exact (hL y' hy'L).choose_spec.2 z' hz'
        obtain ⟨w, hw, hz'w⟩ := hspec
        exact ⟨w, Set.mem_insert_of_mem _ (Set.mem_biUnion hy'L hw), hzz'.trans hz'w⟩

/-- **The AND/OR game yields a strong solution.** -/
theorem mpStrongSolvable_of_mpAndOr [Infinite I] (hP : P.WF) (h : P.MPAndOr P.tnI P.init) :
    P.MPStrongSolvable := by
  classical
  obtain ⟨n₀, hn₀⟩ := MPAndOr.toH hP.actions h
  -- the height of a node
  let H : MPNode F A C I → ℕ := fun x =>
    if hx : ∃ n, P.MPAndOrH n x.net x.state then Nat.find hx else 0
  have H_spec : ∀ x k, (∀ j, P.MPAndOrH j x.net x.state → k + 1 ≤ j) →
      P.MPAndOrH (k + 1) x.net x.state → H x = k + 1 := by
    intro x k hmin hk
    have hex : ∃ n, P.MPAndOrH n x.net x.state := ⟨_, hk⟩
    simp only [H, dif_pos hex]
    exact le_antisymm (Nat.find_min' hex hk) (hmin _ (Nat.find_spec hex))
  have H_le : ∀ x k, P.MPAndOrH k x.net x.state → H x ≤ k := by
    intro x k hk
    have hex : ∃ n, P.MPAndOrH n x.net x.state := ⟨_, hk⟩
    simp only [H, dif_pos hex]
    exact Nat.find_min' hex hk
  -- reachable nodes are well formed and won
  have hreach : ∀ x, P.MPReach P.andOrPolicy x → x.net.WF ∧ ∃ n, P.MPAndOrH n x.net x.state := by
    intro x hx
    induction hx with
    | refl => exact ⟨hP.tnI, n₀, hn₀⟩
    | tail _ hs ih =>
      obtain ⟨k, -, -, hw, hk⟩ := andOrPolicy_step ih.1 hs
      exact ⟨hw, k, hk⟩
  -- steps decrease the height
  have hdec : ∀ x y, x.net.WF → P.MPStep P.andOrPolicy x y → y.net.WF ∧ H y < H x := by
    intro x y hx hs
    obtain ⟨k, hmin, hk, hw, hky⟩ := andOrPolicy_step hx hs
    exact ⟨hw, by rw [H_spec x k hmin hk]; have := H_le y k hky; omega⟩
  have hdec' : ∀ x y, x.net.WF → Relation.TransGen (P.MPStep P.andOrPolicy) x y →
      y.net.WF ∧ H y < H x := by
    intro x y hx hxy
    induction hxy with
    | single hs => exact hdec _ _ hx hs
    | tail _ hs ih =>
      obtain ⟨hw, hlt⟩ := ih
      obtain ⟨hw', hlt'⟩ := hdec _ _ hw hs
      exact ⟨hw', by omega⟩
  -- isomorphic nodes have the same height
  have H_iso : ∀ x y, x.net.WF → y.net.WF → x.Iso y → H x = H y := by
    rintro ⟨tn, s⟩ ⟨tn', s'⟩ hx hy ⟨hs, σ, hσ⟩
    simp only at hs hx hy hσ
    subst hs
    have : ∀ j, P.MPAndOrH j tn s ↔ P.MPAndOrH j tn' s :=
      fun j => MPAndOrH.iff_of_isoVia hx hy hσ
    simp only [H, this]
  refine ⟨P.andOrPolicy, andOrPolicy_wellDefined, ?_, ?_, ?_⟩
  · obtain ⟨S, hS, hcov⟩ := andOrPolicy_finite_from hP.actions n₀ P.mpInit hP.tnI hn₀
    exact ⟨S, hS, fun x hx => hcov x hx⟩
  · intro x y hx hxy hiso
    have hxw := (hreach x hx).1
    obtain ⟨hyw, hlt⟩ := hdec' x y hxw hxy
    have := H_iso x y hxw hyw hiso
    omega
  · intro x hx hterm
    obtain ⟨hxw, n, hn⟩ := hreach x hx
    by_contra hne
    obtain ⟨y, hy⟩ := andOrPolicy_progress hP.actions hxw hn hne
    exact hterm y hy

end Policy

variable [DecidableEq I] {P : Problem F A C I}

/-- **Strong method-based solvability [CB22] is the AND/OR game.** -/
theorem mpStrongSolvable_iff_mpAndOr [Infinite I] (hP : P.WF) :
    P.MPStrongSolvable ↔ P.MPAndOr P.tnI P.init :=
  ⟨mpAndOr_of_mpStrongSolvable, mpStrongSolvable_of_mpAndOr hP⟩

end Problem

end FOND
