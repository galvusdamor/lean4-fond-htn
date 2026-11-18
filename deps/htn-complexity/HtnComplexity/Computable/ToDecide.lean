import HtnComplexity.Computable.StripsDecide
import HtnPlanning.Computable.Bodies
/-!
# Plan existence is decidable for described totally ordered HTN problems

A totally ordered HTN problem is a *context-free* planning problem: by the normal form theorem
`HTN.Problem.solvable_iff_yieldSeq` it is solvable exactly when the initial task sequence can be
refined, leftmost first, into an executable action sequence reaching the goal
(`HTN.Domain.YieldSeq`).  Plan existence is therefore decidable, even though the hierarchy may
be cyclic and the plans unboundedly long: only the *state* a refinement reaches matters, and
there are finitely many relevant states.

This file builds that decision procedure and proves it correct.  The construction is the usual
saturation, in the style of `HtnPlanning/Computable/Reach.lean`:

* only the facts of `HTN.Syn.ToDec.facts d q` — the goal facts and the precondition facts of the
  described actions — are relevant, and an **abstract state** is a sublist of that list
  (`HTN.Syn.ToDec.subsets`); `HTN.Syn.ToDec.Rep U l S` says that the abstract state `l`
  represents the semantic state `S`;
* `HTN.Syn.ToDec.iterR d U n` is a list of triples `(c, l, l')`, read as *"the compound task `c`
  has a refinement that leads from `l` to `l'`"*, computed by `n` rounds of saturation, and
  `HTN.Syn.ToDec.satR` runs enough rounds for the iteration to be stable;
* `HTN.Syn.ToDec.succBody` propagates a set of abstract states along the body of a method, using
  the described action model for the primitive tasks and the current triples for the compound
  ones.

The correctness statement is `HTN.Syn.ToDec.toSolvableB_iff`, and the decider for the class
`TO-HTN` is `HTN.Syn.decider_TO_HTN` in `Computable/ToDecideCell.lean`.
-/

namespace HTN

namespace Syn

namespace ToDec

/-! ### Abstract states -/

/-- The facts that matter: the goal facts and the precondition facts of the described actions.
Whether an action is applicable and whether the goal holds depend on the state only through
these. -/
def facts (d : DomDesc) (q : InstDesc) : List ℕ :=
  q.goalList ++ d.actions.flatMap fun a => a.2.1

/-- The canonical abstract state of a list of facts. -/
def nrm (U l : List ℕ) : List ℕ := U.filter fun f => memB l f

/-- All abstract states: all sublists of the list of relevant facts. -/
def subsets : List ℕ → List (List ℕ)
  | [] => [[]]
  | f :: U => subsets U ++ (subsets U).map fun l => f :: l

/-- The abstract state `l` **represents** the semantic state `S`. -/
def Rep (U l : List ℕ) (S : Set ℕ) : Prop := ∀ f ∈ U, (f ∈ l ↔ f ∈ S)

theorem mem_subsets_filter (p : ℕ → Bool) : ∀ U : List ℕ, U.filter p ∈ subsets U := by
  intro U
  induction U with
  | nil => simp [subsets]
  | cons f U ih =>
    by_cases h : p f
    · rw [List.filter_cons_of_pos h]
      exact List.mem_append_right _ (List.mem_map.2 ⟨U.filter p, ih, rfl⟩)
    · rw [List.filter_cons_of_neg (by simpa using h)]
      exact List.mem_append_left _ ih

theorem nrm_mem_subsets (U l : List ℕ) : nrm U l ∈ subsets U :=
  mem_subsets_filter _ U

@[simp] theorem mem_nrm {U l : List ℕ} {f : ℕ} : f ∈ nrm U l ↔ f ∈ U ∧ f ∈ l := by
  simp [nrm]

theorem rep_nrm (U l : List ℕ) : Rep U (nrm U l) {f | f ∈ l} := by
  intro f hf
  simp [hf]

/-! ### The relevant facts really are the relevant ones -/

variable {d : DomDesc} {q : InstDesc}

/-- The preconditions of a described action are relevant facts. -/
theorem prec_subset_facts (a : ℕ) : ∀ f ∈ (actOf d a).1, f ∈ facts d q := by
  intro f hf
  refine List.mem_append_right _ (List.mem_flatMap.2 ?_)
  rw [actOf_eq] at hf
  rcases h : d.actions.lookup a with _ | v
  · rw [h] at hf; simp at hf
  · rw [h] at hf
    exact ⟨(a, v), mem_of_lookup_eq_some h, hf⟩

/-- The goal facts are relevant facts. -/
theorem goal_subset_facts : ∀ f ∈ q.goalList, f ∈ facts d q := fun _ hf =>
  List.mem_append_left _ hf

/-- Applicability of an action only depends on the relevant facts. -/
theorem applB_congr {U l : List ℕ} {S : Set ℕ} (hU : ∀ a : ℕ, ∀ f ∈ (actOf d a).1, f ∈ U)
    (hrep : Rep U l S) (a : ℕ) :
    applB d l a = true ↔ d.toDomain.Applicable a S := by
  rw [applB_iff]
  simp only [ActionModel.Applicable, DomDesc.toDomain_prec, prec_eq_actOf]
  constructor
  · intro h f hf
    exact (hrep f (hU a f hf)).1 (h hf)
  · intro h f hf
    exact (hrep f (hU a f hf)).2 (h hf)

/-- The state an action reaches, abstractly. -/
theorem rep_step {U l : List ℕ} {S : Set ℕ} (hrep : Rep U l S) (a : ℕ) :
    Rep U (nrm U (stepL d l a)) (d.toDomain.transition a S) := by
  intro f hf
  have h1 : f ∈ nrm U (stepL d l a) ↔ f ∈ stepL d l a := by simp [hf]
  rw [h1]
  simp only [stepL, ActionModel.transition, List.mem_append, List.mem_filter,
    Set.mem_union, Set.mem_diff, DomDesc.toDomain_add, DomDesc.toDomain_del, add_eq_actOf,
    del_eq_actOf, Set.mem_setOf_eq, Bool.not_eq_eq_eq_not, Bool.not_true, memB_eq_false_iff]
  rw [hrep f hf]

/-- The goal test only depends on the relevant facts. -/
theorem goalB_rep {U l : List ℕ} {S : Set ℕ} (hrep : Rep U l S) :
    ∀ gs : List ℕ, (∀ f ∈ gs, f ∈ U) →
      ((gs.foldr (fun f b => memB l f && b) true) = true ↔ {f | f ∈ gs} ⊆ S) := by
  intro gs
  induction gs with
  | nil => intro _; simp
  | cons f fs ih =>
    intro hU
    rw [show ((f :: fs).foldr (fun f b => memB l f && b) true) =
      (memB l f && fs.foldr (fun f b => memB l f && b) true) from rfl]
    rw [Bool.and_eq_true, memB_iff, ih fun x hx => hU x (List.mem_cons_of_mem _ hx),
      hrep f (hU f List.mem_cons_self)]
    constructor
    · rintro ⟨hf, hsub⟩ x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact hsub hx
    · intro hsub
      exact ⟨hsub List.mem_cons_self, fun x hx => hsub (List.mem_cons_of_mem _ hx)⟩

/-! ### The saturation -/

/-- A triple `(c, l, l')`: the compound task `c` leads from the abstract state `l` to `l'`. -/
abbrev Trip : Type := ℕ × List ℕ × List ℕ

/-- Membership in a list of triples, as a `Bool`. -/
def memT (R : List Trip) (t : Trip) : Bool :=
  R.foldr (fun x b => if x = t then true else b) false

@[simp] theorem memT_iff {R : List Trip} {t : Trip} : memT R t = true ↔ t ∈ R := by
  induction R with
  | nil => simp [memT]
  | cons x xs ih =>
    by_cases h : x = t
    · subst h
      simp [memT]
    · rw [show memT (x :: xs) t = memT xs t by simp [memT, h], ih, List.mem_cons]
      exact ⟨fun hn => Or.inr hn, fun hn => hn.resolve_left fun hx => h hx.symm⟩

/-- The abstract states one task leads to. -/
def succTask (d : DomDesc) (U : List ℕ) (R : List Trip) (l : List ℕ) (x : ℕ ⊕ ℕ) :
    List (List ℕ) :=
  match x with
  | Sum.inl a => if applB d l a then [nrm U (stepL d l a)] else []
  | Sum.inr c => (subsets U).filter fun l' => memT R (c, l, l')

/-- The abstract states a task sequence leads to. -/
def succBody (d : DomDesc) (U : List ℕ) (R : List Trip) (ls : List (List ℕ))
    (bs : List (ℕ ⊕ ℕ)) : List (List ℕ) :=
  bs.foldl (fun ls x => ls.flatMap fun l => succTask d U R l x) ls

/-- One round of saturation. -/
def stepR (d : DomDesc) (U : List ℕ) (R : List Trip) : List Trip :=
  R ++ d.methods.flatMap fun e => (subsets U).flatMap fun l =>
    (succBody d U R [l] (TnDesc.seqBody e.2)).map fun l' => (e.1, l, l')

/-- The saturation, after `n` rounds. -/
def iterR (d : DomDesc) (U : List ℕ) : ℕ → List Trip
  | 0 => []
  | n + 1 => stepR d U (iterR d U n)

/-- All triples the saturation can produce. -/
def allTrips (d : DomDesc) (U : List ℕ) : List Trip :=
  d.methods.flatMap fun e => (subsets U).flatMap fun l =>
    (subsets U).map fun l' => (e.1, l, l')

/-- The saturated set of triples. -/
def satR (d : DomDesc) (U : List ℕ) : List Trip :=
  iterR d U ((allTrips d U).length + 1)

/-! ### Elementary properties of the propagation -/

section Propagate

variable {U : List ℕ} {R R' : List Trip} {ls ls' : List (List ℕ)} {l : List ℕ}

@[simp] theorem succBody_nil : succBody d U R ls [] = ls := rfl

theorem succBody_cons (x : ℕ ⊕ ℕ) (bs : List (ℕ ⊕ ℕ)) :
    succBody d U R ls (x :: bs) = succBody d U R (ls.flatMap fun l => succTask d U R l x) bs :=
  rfl

/-- The propagation is computed state by state. -/
theorem succBody_flatMap : ∀ (bs : List (ℕ ⊕ ℕ)) (ls : List (List ℕ)),
    succBody d U R ls bs = ls.flatMap fun l => succBody d U R [l] bs := by
  intro bs
  induction bs with
  | nil =>
    intro ls
    simp
  | cons x bs ih =>
    intro ls
    rw [succBody_cons, ih, List.flatMap_assoc]
    refine congrArg (ls.flatMap ·) (funext fun l => ?_)
    rw [succBody_cons,
      show (List.flatMap (fun l => succTask d U R l x) [l]) = succTask d U R l x by simp,
      ih (succTask d U R l x)]

/-- The propagation along a concatenation. -/
theorem succBody_append : ∀ (bs cs : List (ℕ ⊕ ℕ)) (ls : List (List ℕ)),
    succBody d U R ls (bs ++ cs) = succBody d U R (succBody d U R ls bs) cs := by
  intro bs
  induction bs with
  | nil => intro cs ls; rfl
  | cons x bs ih =>
    intro cs ls
    rw [List.cons_append, succBody_cons, succBody_cons, ih]

theorem succTask_mono (h : R ⊆ R') (l : List ℕ) (x : ℕ ⊕ ℕ) :
    succTask d U R l x ⊆ succTask d U R' l x := by
  cases x with
  | inl a => exact fun y hy => hy
  | inr c =>
    intro y hy
    rw [succTask, List.mem_filter] at hy ⊢
    exact ⟨hy.1, memT_iff.2 (h (memT_iff.1 hy.2))⟩

theorem succBody_mono (h : R ⊆ R') : ∀ (bs : List (ℕ ⊕ ℕ)) {ls ls' : List (List ℕ)},
    ls ⊆ ls' → succBody d U R ls bs ⊆ succBody d U R' ls' bs := by
  intro bs
  induction bs with
  | nil => intro ls ls' hls; exact hls
  | cons x bs ih =>
    intro ls ls' hls
    refine ih ?_
    intro y hy
    obtain ⟨t, ht, hy⟩ := List.mem_flatMap.1 hy
    exact List.mem_flatMap.2 ⟨t, hls ht, succTask_mono h t x hy⟩

theorem succTask_subset_subsets (R : List Trip) (l : List ℕ) (x : ℕ ⊕ ℕ) :
    succTask d U R l x ⊆ subsets U := by
  cases x with
  | inl a =>
    intro y hy
    rw [succTask] at hy
    by_cases h : applB d l a
    · rw [if_pos h, List.mem_singleton] at hy
      rw [hy]
      exact nrm_mem_subsets U _
    · rw [if_neg h] at hy
      simp at hy
  | inr c => exact fun y hy => (List.mem_filter.1 hy).1

theorem succBody_subset_subsets : ∀ (bs : List (ℕ ⊕ ℕ)) {ls : List (List ℕ)},
    ls ⊆ subsets U → succBody d U R ls bs ⊆ subsets U := by
  intro bs
  induction bs with
  | nil => intro ls hls; exact hls
  | cons x bs ih =>
    intro ls hls
    refine ih ?_
    intro y hy
    obtain ⟨t, -, hy⟩ := List.mem_flatMap.1 hy
    exact succTask_subset_subsets R t x hy

/-! ### The saturation is monotone and stabilises -/

theorem subset_stepR : R ⊆ stepR d U R := fun _ hx => List.mem_append_left _ hx

theorem stepR_mono (h : R ⊆ R') : stepR d U R ⊆ stepR d U R' := by
  intro t ht
  rcases List.mem_append.1 ht with ht | ht
  · exact List.mem_append_left _ (h ht)
  · refine List.mem_append_right _ ?_
    obtain ⟨e, he, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨l, hl, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 ht
    exact List.mem_flatMap.2 ⟨e, he, List.mem_flatMap.2 ⟨l, hl,
      List.mem_map.2 ⟨l', succBody_mono h _ (fun y hy => hy) hl', rfl⟩⟩⟩

theorem iterR_subset_succ (n : ℕ) : iterR d U n ⊆ iterR d U (n + 1) := subset_stepR

theorem iterR_mono {m n : ℕ} (h : m ≤ n) : iterR d U m ⊆ iterR d U n := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.1 h
    subst this
    exact fun x hx => hx
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact fun x hx => iterR_subset_succ n (ih (Nat.lt_succ_iff.1 hlt) hx)
    · have : m = n + 1 := le_antisymm h hge
      subst this
      exact fun x hx => hx

theorem iterR_subset_allTrips : ∀ n : ℕ, iterR d U n ⊆ allTrips d U := by
  intro n
  induction n with
  | zero => intro t ht; simp [iterR] at ht
  | succ n ih =>
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact ih ht
    · obtain ⟨e, he, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨l, hl, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 ht
      refine List.mem_flatMap.2 ⟨e, he, List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨l', ?_, rfl⟩⟩⟩
      exact succBody_subset_subsets _ (by simpa using hl) hl'

/-- The saturation is *stable* at `n` when it does not grow at the next step. -/
def StableR (d : DomDesc) (U : List ℕ) (n : ℕ) : Prop := iterR d U (n + 1) ⊆ iterR d U n

theorem stableR_succ {n : ℕ} (h : StableR d U n) : StableR d U (n + 1) :=
  stepR_mono h

theorem stableR_of_le {n m : ℕ} (h : StableR d U n) (hnm : n ≤ m) : StableR d U m := by
  induction m with
  | zero =>
    have : n = 0 := Nat.le_zero.1 hnm
    subst this
    exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact stableR_succ (ih (Nat.lt_succ_iff.1 hlt))
    · have : n = m + 1 := le_antisymm hnm hge
      subst this
      exact h

theorem card_lt_of_not_stableR {n : ℕ} (h : ¬ StableR d U n) :
    (iterR d U n).toFinset.card < (iterR d U (n + 1)).toFinset.card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro x hx
    exact List.mem_toFinset.2 (iterR_subset_succ n (List.mem_toFinset.1 hx))
  · intro hsub
    exact h fun x hx => List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hx))

theorem le_card_of_not_stableR (n : ℕ) (h : ∀ k < n, ¬ StableR d U k) :
    n ≤ (iterR d U n).toFinset.card := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hn := ih fun k hk => h k (by omega)
    have := card_lt_of_not_stableR (d := d) (U := U) (h n (by omega))
    omega

theorem card_iterR_le (n : ℕ) : (iterR d U n).toFinset.card ≤ (allTrips d U).length := by
  have hsub : (iterR d U n).toFinset ⊆ (allTrips d U).toFinset := by
    intro x hx
    exact List.mem_toFinset.2 (iterR_subset_allTrips n (List.mem_toFinset.1 hx))
  exact le_trans (Finset.card_le_card hsub) (List.toFinset_card_le _)

theorem stableR_satR : StableR d U ((allTrips d U).length + 1) := by
  by_cases h : ∃ k ≤ (allTrips d U).length + 1, StableR d U k
  · obtain ⟨k, hk, hstab⟩ := h
    exact stableR_of_le hstab hk
  · push_neg at h
    have hall : ∀ k < (allTrips d U).length + 1, ¬ StableR d U k := fun k hk => h k (by omega)
    have h1 := le_card_of_not_stableR (d := d) (U := U) ((allTrips d U).length + 1) hall
    have h2 := card_iterR_le (d := d) (U := U) ((allTrips d U).length + 1)
    omega

/-- The saturated set of triples is closed under one more round. -/
theorem stepR_satR : stepR d U (satR d U) ⊆ satR d U := stableR_satR

end Propagate

/-- **The decision procedure for described totally ordered HTN problems.** -/
def toSolvableB (d : DomDesc) (q : InstDesc) : Bool :=
  (succBody d (facts d q) (satR d (facts d q)) [nrm (facts d q) q.initList]
      (TnDesc.seqBody q.tnI)).any
    fun l => q.goalList.foldr (fun f b => memB l f && b) true

/-! ### Refinements, as a relation between states -/

/-- The task sequence `xs` refines into an action sequence that is executable in `S` and leads
to `S'`. -/
def Yields (d : DomDesc) (xs : List (ℕ ⊕ ℕ)) (S S' : Set ℕ) : Prop :=
  ∃ as, d.toDomain.YieldSeq xs as ∧ d.toDomain.SeqApplicable as S ∧
    d.toDomain.transitionSeq as S = S'

theorem yields_nil (d : DomDesc) (S : Set ℕ) : Yields d [] S S :=
  ⟨[], Domain.YieldSeq.nil, by simp, rfl⟩

theorem yields_cons {x : ℕ ⊕ ℕ} {xs : List (ℕ ⊕ ℕ)} {S S₁ S' : Set ℕ}
    (h₁ : Yields d [x] S S₁) (h₂ : Yields d xs S₁ S') : Yields d (x :: xs) S S' := by
  obtain ⟨as₁, hy₁, ha₁, rfl⟩ := h₁
  obtain ⟨as₂, hy₂, ha₂, rfl⟩ := h₂
  refine ⟨as₁ ++ as₂, by simpa using hy₁.append hy₂, ?_, ?_⟩
  · exact (ActionModel.seqApplicable_append _ _ _ _).2 ⟨ha₁, ha₂⟩
  · rw [ActionModel.transitionSeq_append]

theorem yields_prim {a : ℕ} {S : Set ℕ} (h : d.toDomain.Applicable a S) :
    Yields d [Sum.inl a] S (d.toDomain.transition a S) :=
  ⟨[a], Domain.YieldSeq.prim Domain.YieldSeq.nil, by simpa using h, by simp⟩

theorem yields_comp {c : ℕ} {bs : List (ℕ ⊕ ℕ)} {S S' : Set ℕ} (hm : d.toDomain.SeqBody c bs)
    (h : Yields d bs S S') : Yields d [Sum.inr c] S S' := by
  obtain ⟨as, hy, ha, rfl⟩ := h
  exact ⟨as, Domain.YieldSeq.comp hm (by simpa using hy), ha, rfl⟩

/-! ### Soundness of the saturation -/

/-- Every triple of `R` describes a genuine refinement. -/
def TripSound (d : DomDesc) (U : List ℕ) (R : List Trip) : Prop :=
  ∀ c l l', (c, l, l') ∈ R → ∀ S : Set ℕ, Rep U l S →
    ∃ S', Yields d [Sum.inr c] S S' ∧ Rep U l' S'

variable {U : List ℕ}

/-- Whatever the propagation along a task sequence produces is a genuine refinement, provided
the triples used are. -/
theorem sound_body (hU : ∀ a : ℕ, ∀ f ∈ (actOf d a).1, f ∈ U) {R : List Trip}
    (hR : TripSound d U R) : ∀ (bs : List (ℕ ⊕ ℕ)) (l l' : List ℕ) (S : Set ℕ),
      l' ∈ succBody d U R [l] bs → Rep U l S → ∃ S', Yields d bs S S' ∧ Rep U l' S' := by
  intro bs
  induction bs with
  | nil =>
    intro l l' S hl' hrep
    rw [succBody_nil, List.mem_singleton] at hl'
    subst hl'
    exact ⟨S, yields_nil d S, hrep⟩
  | cons x bs ih =>
    intro l l' S hl' hrep
    rw [succBody_cons,
      show (([l] : List (List ℕ)).flatMap fun l => succTask d U R l x) = succTask d U R l x by
        simp,
      succBody_flatMap] at hl'
    obtain ⟨t, ht, hbs⟩ := List.mem_flatMap.1 hl'
    clear hl'
    cases x with
    | inl a =>
      rw [succTask] at ht
      by_cases hap : applB d l a
      · rw [if_pos hap, List.mem_singleton] at ht
        subst ht
        obtain ⟨S', hy, hrep'⟩ := ih _ _ _ hbs (rep_step hrep a)
        exact ⟨S', yields_cons (yields_prim ((applB_congr hU hrep a).1 hap)) hy, hrep'⟩
      · rw [if_neg hap] at ht
        simp at ht
    | inr c =>
      have htR : (c, l, t) ∈ R := memT_iff.1 (List.mem_filter.1 ht).2
      obtain ⟨S₁, hy₁, hrep₁⟩ := hR c l t htR S hrep
      obtain ⟨S', hy, hrep'⟩ := ih _ _ _ hbs hrep₁
      exact ⟨S', yields_cons hy₁ hy, hrep'⟩

/-- **The saturation is sound.** -/
theorem tripSound_iterR (hTO : d.MethodsTO) (hU : ∀ a : ℕ, ∀ f ∈ (actOf d a).1, f ∈ U) :
    ∀ n : ℕ, TripSound d U (iterR d U n) := by
  intro n
  induction n with
  | zero =>
    intro c l l' ht
    simp [iterR] at ht
  | succ n ih =>
    intro c l l' ht S hrep
    rcases List.mem_append.1 ht with ht | ht
    · exact ih c l l' ht S hrep
    · obtain ⟨e, he, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨l₀, hl₀, ht⟩ := List.mem_flatMap.1 ht
      obtain ⟨l₁, hl₁, heq⟩ := List.mem_map.1 ht
      have hc : e.1 = c := (Prod.mk.injEq _ _ _ _ ▸ heq).1
      have hl : l₀ = l := by
        have := congrArg (fun t : Trip => t.2.1) heq
        simpa using this
      have hl' : l₁ = l' := by
        have := congrArg (fun t : Trip => t.2.2) heq
        simpa using this
      subst hl; subst hl'; subst hc
      obtain ⟨S', hy, hrep'⟩ := sound_body hU ih _ _ _ _ hl₁ hrep
      refine ⟨S', yields_comp ?_ hy, hrep'⟩
      exact ⟨e.toMethod, ⟨e, he, rfl⟩, rfl,
        Method.hasSeqBody_of_isSeqNet (TnDesc.isSeqNet_lin (hTO e he))⟩

/-! ### Completeness of the saturation -/

/-- **The saturation is complete**: every refinement is found. -/
theorem complete_body (hTO : d.MethodsTO) (hU : ∀ a : ℕ, ∀ f ∈ (actOf d a).1, f ∈ U) :
    ∀ {xs : List (ℕ ⊕ ℕ)} {as : List ℕ}, d.toDomain.YieldSeq xs as →
      ∀ (l : List ℕ) (S : Set ℕ), l ∈ subsets U → Rep U l S →
        d.toDomain.SeqApplicable as S →
        ∃ l' ∈ succBody d U (satR d U) [l] xs,
          Rep U l' (d.toDomain.transitionSeq as S) := by
  intro xs as h
  induction h with
  | nil =>
    intro l S _ hrep _
    exact ⟨l, by simp, by simpa using hrep⟩
  | @prim a xs as _ ih =>
    intro l S hl hrep happ
    rw [ActionModel.seqApplicable_cons] at happ
    have hap : applB d l a = true := (applB_congr hU hrep a).2 happ.1
    set t : List ℕ := nrm U (stepL d l a) with hts
    obtain ⟨l', hl', hrep'⟩ := ih t (d.toDomain.transition a S) (nrm_mem_subsets U _)
      (rep_step hrep a) happ.2
    refine ⟨l', ?_, by simpa using hrep'⟩
    rw [succBody_cons,
      show (([l] : List (List ℕ)).flatMap fun l => succTask d U (satR d U) l (Sum.inl a)) =
        succTask d U (satR d U) l (Sum.inl a) by simp,
      succBody_flatMap]
    refine List.mem_flatMap.2 ⟨t, ?_, hl'⟩
    rw [succTask, if_pos hap, hts]
    exact List.mem_singleton.2 rfl
  | @comp c bs xs as hm _ ih =>
    intro l S hl hrep happ
    obtain ⟨l'', hl'', hrep''⟩ := ih l S hl hrep happ
    rw [succBody_append, succBody_flatMap] at hl''
    obtain ⟨t, ht, hl''⟩ := List.mem_flatMap.1 hl''
    have htsub : t ∈ subsets U :=
      succBody_subset_subsets bs (by simpa using hl) ht
    obtain ⟨m, hm', hhd, hbd⟩ := (DomDesc.seqBody_iff hTO).1 hm
    have hmem : (c, l, t) ∈ satR d U := by
      refine stepR_satR (List.mem_append_right _ ?_)
      refine List.mem_flatMap.2 ⟨d.methods.getI m, getI_mem_methods hm', ?_⟩
      refine List.mem_flatMap.2 ⟨l, hl, List.mem_map.2 ⟨t, ?_, ?_⟩⟩
      · rw [show TnDesc.seqBody (d.methods.getI m).2 = bs from hbd]
        exact ht
      · rw [show (d.methods.getI m).1 = c from hhd]
    refine ⟨l'', ?_, hrep''⟩
    rw [succBody_cons,
      show (([l] : List (List ℕ)).flatMap fun l => succTask d U (satR d U) l (Sum.inr c)) =
        succTask d U (satR d U) l (Sum.inr c) by simp,
      succBody_flatMap]
    refine List.mem_flatMap.2 ⟨t, ?_, hl''⟩
    rw [succTask, List.mem_filter]
    exact ⟨htsub, memT_iff.2 hmem⟩

/-! ### The decision procedure is correct -/

/-- **`toSolvableB` decides plan existence for described totally ordered HTN problems.** -/
theorem toSolvableB_iff (hTO : d.MethodsTO) (hq : q.IsTO) :
    toSolvableB d q = true ↔ Solvable d q := by
  have hU : ∀ a : ℕ, ∀ f ∈ (actOf d a).1, f ∈ facts d q := fun a => prec_subset_facts a
  have hgU : ∀ f ∈ q.goalList, f ∈ facts d q := goal_subset_facts
  have hrep₀ : Rep (facts d q) (nrm (facts d q) q.initList) {f | f ∈ q.initList} :=
    rep_nrm _ _
  have hnorm : Solvable d q ↔ ∃ as : List ℕ,
      d.toDomain.YieldSeq (TnDesc.seqBody q.tnI) as ∧
      d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} :=
    Problem.solvable_iff_yieldSeq (problem_wf d q) (isTO_problem hTO hq).2
      (TnDesc.isSeqNet_lin hq)
  rw [hnorm, toSolvableB, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hgoal⟩
    obtain ⟨S', hy, hrep'⟩ :=
      sound_body hU (tripSound_iterR hTO hU _) _ _ _ _ hl hrep₀
    obtain ⟨as, hys, happ, rfl⟩ := hy
    exact ⟨as, hys, happ, (goalB_rep hrep' q.goalList hgU).1 hgoal⟩
  · rintro ⟨as, hys, happ, hgoal⟩
    obtain ⟨l, hl, hrep'⟩ := complete_body hTO hU hys _ _ (nrm_mem_subsets _ _) hrep₀ happ
    exact ⟨l, hl, (goalB_rep hrep' q.goalList hgU).2 hgoal⟩

end ToDec

end Syn

end HTN
