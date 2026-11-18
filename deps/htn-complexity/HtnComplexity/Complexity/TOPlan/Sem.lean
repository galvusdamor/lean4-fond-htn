import HtnPlanning.Core.ToStateReach
import HtnPlanning.Computable.Bodies
/-!
# Totally ordered planning at a fixed domain is a finite automaton over the task sequence

For a **fixed** domain description `d` with totally ordered methods, plan existence for a totally
ordered instance `q` is decided by a finite automaton reading the task sequence of `q` (its
initial task network, linearised).  This file proves that, semantically:

* only the finitely many facts `HTN.Syn.TOPlan.vocab d` mentioned by the actions of `d` ever
  matter; every other fact is inert (`HTN.Syn.TOPlan.seqReach_inter`,
  `HTN.Syn.TOPlan.seqReach_union`);
* the automaton has as states the sets of subsets of `vocab d` (`HTN.Syn.TOPlan.step`,
  `HTN.Syn.TOPlan.run`), and reading a task sequence computes exactly the projections of the
  states reachable along it (`HTN.Syn.TOPlan.exists_seqReach_iff_run`);
* `HTN.Syn.TOPlan.solvable_iff_run` — **plan existence is acceptance by the automaton**: some
  state reached along `TnDesc.seqBody q.tnI` contains the goal facts of the vocabulary, and the
  goal facts outside the vocabulary hold initially;
* the automaton only distinguishes finitely many letters (`HTN.Syn.TOPlan.step_clsOf`): an action
  that `d` does not describe is a no-op and a compound task without a method kills every run.

Nothing here is about bit strings; the polynomial-time implementation is in the other files of
`HtnComplexity/Complexity/TOPlan/`.
-/

namespace HTN

namespace Syn

namespace TOPlan

open Classical

/-! ### Inert facts -/

section Frame

variable {F A C I : Type} {D : Domain F A C I} {V : Set F}

/-- The actions of `D` mention only facts of `V`. -/
structure Confined (D : Domain F A C I) (V : Set F) : Prop where
  prec : ∀ a, D.prec a ⊆ V
  add : ∀ a, D.add a ⊆ V
  del : ∀ a, D.del a ⊆ V

/-- **Projection to the vocabulary.**  A reachability projects to the vocabulary, and the facts
outside the vocabulary are left untouched. -/
theorem seqReach_inter (hV : Confined D V) {xs : List (A ⊕ C)} {s u : Set F}
    (h : D.SeqReach xs s u) : D.SeqReach xs (s ∩ V) (u ∩ V) ∧ u \ V = s \ V := by
  induction h with
  | nil => exact ⟨.nil, rfl⟩
  | @prim a xs s u happ _ ih =>
    have htr : D.toActionModel.transition a s ∩ V = D.toActionModel.transition a (s ∩ V) := by
      ext f
      simp only [ActionModel.transition, Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
      have := @hV.add a f
      tauto
    have htr' : D.toActionModel.transition a s \ V = s \ V := by
      ext f
      simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
      have h1 := @hV.add a f
      have h2 := @hV.del a f
      tauto
    refine ⟨.prim (fun f hf => ⟨happ hf, hV.prec a hf⟩) (htr ▸ ih.1), ih.2.trans htr'⟩
  | comp hm _ _ ihb ihs => exact ⟨.comp hm ihb.1 ihs.1, ihs.2.trans ihb.2⟩

/-- **Extension by inert facts.** -/
theorem seqReach_union (hV : Confined D V) {xs : List (A ⊕ C)} {s u R : Set F}
    (hR : Disjoint R V) (h : D.SeqReach xs s u) : D.SeqReach xs (s ∪ R) (u ∪ R) := by
  induction h with
  | nil => exact .nil
  | @prim a xs s u happ _ ih =>
    have htr : D.toActionModel.transition a s ∪ R = D.toActionModel.transition a (s ∪ R) := by
      ext f
      simp only [ActionModel.transition, Set.mem_union, Set.mem_diff]
      have h2 := @hV.del a f
      have h3 : f ∈ R → f ∉ V := fun hf hv => Set.disjoint_left.1 hR hf hv
      tauto
    exact .prim (fun f hf => Or.inl (happ hf)) (htr ▸ ih)
  | comp hm _ _ ihb ihs => exact .comp hm ihb ihs

end Frame

/-! ### The vocabulary of a domain description -/

/-- The facts mentioned by the actions of a domain description. -/
def vocab (d : DomDesc) : Finset ℕ :=
  (d.actions.flatMap fun a => a.2.1 ++ a.2.2.1 ++ a.2.2.2).toFinset

theorem mem_vocab_of_lookup {d : DomDesc} {a : ℕ} {e : List ℕ × List ℕ × List ℕ}
    (h : d.actions.lookup a = some e) {f : ℕ} (hf : f ∈ e.1 ++ e.2.1 ++ e.2.2) :
    f ∈ vocab d := by
  rw [vocab, List.mem_toFinset, List.mem_flatMap]
  exact ⟨(a, e), mem_of_lookup_eq_some h, hf⟩

theorem confined_vocab (d : DomDesc) : Confined d.toDomain ↑(vocab d) := by
  refine ⟨fun a f hf => ?_, fun a f hf => ?_, fun a f hf => ?_⟩ <;>
  · simp only [DomDesc.toDomain_prec, DomDesc.toDomain_add, DomDesc.toDomain_del,
      DomDesc.prec, DomDesc.add, DomDesc.del, Set.mem_setOf_eq] at hf
    rcases h : d.actions.lookup a with _ | e
    · rw [h] at hf; simp at hf
    · rw [h] at hf
      exact Finset.mem_coe.2 (mem_vocab_of_lookup h (by simp at hf ⊢; tauto))

/-! ### The automaton -/

variable (d : DomDesc)

/-- The one-letter relation on projected states. -/
def rel (x : ℕ ⊕ ℕ) (s u : Finset ℕ) : Prop := d.toDomain.SeqReach [x] ↑s ↑u

/-- **The transition of the automaton**: the projected states reachable by one task from some
state of the current set. -/
noncomputable def step (S : Finset (Finset ℕ)) (x : ℕ ⊕ ℕ) : Finset (Finset ℕ) :=
  (vocab d).powerset.filter fun u => ∃ s ∈ S, rel d x s u

/-- **The run of the automaton** along a task sequence. -/
noncomputable def run (S : Finset (Finset ℕ)) (xs : List (ℕ ⊕ ℕ)) : Finset (Finset ℕ) :=
  xs.foldl (step d) S

variable {d}

theorem step_subset (S : Finset (Finset ℕ)) (x : ℕ ⊕ ℕ) : step d S x ⊆ (vocab d).powerset :=
  Finset.filter_subset _ _

theorem run_subset {S : Finset (Finset ℕ)} (hS : S ⊆ (vocab d).powerset) :
    ∀ xs, run d S xs ⊆ (vocab d).powerset := by
  intro xs
  induction xs generalizing S with
  | nil => exact hS
  | cons x xs ih => exact ih (step_subset S x)

theorem finset_of_subset_vocab {u : Set ℕ} (hu : u ⊆ ↑(vocab d)) :
    ∃ u' : Finset ℕ, u' ⊆ vocab d ∧ (u' : Set ℕ) = u := by
  refine ⟨(vocab d).filter (· ∈ u), Finset.filter_subset _ _, ?_⟩
  ext f
  simp only [Finset.coe_filter, Set.mem_setOf_eq]
  exact ⟨fun h => h.2, fun h => ⟨hu h, h⟩⟩

/-- **The run computes the reachable states.**  From the states `s ∪ R` (`s` a projected state of
the current set, `R` a set of inert facts), the task sequence `xs` reaches exactly the states
`u' ∪ R` with `u'` in the run. -/
theorem exists_seqReach_iff_run {R : Set ℕ} (hR : Disjoint R ↑(vocab d)) :
    ∀ (xs : List (ℕ ⊕ ℕ)) (S : Finset (Finset ℕ)), S ⊆ (vocab d).powerset → ∀ u : Set ℕ,
      (∃ s ∈ S, d.toDomain.SeqReach xs (↑s ∪ R) u) ↔ ∃ u' ∈ run d S xs, u = ↑u' ∪ R := by
  intro xs
  induction xs with
  | nil =>
    intro S _ u
    simp only [run, List.foldl_nil]
    constructor
    · rintro ⟨s, hs, h⟩
      cases h
      exact ⟨s, hs, rfl⟩
    · rintro ⟨u', hu', rfl⟩
      exact ⟨u', hu', .nil⟩
  | cons x xs ih =>
    intro S hS u
    have hrun : run d S (x :: xs) = run d (step d S x) xs := rfl
    rw [hrun, ← ih (step d S x) (step_subset S x) u]
    constructor
    · rintro ⟨s, hs, h⟩
      obtain ⟨t, h1, h2⟩ := (Domain.seqReach_append_iff (xs := [x]) (ys := xs)).1 h
      obtain ⟨h1', ht⟩ := seqReach_inter (confined_vocab d) h1
      have hsV : (s : Set ℕ) ⊆ ↑(vocab d) := by
        intro f hf; exact Finset.mem_coe.2 (Finset.mem_powerset.1 (hS hs) hf)
      have hsR : (↑s ∪ R) ∩ ↑(vocab d) = (s : Set ℕ) := by
        ext f
        simp only [Set.mem_inter_iff, Set.mem_union]
        have h1 := @hsV f
        have h3 : f ∈ R → f ∉ (vocab d : Set ℕ) := fun h => Set.disjoint_left.1 hR h
        tauto
      obtain ⟨t', ht'V, ht'⟩ := finset_of_subset_vocab (d := d) (u := t ∩ ↑(vocab d))
        Set.inter_subset_right
      refine ⟨t', ?_, ?_⟩
      · rw [step, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨ht'V, s, hs, ?_⟩
        rw [rel, ht', ← hsR]
        exact h1'
      · have htR : t = ↑t' ∪ R := by
          rw [ht']
          have hdiff : t \ ↑(vocab d) = R := by
            rw [ht]
            ext f
            simp only [Set.mem_diff, Set.mem_union]
            have h1 := @hsV f
            have h3 : f ∈ R → f ∉ (vocab d : Set ℕ) := fun h => Set.disjoint_left.1 hR h
            tauto
          ext f
          have := congrArg (f ∈ ·) hdiff
          simp only [Set.mem_diff, eq_iff_iff] at this
          simp only [Set.mem_union, Set.mem_inter_iff]
          tauto
        rw [← htR]
        exact h2
    · rintro ⟨t', ht', h⟩
      rw [step, Finset.mem_filter] at ht'
      obtain ⟨-, s, hs, hrel⟩ := ht'
      refine ⟨s, hs, (Domain.seqReach_append_iff (xs := [x]) (ys := xs)).2
        ⟨↑t' ∪ R, seqReach_union (confined_vocab d) hR hrel, h⟩⟩

/-! ### Plan existence is acceptance -/

/-- The initial projected state of an instance. -/
def initProj (d : DomDesc) (q : InstDesc) : Finset ℕ := (vocab d).filter (· ∈ q.initList)

/-- **Acceptance**: a final projected state contains the goal facts of the vocabulary. -/
def Accepts (d : DomDesc) (q : InstDesc) (S : Finset (Finset ℕ)) : Prop :=
  ∃ u ∈ S, ∀ f ∈ vocab d, f ∈ q.goalList → f ∈ u

/-- The goal facts outside the vocabulary hold initially. -/
def OutOk (d : DomDesc) (q : InstDesc) : Prop :=
  ∀ f ∈ q.goalList, f ∉ vocab d → f ∈ q.initList

/-- **Plan existence for a totally ordered instance over a domain with totally ordered methods
is acceptance by the automaton** along the linearised initial task sequence. -/
theorem solvable_iff_run (hTO : d.MethodsTO) {q : InstDesc} (hq : q.IsTO) :
    Solvable d q ↔
      Accepts d q (run d {initProj d q} (TnDesc.seqBody q.tnI)) ∧ OutOk d q := by
  have hM : (problem d q).IsTO_M := fun m hm => by
    obtain ⟨e, he, rfl⟩ := mem_methods_of_reachable hm
    exact hTO e he
  rw [Solvable, Problem.solvable_iff_seqReach (problem_wf d q) hM
    (TnDesc.isSeqNet_lin hq)]
  set R : Set ℕ := {f | f ∈ q.initList} \ ↑(vocab d) with hRdef
  have hR : Disjoint R ↑(vocab d) := Set.disjoint_left.2 fun f hf => hf.2
  have hinit : {f | f ∈ q.initList} = ↑(initProj d q) ∪ R := by
    ext f
    simp only [hRdef, initProj, Set.mem_setOf_eq, Set.mem_union, Finset.coe_filter,
      Set.mem_diff, Finset.mem_coe]
    tauto
  have hS : ({initProj d q} : Finset (Finset ℕ)) ⊆ (vocab d).powerset := by
    intro s hs
    rw [Finset.mem_singleton.1 hs, Finset.mem_powerset]
    exact Finset.filter_subset _ _
  have key := exists_seqReach_iff_run hR (TnDesc.seqBody q.tnI) {initProj d q} hS
  have hsubrun := run_subset hS (TnDesc.seqBody q.tnI)
  simp only [problem_init, Problem.GoalState, problem_goal]
  change (∃ u, d.toDomain.SeqReach (TnDesc.seqBody q.tnI) {f | f ∈ q.initList} u ∧
    {f | f ∈ q.goalList} ⊆ u) ↔ _
  rw [hinit]
  constructor
  · rintro ⟨u, hu, hg⟩
    obtain ⟨u', hu', rfl⟩ := (key u).1 ⟨_, Finset.mem_singleton_self _, hu⟩
    refine ⟨⟨u', hu', fun f hfv hf => ?_⟩, fun f hf hfv => ?_⟩
    · rcases hg hf with h | h
      · exact h
      · exact absurd (Finset.mem_coe.2 hfv) h.2
    · rcases hg hf with h | h
      · exact absurd (Finset.mem_powerset.1 (hsubrun hu') h) hfv
      · exact h.1
  · rintro ⟨⟨u', hu', hgu⟩, hout⟩
    refine ⟨↑u' ∪ R, ?_, fun f hf => ?_⟩
    · obtain ⟨s, hs, h⟩ := (key (↑u' ∪ R)).2 ⟨u', hu', rfl⟩
      rw [Finset.mem_singleton.1 hs] at h
      exact h
    · by_cases hfv : f ∈ vocab d
      · exact Or.inl (hgu f hfv hf)
      · exact Or.inr ⟨hout f hf hfv, by simpa using hfv⟩

/-! ### Finitely many letters -/

/-- The action names described by `d`. -/
def anames (d : DomDesc) : List ℕ := d.actions.map Prod.fst

/-- The compound task names that have a method in `d`. -/
def heads (d : DomDesc) : List ℕ := d.methods.map Prod.fst

/-- A fresh action name. -/
def freshA (d : DomDesc) : ℕ := (anames d).foldr max 0 + 1

/-- A fresh compound task name. -/
def freshC (d : DomDesc) : ℕ := (heads d).foldr max 0 + 1

theorem le_foldr_max {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem freshA_nmem (d : DomDesc) : freshA d ∉ anames d := fun h => by
  have := le_foldr_max h; simp [freshA] at this

theorem freshC_nmem (d : DomDesc) : freshC d ∉ heads d := fun h => by
  have := le_foldr_max h; simp [freshC] at this

/-- **The class of a letter**: described actions and method heads are kept, every other action
becomes the fresh (no-op) action and every other compound task the fresh (dead) compound
task. -/
def clsOf (d : DomDesc) : ℕ ⊕ ℕ → ℕ ⊕ ℕ
  | Sum.inl a => if a ∈ anames d then Sum.inl a else Sum.inl (freshA d)
  | Sum.inr c => if c ∈ heads d then Sum.inr c else Sum.inr (freshC d)

/-- The letters the automaton distinguishes. -/
def letters (d : DomDesc) : List (ℕ ⊕ ℕ) :=
  (anames d).map Sum.inl ++ (heads d).map Sum.inr ++ [Sum.inl (freshA d), Sum.inr (freshC d)]

theorem clsOf_mem_letters (x : ℕ ⊕ ℕ) : clsOf d x ∈ letters d := by
  rcases x with a | c
  · simp only [clsOf]; split_ifs with h <;> simp [letters, h]
  · simp only [clsOf]; split_ifs with h <;> simp [letters, h]

theorem lookup_none_of_nmem {a : ℕ} (ha : a ∉ anames d) : d.actions.lookup a = none := by
  rcases h : d.actions.lookup a with _ | e
  · rfl
  · exact absurd (List.mem_map.2 ⟨(a, e), mem_of_lookup_eq_some h, rfl⟩) ha

theorem seqReach_nil_iff' {s u : Set ℕ} : d.toDomain.SeqReach [] s u ↔ u = s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem rel_noop {a : ℕ} (ha : a ∉ anames d) (s u : Finset ℕ) : rel d (Sum.inl a) s u ↔ u = s := by
  have hl := lookup_none_of_nmem ha
  rw [rel]
  constructor
  · intro h
    cases h with
    | prim happ hs =>
      rw [seqReach_nil_iff'] at hs
      apply Finset.coe_injective
      rw [hs]
      simp [ActionModel.transition, DomDesc.toDomain_del, DomDesc.toDomain_add, DomDesc.del,
        DomDesc.add, hl]
  · rintro rfl
    refine .prim (fun f hf => ?_) ?_
    · simp [DomDesc.toDomain_prec, DomDesc.prec, hl] at hf
    · have : d.toDomain.toActionModel.transition a ↑u = ↑u := by
        simp [ActionModel.transition, DomDesc.toDomain_del, DomDesc.toDomain_add, DomDesc.del,
          DomDesc.add, hl]
      rw [this]; exact .nil

theorem not_seqBody_of_nmem {c : ℕ} (hc : c ∉ heads d) (bs : List (ℕ ⊕ ℕ)) :
    ¬ d.toDomain.SeqBody c bs := by
  rintro ⟨m, hm, hmc, -⟩
  rw [DomDesc.toDomain_methods] at hm
  obtain ⟨e, he, rfl⟩ := hm
  exact hc (List.mem_map.2 ⟨e, he, hmc⟩)

theorem rel_dead {c : ℕ} (hc : c ∉ heads d) (s u : Finset ℕ) : ¬ rel d (Sum.inr c) s u := by
  intro h
  cases h with
  | comp hm _ _ => exact not_seqBody_of_nmem hc _ hm

/-- **The transition only depends on the class of the letter.** -/
theorem step_clsOf (S : Finset (Finset ℕ)) (x : ℕ ⊕ ℕ) :
    step d S (clsOf d x) = step d S x := by
  rcases x with a | c
  · simp only [clsOf]
    split_ifs with ha
    · rfl
    · ext u
      simp only [step, Finset.mem_filter, rel_noop (freshA_nmem d), rel_noop ha]
  · simp only [clsOf]
    split_ifs with hc
    · rfl
    · ext u
      simp only [step, Finset.mem_filter]
      constructor
      · rintro ⟨-, s, -, h⟩; exact absurd h (rel_dead (freshC_nmem d) _ _)
      · rintro ⟨-, s, -, h⟩; exact absurd h (rel_dead hc _ _)

/-- The run only depends on the classes of the letters. -/
theorem run_map_clsOf (S : Finset (Finset ℕ)) (xs : List (ℕ ⊕ ℕ)) :
    run d S (xs.map (clsOf d)) = run d S xs := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    show run d (step d S (clsOf d x)) (xs.map (clsOf d)) = run d (step d S x) xs
    rw [step_clsOf, ih]

end TOPlan

end Syn

end HTN
