import HtnComplexity.Computable.StripsDecide
/-!
# Plan existence for described `STRIPS` problems, as reachability in a transition system

The target side of the Karp–Lipton cells (`TABLE3-PLAN.md` §1, ingredient 3) needs plan
existence for the target class as a computation with **bounded configurations**.  The classical
form of plan existence, "some sequence of actions is executable and reaches the goal", is not of
that shape: the sequence is unbounded.  Its reachability form is:

    the goal holds in some state reachable, one action at a time, from the initial state.

This file writes that form down for the description language, and proves it equivalent to the
solvability of a described `STRIPS` problem.

* `HTN.Space.Row` — an action of a table: a precondition, an add and a delete list;
* `HTN.Space.StepTbl tbl s s'` — the transition relation: some row of the table is applicable in
  the state `s`, and `s'` lists exactly the facts the row leaves behind;
* `HTN.Space.SolvableTbl tbl s₀ g` — the goal holds somewhere reachable from `s₀`;
* `HTN.Space.solvableTbl_iff_exists_plan` — the relation between the two forms, at the level of
  the executor `HTN.Syn.runL` of `HtnComplexity/Computable/StripsDecide.lean`;
* `HTN.Space.solvable_isStrips_iff_solvableTbl` — **plan existence for a described `STRIPS`
  problem is reachability**: the problem is solvable exactly when the domain has a method with
  an empty body and the goal list is reached from the initial list by the actions the hierarchy
  offers.

Note that a state is a *list* here, and the transition relation is stated up to the set of facts
a list carries, not up to the list itself: the machine of `ComplexityTheory/Space/Model.lean`
may represent a state by any list of the right facts, which is what makes the transition
relation a simple test on two strings.
-/

namespace HTN

namespace Space

open Syn

/-- **A row of an action table**: the precondition, add and delete list of an action. -/
abbrev Row : Type := List ℕ × List ℕ × List ℕ

/-- **The transition relation of an action table**: some row is applicable in `s`, and `s'`
carries exactly the facts the row leaves behind. -/
def StepTbl (tbl : List Row) (s s' : List ℕ) : Prop :=
  ∃ row ∈ tbl, (∀ f ∈ row.1, f ∈ s) ∧ ∀ f, (f ∈ s' ↔ f ∈ row.2.1 ∨ (f ∈ s ∧ f ∉ row.2.2))

/-- Reachability in an action table. -/
def ReachTbl (tbl : List Row) : List ℕ → List ℕ → Prop := Relation.ReflTransGen (StepTbl tbl)

/-- **Solvability of an action table**: the goal list is contained in some reachable state. -/
def SolvableTbl (tbl : List Row) (s₀ g : List ℕ) : Prop :=
  ∃ s, ReachTbl tbl s₀ s ∧ ∀ f ∈ g, f ∈ s

/-! ### The executor, on lists -/

theorem mem_stepL_iff {d : DomDesc} {l : List ℕ} {a f : ℕ} :
    f ∈ stepL d l a ↔ f ∈ (actOf d a).2.1 ∨ (f ∈ l ∧ f ∉ (actOf d a).2.2) := by
  simp only [stepL, List.mem_append, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    memB_eq_false_iff]
  tauto

theorem runL_append (d : DomDesc) (l as bs : List ℕ) :
    runL d l (as ++ bs) = runL d (runL d l as) bs := by
  simp [runL, List.foldl_append]

theorem appB_append (d : DomDesc) (l as bs : List ℕ) :
    appB d l (as ++ bs) = (appB d l as && appB d (runL d l as) bs) := by
  induction as generalizing l with
  | nil => simp
  | cons a as ih => simp [ih, Bool.and_assoc]

theorem applB_iff_mem {d : DomDesc} {l : List ℕ} {a : ℕ} :
    applB d l a = true ↔ ∀ f ∈ (actOf d a).1, f ∈ l := by
  rw [applB_iff]
  simp only [ActionModel.Applicable, DomDesc.toDomain_prec, prec_eq_actOf]
  exact Iff.rfl

theorem applB_congr {d : DomDesc} {l l' : List ℕ} (h : ∀ f, f ∈ l ↔ f ∈ l') (a : ℕ) :
    applB d l a = applB d l' a := by
  rcases hb : applB d l a with _ | _
  · rcases hb' : applB d l' a with _ | _
    · rfl
    · exact absurd (applB_iff_mem.2 fun f hf => (h f).2 (applB_iff_mem.1 hb' f hf)) (by simp [hb])
  · exact (applB_iff_mem.2 fun f hf => (h f).1 (applB_iff_mem.1 hb f hf)).symm

/-! ### The two forms of plan existence -/

/-- A plan produces a run of the transition system. -/
theorem reachTbl_runL {d : DomDesc} {acts : List ℕ} :
    ∀ (as : List ℕ) (s₀ : List ℕ), (∀ a ∈ as, a ∈ acts) → appB d s₀ as = true →
      ReachTbl (acts.map (actOf d)) s₀ (runL d s₀ as) := by
  intro as
  induction as with
  | nil => intro s₀ _ _; exact Relation.ReflTransGen.refl
  | cons a as ih =>
    intro s₀ hmem happ
    rw [appB_cons, Bool.and_eq_true] at happ
    have hstep : StepTbl (acts.map (actOf d)) s₀ (stepL d s₀ a) :=
      ⟨actOf d a, List.mem_map_of_mem (hmem a (by simp)), applB_iff_mem.1 happ.1,
        fun f => mem_stepL_iff⟩
    exact Relation.ReflTransGen.head hstep
      (ih _ (fun b hb => hmem b (List.mem_cons_of_mem _ hb)) happ.2)

/-- A run of the transition system comes from a plan. -/
theorem exists_plan_of_reachTbl {d : DomDesc} {acts : List ℕ} {s₀ s : List ℕ}
    (h : ReachTbl (acts.map (actOf d)) s₀ s) :
    ∃ as : List ℕ, (∀ a ∈ as, a ∈ acts) ∧ appB d s₀ as = true ∧
      ∀ f, f ∈ runL d s₀ as ↔ f ∈ s := by
  induction h with
  | refl => exact ⟨[], by simp, by simp, fun f => Iff.rfl⟩
  | @tail smid s' _ hstep ih =>
    obtain ⟨as, hmem, happ, heq⟩ := ih
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hrow
    refine ⟨as ++ [a], ?_, ?_, ?_⟩
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hmem b hb
      · rw [List.mem_singleton.1 hb]; exact ha
    · rw [appB_append, happ, Bool.true_and, appB_cons, appB_nil, Bool.and_true]
      exact applB_iff_mem.2 fun f hf => (heq f).2 (hprec f hf)
    · intro f
      rw [runL_append, runL_cons, runL_nil, mem_stepL_iff, hpost f]
      exact or_congr Iff.rfl (and_congr_left fun _ => heq f)

/-- **The two forms of plan existence agree.** -/
theorem solvableTbl_iff_exists_plan {d : DomDesc} {acts : List ℕ} {s₀ g : List ℕ} :
    SolvableTbl (acts.map (actOf d)) s₀ g ↔
      ∃ as : List ℕ, (∀ a ∈ as, a ∈ acts) ∧ appB d s₀ as = true ∧
        ∀ f ∈ g, f ∈ runL d s₀ as := by
  constructor
  · rintro ⟨s, hreach, hgoal⟩
    obtain ⟨as, hmem, happ, heq⟩ := exists_plan_of_reachTbl hreach
    exact ⟨as, hmem, happ, fun f hf => (heq f).2 (hgoal f hf)⟩
  · rintro ⟨as, hmem, happ, hgoal⟩
    exact ⟨runL d s₀ as, reachTbl_runL as s₀ hmem happ, hgoal⟩

/-- **Plan existence for a described `STRIPS` problem is reachability in its action table.** -/
theorem solvable_isStrips_iff_solvableTbl {d : DomDesc} {q : InstDesc} (hd : d.IsStrips)
    (hq : q.IsStrips) :
    Solvable d q ↔
      d.HasEmptyMethod ∧ SolvableTbl (d.stepActs.map (actOf d)) q.initList q.goalList := by
  rw [solvable_isStrips_iff hd hq]
  refine and_congr_right fun _ => ?_
  rw [solvableTbl_iff_exists_plan]
  refine exists_congr fun as => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨happ, hgoal⟩
    refine ⟨appB_iff.2 happ, fun f hf => ?_⟩
    have : f ∈ d.toDomain.transitionSeq as {f | f ∈ q.initList} := hgoal hf
    rwa [← mem_runL_iff] at this
  · rintro ⟨happ, hgoal⟩
    refine ⟨appB_iff.1 happ, fun f hf => ?_⟩
    rw [← mem_runL_iff]
    exact hgoal f hf

/-! ### The space bound: runs may be taken through small states

The configurations of a machine must be bounded, and a state of the transition system is bounded
as soon as it is duplicate-free and made of facts that occur in the initial state or in an add
list of the table — and every run may be replaced by one through such states. -/

/-- The facts an action table can produce. -/
def addFacts (tbl : List Row) : List ℕ := tbl.flatMap fun r => r.2.1

/-- **The canonical successor** of a state under a row: the facts the row leaves behind, listed
without repetition. -/
def canonStep (row : Row) (s : List ℕ) : List ℕ :=
  (row.2.1 ++ s.filter fun f => decide (f ∉ row.2.2)).dedup

@[simp] theorem mem_canonStep {row : Row} {s : List ℕ} {f : ℕ} :
    f ∈ canonStep row s ↔ f ∈ row.2.1 ∨ (f ∈ s ∧ f ∉ row.2.2) := by
  simp [canonStep, List.mem_filter]

theorem nodup_canonStep (row : Row) (s : List ℕ) : (canonStep row s).Nodup :=
  List.nodup_dedup _

/-- **A run may be restarted from any state carrying the same facts.** -/
theorem exists_run_of_congr {tbl : List Row} {u s : List ℕ} (h : ReachTbl tbl u s) {u' : List ℕ}
    (hu : ∀ f, f ∈ u' ↔ f ∈ u) : ∃ t, ReachTbl tbl u' t ∧ ∀ f, f ∈ t ↔ f ∈ s := by
  induction h with
  | refl => exact ⟨u', Relation.ReflTransGen.refl, hu⟩
  | @tail smid s' _ hstep ih =>
    obtain ⟨t, hreach, hmem⟩ := ih
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    refine ⟨canonStep row t, hreach.tail ⟨row, hrow, fun f hf => (hmem f).2 (hprec f hf),
      fun f => by rw [mem_canonStep, hmem f]⟩, fun f => ?_⟩
    rw [mem_canonStep, hpost f, hmem f]

/-- **Every run may be replaced by a run through duplicate-free states made of facts of the
initial state and of the add lists of the table**, ending in a state carrying the same facts. -/
theorem exists_canon_run {tbl : List Row} {u s : List ℕ} (h : ReachTbl tbl u s) {u' : List ℕ}
    (hu : ∀ f, f ∈ u' ↔ f ∈ u) (hnd : u'.Nodup) :
    ∃ t, ReachTbl tbl u' t ∧ (∀ f, f ∈ t ↔ f ∈ s) ∧ t.Nodup ∧
      ∀ f ∈ t, f ∈ u' ∨ f ∈ addFacts tbl := by
  induction h with
  | refl => exact ⟨u', Relation.ReflTransGen.refl, hu, hnd, fun f hf => Or.inl hf⟩
  | @tail smid s' _ hstep ih =>
    obtain ⟨t, hreach, hmem, hnodup, hsub⟩ := ih
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    refine ⟨canonStep row t, hreach.tail ⟨row, hrow, fun f hf => (hmem f).2 (hprec f hf),
      fun f => by rw [mem_canonStep, hmem f]⟩, fun f => ?_, nodup_canonStep row t, fun f hf => ?_⟩
    · rw [mem_canonStep, hpost f, hmem f]
    · rcases mem_canonStep.1 hf with hf | ⟨hf, -⟩
      · exact Or.inr (List.mem_flatMap.2 ⟨row, hrow, hf⟩)
      · exact hsub f hf

/-- **Solvability of an action table is reachability through small states.** -/
theorem solvableTbl_iff_small {tbl : List Row} {s₀ g : List ℕ} :
    SolvableTbl tbl s₀ g ↔ ∃ s, ReachTbl tbl s₀.dedup s ∧ s.Nodup ∧
      (∀ f ∈ s, f ∈ s₀ ++ addFacts tbl) ∧ ∀ f ∈ g, f ∈ s := by
  constructor
  · rintro ⟨s, hreach, hgoal⟩
    obtain ⟨t, hreach', hmem, hnodup, hsub⟩ :=
      exists_canon_run hreach (u' := s₀.dedup) (fun f => by simp) (List.nodup_dedup _)
    refine ⟨t, hreach', hnodup, fun f hf => ?_, fun f hf => (hmem f).2 (hgoal f hf)⟩
    rcases hsub f hf with hf' | hf'
    · exact List.mem_append_left _ (List.mem_dedup.1 hf')
    · exact List.mem_append_right _ hf'
  · rintro ⟨s, hreach, -, -, hgoal⟩
    obtain ⟨t, hreach', hmem⟩ := exists_run_of_congr hreach (u' := s₀) (fun f => by simp)
    exact ⟨t, hreach', fun f hf => (hmem f).2 (hgoal f hf)⟩

/-- A duplicate-free state made of facts of a list is no longer than that list. -/
theorem length_le_of_nodup_subset {s L : List ℕ} (hnd : s.Nodup) (hsub : ∀ f ∈ s, f ∈ L) :
    s.length ≤ L.length :=
  (hnd.subperm hsub).length_le

end Space

end HTN
