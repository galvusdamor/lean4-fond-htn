import HtnComplexity.Computable.StripsToAc
import ComplexityTheory.Computable.PrimrecPow
/-!
# Plan existence is decidable for described `STRIPS` problems

The cells of the row `HTN` of the compilability table are proved from two hypotheses: plan
existence for `HTN` is undecidable already for one fixed domain description, and plan existence
for the *target* class is decidable (`HTN.Syn.not_compSynInst_of_undecidable_at`).  This file
discharges the second hypothesis for the class `STRIPS`:

`HTN.Syn.decider_STRIPS : HTN.Syn.SynClass.STRIPS.Decider`

— a primitive recursive function that decides solvability of every described `STRIPS` problem.

The decision procedure is the naive one, and everything it needs is already available:

* a described `STRIPS` problem is solvable exactly when its domain description has a method
  with an empty body and some sequence of the actions the hierarchy offers is executable in the
  initial state and reaches the goal (`HTN.Syn.solvable_isStrips_iff`);
* such a sequence can be taken of length less than `2 ^ K`, where `K = |mutFacts d|` bounds the
  number of facts the offered actions can change
  (`HTN.ClassicalProblem.exists_short_solution`, as used in
  `HtnComplexity/Computable/StripsToAc.lean`).

So it suffices to run every sequence of at most `2 ^ K` offered actions.  The two ingredients
added here are

* an executor on **lists** — `HTN.Syn.runL` computes the state a sequence reaches and
  `HTN.Syn.appB` decides whether it is executable — which agrees with the semantics
  (`HTN.Syn.mem_runL_iff`, `HTN.Syn.appB_iff`); and
* `HTN.Syn.plansUpTo acts n`, the list of all sequences of at most `n` actions of `acts`.

Both are written with `List.foldr` / `List.foldl` and a `Nat` recursion, so they are primitive
recursive.
-/

namespace HTN

namespace Syn

/-! ### The described action model, as lists -/

/-- The precondition, add and delete list of an action, as described — the triple of empty
lists for an action the description does not mention.  This is `List.lookup` written as a
`List.foldr`, which is what makes it primitive recursive. -/
def actOf (d : DomDesc) (a : ℕ) : List ℕ × List ℕ × List ℕ :=
  d.actions.foldr (fun x r => if x.1 = a then x.2 else r) ([], [], [])

theorem actOf_eq (d : DomDesc) (a : ℕ) :
    actOf d a = (d.actions.lookup a).elim ([], [], []) id := by
  simp only [actOf, DomDesc.actions]
  induction d.1 with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    by_cases h : k = a
    · subst h
      rw [List.foldr_cons, if_pos rfl, List.lookup_cons]
      simp
    · have hb : (a == k) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun hx => h hx.symm
      rw [List.foldr_cons, if_neg h, ih, List.lookup_cons]
      simp [hb]

@[simp] theorem memB_eq_false_iff {l : List ℕ} {n : ℕ} : memB l n = false ↔ n ∉ l := by
  rw [← memB_iff]
  cases memB l n <;> simp

@[simp] theorem prec_eq_actOf (d : DomDesc) (a : ℕ) : d.prec a = {f | f ∈ (actOf d a).1} := by
  rw [actOf_eq, DomDesc.prec]
  cases d.actions.lookup a <;> rfl

@[simp] theorem add_eq_actOf (d : DomDesc) (a : ℕ) : d.add a = {f | f ∈ (actOf d a).2.1} := by
  rw [actOf_eq, DomDesc.add]
  cases d.actions.lookup a <;> rfl

@[simp] theorem del_eq_actOf (d : DomDesc) (a : ℕ) : d.del a = {f | f ∈ (actOf d a).2.2} := by
  rw [actOf_eq, DomDesc.del]
  cases d.actions.lookup a <;> rfl

/-! ### The executor -/

/-- The state an action reaches, on lists. -/
def stepL (d : DomDesc) (l : List ℕ) (a : ℕ) : List ℕ :=
  l.filter (fun f => !memB (actOf d a).2.2 f) ++ (actOf d a).2.1

/-- The state a sequence of actions reaches, on lists. -/
def runL (d : DomDesc) (l : List ℕ) (as : List ℕ) : List ℕ := as.foldl (stepL d) l

/-- Whether a single action is applicable, on lists. -/
def applB (d : DomDesc) (l : List ℕ) (a : ℕ) : Bool :=
  (actOf d a).1.foldr (fun f b => memB l f && b) true

/-- The executor: the state reached and whether the sequence was executable. -/
def execL (d : DomDesc) (st : List ℕ × Bool) (as : List ℕ) : List ℕ × Bool :=
  as.foldl (fun st a => (stepL d st.1 a, st.2 && applB d st.1 a)) st

/-- Whether a sequence of actions is executable, on lists. -/
def appB (d : DomDesc) (l : List ℕ) (as : List ℕ) : Bool := (execL d (l, true) as).2

@[simp] theorem runL_nil (d : DomDesc) (l : List ℕ) : runL d l [] = l := rfl

@[simp] theorem runL_cons (d : DomDesc) (l : List ℕ) (a : ℕ) (as : List ℕ) :
    runL d l (a :: as) = runL d (stepL d l a) as := rfl

theorem execL_eq (d : DomDesc) (l : List ℕ) (b : Bool) (as : List ℕ) :
    execL d (l, b) as = (runL d l as, b && appB d l as) := by
  induction as generalizing l b with
  | nil => simp [execL, runL, appB]
  | cons a as ih =>
    show execL d (stepL d l a, b && applB d l a) as = _
    rw [ih, runL_cons]
    have h2 : appB d l (a :: as) = (applB d l a && appB d (stepL d l a) as) := by
      show (execL d (stepL d l a, true && applB d l a) as).2 = _
      rw [show (true && applB d l a) = applB d l a by simp, ih]
    rw [h2, Bool.and_assoc]

@[simp] theorem appB_nil (d : DomDesc) (l : List ℕ) : appB d l [] = true := rfl

@[simp] theorem appB_cons (d : DomDesc) (l : List ℕ) (a : ℕ) (as : List ℕ) :
    appB d l (a :: as) = (applB d l a && appB d (stepL d l a) as) := by
  show (execL d (stepL d l a, true && applB d l a) as).2 = _
  rw [show (true && applB d l a) = applB d l a by simp, execL_eq]

/-! ### The executor agrees with the semantics -/

theorem mem_stepL (d : DomDesc) (l : List ℕ) (a : ℕ) :
    {f | f ∈ stepL d l a} = d.toDomain.transition a {f | f ∈ l} := by
  ext f
  simp only [stepL, ActionModel.transition, Set.mem_setOf_eq, List.mem_append, List.mem_filter,
    Set.mem_union, Set.mem_diff, DomDesc.toDomain_add, DomDesc.toDomain_del, add_eq_actOf,
    del_eq_actOf, Bool.not_eq_eq_eq_not, Bool.not_true, memB_eq_false_iff]

theorem mem_runL_iff (d : DomDesc) (l : List ℕ) (as : List ℕ) :
    {f | f ∈ runL d l as} = d.toDomain.transitionSeq as {f | f ∈ l} := by
  induction as generalizing l with
  | nil => rfl
  | cons a as ih => rw [runL_cons, ih, ActionModel.transitionSeq_cons, mem_stepL]

theorem applB_iff {d : DomDesc} {l : List ℕ} {a : ℕ} :
    applB d l a = true ↔ d.toDomain.Applicable a {f | f ∈ l} := by
  simp only [applB, ActionModel.Applicable, DomDesc.toDomain_prec, prec_eq_actOf]
  induction (actOf d a).1 with
  | nil => simp
  | cons f fs ih =>
    rw [show ((f :: fs).foldr (fun f b => memB l f && b) true) =
      (memB l f && fs.foldr (fun f b => memB l f && b) true) from rfl]
    simp only [Bool.and_eq_true, memB_iff, ih]
    constructor
    · rintro ⟨hf, hsub⟩ x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact hsub hx
    · intro hsub
      exact ⟨hsub (by simp), fun x hx => hsub (List.mem_cons_of_mem _ hx)⟩

theorem appB_iff {d : DomDesc} {l : List ℕ} {as : List ℕ} :
    appB d l as = true ↔ d.toDomain.SeqApplicable as {f | f ∈ l} := by
  induction as generalizing l with
  | nil => simp
  | cons a as ih =>
    rw [appB_cons, Bool.and_eq_true, ih, ActionModel.seqApplicable_cons, applB_iff, mem_stepL]

/-! ### All short sequences of actions -/

/-- All sequences of at most `n` actions of `acts`. -/
def plansUpTo (acts : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => plansUpTo acts n ++ acts.flatMap fun a => (plansUpTo acts n).map fun p => a :: p

theorem mem_acts_of_mem_plansUpTo {acts : List ℕ} :
    ∀ (n : ℕ) {as : List ℕ}, as ∈ plansUpTo acts n → ∀ a ∈ as, a ∈ acts := by
  intro n
  induction n with
  | zero =>
    intro as has
    rw [show plansUpTo acts 0 = [[]] from rfl] at has
    simp at has
    simp [has]
  | succ n ih =>
    intro as has
    rcases List.mem_append.1 has with h | h
    · exact ih h
    · simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, p, hp, rfl⟩ := h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact ih hp x hx

theorem mem_plansUpTo {acts : List ℕ} :
    ∀ (n : ℕ) {as : List ℕ}, (∀ a ∈ as, a ∈ acts) → as.length ≤ n → as ∈ plansUpTo acts n := by
  intro n
  induction n with
  | zero =>
    intro as _ hlen
    have : as = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    subst this
    simp [plansUpTo]
  | succ n ih =>
    intro as hacts hlen
    match as with
    | [] =>
      exact List.mem_append.2 (Or.inl (ih (by simp) (by simp)))
    | a :: as' =>
      refine List.mem_append.2 (Or.inr ?_)
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨a, hacts a (by simp), as', ih (fun x hx => hacts x (List.mem_cons_of_mem _ hx))
        (by simpa using Nat.succ_le_succ_iff.1 hlen), rfl⟩

/-! ### The decision procedure -/

/-- Whether the sequence `as` solves the described problem: it is executable in the initial
state and the state it reaches satisfies the goal. -/
def solvesB (d : DomDesc) (q : InstDesc) (as : List ℕ) : Bool :=
  appB d q.initList as && q.goalList.foldr (fun f b => memB (runL d q.initList as) f && b) true

/-- **The decision procedure for described `STRIPS` problems**: the domain must have a method
with an empty body, and one of the sequences of at most `2 ^ |mutFacts d|` offered actions must
solve the problem. -/
def stripsSolvableB (d : DomDesc) (q : InstDesc) : Bool :=
  hasEmptyMethodB d &&
    (plansUpTo d.stepActs (2 ^ (mutFacts d).length)).any (solvesB d q)

theorem goalB_iff {d : DomDesc} {q : InstDesc} {as : List ℕ} :
    (q.goalList.foldr (fun f b => memB (runL d q.initList as) f && b) true) = true ↔
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} := by
  rw [← mem_runL_iff]
  induction q.goalList with
  | nil => simp
  | cons f fs ih =>
    rw [show ((f :: fs).foldr (fun f b => memB (runL d q.initList as) f && b) true) =
      (memB (runL d q.initList as) f && fs.foldr
        (fun f b => memB (runL d q.initList as) f && b) true) from rfl]
    simp only [Bool.and_eq_true, memB_iff, ih]
    constructor
    · rintro ⟨hf, hsub⟩ x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hf
      · exact hsub hx
    · intro hsub
      exact ⟨hsub (by simp), fun x hx => hsub (List.mem_cons_of_mem _ hx)⟩

theorem solvesB_iff {d : DomDesc} {q : InstDesc} {as : List ℕ} :
    solvesB d q as = true ↔ d.toDomain.SeqApplicable as {f | f ∈ q.initList} ∧
      {f | f ∈ q.goalList} ⊆ d.toDomain.transitionSeq as {f | f ∈ q.initList} := by
  rw [solvesB, Bool.and_eq_true, appB_iff, goalB_iff]

/-- **The decision procedure is correct.** -/
theorem stripsSolvableB_iff {d : DomDesc} {q : InstDesc} (hd : d.IsStrips) (hq : q.IsStrips) :
    stripsSolvableB d q = true ↔ Solvable d q := by
  classical
  rw [solvable_isStrips_iff hd hq, stripsSolvableB, Bool.and_eq_true, hasEmptyMethodB_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨as, has, hsol⟩ := List.any_eq_true.1 h
    exact ⟨as, mem_acts_of_mem_plansUpTo _ has, (solvesB_iff.1 hsol).1, (solvesB_iff.1 hsol).2⟩
  · rintro ⟨as, hus, happ, hgoal⟩
    -- a short plan over the offered actions
    have hmut : ∀ a ∈ {a : ℕ | a ∈ d.stepActs},
        (problem d q).toClassicalProblem.add a ⊆ ↑(mutFacts d).toFinset ∧
        (problem d q).toClassicalProblem.del a ⊆ ↑(mutFacts d).toFinset := by
      intro a ha
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · simpa using add_subset_mutFacts ha hf
      · simpa using del_subset_mutFacts ha hf
    obtain ⟨bs, hbus, ⟨hbapp, hbgoal⟩, hblen⟩ :=
      ClassicalProblem.exists_short_solution (P := (problem d q).toClassicalProblem)
        (Acts := {a : ℕ | a ∈ d.stepActs}) (F₀ := (mutFacts d).toFinset) hmut hus ⟨happ, hgoal⟩
    have hcard : ((mutFacts d).toFinset).card ≤ (mutFacts d).length := List.toFinset_card_le _
    have hlen : bs.length ≤ 2 ^ (mutFacts d).length :=
      le_trans hblen.le (Nat.pow_le_pow_right (by omega) hcard)
    exact List.any_eq_true.2 ⟨bs, mem_plansUpTo _ hbus hlen, solvesB_iff.2 ⟨hbapp, hbgoal⟩⟩

/-! ### The decision procedure is primitive recursive -/

open Primrec

theorem primrec_actOf : Primrec₂ actOf := by
  have hh : Primrec₂ (fun (p : DomDesc × ℕ) (z : ActionDesc × (List ℕ × List ℕ × List ℕ)) =>
      if z.1.1 = p.2 then z.1.2 else z.2) := by
    apply Primrec.ite (c := fun w : (DomDesc × ℕ) × (ActionDesc × (List ℕ × List ℕ × List ℕ)) =>
        w.2.1.1 = w.1.2)
    · exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    · exact Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    · exact Primrec.snd.comp Primrec.snd
  exact Primrec₂.mk (Primrec.list_foldr (primrec_actions.comp Primrec.fst)
    (Primrec.const ([], [], [])) hh)

theorem primrec_stepL : Primrec₂ (fun (p : DomDesc × List ℕ) (a : ℕ) => stepL p.1 p.2 a) := by
  have hact : Primrec (fun w : (DomDesc × List ℕ) × ℕ => actOf w.1.1 w.2) :=
    primrec_actOf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hfil : Primrec (fun w : (DomDesc × List ℕ) × ℕ =>
      w.1.2.filter (fun f => !memB (actOf w.1.1 w.2).2.2 f)) := by
    have hh : Primrec₂ (fun (w : (DomDesc × List ℕ) × ℕ) (z : ℕ × List ℕ) =>
        if memB (actOf w.1.1 w.2).2.2 z.1 = true then z.2 else z.1 :: z.2) := by
      apply Primrec.ite (c := fun v : ((DomDesc × List ℕ) × ℕ) × (ℕ × List ℕ) =>
          memB (actOf v.1.1.1 v.1.2).2.2 v.2.1 = true)
      · exact PrimrecRel.comp Primrec.eq
          (primrec_memB.comp
            ((Primrec.snd.comp (Primrec.snd.comp (hact.comp Primrec.fst))))
            (Primrec.fst.comp Primrec.snd))
          (Primrec.const true)
      · exact Primrec.snd.comp Primrec.snd
      · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)
    have h := Primrec.list_foldr (Primrec.snd.comp Primrec.fst) (Primrec.const ([] : List ℕ)) hh
    refine h.of_eq fun w => ?_
    induction w.1.2 with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.foldr_cons, List.filter_cons, ih]
      by_cases hx : memB (actOf w.1.1 w.2).2.2 x = true <;> simp [hx]
  have hres := Primrec.list_append.comp hfil (Primrec.fst.comp (Primrec.snd.comp hact))
  exact Primrec₂.mk (hres.of_eq fun w => rfl)

theorem primrec_applB : Primrec₂ (fun (p : DomDesc × List ℕ) (a : ℕ) => applB p.1 p.2 a) := by
  have hact : Primrec (fun w : (DomDesc × List ℕ) × ℕ => (actOf w.1.1 w.2).1) :=
    Primrec.fst.comp (primrec_actOf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hh : Primrec₂ (fun (w : (DomDesc × List ℕ) × ℕ) (z : ℕ × Bool) =>
      memB w.1.2 z.1 && z.2) :=
    Primrec.and.comp (primrec_memB.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  have hres := Primrec.list_foldr hact (Primrec.const true) hh
  exact Primrec₂.mk (hres.of_eq fun w => rfl)

set_option maxHeartbeats 1000000 in
theorem primrec_execL :
    Primrec₂ (fun (p : DomDesc × (List ℕ × Bool)) (as : List ℕ) => execL p.1 p.2 as) := by
  have hh : Primrec₂ (fun (p : (DomDesc × (List ℕ × Bool)) × List ℕ) (z : (List ℕ × Bool) × ℕ) =>
      (stepL p.1.1 z.1.1 z.2, z.1.2 && applB p.1.1 z.1.1 z.2)) := by
    have hstep : Primrec (fun w : ((DomDesc × (List ℕ × Bool)) × List ℕ) × ((List ℕ × Bool) × ℕ) =>
        stepL w.1.1.1 w.2.1.1 w.2.2) :=
      primrec_stepL.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    have happ : Primrec (fun w : ((DomDesc × (List ℕ × Bool)) × List ℕ) × ((List ℕ × Bool) × ℕ) =>
        applB w.1.1.1 w.2.1.1 w.2.2) :=
      primrec_applB.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    exact Primrec₂.mk (Primrec.pair hstep
      (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) happ))
  have hres := Primrec.list_foldl Primrec.snd (Primrec.snd.comp Primrec.fst) hh
  exact Primrec₂.mk (hres.of_eq fun w => rfl)

theorem primrec_plansUpTo : Primrec₂ plansUpTo := by
  have hstep : Primrec₂ (fun (acts : List ℕ) (z : ℕ × List (List ℕ)) =>
      z.2 ++ acts.flatMap fun a => z.2.map fun p => a :: p) := by
    have hmap : Primrec₂ (fun (w : List ℕ × (ℕ × List (List ℕ))) (a : ℕ) =>
        w.2.2.map fun p => a :: p) := by
      have : Primrec₂ (fun (v : (List ℕ × (ℕ × List (List ℕ))) × ℕ) (p : List ℕ) => v.2 :: p) :=
        Primrec₂.mk (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      exact Primrec₂.mk (Primrec.list_map
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) this)
    exact Primrec₂.mk (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.list_flatMap Primrec.fst hmap))
  have h := Primrec.nat_rec (f := fun _ : List ℕ => [([] : List ℕ)])
    (Primrec.const _) hstep
  refine Primrec₂.mk ((h.comp Primrec.fst Primrec.snd).of_eq fun x => ?_)
  obtain ⟨acts, n⟩ := x
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only at ih ⊢
    rw [plansUpTo, ← ih]

theorem primrec_runL : Primrec₂ (fun (p : DomDesc × List ℕ) (as : List ℕ) => runL p.1 p.2 as) := by
  have h := primrec_execL.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const true)))
    Primrec.snd
  refine Primrec₂.mk ((Primrec.fst.comp h).of_eq fun w => ?_)
  rw [show execL w.1.1 (w.1.2, true) w.2 = (runL w.1.1 w.1.2 w.2, true && appB w.1.1 w.1.2 w.2)
    from execL_eq _ _ _ _]

theorem primrec_appB : Primrec₂ (fun (p : DomDesc × List ℕ) (as : List ℕ) => appB p.1 p.2 as) := by
  have h := primrec_execL.comp
    (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const true)))
    Primrec.snd
  exact Primrec₂.mk (Primrec.snd.comp h)

set_option maxHeartbeats 1000000 in
theorem primrec_solvesB :
    Primrec₂ (fun (p : DomDesc × InstDesc) (as : List ℕ) => solvesB p.1 p.2 as) := by
  have hinit : Primrec (fun w : (DomDesc × InstDesc) × List ℕ => w.1.2.initList) :=
    primrec_initList.comp (Primrec.snd.comp Primrec.fst)
  have happ : Primrec (fun w : (DomDesc × InstDesc) × List ℕ =>
      appB w.1.1 w.1.2.initList w.2) :=
    primrec_appB.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) hinit) Primrec.snd
  have hrun : Primrec (fun w : (DomDesc × InstDesc) × List ℕ =>
      runL w.1.1 w.1.2.initList w.2) :=
    primrec_runL.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) hinit) Primrec.snd
  have hh : Primrec₂ (fun (w : (DomDesc × InstDesc) × List ℕ) (z : ℕ × Bool) =>
      memB (runL w.1.1 w.1.2.initList w.2) z.1 && z.2) :=
    Primrec.and.comp (primrec_memB.comp (hrun.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hgoal : Primrec (fun w : (DomDesc × InstDesc) × List ℕ =>
      w.1.2.goalList.foldr (fun f b => memB (runL w.1.1 w.1.2.initList w.2) f && b) true) :=
    Primrec.list_foldr (primrec_goalList.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.const true) hh
  have hres := Primrec.and.comp happ hgoal
  exact Primrec₂.mk (hres.of_eq fun w => rfl)

theorem primrec_stripsSolvableB : Primrec₂ stripsSolvableB := by
  have hplans : Primrec (fun p : DomDesc × InstDesc =>
      plansUpTo p.1.stepActs (2 ^ (mutFacts p.1).length)) :=
    primrec_plansUpTo.comp (primrec_stepActs.comp Primrec.fst)
      (Ac.primrec_two_pow.comp (Primrec.list_length.comp (primrec_mutFacts.comp Primrec.fst)))
  have hany : Primrec (fun p : DomDesc × InstDesc =>
      (plansUpTo p.1.stepActs (2 ^ (mutFacts p.1).length)).any (solvesB p.1 p.2)) := by
    have hh : Primrec₂ (fun (p : DomDesc × InstDesc) (z : List ℕ × Bool) =>
        solvesB p.1 p.2 z.1 || z.2) :=
      Primrec.or.comp (primrec_solvesB.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)
    have h := Primrec.list_foldr hplans (Primrec.const false) hh
    refine h.of_eq fun p => ?_
    induction (plansUpTo p.1.stepActs (2 ^ (mutFacts p.1).length)) with
    | nil => rfl
    | cons x xs ih => simp [List.any_cons, ← ih]
  exact Primrec₂.mk (Primrec.and.comp
    (primrec_hasEmptyMethodB.comp Primrec.fst) hany)

end Syn

end HTN
