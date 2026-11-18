import HtnPlanning.Article.DualU
import HtnPlanning.Article.OfSyn
import HtnPlanning.Core.Transfer
/-!
# From descriptions of the article's model to descriptions of `HTN.Problem`

`HTN.Article.toSynDom p`, `HTN.Article.toSynInst p` — the dual-rail translation of a problem
description with negative preconditions and goals into a domain and an instance description of
the rest of the development: the fact `f` becomes `2f` ("`f` holds") and `2f + 1` ("`f` does not
hold"), relative to the facts the description mentions (`HTN.Article.ProbDesc.facts`).  Methods,
the initial task network and the action names are unchanged.

**`HTN.Article.solvable_toSyn_iff`** — a description has an HTN solution (in the article's sense)
iff its translation is solvable (`HTN.Syn.Solvable`).  Through this every decision procedure and
every upper bound proved for `HTN.Syn.Solvable` applies to the article's plan-existence problem.
-/

namespace HTN

namespace Article

open Syn

/-- The fact "`f` holds". -/
def posF (f : ℕ) : ℕ := 2 * f

/-- The fact "`f` does not hold". -/
def negF (f : ℕ) : ℕ := 2 * f + 1

/-- The dual-rail facts as numbers. -/
def encF : ℕ ⊕ ℕ → ℕ
  | Sum.inl f => posF f
  | Sum.inr f => negF f

theorem encF_injective : Function.Injective encF := by
  rintro (a | a) (b | b) h <;> simp [encF, posF, negF] at h ⊢ <;> omega

/-- The negative effects that are not also positive effects. -/
def delOnly (a : ActDesc) : List ℕ := a.2.2.2.2.filter fun f => f ∉ a.2.2.2.1

/-- **The translation of an action.** -/
def actToSyn (a : ActDesc) : ActionDesc :=
  (a.1, a.2.1.map posF ++ a.2.2.1.map negF, a.2.2.2.1.map posF ++ (delOnly a).map negF,
    a.2.2.2.1.map negF ++ (delOnly a).map posF)

/-- The facts a description mentions. -/
def ProbDesc.facts (p : ProbDesc) : List ℕ :=
  p.init ++ p.goalPos ++ p.goalNeg ++
    p.actions.flatMap fun a => a.2.1 ++ a.2.2.1 ++ a.2.2.2.1 ++ a.2.2.2.2

/-- **The translated domain.** -/
def toSynDom (p : ProbDesc) : DomDesc := (p.actions.map actToSyn, p.methods)

/-- **The translated instance.** -/
def toSynInst (p : ProbDesc) : InstDesc :=
  (p.init.map posF ++ (p.facts.filter fun f => f ∉ p.init).map negF,
    p.goalPos.map posF ++ p.goalNeg.map negF, p.tnI)

/-! ### The action model of the translation -/

theorem lookup_actToSyn (l : List ActDesc) (a : ℕ) :
    (l.map actToSyn).lookup a = (l.find? fun x => x.name == a).map fun x => (actToSyn x).2 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x.1 = a
    · have h' : (a == x.1) = true := by simp [h]
      simp [List.lookup, actToSyn, ActDesc.name, h, h']
    · have h' : (a == x.1) = false := by simpa using Ne.symm h
      rw [List.map_cons, List.find?_cons_of_neg (by simp [ActDesc.name, h])]
      simp [List.lookup, actToSyn, h', ih]

theorem image_encF (l l' : List ℕ) :
    encF '' (Sum.inl '' {f | f ∈ l} ∪ Sum.inr '' {f | f ∈ l'}) = {y | y ∈ l.map posF ++ l'.map negF} := by
  ext y
  simp only [Set.mem_image, Set.mem_union, Set.mem_setOf_eq, List.mem_append, List.mem_map]
  constructor
  · rintro ⟨x, (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩), rfl⟩
    · exact Or.inl ⟨f, hf, rfl⟩
    · exact Or.inr ⟨f, hf, rfl⟩
  · rintro (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
    · exact ⟨Sum.inl f, Or.inl ⟨f, hf, rfl⟩, rfl⟩
    · exact ⟨Sum.inr f, Or.inr ⟨f, hf, rfl⟩, rfl⟩

theorem setOf_delOnly (a : ActDesc) :
    {f | f ∈ delOnly a} = {f | f ∈ a.2.2.2.2} \ {f | f ∈ a.2.2.2.1} := by
  ext f; simp [delOnly]

/-! ### Correctness -/

variable (p : ProbDesc)

theorem within_toProblem : p.toProblem.Within {f | f ∈ p.facts} := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · show (p.δ a).Within _
    unfold ProbDesc.δ
    cases h : p.actions.find? (fun x => x.name == a) with
    | none => exact ⟨by simp, by simp, by simp, by simp⟩
    | some x =>
      have hx := List.mem_of_find?_eq_some h
      simp only [ActDesc.toAction, Action.Within]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro f hf <;>
        simp only [Set.mem_setOf_eq, ProbDesc.facts, List.mem_append, List.mem_flatMap] at hf ⊢ <;>
        exact Or.inr ⟨x, hx, by simp [hf]⟩
  · intro f hf; simp only [ProbDesc.facts, Set.mem_setOf_eq, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hf))
  · intro f hf; simp only [ProbDesc.facts, Set.mem_setOf_eq, List.mem_append]
    exact Or.inl (Or.inr hf)

theorem wf_toProblem : p.toProblem.WF :=
  ⟨TnDesc.toTaskNetwork_wf _, by rintro m ⟨e, -, rfl⟩; exact TnDesc.toTaskNetwork_wf _⟩

theorem relabel_refl_tn (tn : TaskNetwork ℕ ℕ ℕ) :
    TaskNetwork.relabel id id (Equiv.refl ℕ) tn = tn :=
  TaskNetwork.ext' (by simp [TaskNetwork.relabel_T]) rfl (by funext x; simp [TaskNetwork.relabel])

theorem relabel_refl_methods (M : Set (Method ℕ ℕ ℕ)) :
    Method.relabel id id (Equiv.refl ℕ) '' M = M := by
  have : ∀ m : Method ℕ ℕ ℕ, Method.relabel id id (Equiv.refl ℕ) m = m := by
    intro m
    cases m
    simp only [Method.relabel, relabel_refl_tn]
    rfl
  ext m
  simp [this]

/-- **The translation decides plan existence.** -/
theorem solvable_toSyn_iff : p.toProblem.Solvable ↔ Syn.Solvable (toSynDom p) (toSynInst p) := by
  rw [Problem.solvable_iff_toPosU (within_toProblem p) (wf_toProblem p)]
  symm
  refine HTN.Problem.solvable_relabel_iff (eF := encF) (eA := id) (eC := id) (eI := Equiv.refl ℕ)
    encF_injective Function.injective_id Function.injective_id
    (fun o _ => ?_) (fun o _ => ?_) (fun o _ => ?_) ?_ ?_ (TnDesc.toTaskNetwork_wf _) ?_ ?_
  · show (toSynDom p).prec o = encF '' (p.δ o).dual.pre
    unfold DomDesc.prec toSynDom DomDesc.actions ProbDesc.δ
    simp only
    rw [lookup_actToSyn]
    cases p.actions.find? (fun x => x.name == o) with
    | none => simp [Action.dual]
    | some x =>
      simp only [Option.map_some, Option.elim_some, ActDesc.toAction, Action.dual]
      exact (image_encF _ _).symm
  · show (toSynDom p).add o = encF '' (p.δ o).dual.add
    unfold DomDesc.add toSynDom DomDesc.actions ProbDesc.δ
    simp only
    rw [lookup_actToSyn]
    cases p.actions.find? (fun x => x.name == o) with
    | none => simp [Action.dual]
    | some x =>
      simp only [Option.map_some, Option.elim_some, ActDesc.toAction, Action.dual]
      rw [← setOf_delOnly]
      exact (image_encF _ _).symm
  · show (toSynDom p).del o = encF '' (p.δ o).dual.del
    unfold DomDesc.del toSynDom DomDesc.actions ProbDesc.δ
    simp only
    rw [lookup_actToSyn]
    cases p.actions.find? (fun x => x.name == o) with
    | none => simp [Action.dual]
    | some x =>
      simp only [Option.map_some, Option.elim_some, ActDesc.toAction, Action.dual]
      rw [← setOf_delOnly, Set.union_comm, image_encF]
      ext y
      simp only [actToSyn, Set.mem_setOf_eq, List.mem_append]
      exact or_comm
  · show {y | y ∈ (toSynInst p).initList} = encF '' encStateU {f | f ∈ p.facts} {f | f ∈ p.init}
    have h1 : {f | f ∈ p.init} ∩ {f | f ∈ p.facts} = {f | f ∈ p.init} := by
      ext f; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_iff_left_iff_imp]
      intro hf; simp [ProbDesc.facts, hf]
    have h2 : {f | f ∈ p.facts} \ {f | f ∈ p.init} = {f | f ∈ p.facts.filter fun f => f ∉ p.init} := by
      ext f; simp
    rw [encStateU, h1, h2, image_encF]
    rfl
  · show {y | y ∈ (toSynInst p).goalList} = encF '' (Sum.inl '' {f | f ∈ p.goalPos} ∪ Sum.inr '' {f | f ∈ p.goalNeg})
    rw [image_encF]; rfl
  · exact (relabel_refl_tn _).symm
  · exact (relabel_refl_methods _).symm

end Article

end HTN
