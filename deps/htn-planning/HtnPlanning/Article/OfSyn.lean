import HtnPlanning.Article.Desc
import HtnPlanning.Computable.Syntax
/-!
# Descriptions of `HTN.Problem` as descriptions of the article's model

A pair of a domain and an instance description of the rest of the development
(`HTN.Syn.DomDesc`, `HTN.Syn.InstDesc`: no negative preconditions, a positive goal) is read as a
description of the article's model by adding empty negative preconditions and an empty negative
goal (`HTN.Article.ofSyn`).

* `HTN.Article.toProblem_ofSyn` — the described problem is `HTN.Article.Problem.ofPos` of the
  problem `HTN.Syn.problem d q`;
* **`HTN.Article.solvable_ofSyn_iff`** — hence it has an HTN solution in the article's sense iff
  `HTN.Syn.Solvable d q`;
* `HTN.Article.valid_ofSyn` — when it is well formed.
-/

namespace HTN

namespace Article

open Syn

/-- An action description without negative preconditions, in the article's format. -/
def ofSynAct (a : ActionDesc) : ActDesc := (a.1, a.2.1, [], a.2.2.1, a.2.2.2)

/-- **A positive description in the article's format.** -/
def ofSyn (d : DomDesc) (q : InstDesc) : ProbDesc :=
  ((d.actions.map ofSynAct, d.methods), (q.initList, q.tnI, q.goalList, []))

theorem find?_ofSynAct (l : List ActionDesc) (a : ℕ) :
    (l.map ofSynAct).find? (fun x => x.name == a) = (l.lookup a).map fun r => ofSynAct (a, r) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨n, r⟩ := x
    by_cases h : n = a
    · subst h; simp [List.lookup, ofSynAct, ActDesc.name]
    · have h' : (a == n) = false := by simpa using Ne.symm h
      rw [List.map_cons, List.find?_cons_of_neg (by simp [ofSynAct, ActDesc.name, h]), ih]
      simp [List.lookup, h']

theorem δ_ofSyn (d : DomDesc) (q : InstDesc) (a : ℕ) :
    (ofSyn d q).δ a = ⟨d.prec a, ∅, d.add a, d.del a⟩ := by
  unfold ProbDesc.δ ProbDesc.actions ofSyn
  simp only
  rw [find?_ofSynAct]
  cases h : d.actions.lookup a with
  | none =>
    simp only [Option.map_none]
    simp [DomDesc.prec, DomDesc.add, DomDesc.del, h]
  | some r =>
    simp only [Option.map_some]
    simp [ActDesc.toAction, ofSynAct, DomDesc.prec, DomDesc.add, DomDesc.del, h]

/-- **The described problem is the problem of the positive description.** -/
theorem toProblem_ofSyn (d : DomDesc) (q : InstDesc) :
    (ofSyn d q).toProblem = Problem.ofPos (Syn.problem d q) := by
  have hδ : (ofSyn d q).δ = fun a => ⟨d.prec a, ∅, d.add a, d.del a⟩ := funext (δ_ofSyn d q)
  unfold ProbDesc.toProblem Problem.ofPos
  rw [hδ]
  congr 1
  · ext f; simp [ProbDesc.goalNeg, ofSyn]

/-- **Solvability in the article's sense of a positive description.** -/
theorem solvable_ofSyn_iff (d : DomDesc) (q : InstDesc) :
    (ofSyn d q).toProblem.Solvable ↔ Syn.Solvable d q := by
  rw [toProblem_ofSyn]
  exact Problem.solvable_ofPos_iff _ (problem_wf d q)

/-- When a positive description is well formed in the article's sense. -/
theorem valid_ofSyn {d : DomDesc} {q : InstDesc} (h₁ : (d.actions.map Prod.fst).Nodup)
    (h₂ : TnValid (· ∈ d.actions.map Prod.fst) q.tnI)
    (h₃ : ∀ m ∈ d.methods, TnValid (· ∈ d.actions.map Prod.fst) m.2) : (ofSyn d q).Valid := by
  have hnames : (ofSyn d q).actions.map ActDesc.name = d.actions.map Prod.fst := by
    simp [ofSyn, ProbDesc.actions, ofSynAct, ActDesc.name, Function.comp_def]
  refine ⟨by rw [hnames]; exact h₁, ?_, ?_⟩
  · unfold ProbDesc.Declared; rw [hnames]; exact h₂
  · intro m hm; unfold ProbDesc.Declared; rw [hnames]; exact h₃ m hm

end Article

end HTN
