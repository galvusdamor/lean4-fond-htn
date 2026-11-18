import HtnComplexity.Article.NoHTNNP
import HtnComplexity.Computable.AddRoot
import HtnComplexity.Article.Undecidability
/-!
# A single initial compound task (Prop. 2.1.1)

Prop. 2.1.1: every problem `(D, s_I, tn_I, g)` can be written as `(D', s_I, c_I, g)` with a single
initial compound task `c_I` — a fresh name with the single method `c_I → tn_I` — in polynomial
time, with the same solutions.

* `HTN.Article.rootDesc p` — the rooted description (`c_I` is one more than every compound name
  of `p`);
* **`HTN.Article.prop_2_1_1`** — it is well formed iff `p` is (one direction suffices here: it is
  well formed if `p` is), its initial task network is the single compound task `c_I`, it has a
  solution iff `p` has one, and it is computed in polynomial time.

On the level of solution *sets* the article's claim `Sol(P) = Sol(P')` holds only up to the
identifiers of the tasks: the decomposition of `c_I` introduces a *fresh* copy of `tn_I`.  What is
formalised is the plan-existence statement, which is what the complexity results use.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime

/-- The compound names of a description: method heads and compound labels. -/
def ProbDesc.cnames (p : ProbDesc) : List ℕ :=
  p.methods.map Prod.fst ++ p.methods.flatMap (fun m => m.2.lbl.map fun q => q.2.2) ++
    p.tnI.lbl.map fun q => q.2.2

/-- A fresh compound name. -/
def ProbDesc.root (p : ProbDesc) : ℕ := p.cnames.foldr max 0 + 1

/-- **The rooted description**: the method `c_I → tn_I` added, `c_I` the initial task network. -/
def rootDesc (p : ProbDesc) : ProbDesc :=
  ((p.actions, p.methods ++ [(p.root, p.tnI)]), (p.init, singleTn p.root, p.goalPos, p.goalNeg))

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem lt_root {p : ProbDesc} {c : ℕ} (h : c ∈ p.cnames) : c < p.root :=
  Nat.lt_succ_of_le (le_foldr_max h)

theorem mem_compoundNames {t : TnDesc} {c : ℕ} (h : c ∈ t.compoundNames) :
    c ∈ t.lbl.map fun q => q.2.2 := by
  unfold TnDesc.compoundNames at h
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 h
  exact List.mem_map.2 ⟨_, CFGEnc.mem_labelList_true hi, rfl⟩

theorem toSynDom_rootDesc (p : ProbDesc) :
    toSynDom (rootDesc p) = addRootDom p.root p.tnI (toSynDom p) := rfl

theorem facts_rootDesc (p : ProbDesc) : (rootDesc p).facts = p.facts := rfl

theorem toSynInst_rootDesc (p : ProbDesc) :
    toSynInst (rootDesc p) = addRootInst p.root (toSynInst p) := rfl

/-- **Rooting preserves plan existence.** -/
theorem solvable_rootDesc_iff (p : ProbDesc) :
    (rootDesc p).toProblem.Solvable ↔ p.toProblem.Solvable := by
  rw [solvable_toSyn_iff, solvable_toSyn_iff, toSynDom_rootDesc, toSynInst_rootDesc,
    solvable_addRoot_iff]
  · rfl
  · intro e he hr
    have : e.1 ∈ p.cnames := List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨e, he, rfl⟩))
    exact absurd (lt_root this) (by omega)
  · intro e he hr
    have : p.root ∈ p.cnames := List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨e, he, mem_compoundNames hr⟩))
    exact absurd (lt_root this) (lt_irrefl _)
  · intro hr
    have : p.root ∈ p.cnames := List.mem_append_right _ (mem_compoundNames hr)
    exact absurd (lt_root this) (lt_irrefl _)

theorem valid_rootDesc {p : ProbDesc} (hp : p.Valid) : (rootDesc p).Valid := by
  refine ⟨hp.names_nodup, ?_, ?_⟩
  · exact CFGEnc.tnValid_singleTn _
  · intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact hp.methods m hm
    · simp only [List.mem_singleton] at hm; subst hm; exact hp.tnI

theorem pt_rootDesc : PT rootDesc := by
  have hcn : PT ProbDesc.cnames := by
    unfold ProbDesc.cnames ProbDesc.methods ProbDesc.tnI
    have hm : PT fun q : ProbDesc × MethodDesc => q.2.2.lbl.map fun (r : ℕ × Bool × ℕ) => r.2.2 :=
      PT.map (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))) (PT.snd.comp (PT.snd.comp PT.snd))
    exact PT.append (PT.append (PT.map (PT.snd.comp PT.fst) (PT.fst.comp PT.snd))
      (PT.flatMap (g := fun (_ : ProbDesc) (m : MethodDesc) => m.2.lbl.map fun (r : ℕ × Bool × ℕ) => r.2.2)
        (PT.snd.comp PT.fst) hm))
      (PT.map (PT.snd.comp (PT.snd.comp (PT.fst.comp (PT.snd.comp PT.snd))))
        (PT.snd.comp (PT.snd.comp PT.snd)))
  have hr : PT ProbDesc.root := by
    obtain ⟨c, d, hcd⟩ := hcn.pb
    unfold ProbDesc.root
    refine PT.succ (PT.foldr (l := ProbDesc.cnames) (init := fun _ => (0 : ℕ))
      (g := fun _ a b => max a b) hcn (PT.const 0) ?_ (c := c) (d := d) ?_)
    · exact (PT.ite (PT.le (PT.fst.comp PT.snd) (PT.snd.comp PT.snd)) (PT.snd.comp PT.snd)
        (PT.fst.comp PT.snd)).of_eq fun q => (max_def _ _).symm
    · intro a s b hb
      have h1 : sz b ≤ sz a.cnames := sz_le_of_mem hb
      have h2 := hcd a
      show sz (max b s) ≤ _
      rcases le_total b s with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; omega
  have hp := (PT.id : PT fun p : ProbDesc => p)
  have hact : PT fun p : ProbDesc => p.actions := PT.fst.comp PT.fst
  have hmeth : PT fun p : ProbDesc => p.methods := PT.snd.comp PT.fst
  have htn : PT fun p : ProbDesc => p.tnI := PT.fst.comp (PT.snd.comp PT.snd)
  have hi : PT fun p : ProbDesc => p.init := PT.fst.comp PT.snd
  have hgp : PT fun p : ProbDesc => p.goalPos := PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))
  have hgn : PT fun p : ProbDesc => p.goalNeg := PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))
  unfold rootDesc singleTn
  exact PT.pair (PT.pair hact (PT.append hmeth (PT.single (PT.pair hr htn))))
    (PT.pair hi (PT.pair (PT.pair (PT.const [0]) (PT.pair PT.nil (PT.single (PT.pair (PT.const 0)
      (PT.pair (PT.const true) hr))))) (PT.pair hgp hgn)))

/-- **Proposition 2.1.1.** The rooted description is computed in polynomial time, is well formed
when `p` is, has a single compound task as its initial task network, and has a solution iff `p`
has one. -/
theorem prop_2_1_1 :
    PT rootDesc ∧ (∀ p, p.Valid → (rootDesc p).Valid) ∧
      (∀ p, (rootDesc p).tnI = singleTn p.root) ∧
      (∀ p, (rootDesc p).toProblem.Solvable ↔ p.toProblem.Solvable) :=
  ⟨pt_rootDesc, fun _ => valid_rootDesc, fun _ => rfl, solvable_rootDesc_iff⟩

end Article

end HTN
