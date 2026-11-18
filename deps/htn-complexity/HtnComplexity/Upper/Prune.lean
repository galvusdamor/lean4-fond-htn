import HtnPlanning.Core.MethodRestrict
import HtnComplexity.Computable.TrDecideCell
import HtnComplexity.Computable.AcDecideCell
import HtnComplexity.Upper.Records
/-!
# Pruning a described domain to the methods an instance can reach

The decision procedure for tail-recursive descriptions (`HTN.Syn.trSolvableB`) is correct for
domain descriptions that are tail-recursive *as a whole* (`HTN.Syn.DomDesc.IsTailRec`), whereas
the semantic class `HTN-TR` only constrains the methods that are reachable from the initial task
network.  A decision procedure that reads a domain and an instance separately therefore first
throws away the methods whose compound task name cannot be reached from a compound task of the
initial task network:

* `HTN.Upper.pruneD d q` — the domain description `d` restricted to these methods;
* `HTN.Upper.solvable_pruneD` — this does not change plan existence;
* `HTN.Upper.primrec_pruneD` — it is primitive recursive.

Reachability is the reflexive-transitive closure of the dependency graph of the description
(`HTN.Syn.compEdges`), computed by `HTN.Syn.reachB`.
-/

namespace HTN

namespace Upper

open Syn

/-- Whether a compound name `c` reaches the name `n` in the dependency graph of `d` (reflexively). -/
def reachesB (d : DomDesc) (c n : ℕ) : Bool := decide (c = n) || reachB (compEdges d) c n

theorem reachesB_iff {d : DomDesc} {c n : ℕ} : reachesB d c n = true ↔ WReach d c n := by
  simp only [reachesB, Bool.or_eq_true, decide_eq_true_eq, WReach]
  exact or_congr Iff.rfl reachB_iff

/-- Whether a method description is kept: its compound name is reachable from a compound task of
the initial task network. -/
def keepB (d : DomDesc) (q : InstDesc) (e : MethodDesc) : Bool :=
  decide (0 < (q.tnI.compoundNames.filter fun c => reachesB d c e.1).length)

theorem keepB_iff {d : DomDesc} {q : InstDesc} {e : MethodDesc} :
    keepB d q e = true ↔ ∃ c ∈ q.tnI.compoundNames, WReach d c e.1 := by
  simp only [keepB, decide_eq_true_eq, List.length_pos_iff_exists_mem, List.mem_filter,
    reachesB_iff]

/-- **The domain description restricted to the methods the instance can reach.** -/
def pruneD (d : DomDesc) (q : InstDesc) : DomDesc := (d.actions, d.methods.filter (keepB d q))

theorem mem_pruneD_methods {d : DomDesc} {q : InstDesc} {e : MethodDesc} :
    e ∈ (pruneD d q).methods ↔ e ∈ d.methods ∧ ∃ c ∈ q.tnI.compoundNames, WReach d c e.1 := by
  show e ∈ d.methods.filter (keepB d q) ↔ _
  rw [List.mem_filter, keepB_iff]

theorem WReach.tail_edge {d : DomDesc} {a b c : ℕ} (h : WReach d a b)
    (hbc : (b, c) ∈ compEdges d) : WReach d a c := by
  rcases h with rfl | h
  · exact Or.inr (Relation.TransGen.single hbc)
  · exact Or.inr (h.tail hbc)

/-- Every reachable compound task name of a described problem is reachable in the dependency
graph from a compound task of the initial task network. -/
theorem wReach_of_reachableName {d : DomDesc} {q : InstDesc} {c : ℕ}
    (h : (problem d q).ReachableName c) : ∃ c0 ∈ q.tnI.compoundNames, WReach d c0 c := by
  induction h with
  | tnI ht hc =>
    exact ⟨_, TnDesc.mem_compoundNames.2 ⟨_, List.mem_toFinset.1 ht, hc⟩, WReach.refl d _⟩
  | method hm _ ht hc ih =>
    obtain ⟨c0, hc0, hw⟩ := ih
    obtain ⟨e, he, rfl⟩ := hm
    exact ⟨c0, hc0, WReach.tail_edge hw
      (mem_compEdges.2 ⟨e, he, rfl, _, List.mem_toFinset.1 ht, hc⟩)⟩

/-- **Pruning does not change plan existence.** -/
theorem solvable_pruneD {d : DomDesc} {q : InstDesc} :
    Solvable (pruneD d q) q ↔ Solvable d q := by
  show ((problem d q).withMethods {m | ∃ e ∈ (pruneD d q).methods, e.toMethod = m}).Solvable ↔
    (problem d q).Solvable
  refine Problem.solvable_withMethods_iff ?_ ?_
  · rintro m ⟨e, he, rfl⟩
    exact ⟨e, (mem_pruneD_methods.1 he).1, rfl⟩
  · rintro m ⟨⟨e, he, rfl⟩, hr⟩
    exact ⟨e, mem_pruneD_methods.2 ⟨he, wReach_of_reachableName hr⟩, rfl⟩

/-! ### Pruning is primitive recursive -/

theorem primrec_keepB :
    Primrec₂ fun (w : DomDesc × InstDesc) (e : MethodDesc) => keepB w.1 w.2 e := by
  have hl : Primrec fun v : (DomDesc × InstDesc) × MethodDesc => v.1.2.tnI.compoundNames :=
    primrec_compoundNames.comp (primrec_tnI.comp (Primrec.snd.comp Primrec.fst))
  have hp : Primrec₂ fun (v : (DomDesc × InstDesc) × MethodDesc) (c : ℕ) =>
      reachesB v.1.1 c v.2.1 := by
    refine Primrec₂.mk ?_
    have hn : Primrec fun u : ((DomDesc × InstDesc) × MethodDesc) × ℕ => u.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hd : Primrec fun u : ((DomDesc × InstDesc) × MethodDesc) × ℕ => u.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have h1 : Primrec fun u : ((DomDesc × InstDesc) × MethodDesc) × ℕ => decide (u.2 = u.1.2.1) :=
      (PrimrecRel.comp Primrec.eq Primrec.snd hn).decide
    have h2 : Primrec fun u : ((DomDesc × InstDesc) × MethodDesc) × ℕ =>
        reachB (compEdges u.1.1.1) u.2 u.1.2.1 :=
      primrec_reachB.comp (Primrec.pair (primrec_compEdges.comp hd) Primrec.snd) hn
    exact (Primrec.or.comp h1 h2).of_eq fun u => rfl
  have hf := primrec_filter_bool hl hp
  refine Primrec₂.mk ?_
  exact ((PrimrecRel.comp Primrec.nat_lt (Primrec.const 0)
    (Primrec.list_length.comp hf)).decide).of_eq fun v => rfl

theorem primrec_pruneD : Primrec₂ pruneD :=
  Primrec₂.mk (Primrec.pair (primrec_actions.comp Primrec.fst)
    (primrec_filter_bool (primrec_methods.comp Primrec.fst) primrec_keepB))

end Upper

end HTN
