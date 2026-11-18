import HtnComplexity.Computable.PoRank
/-!
# Plan existence is decidable for acyclic domain descriptions

This file assembles the decision procedure:

* `HTN.Syn.bfs d c₀ n` — the configurations the search of `Computable/PoSearch.lean` reaches
  from `c₀` in at most `n` rounds;
* `HTN.Syn.acSolvableB d q` — the decision: run `HTN.Syn.phi d` rounds from the initial
  configuration and test every configuration reached for the goal;
* `HTN.Syn.acSolvableB_iff` — **it is correct for every acyclic domain description**.

The bound is the measure of `Computable/PoRank.lean`: a step strictly decreases it
(`HTN.Syn.phi_lt_of_pStep`), so a configuration reachable at all is reachable in at most
`phi d (initConfig q).2` steps.
-/

namespace HTN

namespace Syn

/-- The configurations reachable in at most `n` rounds of the search. -/
def bfs (d : DomDesc) (c₀ : PConfig) : ℕ → List PConfig
  | 0 => [c₀]
  | n + 1 => bfs d c₀ n ++ (bfs d c₀ n).flatMap (succsOf d)

theorem mem_bfs_start (d : DomDesc) (c₀ : PConfig) : ∀ n, c₀ ∈ bfs d c₀ n := by
  intro n
  induction n with
  | zero => simp [bfs]
  | succ n ih => exact List.mem_append.2 (Or.inl ih)

theorem pReach_of_mem_bfs {d : DomDesc} {c₀ c : PConfig} :
    ∀ n, c ∈ bfs d c₀ n → PReach d c₀ c := by
  intro n
  induction n generalizing c with
  | zero =>
    intro hc
    rw [show bfs d c₀ 0 = [c₀] from rfl, List.mem_singleton] at hc
    subst hc
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro hc
    rcases List.mem_append.1 hc with h | h
    · exact ih h
    · obtain ⟨b, hb, hbc⟩ := List.mem_flatMap.1 h
      exact (ih hb).tail hbc

theorem phi_le_of_pReach {d : DomDesc} (hd : d.IsAcyclic) {c₀ c : PConfig} (hOk : PNet.Ok c₀.2)
    (h : PReach d c₀ c) : phi d c.2 ≤ phi d c₀.2 := by
  induction h with
  | refl => exact le_rfl
  | @tail b c' hr hstep ih =>
    have hOkb : PNet.Ok b.2 := ok_of_pReach hOk hr
    exact le_trans (le_of_lt (phi_lt_of_pStep hd hOkb hstep)) ih

theorem mem_bfs_of_pReach {d : DomDesc} (hd : d.IsAcyclic) {c₀ c : PConfig} (hOk : PNet.Ok c₀.2)
    (h : PReach d c₀ c) : ∀ n, phi d c₀.2 ≤ n + phi d c.2 → c ∈ bfs d c₀ n := by
  induction h with
  | refl => exact fun n _ => mem_bfs_start d c₀ n
  | @tail b c' hr hstep ih =>
    intro n hn
    have hOkb : PNet.Ok b.2 := ok_of_pReach hOk hr
    have hlt : phi d c'.2 < phi d b.2 := phi_lt_of_pStep hd hOkb hstep
    have hble : phi d b.2 ≤ phi d c₀.2 := phi_le_of_pReach hd hOk hr
    match n with
    | 0 => exact absurd hn (by omega)
    | m + 1 =>
      have hb : b ∈ bfs d c₀ m := ih m (by omega)
      exact List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨b, hb, hstep⟩))

/-- **The decision procedure for acyclic domain descriptions.** -/
def acSolvableB (d : DomDesc) (q : InstDesc) : Bool :=
  (bfs d (initConfig q) (phi d (initConfig q).2)).any (isGoalB q)

/-- **The decision procedure is correct.** -/
theorem acSolvableB_iff {d : DomDesc} {q : InstDesc} (hd : d.IsAcyclic) :
    acSolvableB d q = true ↔ Solvable d q := by
  constructor
  · intro h
    obtain ⟨c, hc, hg⟩ := List.any_eq_true.1 h
    exact solvable_of_pReach (pReach_of_mem_bfs _ hc) hg
  · intro h
    obtain ⟨c, hr, hg⟩ := exists_pReach_of_solvable h
    refine List.any_eq_true.2 ⟨c, ?_, hg⟩
    exact mem_bfs_of_pReach hd (ok_initConfig q) hr _ (by omega)

end Syn

end HTN
