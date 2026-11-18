import HtnComplexity.Computable.RegNorm
/-!
# Configurations that denote the same situation

Two search configurations are **similar** iff they have the same state and isomorphic search
networks.  Similar configurations are interchangeable for the search:

* `HTN.Syn.isGoalB_of_sim` — they pass the goal test together;
* `HTN.Syn.exists_pStep_of_sim` — every step of one can be replayed by the other, up to
  similarity again.

The second statement is a **bisimulation**, and it is a direct consequence of the two halves of
`HtnComplexity/Computable/PoSearch.lean`: a step of the search denotes a step of the
semantics (`HTN.Syn.step_of_pStep`), and a step of the semantics can be replayed by the search
from any configuration denoting an isomorphic task network (`HTN.Syn.exists_pStep_of_step`).

Together with `HTN.Syn.sim_normCfg` — a configuration is similar to its normal form — this is
what lets the decision procedure of `HtnComplexity/Computable/RegDecide.lean` shortcut a
solution path whenever it visits two configurations with the same normal form.
-/

namespace HTN

namespace Syn

/-- **Similar configurations**: the same state and isomorphic search networks. -/
def Sim (c₁ c₂ : PConfig) : Prop :=
  {f | f ∈ c₁.1} = {f | f ∈ c₂.1} ∧ (PNet.toTN c₁.2).Iso (PNet.toTN c₂.2)

@[refl] theorem Sim.refl (c : PConfig) : Sim c c := ⟨rfl, TaskNetwork.Iso.refl _⟩

theorem Sim.symm {c₁ c₂ : PConfig} (h : Sim c₁ c₂) : Sim c₂ c₁ := ⟨h.1.symm, h.2.symm⟩

theorem Sim.trans {c₁ c₂ c₃ : PConfig} (h : Sim c₁ c₂) (h' : Sim c₂ c₃) : Sim c₁ c₃ :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-- **A configuration is similar to its normal form.** -/
theorem sim_normCfg {d : DomDesc} {q : InstDesc} {B : ℕ} {c : PConfig} (h : CfgInv d q B c) :
    Sim (normCfg d q c) c :=
  ⟨state_normCfg h.facts, (toTN_normNet_iso h.ok).symm⟩

/-- Similar configurations pass the goal test together. -/
theorem isGoalB_of_sim {q : InstDesc} {c₁ c₂ : PConfig} (hsim : Sim c₁ c₂)
    (hg : isGoalB q c₂ = true) : isGoalB q c₁ = true := by
  simp only [isGoalB, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at hg ⊢
  obtain ⟨hstate, hiso⟩ := hsim
  refine ⟨?_, ?_⟩
  · have hcard := hiso.card_eq
    have h2 : (PNet.toTN c₂.2).T = ∅ := by
      show c₂.2.ids.toFinset = ∅
      rw [hg.1]
      rfl
    rw [h2] at hcard
    simpa using hcard
  · intro f hf
    have := hg.2 f hf
    rw [memB_iff] at this ⊢
    have : f ∈ {f | f ∈ c₂.1} := this
    rwa [← hstate] at this

/-- **The search is a bisimulation up to similarity**: a step from a configuration can be
replayed from every similar configuration. -/
theorem exists_pStep_of_sim {d : DomDesc} {q : InstDesc} {c₁ c₂ c₂' : PConfig}
    (h₁ : PNet.Ok c₁.2) (h₂ : PNet.Ok c₂.2) (hsim : Sim c₁ c₂) (hstep : PStep d c₂ c₂') :
    ∃ c₁', PStep d c₁ c₁' ∧ Sim c₁' c₂' := by
  obtain ⟨hstate, hiso⟩ := hsim
  obtain ⟨π', hsem⟩ := step_of_pStep (q := q) h₂ hstep []
  obtain ⟨c₁', hstep', hstate', hiso'⟩ :=
    exists_pStep_of_step (d := d) (q := q) (c := c₁)
      (n := ⟨{f | f ∈ c₂.1}, PNet.toTN c₂.2, []⟩) (n' := ⟨{f | f ∈ c₂'.1}, PNet.toTN c₂'.2, π'⟩)
      h₁ hstate hiso (PNet.toTN_wf h₂) hsem
  exact ⟨c₁', hstep', hstate', hiso'⟩

end Syn

end HTN
