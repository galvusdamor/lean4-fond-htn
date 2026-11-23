import FondHtn.FairUndec.RecSound
import FondHtn.FairUndec.Main
/-!
# Recurrence reduces to fair strong cyclic MP plan existence

**`FOND.FU.rec_reduces_fairMP`**: for every two-stack machine `M`, predicate `tk` on control
states and first stack `s₁`, there is a computable (indeed polynomial-time) map `g` with

  `PlanExMPFair FClass.UNRES (g s₂) ↔ Rec tk M ⟨M.start, s₁, s₂⟩`,

i.e. the **recurrence problem** of `M` (is there a run entering a `tk`-state infinitely often?)
many-one reduces to fair strong cyclic method-based plan existence.

By Harel (1986, *Effective transformations on infinite trees*), recurrence of nondeterministic
machines is `Σ¹₁`-complete, already for a fixed machine with varying input; a fixed two-stack
machine simulates it.  Hence fair strong cyclic MP plan existence is `Σ¹₁`-hard, so in
particular not arithmetical.  That part of the argument (Harel's theorem, the analytical
hierarchy) is **not** formalised: Mathlib has no analytical hierarchy.
-/

namespace FOND

namespace FU

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime HTN.Undec AcycHard.Sav TOHard2

/-- **Recurrence reduces to fair strong cyclic MP plan existence.** -/
theorem rec_reduces_fairMP (M : TSM) (tk : ℕ → Bool) (s₁ : List ℕ) :
    ∃ g : List ℕ → List Bool, Computable g ∧
      ∀ s₂, PlanExMPFair FClass.UNRES (g s₂) ↔ Rec tk M ⟨M.start, s₁, s₂⟩ := by
  obtain ⟨F, hF, hFe⟩ := pt_desc_s₂ M s₁ tk
  refine ⟨fun s₂ => enc (desc M s₁ s₂ tk), ?_, fun s₂ => ?_⟩
  · refine ((polyTimeFun_of_uc hF).computable.comp PEnc.primrec_enc.to_comp).of_eq fun s₂ => ?_
    exact hFe s₂
  · rw [HardTR.planExMPFair_enc_iff, ← fair_iff_rec]
    exact ⟨fun h => h.2.2, fun h => ⟨valid _ _ _ _, trivial, h⟩⟩

end FU

end FOND
