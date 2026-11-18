import HtnComplexity.Undec.Bridge
import HtnComplexity.Undec.Run
/-!
# The encoding is correct

Putting the three previous files together:

> `HTN.Undec.solvable_tsm_iff` — the described problem `(tsmDom M, tsmInst M s₁ s₂)` is solvable
> exactly when the two-stack machine `M`, started with the stacks `s₁` and `s₂`, halts.

The plan existence problem of one fixed HTN domain description is therefore at least as hard as
the halting problem of one fixed two-stack machine.
-/

namespace HTN

namespace Undec

open Syn Domain

/-- **Correctness of the encoding.** -/
theorem solvable_tsm_iff (M : TSM) (s1 s2 : List ℕ) :
    Syn.Solvable (tsmDom M) (tsmInst M s1 s2) ↔ M.Halts s1 s2 := by
  rw [solvable_tsm_iff_grid]
  constructor
  · rintro ⟨as, hy, happ, hgoal⟩
    obtain ⟨y1, y2, h1, h2, hint⟩ := gridYield_iff.1 hy
    exact reaches_of_plan h1 h2 hint happ hgoal
  · intro h
    obtain ⟨as, y1, y2, h1, h2, hint, happ, hst⟩ := exists_plan_of_reaches h
    exact ⟨as, gridYield_iff.2 ⟨y1, y2, h1, h2, hint⟩, happ, by rw [hst]⟩

end Undec

end HTN
