import HtnComplexity.Undec.Correct
/-!
# A sanity check for the encoding

The reduction of `HtnComplexity/Undec/Correct.lean` is only interesting if the described
problems it produces are neither always solvable nor never solvable.  This file exhibits both
for one two-stack machine `probeTSM`, which has the single transition "pop `0` from the first
stack, push nothing, and accept":

* `HTN.Undec.solvable_probe_one` — with the first stack holding `[0]` the described problem is
  solvable;
* `HTN.Undec.not_solvable_probe_nil` — with both stacks empty it is not (the machine cannot
  move, and its initial state is not accepting).
-/

namespace HTN

namespace Undec

/-- The transition "pop `0` from the first stack and accept". -/
def probeTr : Tr := ⟨0, false, 0, [], 1⟩

/-- A two-stack machine with a single transition. -/
def probeTSM : TSM := ⟨[probeTr], 0, 1⟩

@[simp] theorem probeTSM_trAt_zero : probeTSM.trAt 0 = probeTr := rfl

/-- The machine halts when the first stack holds `[0]`. -/
theorem probe_halts : probeTSM.Halts [0] [] := by
  refine Relation.ReflTransGen.single ?_
  exact ⟨probeTr, by simp [probeTSM], rfl, Or.inl ⟨rfl, [], rfl, rfl⟩⟩

/-- The machine does not halt when both stacks are empty: it cannot move, and its initial state
is not the accepting one. -/
theorem probe_not_halts : ¬ probeTSM.Halts [] [] := by
  intro h
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨c, hstep, -⟩
  · simp [Cfg.mk.injEq, probeTSM] at heq
  · obtain ⟨t, ht, -, hcase⟩ := hstep
    rcases hcase with ⟨-, rest, hrest, -⟩ | ⟨-, rest, hrest, -⟩ <;> simp at hrest

/-- **The encoding of a machine that halts is solvable.** -/
theorem solvable_probe_one : Syn.Solvable (tsmDom probeTSM) (tsmInst probeTSM [0] []) :=
  (solvable_tsm_iff probeTSM [0] []).2 probe_halts

/-- **The encoding of a machine that does not halt is unsolvable.** -/
theorem not_solvable_probe_nil : ¬ Syn.Solvable (tsmDom probeTSM) (tsmInst probeTSM [] []) :=
  fun h => probe_not_halts ((solvable_tsm_iff probeTSM [] []).1 h)

end Undec

end HTN
