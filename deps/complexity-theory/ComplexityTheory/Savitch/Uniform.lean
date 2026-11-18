import ComplexityTheory.Savitch.Main
/-!
# Savitch's theorem without advice

`HTN.Savitch.inPSpace_of_inNSpace`: a language a nondeterministic polynomial-space machine
accepts (`HTN.Space.InNSpace`) is in `PSPACE` (`HTN.PSpace.InPSpace`).  The predicate is the
formula of `HTN.Savitch.inPSpacePoly_of_inNSpacePoly` with the empty string for the advice.
-/

namespace HTN

namespace Savitch

open PTime PSpace Space

/-- **Savitch's theorem** (`NPSPACE ⊆ PSPACE`). -/
theorem inPSpace_of_inNSpace {L : List Bool → Prop} (h : InNSpace L) : InPSpace L := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨f0, hf0c, hf0⟩ := exists_cobham_len_ge M.bound
  refine ⟨fun args => qEx2 M f0 [proj 0 args, (fun _ => []) args],
    (psQEx2 hf0c).comp2 (PSpaceF.cobham (Cobham.proj 0)) (PSpaceF.cobham (cobham_const [])),
    fun x => ?_⟩
  rw [hM x]
  exact (qEx2_iff M hf0 x []).symm

end Savitch

end HTN
