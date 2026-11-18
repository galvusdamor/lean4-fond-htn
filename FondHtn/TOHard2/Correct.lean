import FondHtn.TOHard2.CompleteK
/-!
# Correctness of the description

**`FOND.TOHard2.mpStrong_desc_iff`**: if the parameters `P` describe the tableau `tabC`
(`FOND.TOHard2.Hyp`), the description `FOND.TOHard2.desc P` is strongly solvable by a
method-based policy iff some entry of the last row of the tableau is accepting.
-/

namespace FOND

namespace TOHard2

open HTN HTN.Article HTN.Syn HardMP

theorem mpStrong_desc_iff {P : Par} {d : TabData} {tabC : ℕ → ℕ → ℕ} (H : Hyp P d tabC) :
    (desc P).toProblem.MPStrongSolvable ↔ ∃ i < 2 ^ d.B, tabC (2 ^ d.B - 1) i ∈ d.acc := by
  rw [desc, mpStrong_compile_iff (gram_good P) enc_s₀]
  exact ⟨root_sound H, root_complete H⟩

theorem desc_valid (P : Par) : (desc P).Valid := compile_valid (gram_good P) _ _

theorem desc_TO (P : Par) : FClass.TO (desc P).toProblem := compile_TO _ _

end TOHard2

end FOND
