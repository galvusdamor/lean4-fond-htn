import HtnComplexity.SpaceEnc.Size
import HtnComplexity.SpaceEnc.RenderTR
import HtnComplexity.Space.NexpFamily
import HtnComplexity.Computable.Guard
import HtnComplexity.Hypotheses.ExpSpace
/-!
# `HTN-TR-1` is `EXPSPACE`-hard; the cells (`HTN-TR`, `HTN-AC`) on `EXPSPACE ⊄ NEXPTIME/poly`

For a language of `EXPSPACE`, given by a nondeterministic machine `N` and a polynomial `p` with
`L w ↔ N` accepts `w` within `2 ^ p(|w|)` tape cells, the family is

* domain for the inputs of length `n`: the rendered tail-recursive encoding
  `HTN.SpaceEnc.rend (p n) n some N n _` (it does not depend on the word);
* instance of a word `w`: `HTN.Space.hardInst w`, the instance map of the `NEXPTIME` family
  (polynomial time, injective, rooted).

Main results:

* `HTN.SpaceEnc.expSpaceHardSourceNU_HTN_TR_root` — `HTN-TR-1` is `EXPSPACE`-hard in the family
  sense (polynomial-time instance map, polynomial-size domains);
* `HTN.SpaceEnc.htnTR_htnAC_cells_of_expspaceNotInNexpPoly` — the three cells (`HTN-TR`,
  `HTN-AC`), (`HTN-TR-1`, `HTN-AC`), (`HTN-TR-1`, `HTN-AC-1`) admit no polynomial-size
  compilation with polynomial-time instance translation, assuming only
  `EXPSPACE ⊄ NEXPTIME/poly`.
-/

namespace HTN

namespace SpaceEnc

open TM Syn Syn.Coded Space

variable {k : ℕ}

/-- **The domain description** for the inputs of length `n`. -/
noncomputable def spDom (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (n : ℕ) : DomDesc :=
  (rend (p.eval n) n some N n (List.replicate n false)).domDesc

/-- The polynomial bound on the domain size. -/
noncomputable def spBound (k : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  let B : Polynomial ℕ := 2 * Polynomial.X + 16 * p +
    Polynomial.C (2 * Fintype.card TapeSym + 6 * (k ^ 2 * Fintype.card TapeSym ^ 2) + k + 30)
  3 * B * (3 * p + Polynomial.C (Fintype.card TapeSym + 21)) + 10 * B

theorem size_spDom_le (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (n : ℕ) :
    (spDom N p n).size ≤ (spBound k p).eval n := by
  have h := size_domDesc_rend_le (p.eval n) n some N n (List.replicate n false)
  simp only [bodiesBound, Fintype.card_fin] at h
  refine h.trans (le_of_eq ?_)
  simp [spBound]
  ring

theorem solvable_spDom_iff (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (w : List Bool) :
    Solvable (spDom N p w.length) (hardInst w) ↔
      N.AcceptsInSpace (w.map some) (2 ^ p.eval w.length) := by
  have h1 : spDom N p w.length =
      (rend (p.eval w.length) w.length some N w.length w).domDesc := rfl
  rw [h1, ← instDesc_rend (p.eval w.length) w.length some N w]
  exact solvable_rend_iff _ _ _ _ rfl _

/-- **The `EXPSPACE` hardness family**, in `HTN-TR-1`. -/
noncomputable def spFamily (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) :
    HardFamilyNU codingSer SynClass.HTN_TR_root
      (fun w => N.AcceptsInSpace (w.map some) (2 ^ p.eval w.length)) where
  dom := spDom N p
  inst := hardInst
  bound := spBound k p + Polynomial.X + 3
  dom_size := fun n => by
    have := size_spDom_le N p n
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  inst_size := fun w => by
    rw [size_hardInst]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  dom_ok := fun n => isTailRec_domDesc_rend _ _ _ _ _ _
  inst_ok := fun w => guardInst_isRooted
  inst_injective := hardInst_injective
  correct := solvable_spDom_iff N p
  inst_polyTime := polyTimeCode_hardInst

/-- **`HTN-TR-1` is `EXPSPACE`-hard in the family sense**, with non-uniform domains. -/
theorem expSpaceHardSourceNU_HTN_TR_root : ExpSpaceHardSourceNU codingSer SynClass.HTN_TR_root := by
  rintro L ⟨k, N, p, hL⟩
  exact ⟨(spFamily N p).congrLang fun w => (hL w).symm⟩

end SpaceEnc

end HTN
