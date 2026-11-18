import HtnComplexity.Computable.TMRenderClass
import HtnComplexity.Computable.TMRenderSize
/-!
# The family construction, with free numberings of the facts and of the compound tasks

`HtnComplexity/Computable/TMRender.lean` writes the re-split construction of Theorem 4.3.7
down as a pair of descriptions with the numberings `HTN.TMEnc.Fam.encGFact q g` of the facts and
`HTN.TMEnc.encTMTask g` of the compound task names.  A rendering accepts *any* injective
numbering, and the polynomial-time bound on the instance map needs a different one: the input
facts must be numbered the way the positional encoding of `HtnComplexity/Complexity/
PosFamily.lean` numbers them, which depends on the input length.

This file repeats the construction with the two numberings as parameters:

* `HTN.TMEnc.Fam.famRenderingG`, `HTN.TMEnc.Fam.famDomDescG`, `HTN.TMEnc.Fam.famInstDescG`;
* `HTN.TMEnc.Fam.solvable_famDescG_iff` — solvable exactly when `problemFix N w K` is;
* `HTN.TMEnc.Fam.isAcyclic_famDomDescG`, `HTN.TMEnc.Fam.isRooted_famInstDescG` — the class
  conditions;
* `HTN.TMEnc.Fam.size_famDomDescG_le` — the size bound `famDomBound`, which does not depend on the
  numberings.
-/

namespace HTN

namespace TMEnc

namespace Fam

open scoped Classical

open TM TaskNetwork GuardTask Syn

variable {Q Γ : Type} [Fintype Q] [Fintype Γ]

/-- **The rendering of the family problem with free numberings** `eF` of the facts and `eC` of
the compound task names. -/
noncomputable def famRenderingG (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (w : List Γ) (K : ℕ) :
    Rendering ((famDomain N w.length K).mkProblem (famInstance N w)) :=
  { famRendering N hq hg w K with
    eF := eF
    eC := eC
    eF_inj := heF
    eC_inj := heC }

/-- **The description of the family domain, with free numberings.** -/
noncomputable def famDomDescG (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (eF : GFact Q Γ → ℕ)
    (eC : TMTask Q Γ → ℕ) (n K : ℕ) : DomDesc :=
  ((famActs n).map fun o =>
      (encGAct q g o, ((gPrecL o).map eF, (gAddL o).map eF, (gDelL o).map eF)),
    (famBodies N n K).map fun p => (eC p.1, p.2.desc (encGAct q g) eC))

/-- **The description of the family instance, with free numberings.** -/
def famInstDescG (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (eF : GFact Q Γ → ℕ)
    (eC : TMTask Q Γ → ℕ) (w : List Γ) : InstDesc :=
  ((famInitL N w).map eF, [],
    (Shape.mk [[(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]] 0).desc (encGAct q g) eC)

lemma famDomDescG_encGFact (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (n K : ℕ) :
    famDomDescG N q g (encGFact q g) (encTMTask g) n K = famDomDesc N q g n K := rfl

lemma domDesc_famRenderingG (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (w : List Γ) (K : ℕ) :
    (famRenderingG N hq hg heF heC w K).domDesc = famDomDescG N q g eF eC w.length K := rfl

lemma instDesc_famRenderingG (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (w : List Γ) (K : ℕ) :
    (famRenderingG N hq hg heF heC w K).instDesc = famInstDescG N q g eF eC w := rfl

/-- **The described family problem, with free numberings, is the encoding of Theorem 4.3.7.** -/
theorem solvable_famDescG_iff (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (w : List Γ) (K : ℕ) :
    Syn.Solvable (famDomDescG N q g eF eC w.length K) (famInstDescG N q g eF eC w) ↔
      (problemFix N w K).Solvable := by
  rw [← domDesc_famRenderingG N hq hg heF heC w K, ← instDesc_famRenderingG N hq hg heF heC w K,
    (famRenderingG N hq hg heF heC w K).solvable_iff]
  exact solvable_famDomain_iff N w K

/-- **The described family domain, with free numberings, is acyclic.** -/
theorem isAcyclic_famDomDescG (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (n K : ℕ) : DomDesc.IsAcyclic (famDomDescG N q g eF eC n K) := by
  have h := (famRenderingG N hq hg heF heC (wpad N n) K).isAcyclic_domDesc (rank K n)
    (fun p hp row hrow x hx c hc => by
      subst hc
      exact rank_lt_of_mem_famBodies (by simpa [famRenderingG, famRendering] using hp) hrow hx)
  rwa [domDesc_famRenderingG, length_wpad] at h

/-- **The described family instance, with free numberings, is rooted.** -/
theorem isRooted_famInstDescG (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) {eF : GFact Q Γ → ℕ}
    (heF : Function.Injective eF) {eC : TMTask Q Γ → ℕ} (heC : Function.Injective eC)
    (w : List Γ) : InstDesc.IsRooted (famInstDescG N q g eF eC w) := by
  have h := (famRenderingG N hq hg heF heC w 0).isRooted_instDesc (c := TMTask.sI) rfl
  rwa [instDesc_famRenderingG] at h

/-- **The size of the described family domain does not depend on the numberings.** -/
theorem size_famDomDescG_le (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (eF : GFact Q Γ → ℕ)
    (eC : TMTask Q Γ → ℕ) (n K : ℕ) :
    (famDomDescG N q g eF eC n K).size ≤
      famDomBound (Fintype.card Q) (Fintype.card Γ) n
        ((2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
          (2 * Nat.log 2 (K - n) + 2))
        (2 * Nat.log 2 (K - 1) + 2) := by
  unfold famDomBound
  -- the size of the described domain, read off the lists
  have hsize : (famDomDescG N q g eF eC n K).size ≤
      ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
        1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length).sum +
      ((famBodies N n K).map fun p => 1 + 3 * p.2.cells + p.2.after).sum := by
    refine Nat.add_le_add ?_ ?_
    · show ((((famActs (Q := Q) (Γ := Γ) n).map fun o =>
        (encGAct q g o, ((gPrecL o).map (eF), (gAddL o).map (eF),
          (gDelL o).map (eF))))).map ActionDesc.size).sum ≤ _
      rw [List.map_map]
      refine List.sum_le_sum fun o _ => ?_
      simp [ActionDesc.size]
    · show (((famBodies N n K).map fun p =>
        (eC p.1, p.2.desc (encGAct q g) eC)).map MethodDesc.size).sum ≤ _
      rw [List.map_map]
      refine List.sum_le_sum fun p _ => ?_
      have := Shape.size_desc_le (encGAct q g) eC p.2
      show 1 + (p.2.desc (encGAct q g) eC).size ≤ 1 + 3 * p.2.cells + p.2.after
      omega
  -- the actions
  have hacts : ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
      1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length).sum ≤
      (famActs (Q := Q) (Γ := Γ) n).length * (Fintype.card Γ + 8) := by
    have h := List.sum_le_card_nsmul ((famActs (Q := Q) (Γ := Γ) n).map fun o =>
      1 + (gPrecL o).length + (gAddL o).length + (gDelL o).length) (Fintype.card Γ + 8) (by
        intro x hx
        obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
        exact act_size_le o)
    simpa [smul_eq_mul] using h
  -- the bodies
  have hbodies : ((famBodies N n K).map fun p => 1 + 3 * p.2.cells + p.2.after).sum ≤
      (famBodies N n K).length * 34 := by
    have h := List.sum_le_card_nsmul ((famBodies N n K).map fun p =>
      1 + 3 * p.2.cells + p.2.after) 34 (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
        exact body_size_le hp)
    simpa [smul_eq_mul] using h
  -- the counts
  have hops := card_opFinset_le (qs := (Finset.univ : Finset Q)) (gs := (Finset.univ : Finset Γ))
  simp only [Finset.card_univ] at hops
  have hlen := length_famActs (Q := Q) (Γ := Γ) n
  have hbl := length_famBodies_le N n K
  have htf := card_taskFinsetFam_le N n K
  have htfix := card_taskFinsetFix_le N (wpad N n) K
  have htask := card_taskFinset_le (N := N) (w := wpad N n) (K := K)
  have hcnt := card_countFinset_le K n
  rw [length_wpad] at htask
  set L := (2 * Nat.log 2 K + 2) + (2 * Nat.log 2 (K + 1) + 2) + (2 * Nat.log 2 (K + 2) + 2) +
    (2 * Nat.log 2 (K - n) + 2)
  set c := (countFinset K n).card
  set B := ((Fintype.card Γ + 1) + Fintype.card Q * (Fintype.card Γ *
    (Fintype.card Q * (Fintype.card Γ * 3))) + Fintype.card Q + 2) + Fintype.card Γ
  have hcc : 25 + 2 * n + 13 * c + c * c ≤ 25 + 2 * n + 13 * L + L * L := by
    have := Nat.mul_le_mul hcnt hcnt
    omega
  have hT : (taskFinsetFam N n K).card ≤
      25 + 2 * n + 13 * L + L * L + (2 * Nat.log 2 (K - 1) + 2) + Fintype.card Γ := by
    omega
  have h1 : (famActs (Q := Q) (Γ := Γ) n).length * (Fintype.card Γ + 8) ≤
      (1 + n * Fintype.card Γ + ((Fintype.card Γ + 1) + (Fintype.card Γ + Fintype.card Q + 9) +
        12 + 2 + Fintype.card Q * ((Fintype.card Γ + 1) * (Fintype.card Q *
          (Fintype.card Γ + 1))))) * (Fintype.card Γ + 8) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (famBodies N n K).length * 34 ≤
      34 * ((25 + 2 * n + 13 * L + L * L + (2 * Nat.log 2 (K - 1) + 2) + Fintype.card Γ) * B + 1) := by
    rw [Nat.mul_comm]
    refine Nat.mul_le_mul_left _ (le_trans hbl (Nat.add_le_add_right ?_ _))
    exact Nat.mul_le_mul_right _ hT
  omega

end Fam

end TMEnc

end HTN
