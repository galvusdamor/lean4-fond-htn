import HtnComplexity.AcVerify.NExp
import HtnComplexity.AcVerify.BoundFine
/-!
# The `HTN-AC` verifier with the refined certificate bound

`HTN.Syn.AcVer.nExpDecidableAdv_HTN_AC` checks plans of `HTN-AC` with certificates of length
`2 ^ p(n)`.  With the refined bound of `HtnComplexity/AcVerify/BoundFine.lean` the same
verifier `acV` and the same advice (the renamed table of `D n`) need only certificates of length

    256 · (X + 1) ^ 3 · (|D n| + 1) ^ (2 |D n| + 2),     X = rq(n) + r(n) + (rq(n) + 2 r(n) + 1),

polynomial in `n` as soon as `|D n| · log |D n| = O(log n)`
(**`HTN.Syn.AcVer.fineVerifier_HTN_AC`**).  This is the target side of the conditional
refutation of (`HTN-REGM`, `HTN-AC`) in `PROOFIDEAS.md`, 8e.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

/-- The common bound on the instance size, the domain size and the bit length of the names. -/
noncomputable def fineX (r rq : Polynomial ℕ) (n : ℕ) : ℕ :=
  rq.eval n + r.eval n + (rq.eval n + 2 * r.eval n + 1)

/-- **The `HTN-AC` verifier with short certificates.**  For every family `D` of acyclic domain
descriptions of size at most `r(n)` there is an advice of polynomial length such that an
instance `q` of code length at most `rq(n)` is solvable over `D n` iff `acV` accepts some
certificate of length at most `256 · (X + 1) ^ 3 · (|D n| + 1) ^ (2 |D n| + 2)`. -/
theorem fineVerifier_HTN_AC (D : ℕ → DomDesc) (r rq : Polynomial ℕ)
    (hok : ∀ n, (D n).IsAcyclic) (hsize : ∀ n, (D n).size ≤ r.eval n) :
    ∃ A : ℕ → List Bool, (∀ n, (A n).length ≤ (advP r rq).eval n) ∧
      ∀ (n : ℕ) (q : InstDesc), (instSer q).length ≤ rq.eval n →
        (Solvable (D n) q ↔ ∃ w : List Bool,
          w.length ≤ 256 * (fineX r rq n + 1) ^ 3 * ((D n).size + 1) ^ (2 * (D n).size + 2) ∧
          acV [instSer q, A n, w] = true) := by
  set L : ℕ → ℕ := fun n => rq.eval n
  set k : ℕ → ℕ := fun n => 2 * r.eval n
  have hk : ∀ n, 2 * (D n).size ≤ k n := fun n => by have := hsize n; simp only [k]; omega
  refine ⟨fun n => advOf (renDom (D n) (L n) (k n)), fun n => ?_, fun n q hq => ?_⟩
  · obtain ⟨-, hsz, hB, -⟩ := renDom_props (hok n) (hk n)
    refine (length_advOf_le hB).trans ?_
    rw [hsz]
    refine (advBound_mono (hsize n) le_rfl).trans (le_of_eq ?_)
    simp [advBound, rowBound, advP, bitsP, L, k]
  · obtain ⟨hac, hsz, hB, hsol⟩ := renDom_props (hok n) (hk n) (L := L n)
    have hq' : (instSer q).length ≤ L n := hq
    constructor
    · intro hs
      obtain ⟨W, hW, h0⟩ := exists_pathOK0_of_solvable ((hsol q hq').2 hs)
      refine ⟨_, ?_, acV_certOf hW h0⟩
      set X := fineX r rq n
      have hN : NamesLt (renDom (D n) (L n) (k n)) q (L n + k n + 1) :=
        ⟨hB.dom, fun x hx => (lt_of_mem_names hq' hx).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega)), hB.meth⟩
      refine (length_certOf_le_fine hac hN hW h0).trans ?_
      refine (certBoundF_le _ _ _ _).trans ?_
      have hqs : q.size ≤ X :=
        (size_le_length_instSer q).trans (by simp only [X, fineX, L] at hq' ⊢; omega)
      have hnI : q.tnI.ids.length ≤ X := by
        have : q.tnI.ids.length ≤ q.size := by simp only [InstDesc.size, TnDesc.size]; omega
        omega
      have hBX : L n + k n + 1 ≤ X := by simp only [X, fineX, L, k]; omega
      rw [hsz]
      set P := ((D n).size + 1) ^ (2 * (D n).size + 2)
      have h1 : (q.tnI.ids.length + 1) * (q.size + 1) * (L n + k n + 1 + 1) ≤
          (X + 1) * (X + 1) * (X + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      calc 256 * (q.tnI.ids.length + 1) * (q.size + 1) * (L n + k n + 1 + 1) * P
          = 256 * ((q.tnI.ids.length + 1) * (q.size + 1) * (L n + k n + 1 + 1)) * P := by ring
        _ ≤ 256 * ((X + 1) * (X + 1) * (X + 1)) * P := by gcongr
        _ = 256 * (X + 1) ^ 3 * P := by ring
    · rintro ⟨w, -, hw⟩
      exact (hsol q hq').1 (solvable_of_acV hw)

end AcVer

end Syn

end HTN
