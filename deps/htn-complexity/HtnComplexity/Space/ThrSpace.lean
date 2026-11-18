import HtnComplexity.Space.ThrSize
import HtnComplexity.Space.SeqSpace
/-!
# The planner P-REG: regular HTN with an arbitrary initial task network

    HTN.Space.spaceDecidableAdv_HTN_REG : SpaceDecidableAdv codingSer SynClass.HTN_REG

"Plan existence for a regular HTN description and an arbitrary instance (partially ordered
initial task network, any number of initial compound tasks) is decidable in nondeterministic
polynomial space, the domain description being supplied as advice" — with no hypothesis left.

The machine is `HTN.Space.Thr.thrMachine`; the advice for the inputs of length `n` is
`HTN.Space.Thr.thrAdv`: the flag bit (unused), the two marker rows of P-TR (only the vocabulary
marker is read) and the numbered thread table `(thrTbl d N).map (encRow enc)` for
`N = 2·rq(n) + 1` threads and nodes, with its large facts renamed (`HTN.Space.tblNorm`).  As in
`HtnComplexity/Space/SeqSpace.lean`, only the length of the advice is bounded, by
`HTN.Space.Thr.tblSize_thrTbl_le`.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

open Classical

/-- The `→` half of `thr_solvable_iff`, for the canonical configuration itself. -/
theorem solvableTbl_canonS {d : DomDesc} {q : InstDesc} {N : ℕ} (hreg : d.MethodsReg)
    (hN : (wnodes q.tnI).length < N) (hs : Solvable d q) :
    SolvableTbl ((thrTbl d N).map (encRow enc)) (canonS d q) ((goalF q.goalList).map enc) := by
  have h := initOk_canonS (d := d) (q := q)
  have hC := hypC_canonS hreg hN
  refine (solvableTbl_iff_solvF enc_injective (initG_eq h) _).2 ?_
  exact (tsolv_iff_solvF hC).1
    ((solvable_iff_tsolv (P := parOf d q (canonS d q)) hC.good (iso_of_initOk h)).1 hs)

/-- The numbered thread table. -/
noncomputable def thrT (d : DomDesc) (N : ℕ) : List Row := (thrTbl d N).map (encRow enc)

/-- **The advice**: the flag bit, the marker rows and the renamed numbered thread table for at
most `N` threads and nodes; `K` bounds the action names announced by the marker row, `L` the
facts kept by the renaming. -/
noncomputable def thrAdv (d : DomDesc) (N K L : ℕ) : List Bool :=
  tblAdv true (markRows d K ++ (thrT d N).map (mapRow (tblNorm L (thrT d N))))

/-- **The length of the advice.** -/
theorem length_thrAdv_le (d : DomDesc) (N K L : ℕ) :
    (thrAdv d N K L).length ≤ 8 * (d.size + 3 + tblSize (thrT d N) +
      (d.size + 2 * K + 2 + L + tblSize (thrT d N)) + 3) ^ 3 :=
  length_tblAdv_markRows_le d K L _ _

theorem mem_goalF_lt {q : InstDesc} {L : ℕ} (hL : (instSer q).length + 7 ≤ L) :
    ∀ f ∈ (goalF q.goalList).map enc, f < 2 ^ L := by
  intro f hf
  refine lt_two_pow_of_length_bitsOfNat_le ?_
  rcases mem_goalF_enc.1 hf with ⟨v, hv, rfl⟩ | rfl
  · have := length_bitsOfNat_add_two_le_of_mem_goalList hv
    rw [bitsOfNat_cfI]; simp [tagI3]; omega
  · rw [length_bitsOfNat_cfG]; simp [gbits]; omega

/-- **Correctness of the thread machine with the advice**, for one instance. -/
theorem thr_correct {d : DomDesc} {q : InstDesc} {N K L : ℕ} (hreg : d.MethodsReg)
    (hN : 2 * (instSer q).length < N) (hK : (instSer q).length ≤ K)
    (hL : 4 * (instSer q).length + 10 ≤ L) :
    Solvable d q ↔ thrMachine.Accepts (instSer q) (thrAdv d N K L) := by
  have hN' : (wnodes q.tnI).length < N := lt_of_le_of_lt (length_wnodes_le q) hN
  have hbnd : ∀ S : List ℕ, ThrInitOk d q S → ∀ f ∈ S, f < 2 ^ L := fun S h f hf =>
    lt_two_pow_of_length_bitsOfNat_le ((bits_le_of_thrInitOk h f hf).trans (by unfold thrBnd; omega))
  have hg : ∀ f ∈ (goalF q.goalList).map enc, f < 2 ^ L := mem_goalF_lt (by omega)
  constructor
  · intro hs
    have ht := solvableTbl_canonS hreg hN' hs
    have hI : ThrInitOk d q (canonS d q).dedup :=
      ThrInitOk.congr initOk_canonS fun f => List.mem_dedup
    have ht' : SolvableTbl (thrT d N) (canonS d q).dedup ((goalF q.goalList).map enc) :=
      solvableTbl_congr (fun _ => List.mem_dedup) ht
    have hn := (solvableTbl_tblNorm (hbnd _ hI) hg).2 ht'
    exact thrMachine_complete hK hn
  · intro hA
    obtain ⟨S, hI, hsolv⟩ := thrMachine_sound hK hA
    have hS := (solvableTbl_tblNorm (hbnd S hI) hg).1 hsolv
    exact (thr_solvable_iff hreg hN').2 ⟨S, hI, hS⟩

end Thr

open Syn PTime SeqG SeqM Thr

/-- **Plan existence for a regular HTN description and an arbitrary instance is decidable in
nondeterministic polynomial space, the domain description being supplied as advice** (the
planner P-REG of `TABLE4-PLAN.md`).  The instance may carry an arbitrary, partially ordered,
initial task network with any number of compound tasks. -/
theorem spaceDecidableAdv_HTN_REG : SpaceDecidableAdv codingSer SynClass.HTN_REG := by
  intro D r rq hdomOk hsize
  set P4 : Polynomial ℕ := 64 * (2 * rq + r + 2) ^ 4 with hP4
  refine ⟨thrMachine, fun n => thrAdv (D n) (2 * rq.eval n + 1) (rq.eval n)
      (4 * rq.eval n + 10), 8 * (2 * r + 2 * P4 + 6 * rq + 20) ^ 3, fun n => ?_,
    fun n q _ hlen => ?_⟩
  · refine (length_thrAdv_le _ _ _ _).trans ?_
    have hs := hsize n
    have hT : tblSize (thrT (D n) (2 * rq.eval n + 1)) ≤ P4.eval n := by
      refine (tblSize_thrTbl_le _ _).trans ?_
      simp only [hP4, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_ofNat]
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 4)
      omega
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_ofNat]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
    omega
  · have hlen' : (instSer q).length ≤ rq.eval n := by simpa using hlen
    rw [codingSer_code]
    exact thr_correct (hdomOk n) (by omega) hlen' (by omega)

end Space

end HTN
