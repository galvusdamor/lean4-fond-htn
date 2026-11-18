import HtnComplexity.Space.AltSeqMachine
/-!
# The planner P-TO: totally ordered HTN with an initial task network, in alternating polynomial
space

    HTN.Space.altDecidableAdv_TO_HTN : AltDecidableAdv codingSer SynClass.TO_HTN

"Plan existence for a totally ordered HTN description and a totally ordered instance (with an
arbitrary initial task network) is decidable in alternating polynomial space (`= EXPTIME`), the
domain description being supplied as advice" — **with no hypothesis left**.

The instance is first put into the rooted form of the sequencing gadget
(`HTN.Syn.SeqG.solvable_seq_iff`), whose compiled initial state the machine guesses and checks
locally (`HTN.Space.SeqM.seqInitB`, as for the planner P-TR of
`HtnComplexity/Space/SeqSpace.lean`); the rooted gadget problem is solvability of the layout
of the gadget domain, a table with calls (`HTN.Space.solvable_to_iff_aSolvable`), which the
alternating machine decides (`HtnComplexity/Space/AltSeqMachine.lean`).

The advice `HTN.Space.altSeqAdv` is the marker rows of the gadget (root numeral, short action
names), `P` padding rows (so that the guessed configurations fit into the space bound of the
alternating machine) and the layout of the gadget domain for sequences of length at most `rq(n)`,
its facts renamed by `tblNorm`.  As for the other planners, nothing is assumed about the cost of
computing the advice; only its length is bounded.
-/

namespace HTN

namespace Space

open Syn PTime SeqG SeqM

/-- **Plan existence as solvability of a table with calls, through a checked witness.** -/
theorem solvable_iff_aSolvable_of_wit {d : DomDesc} {q : InstDesc} {N : ℕ} (hTO : d.MethodsTO)
    (hq : q.IsTO) (hN : q.tnI.ids.length ≤ N) {ws : List (ℕ × ℕ)} {xs : List (ℕ ⊕ ℕ)}
    (hw : WitOk q.tnI ws) (hx : WitSeq q.tnI ws xs) :
    Solvable d q ↔ ASolvable kPush kRet (toLayout (seqDom (code d) d N))
      {f | f ∈ regInitR (seqInst (code d) d q xs ws)} {f | f ∈ seqGoal d q} := by
  obtain ⟨l, hl⟩ := isSeqNet_of_witSeq hq hw hx
  rw [solvable_seq_iff (code_fresh d) hTO hl ((length_le_of_witSeq hx).trans hN) ws,
    solvable_to_iff_aSolvable (methodsTO_seqDom hTO) (isRooted_seqInst _ d q xs ws),
    regGoalR_seqInst]

/-- The padded layout of the gadget domain. -/
noncomputable def altSeqTbl (d : DomDesc) (N P : ℕ) : List Row :=
  padRows P ++ toLayout (seqDom (code d) d N)

/-- **The advice** of the alternating planner. -/
noncomputable def altSeqAdv (d : DomDesc) (N K L P : ℕ) : List Bool :=
  tblAdv true (markRows d K ++ (altSeqTbl d N P).map (mapRow (tblNorm L (altSeqTbl d N P))))

/-- **Correctness of the alternating machine with the advice**, for one instance. -/
theorem altSeq_correct {d : DomDesc} {q : InstDesc} {N K L P : ℕ} (hTO : d.MethodsTO)
    (hq : q.IsTO) (hN : (instSer q).length ≤ N) (hK : (instSer q).length ≤ K)
    (hL : 2 * (instSer q).length + (bitsOfNat (cRoot d)).length + 10 ≤ L)
    (hP : 4 * (instSer q).length + 10 ≤ P) :
    Solvable d q ↔ altSeqMachine.Accepts (instSer q) (altSeqAdv d N K L P) := by
  have hN' : q.tnI.ids.length ≤ N := (length_ids_le q).trans hN
  set T := altSeqTbl d N P with hT
  have hbnd : ∀ S : List ℕ, (∀ f ∈ S, (bitsOfNat f).length ≤ seqBnd d q) → ∀ f ∈ S, f < 2 ^ L :=
    fun S h f hf => lt_two_pow_of_length_bitsOfNat_le ((h f hf).trans (by unfold seqBnd; omega))
  have hg : ∀ f ∈ seqGoal d q, f < 2 ^ L := mem_seqGoal_lt (by omega)
  have h10 : (2 : ℕ) ^ 10 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkp : kPush < 2 ^ L := by simp only [kPush]; omega
  have hkr : kRet < 2 ^ L := by simp only [kRet]; omega
  constructor
  · intro hs
    obtain ⟨xs, hx⟩ := exists_witSeq hq (witOk_canonWit hq)
    have h1 := (solvable_iff_aSolvable_of_wit hTO hq hN' (witOk_canonWit hq) hx).1 hs
    have hset : {f | f ∈ regInitR (seqInst (code d) d q xs (canonWit q.tnI))} =
        {f | f ∈ canonCfg d q xs} := by
      ext f; simp [canonCfg]
    rw [hset] at h1
    have h2 : ASolvable kPush kRet T {f | f ∈ canonCfg d q xs} {f | f ∈ seqGoal d q} :=
      (aSolvable_noop_append (noop_padRows P)).2 h1
    have hc : ∀ f ∈ canonCfg d q xs, f < 2 ^ L := by
      refine hbnd _ ?_
      have := bits_le_of_seqInitB (canon_map_bitsOfNat _) hK
        (canon_seqInitB (d := d) hq hx hK true [])
      rwa [decSt_map_bitsOfNat] at this
    have h3 := (aSolvable_tblNorm (T := T) hc hg hkp hkr).2 h2
    have h4 := (aSolvable_noop_append (noop_markRows d K)).2 h3
    refine altSeq_complete hq hK hx ?_ h4
    simp [hT, altSeqTbl, markRows]
    omega
  · intro hA
    obtain ⟨S, hI, hB, hsolv⟩ := altSeq_sound hK hA
    have h1 := (aSolvable_noop_append (noop_markRows d K)).1 hsolv
    have h2 := (aSolvable_tblNorm (T := T) (hbnd S hB) hg hkp hkr).1 h1
    have h3 := (aSolvable_noop_append (noop_padRows P)).1 h2
    obtain ⟨ws, xs, hw, hx, hSR⟩ := (initOk_iff hq).1 hI
    have hset : {f | f ∈ S} = {f | f ∈ regInitR (seqInst (code d) d q xs ws)} := by
      ext f; exact hSR f
    rw [hset] at h3
    exact (solvable_iff_aSolvable_of_wit hTO hq hN' hw hx).2 h3

/-- The size of the padded layout. -/
theorem tblSize_altSeqTbl_le (d : DomDesc) (N P : ℕ) :
    tblSize (altSeqTbl d N P) ≤ P + 3 * (seqDom (code d) d N).size *
      ((seqDom (code d) d N).size + 3) * ((seqDom (code d) d N).size + 5) := by
  rw [altSeqTbl, tblSize_append, tblSize_padRows]
  have := tblSize_toLayout_le (seqDom (code d) d N)
  omega

/-- **Plan existence for a totally ordered HTN description and a totally ordered instance is
decidable in alternating polynomial space, the domain description being supplied as advice**
(the planner P-TO of `TABLE4-PLAN.md`).  The instance may carry an arbitrary (totally ordered)
initial task network. -/
theorem altDecidableAdv_TO_HTN : AltDecidableAdv codingSer SynClass.TO_HTN := by
  intro D r rq hdomOk hsize
  set Q : Polynomial ℕ := r + 15 * ((rq + 1) * (2 * r + 2)) with hQ
  let pT : Polynomial ℕ := 3 * Polynomial.X * (Polynomial.X + 3) * (Polynomial.X + 5)
  refine ⟨altSeqMachine, fun n => altSeqAdv (D n) (rq.eval n) (rq.eval n)
      (2 * rq.eval n + (bitsOfNat (cRoot (D n))).length + 10) (4 * rq.eval n + 10),
    8 * (3 * r + 2 * pT.comp Q + 12 * rq + 50) ^ 3, fun n => ?_, fun n q hq hlen => ?_⟩
  · refine (length_tblAdv_markRows_le _ _ _ _ _).trans ?_
    have hs := hsize n
    have hsz : (seqDom (code (D n)) (D n) (rq.eval n)).size ≤ Q.eval n := by
      refine (size_seqDom_le _ _).trans ?_
      simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_one]
      have h2 : 2 * (D n).size + 2 ≤ 2 * r.eval n + 2 := by omega
      have h3 := Nat.mul_le_mul_left (rq.eval n + 1) h2
      omega
    have hT : tblSize (altSeqTbl (D n) (rq.eval n) (4 * rq.eval n + 10)) ≤
        4 * rq.eval n + 10 + (pT.comp Q).eval n := by
      refine (tblSize_altSeqTbl_le _ _ _).trans ?_
      have : 3 * (seqDom (code (D n)) (D n) (rq.eval n)).size *
          ((seqDom (code (D n)) (D n) (rq.eval n)).size + 3) *
          ((seqDom (code (D n)) (D n) (rq.eval n)).size + 5) ≤
          3 * Q.eval n * (Q.eval n + 3) * (Q.eval n + 5) := by
        gcongr
      simp only [pT, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have hc := bits_cRoot_le (D n)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_ofNat]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
    omega
  · have hlen' : (instSer q).length ≤ rq.eval n := by simpa using hlen
    rw [codingSer_code]
    exact altSeq_correct (hdomOk n) hq hlen' hlen' (by omega) (by omega)

end Space

end HTN
