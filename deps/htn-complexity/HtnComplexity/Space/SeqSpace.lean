import HtnComplexity.Space.SeqSize
import HtnComplexity.Space.TrSpace
/-!
# The planner P-TR: totally ordered tail-recursive HTN with an initial task network

    HTN.Space.spaceDecidableAdv_TO_HTN_TR : SpaceDecidableAdv codingSer SynClass.TO_HTN_TR

"Plan existence for a totally ordered tail-recursive HTN description and a totally ordered
instance (with an arbitrary initial task network) is decidable in nondeterministic polynomial
space, the domain description being supplied as advice" — **with no hypothesis left**.

The machine is `HTN.Space.SeqM.seqMachine`; the advice for the inputs of length `n` is
`HTN.Space.SeqM.seqAdv`: the flag bit (does the compiled domain have an empty method), the two
marker rows (the root numeral of the gadget and the short action names of the domain), and the
action table of the compiled `STRIPS` domain of the sequencing gadget for sequences of length at
most `rq(n)`, with its large facts renamed (`HTN.Space.tblNorm`).  As in
`HtnComplexity/Space/TrSpace.lean`, nothing is assumed about the cost of computing the
advice; only its length is bounded, by `HTN.Space.SeqM.size_seqDom_le` and
`HTN.Space.tblSize_trTableR_le`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

open Classical

/-- **The advice**: the flag bit, the marker rows and the renamed action table of the compiled
gadget domain for sequences of length at most `N`; `K` bounds the action names announced by the
marker row, `L` the facts kept by the renaming. -/
noncomputable def seqAdv (d : DomDesc) (N K L : ℕ) : List Bool :=
  tblAdv (decide (trDom (seqDom (code d) d N)).HasEmptyMethod)
    (markRows d K ++ (trTableR (seqDom (code d) d N)).map
      (mapRow (tblNorm L (trTableR (seqDom (code d) d N)))))

theorem mem_tblFacts_append {t t' : List Row} {f : ℕ} :
    f ∈ tblFacts (t ++ t') ↔ f ∈ tblFacts t ∨ f ∈ tblFacts t' := by
  simp [tblFacts, List.flatMap_append]

/-- The length of an advice of the shape of `seqAdv`. -/
theorem length_tblAdv_markRows_le (d : DomDesc) (K L : ℕ) (b : Bool) (T : List Row) :
    (tblAdv b (markRows d K ++ T.map (mapRow (tblNorm L T)))).length ≤
      8 * (d.size + 3 + tblSize T + (d.size + 2 * K + 2 + L + tblSize T) + 3) ^ 3 := by
  have hm : ∀ f ∈ tblFacts (markRows d K ++ T.map (mapRow (tblNorm L T))),
      (bitsOfNat f).length ≤ d.size + 2 * K + 2 + L + tblSize T := by
    intro f hf
    rcases mem_tblFacts_append.1 hf with hf | hf
    · have := bits_markRows_le d K f hf
      omega
    · obtain ⟨c, hc, rfl⟩ := mem_tblFacts_of_mem_map hf
      have := length_bitsOfNat_le_of_lt_two_pow (tblNorm_lt (L := L) hc)
      omega
  have h := length_tblAdv_le b _ _ hm
  rw [tblSize_append, tblSize_map_mapRow] at h
  have hmk := tblSize_markRows_le d K
  refine h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3))
  omega

/-- **The length of the advice.** -/
theorem length_seqAdv_le (d : DomDesc) (N K L : ℕ) :
    (seqAdv d N K L).length ≤ 8 * (d.size + 3 + tblSize (trTableR (seqDom (code d) d N)) +
      (d.size + 2 * K + 2 + L + tblSize (trTableR (seqDom (code d) d N))) + 3) ^ 3 :=
  length_tblAdv_markRows_le d K L _ _

theorem mem_seqGoal_lt {d : DomDesc} {q : InstDesc} {L : ℕ} (hL : (instSer q).length + 7 ≤ L) :
    ∀ f ∈ seqGoal d q, f < 2 ^ L := by
  intro f hf
  refine lt_two_pow_of_length_bitsOfNat_le ?_
  rcases mem_seqGoal.1 hf with ⟨v, hv, rfl⟩ | rfl | rfl
  · have := length_bitsOfNat_add_two_le_of_mem_goalList hv
    rw [bitsOfNat_cfI]; simp [tagI3]; omega
  · rw [length_bitsOfNat_cfG]; simp [gbits]; omega
  · simp

/-- **Correctness of the machine with the advice**, for one instance. -/
theorem seq_correct {d : DomDesc} {q : InstDesc} {N K L : ℕ} (hTO : d.MethodsTO)
    (hTR : d.IsTailRec) (hq : q.IsTO) (hN : (instSer q).length ≤ N)
    (hK : (instSer q).length ≤ K)
    (hL : 2 * (instSer q).length + (bitsOfNat (cRoot d)).length + 10 ≤ L) :
    Solvable d q ↔ seqMachine.Accepts (instSer q) (seqAdv d N K L) := by
  have hN' : q.tnI.ids.length ≤ N := (length_ids_le q).trans hN
  have hbnd : ∀ S : List ℕ, (∀ f ∈ S, (bitsOfNat f).length ≤ seqBnd d q) → ∀ f ∈ S, f < 2 ^ L :=
    fun S h f hf => lt_two_pow_of_length_bitsOfNat_le ((h f hf).trans (by unfold seqBnd; omega))
  have hg : ∀ f ∈ seqGoal d q, f < 2 ^ L := mem_seqGoal_lt (by omega)
  constructor
  · intro hs
    obtain ⟨xs, hx⟩ := exists_witSeq hq (witOk_canonWit hq)
    obtain ⟨he, ht⟩ := (solvable_iff_tbl_of_wit hTO hTR hq hN' (witOk_canonWit hq) hx).1 hs
    rw [regGoalR_seqInst] at ht
    have ht' : SolvableTbl (trTableR (seqDom (code d) d N)) (canonCfg d q xs) (seqGoal d q) :=
      solvableTbl_congr (fun _ => List.mem_dedup) ht
    have hc : ∀ f ∈ canonCfg d q xs, f < 2 ^ L := by
      refine hbnd _ ?_
      have := bits_le_of_seqInitB (canon_map_bitsOfNat _) hK (canon_seqInitB (d := d) hq hx hK true [])
      rwa [decSt_map_bitsOfNat] at this
    have hn := (solvableTbl_tblNorm hc hg).2 ht'
    unfold seqAdv
    rw [decide_eq_true he]
    exact seqMachine_complete hq hK hx hn
  · intro hA
    obtain ⟨hb, S, hI, hB, hsolv⟩ := seqMachine_sound hK hA
    have hS := (solvableTbl_tblNorm (hbnd S hB) hg).1 hsolv
    exact (solvable_iff_exists_initOk hTO hTR hq hN').2 ⟨of_decide_eq_true hb, S, hI, hS⟩

end SeqM

open Syn PTime SeqG SeqM

/-- **Plan existence for a totally ordered tail-recursive HTN description and a totally ordered
instance is decidable in nondeterministic polynomial space, the domain description being
supplied as advice** (the planner P-TR of `TABLE4-PLAN.md`).  The instance may carry an
arbitrary (totally ordered) initial task network. -/
theorem spaceDecidableAdv_TO_HTN_TR : SpaceDecidableAdv codingSer SynClass.TO_HTN_TR := by
  obtain ⟨ptbl, hptbl⟩ := tblSize_trTableR_le
  intro D r rq hdomOk hsize
  set Q : Polynomial ℕ := r + 15 * ((rq + 1) * (2 * r + 2)) with hQ
  refine ⟨seqMachine, fun n => seqAdv (D n) (rq.eval n) (rq.eval n)
      (2 * rq.eval n + (bitsOfNat (cRoot (D n))).length + 10),
    8 * (3 * r + 2 * ptbl.comp Q + 4 * rq + 20) ^ 3, fun n => ?_, fun n q hq hlen => ?_⟩
  · refine (length_seqAdv_le _ _ _ _).trans ?_
    have hs := hsize n
    have hT : tblSize (trTableR (seqDom (code (D n)) (D n) (rq.eval n))) ≤ (ptbl.comp Q).eval n := by
      calc _ ≤ ptbl.eval (seqDom (code (D n)) (D n) (rq.eval n)).size := hptbl _
        _ ≤ ptbl.eval (Q.eval n) := by
          refine Polynomial.eval_mono_nat _ ((size_seqDom_le _ _).trans ?_)
          simp only [hQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
            Polynomial.eval_one]
          have : rq.eval n + 1 ≤ rq.eval n + 1 := le_rfl
          have h2 : 2 * (D n).size + 2 ≤ 2 * r.eval n + 2 := by omega
          have h3 := Nat.mul_le_mul_left (rq.eval n + 1) h2
          omega
        _ = (ptbl.comp Q).eval n := by simp
    have hc := bits_cRoot_le (D n)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_ofNat]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 3)
    omega
  · have hlen' : (instSer q).length ≤ rq.eval n := by simpa using hlen
    rw [codingSer_code]
    exact seq_correct (hdomOk n).1 (hdomOk n).2 hq hlen' hlen' (by omega)

/-- The same for totally ordered acyclic descriptions. -/
theorem spaceDecidableAdv_TO_HTN_AC : SpaceDecidableAdv codingSer SynClass.TO_HTN_AC :=
  spaceDecidableAdv_TO_HTN_TR.mono SynClass.sub_TO_HTN_AC_TO_HTN_TR

/-- The same for totally ordered regular descriptions. -/
theorem spaceDecidableAdv_TO_HTN_REG : SpaceDecidableAdv codingSer SynClass.TO_HTN_REG :=
  spaceDecidableAdv_TO_HTN_TR.mono SynClass.sub_TO_HTN_REG_TO_HTN_TR

end Space

end HTN
