import HtnComplexity.Space.AltSeqTbl
/-!
# The alternating machine for totally ordered instances with an initial task network

The alternating machine `HTN.Space.altMachine` with its initial test replaced: the first state
`A` is *guessed* and checked by `HTN.Space.SeqM.seqInitB` (it is the compiled initial state of
the sequencing gadget instance, with rank witnesses, checked locally against the code of the
instance and the marker rows of the advice), and the target state `B` must pass
`HTN.Space.SeqM.seqAccB` (it contains the goal of the gadget instance).  The steps are those of
`altMachine`, so its correctness proofs (`HTN.Space.acc_sound`, `HTN.Space.acc_complete`) are
reused verbatim.

* `HTN.Space.altSeq_sound` — an accepting run gives a configuration satisfying `InitOk d q`,
  with facts of at most `seqBnd d q` bits, from which the table with calls reaches the goal;
* `HTN.Space.altSeq_complete` — if the table (with at least `4|x| + 10` rows) reaches the goal
  from the canonical configuration, the machine accepts.
-/

namespace HTN

namespace Space

open Syn PTime SeqG SeqM

/-- **The alternating machine for totally ordered instances with an initial task network.** -/
noncomputable def altSeqMachine : AltSpace where
  k := 5
  initB := fun args =>
    decide (args.getD 2 [] = tE) && decide (args.getD 3 [] = []) && decide (args.getD 6 [] = []) &&
      wfB (args.getD 4 []) (cubeF 0 1 args) && wfB (args.getD 5 []) (cubeF 0 1 args) &&
      seqInitB (args.getD 4 []) (args.getD 0 []) (args.getD 1 []) &&
      seqAccB (args.getD 5 []) (args.getD 0 []) (args.getD 1 [])
  accB := altMachine.accB
  univB := altMachine.univB
  stepB := altMachine.stepB
  cobham_initB :=
    ((((((cb_eqc 2 tE).and (cb_eqc 3 [])).and (cb_eqc 6 [])).and (cb_wf 4)).and (cb_wf 5)).and
      (cobhamB_seqInitB (Cobham.proj 4) (Cobham.proj 0) (Cobham.proj 1))).and
      (cobhamB_seqAccB (Cobham.proj 5) (Cobham.proj 0) (Cobham.proj 1)) |>.of_eq
      fun args => by simp [proj]
  cobham_accB := altMachine.cobham_accB
  cobham_univB := altMachine.cobham_univB
  cobham_stepB := altMachine.cobham_stepB
  bound := (Polynomial.X + 2) ^ 3
  initB_length := by
    intro x a c hc h w hw
    match c, hc with
    | [tg, u, A, B, C], _ =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, Bool.and_eq_true,
        decide_eq_true_eq, cubeF_cons] at h
      obtain ⟨⟨⟨⟨⟨⟨htg, hu⟩, hC⟩, hA⟩, hB⟩, -⟩, -⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact small_le_bound x a (Or.inl (by rw [htg]; simp [tE]))
      · exact small_le_bound x a (Or.inl (by rw [hu]; simp))
      · exact (length_le_of_wfB hA).trans (cube_le_bound x a)
      · exact (length_le_of_wfB hB).trans (cube_le_bound x a)
      · exact small_le_bound x a (Or.inl (by rw [hC]; simp))
  stepB_length := altMachine.stepB_length

theorem altSeq_acc_to {x a : List Bool} {c : Args} (h : altSeqMachine.Acc x a c) :
    altMachine.Acc x a c := by
  induction h with
  | acc hc hacc => exact AltSpace.Acc.acc hc hacc
  | univ hc hu _ ih => exact AltSpace.Acc.univ hc hu fun c' hc' hs => ih c' hc' hs
  | ex hc hu hc' hs _ ih => exact AltSpace.Acc.ex hc hu hc' hs ih

theorem altSeq_acc_of {x a : List Bool} {c : Args} (h : altMachine.Acc x a c) :
    altSeqMachine.Acc x a c := by
  induction h with
  | acc hc hacc => exact AltSpace.Acc.acc hc hacc
  | univ hc hu _ ih => exact AltSpace.Acc.univ hc hu fun c' hc' hs => ih c' hc' hs
  | ex hc hu hc' hs _ ih => exact AltSpace.Acc.ex hc hu hc' hs ih

theorem altSeq_init_iff (x a tg u A B C : List Bool) :
    altSeqMachine.initB (x :: a :: [tg, u, A, B, C]) = true ↔
      tg = tE ∧ u = [] ∧ C = [] ∧ WfC x a A ∧ WfC x a B ∧ seqInitB A x a = true ∧
        seqAccB B x a = true := by
  show (decide _ && decide _ && decide _ && wfB _ _ && wfB _ _ && seqInitB _ _ _ &&
    seqAccB _ _ _) = true ↔ _
  simp only [List.getD_cons_succ, List.getD_cons_zero, cubeF_cons, Bool.and_eq_true,
    decide_eq_true_eq, WfC]
  tauto

/-- **Soundness of the alternating machine.** -/
theorem altSeq_sound {d : DomDesc} {K : ℕ} {q : InstDesc} {T : List Row}
    (hK : (instSer q).length ≤ K)
    (h : altSeqMachine.Accepts (instSer q) (tblAdv true (markRows d K ++ T))) :
    ∃ S, InitOk d q S ∧ (∀ f ∈ S, (bitsOfNat f).length ≤ seqBnd d q) ∧
      ASolvable kPush kRet (markRows d K ++ T) {f | f ∈ S} {f | f ∈ seqGoal d q} := by
  obtain ⟨c, hc, hinit, hacc⟩ := h
  obtain ⟨tg, u, A, B, C, rfl⟩ := length_five hc
  obtain ⟨rfl, rfl, rfl, hA, hB, hini, hgoal⟩ := (altSeq_init_iff _ _ _ _ _ _ _).1 hinit
  obtain ⟨S, rfl, hS⟩ := exists_of_wfC hA
  obtain ⟨S', rfl, hS'⟩ := exists_of_wfC hB
  have hreach := (acc_sound (altSeq_acc_to hacc)).1 [] S S' [] rfl hA hB
  have hI := initOk_of_seqInitB hS hK hini
  have hbits := bits_le_of_seqInitB hS hK hini
  obtain ⟨-, hg⟩ := (seqAccB_iff hS' d q true _).1 hgoal
  exact ⟨decSt S, hI, hbits, dset S', hreach, fun f hf => hg f hf⟩

/-- **Completeness of the alternating machine.** -/
theorem altSeq_complete {d : DomDesc} {K : ℕ} {q : InstDesc} {T : List Row} (hq : q.IsTO)
    (hK : (instSer q).length ≤ K) {xs : List (ℕ ⊕ ℕ)} (hx : WitSeq q.tnI (canonWit q.tnI) xs)
    (hpad : 4 * (instSer q).length + 10 ≤ (markRows d K ++ T).length)
    (hsolv : ASolvable kPush kRet (markRows d K ++ T) {f | f ∈ canonCfg d q xs}
      {f | f ∈ seqGoal d q}) :
    altSeqMachine.Accepts (instSer q) (tblAdv true (markRows d K ++ T)) := by
  set tbl := markRows d K ++ T with htbl
  set x := instSer q with hx'
  set a := tblAdv true tbl with ha
  set s := canonCfg d q xs with hs
  set Bl := s ++ addFacts tbl with hBl
  have hinitB : seqInitB (blist (s.map bitsOfNat)) x a = true := canon_seqInitB hq hx hK true T
  have hsplit := length_tblAdv_split true tbl
  have hI := length_le_idEnts tbl
  have hF := length_addFacts_le_factEnts tbl
  have hC : (bitsOfNat (cRoot d)).length ≤ (blist (factEnts tbl)).length :=
    length_bitsOfNat_cRoot_le_factEnts d K T
  have hslen : s.length ≤ 5 * x.length + 3 := length_canonCfg_le hx
  have hlen : Bl.length ≤ x.length + a.length := by
    simp only [hBl, List.length_append]
    rw [← ha] at hsplit
    omega
  have hsbits : ∀ f ∈ s, (bitsOfNat f).length ≤ x.length + a.length := by
    intro f hf
    have h1 : (bitsOfNat f).length ≤ 2 * x.length + (bitsOfNat (cRoot d)).length + 10 :=
      bits_le_of_seqInitB (canon_map_bitsOfNat s) hK hinitB f
        (by rw [decSt_map_bitsOfNat]; exact hf)
    rw [← ha] at hsplit
    omega
  have hbits : ∀ f ∈ Bl, (bitsOfNat f).length ≤ x.length + a.length := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · exact hsbits f hf
    · have h1 := length_bitsOfNat_le_factEnts hf
      rw [← ha] at hsplit
      omega
  have hadd : ∀ f ∈ addFacts tbl, f ∈ Bl := fun f hf => List.mem_append_right _ hf
  obtain ⟨s', hreach, hgoal⟩ := hsolv
  have hs0 : {f | f ∈ s} ⊆ {f | f ∈ Bl} := fun f hf => List.mem_append_left _ hf
  have hs' : s' ⊆ {f | f ∈ Bl} := by
    intro f hf
    rcases hreach.subset_union_adds hf with hf | hf
    · exact hs0 hf
    · exact hadd f hf
  have hW0 : WfC x a (blist (s.map bitsOfNat)) := by
    refine wfB_iff.2 ⟨s.map bitsOfNat, rfl, canon_map_bitsOfNat _, ?_⟩
    rw [length_cubeF]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have := length_encState_le_cube (S := s) (le_trans (by simp [hBl]) hlen) hsbits
    simpa [encState] using this
  have hW' := wfC_rep (tbl := tbl) (x := x) hlen hbits s'
  have hd0 : dset (s.map bitsOfNat) = {f | f ∈ s} := by
    simp [dset, decSt_map_bitsOfNat]
  refine ⟨[tE, [], blist (s.map bitsOfNat), blist (rep Bl s'), []], rfl, ?_,
    altSeq_acc_of (acc_complete hlen hbits hadd hreach hs0 _ _ hW0 hW' hd0 (dset_rep hs'))⟩
  refine (altSeq_init_iff _ _ _ _ _ _ _).2 ⟨rfl, rfl, rfl, hW0, hW', hinitB, ?_⟩
  refine (seqAccB_iff (canon_rep _) d q true tbl).2 ⟨rfl, fun f hf => ?_⟩
  have := dset_rep (Bl := Bl) hs'
  have hf' : f ∈ s' := hgoal hf
  rw [← this] at hf'
  exact hf'

end Space

end HTN
