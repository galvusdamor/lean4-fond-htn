import HtnComplexity.Space.ThrTestsSem5
import HtnComplexity.Space.SeqMachine
/-!
# The thread machine

Layer (D) of the planner P-REG (`NOTES.md` §64–67).  The machine of
`HtnComplexity/Space/SeqMachine.lean` with the initial and accepting tests replaced by
`HTN.Space.Thr.thrInitB` and `HTN.Space.Thr.thrAccB`, and the space bound raised to
`(n + 33)^4` (the canonical configuration has quadratically many facts: the `cl` and `nc`
entries).

* `HTN.Space.Thr.thrMachine_sound` — an accepting run gives a configuration satisfying
  `ThrInitOk d q` from which the table (without the marker rows) reaches the numbered goal;
* `HTN.Space.Thr.thrMachine_complete` — if the table reaches the numbered goal from the
  canonical configuration, the machine accepts.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-! ### The local conditions depend only on the set of facts -/

theorem ThrInitOk.congr {d : DomDesc} {q : InstDesc} {S S' : List ℕ} (h : ThrInitOk d q S)
    (hS : ∀ f, f ∈ S' ↔ f ∈ S) : ThrInitOk d q S' where
  shape f hf := h.shape f ((hS f).1 hf)
  inst v := by rw [hS]; exact h.inst v
  cur p := by rw [hS]; exact h.cur p
  fin := by rw [hS]; exact h.fin
  wit := h.wit.congr fun w => by
    obtain ⟨p, a⟩ := w
    rw [mem_witList, mem_witList, hS]
  lab p x := by simp only [hS]; exact h.lab p x
  nop p := by simp only [hS]; exact h.nop p
  len k := by simp only [hS]; exact h.len k
  edge x y := by simp only [hS]; exact h.edge x y
  cl1 x y := by simp only [hS]; exact h.cl1 x y
  cl2 x y z := by simp only [hS]; exact h.cl2 x y z
  nc x y := by simp only [hS]; exact h.nc x y
  clpos x y := by simp only [hS]; exact h.clpos x y
  ncpos x y := by simp only [hS]; exact h.ncpos x y

/-! ### The length of the canonical configuration -/

theorem length_initList_le (q : InstDesc) : q.initList.length ≤ (instSer q).length := by
  have := length_succ_le_length_blist (q.initList.map bitsOfNat)
  have hx := congrArg List.length (instSer_split q)
  simp only [List.length_append, List.length_map] at hx this
  omega

theorem length_ordList_le (q : InstDesc) : q.tnI.ordList.length ≤ (instSer q).length := by
  have := length_succ_le_length_blist (q.tnI.ordList.map serPair)
  have hx := congrArg List.length (instSer_split q)
  simp only [List.length_append, List.length_map] at hx this
  omega

theorem length_allL_le_code (q : InstDesc) : (allL q.tnI).length ≤ 2 * (instSer q).length :=
  length_allL_le.trans (length_wnodes_le q)

theorem length_canonR_le (q : InstDesc) : (canonR q.tnI).length ≤ (allL q.tnI).length := by
  have := List.length_filterMap_le (fun p => (allL q.tnI)[p]?.map (p, ·))
    (List.range (allL q.tnI).length)
  simpa [canonR] using this

open Classical in
/-- **The canonical configuration has quadratically many facts.** -/
theorem length_canonS_le (d : DomDesc) (q : InstDesc) :
    (canonS d q).length ≤ 8 * (instSer q).length ^ 2 + 8 * (instSer q).length + 2 := by
  have hA : (allL q.tnI).length ≤ 2 * (instSer q).length := length_allL_le_code q
  have hR : (canonR q.tnI).length ≤ (allL q.tnI).length := length_canonR_le q
  have hI := length_initList_le q
  have hO := length_ordList_le q
  have hN : nIds q ≤ (allL q.tnI).length := nIds_le_allL
  have h1 := List.length_filter_le (fun w : ℕ × ℕ => decide (w.2 ∈ q.tnI.ids)) (canonR q.tnI)
  have h2 := List.length_filter_le (fun w : ℕ × ℕ => decide (w.2 ∈ q.tnI.ids) &&
    unknownPrimB d (q.tnI.label w.2)) (canonR q.tnI)
  have h3 := List.length_filter_le (fun p : ℕ × ℕ => decide (Relation.TransGen (cE q) p.1 p.2))
    (List.range (allL q.tnI).length ×ˢ List.range (allL q.tnI).length)
  have h4 := List.length_filter_le (fun p : ℕ × ℕ => decide (¬ Relation.TransGen (cE q) p.1 p.2))
    (List.range (nIds q) ×ˢ List.range (nIds q))
  simp only [List.length_product, List.length_range] at h3 h4
  have hAA : (allL q.tnI).length * (allL q.tnI).length ≤ 4 * (instSer q).length ^ 2 := by
    nlinarith
  have hNN : nIds q * nIds q ≤ 4 * (instSer q).length ^ 2 := by nlinarith
  simp only [canonS, List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

/-! ### The machine -/

/-- A string of length the fourth power of the length of `padBF`. -/
def quartBF (i j : ℕ) : Fn := fun args => List.replicate ((padBF i j args).length ^ 4) false

theorem length_quartBF (i j : ℕ) (args : Args) :
    (quartBF i j args).length = ((args.getD i []).length + (args.getD j []).length + 33) ^ 4 := by
  simp [quartBF, padBF, length_padF]

theorem cobham_quartBF (i j : ℕ) : Cobham (quartBF i j) := by
  have h2 : Cobham fun args =>
      List.replicate ((padBF i j args).length * (padBF i j args).length) false :=
    (cobham_c2 Cobham.smash (cobham_padBF i j) (cobham_padBF i j)).of_eq' fun args => by
      simp [compFn, smashFn]
  refine (cobham_c2 Cobham.smash h2 h2).of_eq' fun args => ?_
  simp only [compFn, smashFn, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.length_replicate, quartBF]
  congr 1
  ring

/-- **The thread machine.** -/
noncomputable def thrMachine : NSpace where
  initB := fun args =>
    wfB (args.getD 0 []) (quartBF 1 2 args) &&
      thrInitB (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])
  stepB := fun args =>
    wfB (args.getD 0 []) (quartBF 2 3 args) &&
      stepCoreB (args.getD 3 []) (args.getD 1 []) (args.getD 0 [])
  accB := fun args => thrAccB (args.getD 0 []) (args.getD 1 [])
  cobham_initB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_quartBF 1 2)).and
      (cobhamB_thrInitB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2))).of_eq fun args => by
        simp [proj]
  cobham_stepB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_quartBF 2 3)).and
      (cobhamB_stepCoreB (Cobham.proj 3) (Cobham.proj 1) (Cobham.proj 0))).of_eq
        fun args => by simp [proj]
  cobham_accB :=
    (cobhamB_thrAccB (Cobham.proj 0) (Cobham.proj 1)).of_eq fun args => by simp [proj]
  bound := (Polynomial.X + 33) ^ 4
  initB_length := by
    intro c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_quartBF] at hlen
    simpa using hlen
  stepB_length := by
    intro c' c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_quartBF] at hlen
    simpa using hlen

theorem thrMachine_initB_iff (c x a : List Bool) :
    thrMachine.initB [c, x, a] = true ↔
      wfB c (quartBF 1 2 [c, x, a]) = true ∧ thrInitB c x a = true := by
  simp [thrMachine, Bool.and_eq_true]

theorem thrMachine_stepB_iff (c' c x a : List Bool) :
    thrMachine.stepB [c', c, x, a] = true ↔
      wfB c' (quartBF 2 3 [c', c, x, a]) = true ∧ stepCoreB a c c' = true := by
  simp [thrMachine, Bool.and_eq_true]

theorem thrMachine_accB_iff (c x a : List Bool) :
    thrMachine.accB [c, x, a] = true ↔ thrAccB c x = true := Iff.rfl

theorem thr_reach_decode {tbl : List Row} {b : Bool} {x : List Bool} {S₀ : List (List Bool)}
    (hS₀ : ∀ w ∈ S₀, IsCanon w) {c : List Bool}
    (h : thrMachine.Reach x (tblAdv b tbl) (blist S₀) c) :
    ∃ S, c = blist S ∧ (∀ w ∈ S, IsCanon w) ∧ ReachTbl tbl (decSt S₀) (decSt S) := by
  induction h with
  | refl => exact ⟨S₀, rfl, hS₀, Relation.ReflTransGen.refl⟩
  | @tail c c' _ hstep ih =>
    obtain ⟨S, rfl, hS, hreach⟩ := ih
    rw [NSpace.Step, thrMachine_stepB_iff] at hstep
    obtain ⟨hwf, hstepC⟩ := hstep
    obtain ⟨S', rfl, hS', -⟩ := wfB_iff.1 hwf
    exact ⟨S', rfl, hS', hreach.tail ((stepCoreB_iff hS hS' b).1 hstepC)⟩

/-- **Soundness of the thread machine.** -/
theorem thrMachine_sound {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row}
    (hK : (instSer q).length ≤ K)
    (h : thrMachine.Accepts (instSer q) (tblAdv b (markRows d K ++ T))) :
    ∃ S, ThrInitOk d q S ∧ SolvableTbl T S ((goalF q.goalList).map enc) := by
  obtain ⟨c₀, c, hinit, hreach, hacc⟩ := h
  rw [thrMachine_initB_iff] at hinit
  obtain ⟨S₀, rfl, hS₀, -⟩ := wfB_iff.1 hinit.1
  have hI := thrInitOk_of_thrInitB hS₀ hK hinit.2
  obtain ⟨S, rfl, hS, hreachTbl⟩ := thr_reach_decode hS₀ hreach
  rw [thrMachine_accB_iff, thrAccB_iff hS] at hacc
  exact ⟨decSt S₀, hI, solvableTbl_markRows.1 ⟨decSt S, hreachTbl, hacc⟩⟩

/-- **Completeness of the thread machine.** -/
theorem thrMachine_complete {d : DomDesc} {K : ℕ} {q : InstDesc} {T : List Row}
    (hK : (instSer q).length ≤ K)
    (hsolv : SolvableTbl T (canonS d q).dedup ((goalF q.goalList).map enc)) :
    thrMachine.Accepts (instSer q) (tblAdv true (markRows d K ++ T)) := by
  set tbl := markRows d K ++ T with htbl
  set x := instSer q with hx'
  set a := tblAdv true tbl with ha
  set s := (canonS d q).dedup with hs
  have hsnd : s.Nodup := List.nodup_dedup _
  obtain ⟨sf, hreach, hgoal⟩ := solvableTbl_markRows.2 hsolv
  set B := s ++ addFacts tbl with hB
  obtain ⟨t, hsmall, hnd, hsub, hmem⟩ :=
    exists_smallReach (B := B) hreach (u' := s) (fun f => Iff.rfl) hsnd
      (fun f hf => List.mem_append_left _ hf)
      (fun f hf => List.mem_append_right _ hf)
  set n := x.length + a.length with hn
  have hsI : ThrInitOk d q s :=
    ThrInitOk.congr initOk_canonS fun f => List.mem_dedup
  have hinitB : thrInitB (blist (s.map bitsOfNat)) x a = true := by
    refine thrInitB_of_thrInitOk (canon_map_bitsOfNat s) hK ?_
    rw [decSt_map_bitsOfNat]; exact hsI
  have hBlen : B.length ≤ 8 * n ^ 2 + 9 * n + 2 := by
    have h1 : s.length ≤ 8 * x.length ^ 2 + 8 * x.length + 2 :=
      (List.dedup_sublist _).length_le.trans (length_canonS_le d q)
    have h2 : (addFacts tbl).length ≤ a.length := length_addFacts_le_tblAdv
    have h3 : x.length ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simp only [hB, List.length_append]
    omega
  have hBbits : ∀ f ∈ B, (bitsOfNat f).length ≤ 4 * n + 10 := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · have h1 : (bitsOfNat f).length ≤ thrBnd q := bits_le_of_thrInitOk hsI f hf
      have hxl : (instSer q).length = x.length := rfl
      unfold thrBnd at h1
      omega
    · have h1 : (bitsOfNat f).length ≤ a.length := length_bitsOfNat_le_tblAdv hf
      omega
  have hconf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
      (encState S).length ≤ (n + 33) ^ 4 := by
    intro S hnodup hsubS
    have hl : S.length ≤ 8 * n ^ 2 + 9 * n + 2 :=
      le_trans (length_le_of_nodup_subset hnodup hsubS) hBlen
    have h := length_blist_le (l := S.map bitsOfNat) (N := 8 * n ^ 2 + 9 * n + 2)
      (K := 4 * n + 10) (by simpa using hl)
      (by
        intro y hy
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
        exact hBbits f (hsubS f hf))
    rw [encState]
    nlinarith [h, Nat.zero_le n]
  have hwf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
      wfB (encState S) (quartBF 2 3 [encState S, encState S, x, a]) = true := by
    intro S hnodup hsubS
    refine wfB_iff.2 ⟨S.map bitsOfNat, rfl, canon_map_bitsOfNat S, ?_⟩
    rw [length_quartBF]
    simpa using hconf S hnodup hsubS
  have hrun : ∀ u v : List ℕ, SmallReach tbl B u v → u.Nodup → (∀ f ∈ u, f ∈ B) →
      thrMachine.Reach x a (encState u) (encState v) := by
    intro u v hsr
    induction hsr with
    | refl => exact fun _ _ => Relation.ReflTransGen.refl
    | @tail w v _ hstep ih =>
      intro hnodup hsubS
      refine (ih hnodup hsubS).tail ?_
      rw [NSpace.Step, thrMachine_stepB_iff]
      refine ⟨?_, ?_⟩
      · have := hwf v hstep.2.1 hstep.2.2
        simpa [encState] using this
      · rw [ha, encState, encState]
        exact (stepCoreB_iff (canon_map_bitsOfNat w) (canon_map_bitsOfNat v) true).2 (by
          simpa [decSt_map_bitsOfNat] using hstep.1)
  refine ⟨encState s, encState t, ?_, ?_, ?_⟩
  · rw [thrMachine_initB_iff]
    refine ⟨?_, hinitB⟩
    refine wfB_iff.2 ⟨s.map bitsOfNat, rfl, canon_map_bitsOfNat _, ?_⟩
    rw [length_quartBF]
    have := hconf s hsnd (fun f hf => List.mem_append_left _ hf)
    simpa [encState] using this
  · exact hrun _ _ hsmall hsnd (fun f hf => List.mem_append_left _ hf)
  · rw [thrMachine_accB_iff, encState]
    refine (thrAccB_iff (canon_map_bitsOfNat _) q).2 ?_
    intro f hf
    rw [decSt_map_bitsOfNat]
    exact (hmem f).2 (hgoal f hf)

end Thr

end Space

end HTN
