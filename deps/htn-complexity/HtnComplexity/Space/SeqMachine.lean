import HtnComplexity.Space.SeqSem7
/-!
# The machine for totally ordered instances with an initial task network

The machine of `HtnComplexity/Space/InstMachine.lean` with the initial and accepting tests
replaced by `HTN.Space.SeqM.seqInitB` and `HTN.Space.SeqM.seqAccB`: the first configuration is
*guessed* (it is the compiled initial state of the gadget instance, with rank witnesses) and
checked locally against the code of the instance and the two marker rows of the advice; the run
then steps through the action table given as advice, exactly as before.

* `HTN.Space.SeqM.seqMachine_sound` — an accepting run gives a configuration satisfying
  `InitOk d q`, with facts of at most `seqBnd d q` bits, from which the table (without the marker
  rows) reaches the goal `seqGoal d q`;
* `HTN.Space.SeqM.seqMachine_complete` — if the table reaches the goal from the canonical
  configuration, the machine accepts.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-- The two arguments, a separator and 32 more bits. -/
def padBF (i j : ℕ) : Fn := fun args => padF i j args ++ List.replicate 32 false

/-- A string of length the cube of the length of `padBF`. -/
def cubeBF (i j : ℕ) : Fn := fun args => List.replicate ((padBF i j args).length ^ 3) false

theorem length_cubeBF (i j : ℕ) (args : Args) :
    (cubeBF i j args).length = ((args.getD i []).length + (args.getD j []).length + 33) ^ 3 := by
  simp [cubeBF, padBF, length_padF]

theorem cobham_padBF (i j : ℕ) : Cobham (padBF i j) :=
  (cobham_app (cobham_padF i j) (cobham_const (List.replicate 32 false))).of_eq' fun _ => rfl

theorem cobham_cubeBF (i j : ℕ) : Cobham (cubeBF i j) := by
  have h2 : Cobham fun args =>
      List.replicate ((padBF i j args).length * (padBF i j args).length) false :=
    (cobham_c2 Cobham.smash (cobham_padBF i j) (cobham_padBF i j)).of_eq' fun args => by
      simp [compFn, smashFn, proj]
  refine (cobham_c2 Cobham.smash h2 (cobham_padBF i j)).of_eq' fun args => ?_
  simp only [compFn, smashFn, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.length_replicate, cubeBF]
  congr 1
  ring

/-- **The machine for totally ordered instances with an initial task network.** -/
noncomputable def seqMachine : NSpace where
  initB := fun args =>
    wfB (args.getD 0 []) (cubeBF 1 2 args) &&
      seqInitB (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])
  stepB := fun args =>
    wfB (args.getD 0 []) (cubeBF 2 3 args) &&
      stepCoreB (args.getD 3 []) (args.getD 1 []) (args.getD 0 [])
  accB := fun args => seqAccB (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])
  cobham_initB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeBF 1 2)).and
      (cobhamB_seqInitB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2))).of_eq fun args => by
        simp [proj]
  cobham_stepB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeBF 2 3)).and
      (cobhamB_stepCoreB (Cobham.proj 3) (Cobham.proj 1) (Cobham.proj 0))).of_eq
        fun args => by simp [proj]
  cobham_accB :=
    (cobhamB_seqAccB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)).of_eq
      fun args => by simp [proj]
  bound := (Polynomial.X + 33) ^ 3
  initB_length := by
    intro c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_cubeBF] at hlen
    simpa using hlen
  stepB_length := by
    intro c' c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_cubeBF] at hlen
    simpa using hlen

theorem seqMachine_initB_iff (c x a : List Bool) :
    seqMachine.initB [c, x, a] = true ↔
      wfB c (cubeBF 1 2 [c, x, a]) = true ∧ seqInitB c x a = true := by
  simp [seqMachine, Bool.and_eq_true]

theorem seqMachine_stepB_iff (c' c x a : List Bool) :
    seqMachine.stepB [c', c, x, a] = true ↔
      wfB c' (cubeBF 2 3 [c', c, x, a]) = true ∧ stepCoreB a c c' = true := by
  simp [seqMachine, Bool.and_eq_true]

theorem seqMachine_accB_iff (c x a : List Bool) :
    seqMachine.accB [c, x, a] = true ↔ seqAccB c x a = true := Iff.rfl

theorem seq_reach_decode {tbl : List Row} {b : Bool} {x : List Bool} {S₀ : List (List Bool)}
    (hS₀ : ∀ w ∈ S₀, IsCanon w) {c : List Bool}
    (h : seqMachine.Reach x (tblAdv b tbl) (blist S₀) c) :
    ∃ S, c = blist S ∧ (∀ w ∈ S, IsCanon w) ∧ ReachTbl tbl (decSt S₀) (decSt S) := by
  induction h with
  | refl => exact ⟨S₀, rfl, hS₀, Relation.ReflTransGen.refl⟩
  | @tail c c' _ hstep ih =>
    obtain ⟨S, rfl, hS, hreach⟩ := ih
    rw [NSpace.Step, seqMachine_stepB_iff] at hstep
    obtain ⟨hwf, hstepC⟩ := hstep
    obtain ⟨S', rfl, hS', -⟩ := wfB_iff.1 hwf
    exact ⟨S', rfl, hS', hreach.tail ((stepCoreB_iff hS hS' b).1 hstepC)⟩

/-- **Soundness of the machine.** -/
theorem seqMachine_sound {d : DomDesc} {K : ℕ} {q : InstDesc} {b : Bool} {T : List Row}
    (hK : (instSer q).length ≤ K)
    (h : seqMachine.Accepts (instSer q) (tblAdv b (markRows d K ++ T))) :
    b = true ∧ ∃ S, InitOk d q S ∧ (∀ f ∈ S, (bitsOfNat f).length ≤ seqBnd d q) ∧
      SolvableTbl T S (seqGoal d q) := by
  obtain ⟨c₀, c, hinit, hreach, hacc⟩ := h
  rw [seqMachine_initB_iff] at hinit
  obtain ⟨S₀, rfl, hS₀, -⟩ := wfB_iff.1 hinit.1
  have hI := initOk_of_seqInitB hS₀ hK hinit.2
  have hB := bits_le_of_seqInitB hS₀ hK hinit.2
  obtain ⟨S, rfl, hS, hreachTbl⟩ := seq_reach_decode hS₀ hreach
  rw [seqMachine_accB_iff, seqAccB_iff hS d] at hacc
  obtain ⟨hb, hgoal⟩ := hacc
  exact ⟨hb, decSt S₀, hI, hB, solvableTbl_markRows.1 ⟨decSt S, hreachTbl, hgoal⟩⟩

/-- **Completeness of the machine.** -/
theorem seqMachine_complete {d : DomDesc} {K : ℕ} {q : InstDesc} {T : List Row}
    (hq : q.IsTO) (hK : (instSer q).length ≤ K) {xs : List (ℕ ⊕ ℕ)}
    (hx : WitSeq q.tnI (canonWit q.tnI) xs)
    (hsolv : SolvableTbl T (canonCfg d q xs) (seqGoal d q)) :
    seqMachine.Accepts (instSer q) (tblAdv true (markRows d K ++ T)) := by
  set tbl := markRows d K ++ T with htbl
  set x := instSer q with hx'
  set a := tblAdv true tbl with ha
  set s := canonCfg d q xs with hs
  have hsnd : s.Nodup := List.nodup_dedup _
  obtain ⟨sf, hreach, hgoal⟩ := solvableTbl_markRows.2 hsolv
  set B := s ++ addFacts tbl with hB
  obtain ⟨t, hsmall, hnd, hsub, hmem⟩ :=
    exists_smallReach (B := B) hreach (u' := s) (fun f => Iff.rfl) hsnd
      (fun f hf => List.mem_append_left _ hf)
      (fun f hf => List.mem_append_right _ hf)
  set n := x.length + a.length with hn
  have hinitB : seqInitB (blist (s.map bitsOfNat)) x a = true := canon_seqInitB hq hx hK true T
  have hBlen : B.length ≤ 6 * n + 3 := by
    have h1 : s.length ≤ 5 * x.length + 3 := length_canonCfg_le hx
    have h2 : (addFacts tbl).length ≤ a.length := length_addFacts_le_tblAdv
    simp only [hB, List.length_append]
    omega
  have hBbits : ∀ f ∈ B, (bitsOfNat f).length ≤ 2 * n + 10 := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · have h1 : (bitsOfNat f).length ≤ 2 * x.length + (bitsOfNat (cRoot d)).length + 10 :=
        bits_le_of_seqInitB (canon_map_bitsOfNat s) hK hinitB f
          (by rw [decSt_map_bitsOfNat]; exact hf)
      have h2 : (bitsOfNat (cRoot d)).length ≤ a.length := length_bitsOfNat_cRoot_le d K true T
      omega
    · have h1 : (bitsOfNat f).length ≤ a.length := length_bitsOfNat_le_tblAdv hf
      omega
  have hconf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
      (encState S).length ≤ (n + 33) ^ 3 := by
    intro S hnodup hsubS
    have hl : S.length ≤ 6 * n + 3 := le_trans (length_le_of_nodup_subset hnodup hsubS) hBlen
    have h := length_blist_le (l := S.map bitsOfNat) (N := 6 * n + 3) (K := 2 * n + 10)
      (by simpa using hl)
      (by
        intro y hy
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
        exact hBbits f (hsubS f hf))
    rw [encState]
    nlinarith [h, Nat.zero_le n]
  have hwf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
      wfB (encState S) (cubeBF 2 3 [encState S, encState S, x, a]) = true := by
    intro S hnodup hsubS
    refine wfB_iff.2 ⟨S.map bitsOfNat, rfl, canon_map_bitsOfNat S, ?_⟩
    rw [length_cubeBF]
    simpa using hconf S hnodup hsubS
  have hrun : ∀ u v : List ℕ, SmallReach tbl B u v → u.Nodup → (∀ f ∈ u, f ∈ B) →
      seqMachine.Reach x a (encState u) (encState v) := by
    intro u v hsr
    induction hsr with
    | refl => exact fun _ _ => Relation.ReflTransGen.refl
    | @tail w v _ hstep ih =>
      intro hnodup hsubS
      refine (ih hnodup hsubS).tail ?_
      rw [NSpace.Step, seqMachine_stepB_iff]
      refine ⟨?_, ?_⟩
      · have := hwf v hstep.2.1 hstep.2.2
        simpa [encState] using this
      · rw [ha, encState, encState]
        exact (stepCoreB_iff (canon_map_bitsOfNat w) (canon_map_bitsOfNat v) true).2 (by
          simpa [decSt_map_bitsOfNat] using hstep.1)
  refine ⟨encState s, encState t, ?_, ?_, ?_⟩
  · rw [seqMachine_initB_iff]
    refine ⟨?_, hinitB⟩
    refine wfB_iff.2 ⟨s.map bitsOfNat, rfl, canon_map_bitsOfNat _, ?_⟩
    rw [length_cubeBF]
    have := hconf s hsnd (fun f hf => List.mem_append_left _ hf)
    simpa [encState] using this
  · exact hrun _ _ hsmall hsnd (fun f hf => List.mem_append_left _ hf)
  · rw [seqMachine_accB_iff, encState]
    refine (seqAccB_iff (canon_map_bitsOfNat _) d q true tbl).2 ⟨rfl, ?_⟩
    intro f hf
    rw [decSt_map_bitsOfNat]
    exact (hmem f).2 (hgoal f hf)

end SeqM

end Space

end HTN
