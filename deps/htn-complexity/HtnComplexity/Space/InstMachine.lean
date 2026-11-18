import HtnComplexity.Space.TblMachine
import HtnComplexity.Space.InstTests
/-!
# The target-side machine, reading the code of the instance

`HtnComplexity/Space/TblMachine.lean` builds a nondeterministic polynomial-space machine
that decides reachability in an action table given as advice, its input being the initial state
and the goal written out as `HTN.Space.encProblem`.  For the target side of Table 3 the input is
the **code of an instance description**, and the table problem is the compiled one.  This file
repeats the construction with the two tests of `HtnComplexity/Space/InstTests.lean` in place
of `HTN.Space.initCoreB` and `HTN.Space.accCoreB`, so that no translation of the input has to be
computed at all:

    HTN.Space.instMachine_accepts_iff :
      instMachine.Accepts (instSer q) (tblAdv b tbl)
        ↔ (b = true ∧ SolvableTbl tbl (regInitR q) (regGoalR q))

`HTN.Space.instSolver` packages it with the length bound on the advice, in the shape the bridge
of `HtnCompilability/Space/RegSpace.lean` consumes.  As in `TblMachine.lean`, **nothing is
assumed about the cost of computing the table**: it is advice, and only its length is
constrained.
-/

namespace HTN

namespace Space

open Syn PTime

/-- **The machine that decides reachability in an action table given as advice, reading the
compiled problem off the code of an instance description.** -/
noncomputable def instMachine : NSpace where
  initB := fun args =>
    wfB (args.getD 0 []) (cubeF 1 2 args) && initCoreR (args.getD 0 []) (args.getD 1 [])
  stepB := fun args =>
    wfB (args.getD 0 []) (cubeF 2 3 args) &&
      stepCoreB (args.getD 3 []) (args.getD 1 []) (args.getD 0 [])
  accB := fun args => accCoreR (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])
  cobham_initB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeF 1 2)).and
      (cobhamB_initCoreR (Cobham.proj 0) (Cobham.proj 1))).of_eq fun args => by simp [proj]
  cobham_stepB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeF 2 3)).and
      (cobhamB_stepCoreB (Cobham.proj 3) (Cobham.proj 1) (Cobham.proj 0))).of_eq
        fun args => by simp [proj]
  cobham_accB :=
    (cobhamB_accCoreR (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)).of_eq
      fun args => by simp [proj]
  bound := (Polynomial.X + 1) ^ 3
  initB_length := by
    intro c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_cubeF] at hlen
    simpa using hlen
  stepB_length := by
    intro c' c x a h
    rw [Bool.and_eq_true] at h
    obtain ⟨S, -, -, hlen⟩ := wfB_iff.1 h.1
    rw [length_cubeF] at hlen
    simpa using hlen

theorem instMachine_initB_iff (c x a : List Bool) :
    instMachine.initB [c, x, a] = true ↔
      wfB c (cubeF 1 2 [c, x, a]) = true ∧ initCoreR c x = true := by
  simp [instMachine, Bool.and_eq_true]

theorem instMachine_stepB_iff (c' c x a : List Bool) :
    instMachine.stepB [c', c, x, a] = true ↔
      wfB c' (cubeF 2 3 [c', c, x, a]) = true ∧ stepCoreB a c c' = true := by
  simp [instMachine, Bool.and_eq_true]

theorem instMachine_accB_iff (c x a : List Bool) :
    instMachine.accB [c, x, a] = true ↔ accCoreR c x a = true := Iff.rfl

/-- Every configuration a run of the machine visits is a serialised list of canonical numerals,
and the state it carries is reachable from the state the first configuration carries. -/
theorem inst_reach_decode {tbl : List Row} {b : Bool} {x : List Bool} {S₀ : List (List Bool)}
    (hS₀ : ∀ w ∈ S₀, IsCanon w) {c : List Bool}
    (h : instMachine.Reach x (tblAdv b tbl) (blist S₀) c) :
    ∃ S, c = blist S ∧ (∀ w ∈ S, IsCanon w) ∧ ReachTbl tbl (decSt S₀) (decSt S) := by
  induction h with
  | refl => exact ⟨S₀, rfl, hS₀, Relation.ReflTransGen.refl⟩
  | @tail c c' _ hstep ih =>
    obtain ⟨S, rfl, hS, hreach⟩ := ih
    rw [NSpace.Step, instMachine_stepB_iff] at hstep
    obtain ⟨hwf, hstepC⟩ := hstep
    obtain ⟨S', rfl, hS', -⟩ := wfB_iff.1 hwf
    exact ⟨S', rfl, hS', hreach.tail ((stepCoreB_iff hS hS' b).1 hstepC)⟩

/-- **The machine accepts exactly the instances whose compiled problem is solvable.** -/
theorem instMachine_accepts_iff (b : Bool) (tbl : List Row) (q : InstDesc) :
    instMachine.Accepts (instSer q) (tblAdv b tbl) ↔
      (b = true ∧ SolvableTbl tbl (regInitR q) (regGoalR q)) := by
  set x := instSer q with hx
  set a := tblAdv b tbl with ha
  set s := regInitR q with hs
  set g := regGoalR q with hg
  constructor
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    rw [instMachine_initB_iff] at hinit
    obtain ⟨S₀, rfl, hS₀, -⟩ := wfB_iff.1 hinit.1
    have hinit0 := (initCoreR_iff hS₀ q).1 hinit.2
    obtain ⟨S, rfl, hS, hreachTbl⟩ := inst_reach_decode hS₀ hreach
    rw [instMachine_accB_iff] at hacc
    obtain ⟨hb, hgoal⟩ := (accCoreR_iff hS q b tbl).1 hacc
    refine ⟨hb, ?_⟩
    obtain ⟨t, hreach', hmem⟩ := exists_run_of_congr hreachTbl (u' := s) fun f => (hinit0 f).symm
    exact ⟨t, hreach', fun f hf => (hmem f).2 (hgoal f hf)⟩
  · rintro ⟨rfl, hsolv⟩
    obtain ⟨sf, hreach, hgoal⟩ := hsolv
    set B := s ++ addFacts tbl with hB
    obtain ⟨t, hsmall, hnd, hsub, hmem⟩ :=
      exists_smallReach (B := B) hreach (u' := s.dedup) (fun f => by simp) (List.nodup_dedup _)
        (fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf))
        (fun f hf => List.mem_append_right _ hf)
    set n := x.length + a.length with hn
    have hBlen : B.length ≤ n := by
      have h1 : s.length ≤ x.length := length_regInitR_le q
      have h2 : (addFacts tbl).length ≤ a.length := length_addFacts_le_tblAdv
      simp only [hB, List.length_append]
      omega
    have hBbits : ∀ f ∈ B, (bitsOfNat f).length ≤ n := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · have h1 : (bitsOfNat f).length ≤ x.length := length_bitsOfNat_le_of_mem_regInitR hf
        omega
      · have h1 : (bitsOfNat f).length ≤ a.length := length_bitsOfNat_le_tblAdv hf
        omega
    have hconf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
        (encState S).length ≤ (n + 1) ^ 3 := by
      intro S hnodup hsubS
      refine length_encState_le_cube ?_ fun f hf => hBbits f (hsubS f hf)
      exact le_trans (length_le_of_nodup_subset hnodup hsubS) hBlen
    have hwf : ∀ S : List ℕ, S.Nodup → (∀ f ∈ S, f ∈ B) →
        wfB (encState S) (cubeF 2 3 [encState S, encState S, x, a]) = true := by
      intro S hnodup hsubS
      refine wfB_iff.2 ⟨S.map bitsOfNat, rfl, canon_map_bitsOfNat S, ?_⟩
      rw [length_cubeF]
      simpa using hconf S hnodup hsubS
    have hrun : ∀ u v : List ℕ, SmallReach tbl B u v → u.Nodup → (∀ f ∈ u, f ∈ B) →
        instMachine.Reach x a (encState u) (encState v) := by
      intro u v hsr
      induction hsr with
      | refl => exact fun _ _ => Relation.ReflTransGen.refl
      | @tail w v _ hstep ih =>
        intro hnodup hsubS
        refine (ih hnodup hsubS).tail ?_
        rw [NSpace.Step, instMachine_stepB_iff]
        refine ⟨?_, ?_⟩
        · have := hwf v hstep.2.1 hstep.2.2
          simpa [encState] using this
        · rw [ha, encState, encState]
          exact (stepCoreB_iff (canon_map_bitsOfNat w) (canon_map_bitsOfNat v) true).2 (by
            simpa [decSt_map_bitsOfNat] using hstep.1)
    refine ⟨encState s.dedup, encState t, ?_, ?_, ?_⟩
    · rw [instMachine_initB_iff]
      refine ⟨?_, ?_⟩
      · refine wfB_iff.2 ⟨s.dedup.map bitsOfNat, rfl, canon_map_bitsOfNat _, ?_⟩
        rw [length_cubeF]
        have := hconf s.dedup (List.nodup_dedup _)
          (fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf))
        simpa [encState] using this
      · rw [encState]
        exact (initCoreR_iff (canon_map_bitsOfNat _) q).2 (by simp [decSt_map_bitsOfNat, hs])
    · exact hrun _ _ hsmall (List.nodup_dedup _)
        (fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf))
    · rw [instMachine_accB_iff, encState]
      refine (accCoreR_iff (canon_map_bitsOfNat _) q true tbl).2 ⟨rfl, ?_⟩
      intro f hf
      rw [decSt_map_bitsOfNat]
      exact (hmem f).2 (hgoal f hf)

/-- **The target side of the table, as one statement**: a nondeterministic polynomial-space
machine decides, from the code of an instance description and an action table given as advice,
whether the compiled problem is solvable.  The advice is polynomially long in the number of
symbols of the table and in the bound `L` on the facts of the compiled problem. -/
theorem instSolver :
    ∃ (M : NSpace) (enc : Bool → ℕ → List Row → List Bool) (P : Polynomial ℕ),
      (∀ (b : Bool) (L : ℕ) (tbl : List Row), (enc b L tbl).length ≤ P.eval (tblSize tbl + L)) ∧
        ∀ (b : Bool) (L : ℕ) (tbl : List Row) (q : InstDesc),
          (∀ f ∈ regInitR q, f < 2 ^ L) → (∀ f ∈ regGoalR q, f < 2 ^ L) →
            (M.Accepts (instSer q) (enc b L tbl) ↔
              (b = true ∧ SolvableTbl tbl (regInitR q) (regGoalR q))) := by
  refine ⟨instMachine, fun b L tbl => tblAdv b (tbl.map (mapRow (tblNorm L tbl))),
    8 * (2 * Polynomial.X + 3) ^ 3, fun b L tbl => ?_, fun b L tbl q hs hg => ?_⟩
  · show (tblAdv b (tbl.map (mapRow (tblNorm L tbl)))).length ≤ _
    have hm : ∀ f ∈ tblFacts (tbl.map (mapRow (tblNorm L tbl))),
        (bitsOfNat f).length ≤ L + tblSize tbl := by
      intro f hf
      obtain ⟨c, hc, rfl⟩ := mem_tblFacts_of_mem_map hf
      exact length_bitsOfNat_le_of_lt_two_pow (tblNorm_lt hc)
    have h := length_tblAdv_le b (tbl.map (mapRow (tblNorm L tbl))) (L + tblSize tbl) hm
    rw [tblSize_map_mapRow] at h
    have hmono : 8 * (tblSize tbl + (L + tblSize tbl) + 3) ^ 3
        ≤ (8 * (2 * Polynomial.X + 3) ^ 3).eval (tblSize tbl + L) := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      have : tblSize tbl + (L + tblSize tbl) + 3 ≤ 2 * (tblSize tbl + L) + 3 := by omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
    omega
  · rw [instMachine_accepts_iff]
    refine and_congr Iff.rfl ?_
    exact solvableTbl_tblNorm hs hg

end Space

end HTN
