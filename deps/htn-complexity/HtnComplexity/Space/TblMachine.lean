import HtnComplexity.Space.TestsSem
import HtnComplexity.Space.TestsCobham
/-!
# The target-side machine: reachability in an action table in nondeterministic polynomial space

This file proves `HTN.Space.TblSolver` (`HtnComplexity/Space/TblSolver.lean`), the machine
hypothesis the target side of Table 3 was left resting on:

> there is a nondeterministic polynomial-space machine which, given the initial state and the
> goal of a table problem as its input and an encoding of the table as its advice, accepts
> exactly the solvable problems.

The machine `HTN.Space.tblMachine` keeps a **state of the transition system** as its
configuration, written as the serialised list of the canonical numerals of its facts.  Its
transition test picks a row of the table out of the advice and checks the four conditions of a
transition (`HTN.Space.rowStepB`); its initial and accepting tests read the initial state and the
goal off the input.  The space bound is a cube: by `HTN.Space.exists_smallReach` a solvable
problem has a solution through duplicate-free states made of facts of the initial state and of
the add lists of the table, and such a state is shorter than the cube of the length of the input
and the advice, so the length test the three tests carry removes no solution.

The advice is `HTN.Space.tblAdv` applied to the table **normalised** against the bound `L` on the
facts of the input (`HtnComplexity/Space/Norm.lean`): the facts of the table that no
admissible input can mention are renamed to short fresh names, which is what makes the advice
polynomially long in the *number of symbols* of the table.  Nothing here assumes that the table
can be computed from anything in polynomial time — it is advice.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Runs through small states -/

/-- Reachability through duplicate-free states made of facts of `B`. -/
def SmallReach (tbl : List Row) (B : List ℕ) : List ℕ → List ℕ → Prop :=
  Relation.ReflTransGen fun a b => StepTbl tbl a b ∧ b.Nodup ∧ ∀ f ∈ b, f ∈ B

/-- **Every run may be replaced by a run through duplicate-free states made of facts of the
initial state and of the add lists of the table.** -/
theorem exists_smallReach {tbl : List Row} {B : List ℕ} {u s : List ℕ} (h : ReachTbl tbl u s)
    {u' : List ℕ} (hu : ∀ f, f ∈ u' ↔ f ∈ u) (hnd : u'.Nodup) (hB : ∀ f ∈ u', f ∈ B)
    (hadd : ∀ f ∈ addFacts tbl, f ∈ B) :
    ∃ t, SmallReach tbl B u' t ∧ t.Nodup ∧ (∀ f ∈ t, f ∈ B) ∧ ∀ f, f ∈ t ↔ f ∈ s := by
  induction h with
  | refl => exact ⟨u', Relation.ReflTransGen.refl, hnd, hB, hu⟩
  | @tail w v _ hstep ih =>
    obtain ⟨t, hreach, hnodup, hsub, hmem⟩ := ih
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    refine ⟨canonStep row t, hreach.tail ⟨⟨row, hrow, fun f hf => (hmem f).2 (hprec f hf),
      fun f => by rw [mem_canonStep, hmem f]⟩, nodup_canonStep row t, fun f hf => ?_⟩,
      nodup_canonStep row t, fun f hf => ?_, fun f => ?_⟩
    · rcases mem_canonStep.1 hf with hf' | ⟨hf', -⟩
      · exact hadd f (List.mem_flatMap.2 ⟨row, hrow, hf'⟩)
      · exact hsub f hf'
    · rcases mem_canonStep.1 hf with hf' | ⟨hf', -⟩
      · exact hadd f (List.mem_flatMap.2 ⟨row, hrow, hf'⟩)
      · exact hsub f hf'
    · rw [mem_canonStep, hpost f, hmem f]

/-! ### States as configurations -/

theorem decSt_map_bitsOfNat (S : List ℕ) : decSt (S.map bitsOfNat) = S := by
  rw [decSt, List.map_map]
  exact (List.map_congr_left fun f _ => natOfBits_bitsOfNat f).trans (List.map_id S)

theorem canon_map_bitsOfNat (S : List ℕ) : ∀ w ∈ S.map bitsOfNat, IsCanon w := by
  intro w hw
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hw
  exact isCanon_bitsOfNat f

theorem length_encState_le_cube {S : List ℕ} {n : ℕ} (hlen : S.length ≤ n)
    (hk : ∀ f ∈ S, (bitsOfNat f).length ≤ n) : (encState S).length ≤ (n + 1) ^ 3 := by
  have h := length_blist_le (l := S.map bitsOfNat) (N := n) (K := n) (by simpa using hlen)
    (by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
      exact hk f hf)
  rw [encState]
  nlinarith [h, Nat.zero_le n]

/-! ### The length bound -/

/-- The input and the advice, concatenated, with one bit added. -/
def padF (i j : ℕ) : Fn := fun args => (args.getD i [] ++ args.getD j []) ++ [false]

/-- A string of length the cube of the length of `HTN.Space.padF`. -/
def cubeF (i j : ℕ) : Fn := fun args => List.replicate ((padF i j args).length ^ 3) false

theorem length_padF (i j : ℕ) (args : Args) :
    (padF i j args).length = (args.getD i []).length + (args.getD j []).length + 1 := by
  simp only [padF, List.length_append, List.length_cons, List.length_nil]

theorem length_cubeF (i j : ℕ) (args : Args) :
    (cubeF i j args).length = ((args.getD i []).length + (args.getD j []).length + 1) ^ 3 := by
  simp [cubeF, length_padF]

theorem cobham_padF (i j : ℕ) : Cobham (padF i j) :=
  (cobham_app (cobham_app (Cobham.proj i) (Cobham.proj j))
    (cobham_const [false])).of_eq' fun args => by simp [padF, proj]

theorem cobham_cubeF (i j : ℕ) : Cobham (cubeF i j) := by
  have h2 : Cobham fun args =>
      List.replicate ((padF i j args).length * (padF i j args).length) false :=
    (cobham_c2 Cobham.smash (cobham_padF i j) (cobham_padF i j)).of_eq' fun args => by
      simp [compFn, smashFn, proj]
  refine (cobham_c2 Cobham.smash h2 (cobham_padF i j)).of_eq' fun args => ?_
  simp only [compFn, smashFn, List.map_cons, List.map_nil, List.getD_cons_zero,
    List.getD_cons_succ, List.length_replicate, cubeF]
  congr 1
  ring

/-! ### The machine -/

/-- **The machine that decides reachability in an action table given as advice.** -/
noncomputable def tblMachine : NSpace where
  initB := fun args =>
    wfB (args.getD 0 []) (cubeF 1 2 args) && initCoreB (args.getD 0 []) (args.getD 1 [])
  stepB := fun args =>
    wfB (args.getD 0 []) (cubeF 2 3 args) &&
      stepCoreB (args.getD 3 []) (args.getD 1 []) (args.getD 0 [])
  accB := fun args => accCoreB (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])
  cobham_initB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeF 1 2)).and
      (cobhamB_initCoreB (Cobham.proj 0) (Cobham.proj 1))).of_eq fun args => by simp [proj]
  cobham_stepB :=
    ((cobhamB_wfB (Cobham.proj 0) (cobham_cubeF 2 3)).and
      (cobhamB_stepCoreB (Cobham.proj 3) (Cobham.proj 1) (Cobham.proj 0))).of_eq
        fun args => by simp [proj]
  cobham_accB :=
    (cobhamB_accCoreB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)).of_eq
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

/-! ### Correctness -/

theorem tblMachine_initB_iff (c x a : List Bool) :
    tblMachine.initB [c, x, a] = true ↔
      wfB c (cubeF 1 2 [c, x, a]) = true ∧ initCoreB c x = true := by
  simp [tblMachine, Bool.and_eq_true]

theorem tblMachine_stepB_iff (c' c x a : List Bool) :
    tblMachine.stepB [c', c, x, a] = true ↔
      wfB c' (cubeF 2 3 [c', c, x, a]) = true ∧ stepCoreB a c c' = true := by
  simp [tblMachine, Bool.and_eq_true]

theorem tblMachine_accB_iff (c x a : List Bool) :
    tblMachine.accB [c, x, a] = true ↔ accCoreB c x a = true := Iff.rfl

/-- Every configuration a run of the machine visits is a serialised list of canonical numerals,
and the state it carries is reachable from the state the first configuration carries. -/
theorem reach_decode {tbl : List Row} {b : Bool} {s g : List ℕ} {S₀ : List (List Bool)}
    (hS₀ : ∀ w ∈ S₀, IsCanon w) {c : List Bool}
    (h : tblMachine.Reach (encProblem s g) (tblAdv b tbl) (blist S₀) c) :
    ∃ S, c = blist S ∧ (∀ w ∈ S, IsCanon w) ∧ ReachTbl tbl (decSt S₀) (decSt S) := by
  induction h with
  | refl => exact ⟨S₀, rfl, hS₀, Relation.ReflTransGen.refl⟩
  | @tail c c' _ hstep ih =>
    obtain ⟨S, rfl, hS, hreach⟩ := ih
    rw [NSpace.Step, tblMachine_stepB_iff] at hstep
    obtain ⟨hwf, hstepC⟩ := hstep
    obtain ⟨S', rfl, hS', -⟩ := wfB_iff.1 hwf
    exact ⟨S', rfl, hS', hreach.tail ((stepCoreB_iff hS hS' b).1 hstepC)⟩

/-- **The machine accepts exactly the solvable problems.** -/
theorem tblMachine_accepts_iff (b : Bool) (tbl : List Row) (s g : List ℕ) :
    tblMachine.Accepts (encProblem s g) (tblAdv b tbl) ↔ (b = true ∧ SolvableTbl tbl s g) := by
  set x := encProblem s g with hx
  set a := tblAdv b tbl with ha
  constructor
  · rintro ⟨c₀, c, hinit, hreach, hacc⟩
    rw [tblMachine_initB_iff] at hinit
    obtain ⟨S₀, rfl, hS₀, -⟩ := wfB_iff.1 hinit.1
    have hinit0 := (initCoreB_iff hS₀ s g).1 hinit.2
    obtain ⟨S, rfl, hS, hreachTbl⟩ := reach_decode hS₀ hreach
    rw [tblMachine_accB_iff] at hacc
    obtain ⟨hb, hgoal⟩ := (accCoreB_iff hS s g b tbl).1 hacc
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
    -- the length bound available to a state made of facts of `B`
    set n := x.length + a.length with hn
    have hBlen : B.length ≤ n := by
      have h1 : s.length ≤ x.length := by
        refine le_trans (length_le_encState s) ?_
        rw [hx, encProblem]
        simp
      have h2 : (addFacts tbl).length ≤ a.length := length_addFacts_le_tblAdv
      simp only [hB, List.length_append]
      omega
    have hBbits : ∀ f ∈ B, (bitsOfNat f).length ≤ n := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · have h1 : (bitsOfNat f).length ≤ (encState s).length := length_bitsOfNat_le_encState hf
        have h2 : (encState s).length ≤ x.length := by
          rw [hx, encProblem]
          simp
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
    -- transport the run
    have hrun : ∀ u v : List ℕ, SmallReach tbl B u v → u.Nodup → (∀ f ∈ u, f ∈ B) →
        tblMachine.Reach x a (encState u) (encState v) := by
      intro u v hsr
      induction hsr with
      | refl => exact fun _ _ => Relation.ReflTransGen.refl
      | @tail w v _ hstep ih =>
        intro hnodup hsubS
        refine (ih hnodup hsubS).tail ?_
        rw [NSpace.Step, tblMachine_stepB_iff]
        refine ⟨?_, ?_⟩
        · have := hwf v hstep.2.1 hstep.2.2
          simpa [encState] using this
        · rw [ha, encState, encState]
          exact (stepCoreB_iff (canon_map_bitsOfNat w) (canon_map_bitsOfNat v) true).2 (by
            simpa [decSt_map_bitsOfNat] using hstep.1)
    refine ⟨encState s.dedup, encState t, ?_, ?_, ?_⟩
    · rw [tblMachine_initB_iff]
      refine ⟨?_, ?_⟩
      · refine wfB_iff.2 ⟨s.dedup.map bitsOfNat, rfl, canon_map_bitsOfNat _, ?_⟩
        rw [length_cubeF]
        have := hconf s.dedup (List.nodup_dedup _)
          (fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf))
        simpa [encState] using this
      · rw [encState]
        exact (initCoreB_iff (canon_map_bitsOfNat _) s g).2 (by simp [decSt_map_bitsOfNat])
    · exact hrun _ _ hsmall (List.nodup_dedup _)
        (fun f hf => List.mem_append_left _ (List.mem_dedup.1 hf))
    · rw [tblMachine_accB_iff, encState]
      refine (accCoreB_iff (canon_map_bitsOfNat _) s g true tbl).2 ⟨rfl, ?_⟩
      intro f hf
      rw [decSt_map_bitsOfNat]
      exact (hmem f).2 (hgoal f hf)

/-! ### The target-side machine hypothesis -/

theorem tblSize_map_mapRow (ρ : ℕ → ℕ) (tbl : List Row) :
    tblSize (tbl.map (mapRow ρ)) = tblSize tbl := by
  rw [tblSize, tblSize, List.length_map, List.map_map]
  congr 2
  refine List.map_congr_left fun r _ => ?_
  simp [mapRow]

/-- **The target-side machine hypothesis of `HtnComplexity/Space/TblSolver.lean` holds.** -/
theorem tblSolver : TblSolver := by
  refine ⟨tblMachine, fun b L tbl => tblAdv b (tbl.map (mapRow (tblNorm L tbl))),
    8 * (2 * Polynomial.X + 3) ^ 3, fun b L tbl => ?_, fun b L tbl s g hs hg => ?_⟩
  · show (tblAdv b (tbl.map (mapRow (tblNorm L tbl)))).length ≤ _
    have hm : ∀ f ∈ tblFacts (tbl.map (mapRow (tblNorm L tbl))),
        (bitsOfNat f).length ≤ L + tblSize tbl := by
      intro f hf
      obtain ⟨a, ha, rfl⟩ := mem_tblFacts_of_mem_map hf
      exact length_bitsOfNat_le_of_lt_two_pow (tblNorm_lt ha)
    have h := length_tblAdv_le b (tbl.map (mapRow (tblNorm L tbl))) (L + tblSize tbl) hm
    rw [tblSize_map_mapRow] at h
    have hmono : 8 * (tblSize tbl + (L + tblSize tbl) + 3) ^ 3
        ≤ (8 * (2 * Polynomial.X + 3) ^ 3).eval (tblSize tbl + L) := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      have : tblSize tbl + (L + tblSize tbl) + 3 ≤ 2 * (tblSize tbl + L) + 3 := by omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
    omega
  · rw [tblMachine_accepts_iff]
    refine and_congr Iff.rfl ?_
    exact solvableTbl_tblNorm hs hg

end Space

end HTN
