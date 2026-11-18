import HtnComplexity.Space.TrTable
import HtnComplexity.Space.InstBound
import HtnComplexity.Space.Bridge
import HtnComplexity.Space.InstMachine
/-!
# The target side for totally ordered tail-recursive (and acyclic) HTN

This file does for the targets `TO-HTN-TR-1` and `TO-HTN-AC-1` what
`HtnCompilability/Space/RegSpace.lean` does for `HTN-REG-1`: it proves

    HTN.Syn.SpaceDecidableAdv codingSer SynClass.TO_HTN_TR_root

— "plan existence for a totally ordered tail-recursive HTN description with a rooted instance is
decidable in nondeterministic polynomial space with the domain supplied as advice" — **with no
hypothesis left**, and derives the same statement for `TO-HTN-AC-1`, `TO-HTN-REG-1` and `STRIPS`
by monotonicity.  The ingredients:

* `HTN.Space.solvable_tr_iff_solvableTblR` — plan existence *is* reachability in the renamed
  action table of the compiled `STRIPS` domain of Alford's bounded stack machine, the instance
  side being *literally* the lists `HTN.Space.regInitR q`, `HTN.Space.regGoalR q` of the regular
  case;
* `HTN.Space.tblSize_trTableR_le` — the table has polynomially many symbols in the number of
  symbols of the source domain, so it fits into the advice;
* `HTN.Space.instSolver` — the machine, reused verbatim: it reads the compiled initial state and
  goal off the code of the instance description and the action table off its advice.

**Nothing is assumed about the cost of the domain translation**: the table is advice, an
arbitrary — in particular arbitrarily expensive — function of the domain description of
polynomially bounded length.  This is the whole point of the construction.

Cell 1 of `TABLE3-PLAN.md`, (`TO-HTN`, `TO-HTN-TR`), follows on the single complexity-theoretic
hypothesis `¬ InNSpacePoly G.L` ("`EXPTIME ⊄ PSPACE/poly`"), and so does the target half of
cells 6 and 8, whose target is `TO-HTN-TR-1` resp. `TO-HTN-AC-1`.
-/

namespace HTN

namespace Space

open Syn PTime

open Classical in
/-- **Plan existence for a totally ordered tail-recursive HTN description with a rooted instance
is decidable in nondeterministic polynomial space, the domain description being supplied as
advice.**  The machine is `HTN.Space.instMachine`, the advice the renamed action table
`HTN.Space.trTableR` of the compiled `STRIPS` domain. -/
theorem spaceDecidableAdv_TO_HTN_TR_root :
    SpaceDecidableAdv codingSer SynClass.TO_HTN_TR_root := by
  obtain ⟨M, enc, P, hPlen, hM⟩ := instSolver
  obtain ⟨ptbl, hptbl⟩ := tblSize_trTableR_le
  intro D r rq hdomOk hsize
  refine ⟨M,
    fun n => enc (decide ((trDom (D n)).HasEmptyMethod)) (rq.eval n + 2) (trTableR (D n)),
    P.comp (ptbl.comp r + rq + 2), fun n => ?_, fun n q hq hlen => ?_⟩
  · refine (hPlen _ _ _).trans ?_
    have hle : tblSize (trTableR (D n)) + (rq.eval n + 2)
        ≤ (ptbl.comp r + rq + 2).eval n := by
      have h1 : tblSize (trTableR (D n)) ≤ (ptbl.comp r).eval n := by
        calc tblSize (trTableR (D n)) ≤ ptbl.eval (D n).size := hptbl _
          _ ≤ ptbl.eval (r.eval n) := Polynomial.eval_mono_nat _ (hsize n)
          _ = (ptbl.comp r).eval n := by simp
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    simpa using Polynomial.eval_mono_nat P hle
  · have hlen' : (instSer q).length ≤ rq.eval n := by simpa using hlen
    have hfi : ∀ g ∈ regInitR q, g < 2 ^ (rq.eval n + 2) := fun _ hg =>
      mem_regInitR_lt hlen' hg
    have hfg : ∀ g ∈ regGoalR q, g < 2 ^ (rq.eval n + 2) := fun _ hg =>
      mem_regGoalR_lt hlen' hg
    rw [solvable_tr_iff_solvableTblR (hdomOk n).1 (hdomOk n).2 hq, codingSer_code,
      hM _ _ _ _ hfi hfg]
    simp

/-- **Plan existence for a totally ordered acyclic HTN description with a rooted instance** is
decidable in nondeterministic polynomial space with the domain as advice: acyclic descriptions
are tail recursive. -/
theorem spaceDecidableAdv_TO_HTN_AC_root :
    SpaceDecidableAdv codingSer SynClass.TO_HTN_AC_root :=
  spaceDecidableAdv_TO_HTN_TR_root.mono SynClass.sub_TO_HTN_AC_root_TO_HTN_TR_root

/-- The same for totally ordered regular descriptions with a rooted instance. -/
theorem spaceDecidableAdv_TO_HTN_REG_root :
    SpaceDecidableAdv codingSer SynClass.TO_HTN_REG_root :=
  spaceDecidableAdv_TO_HTN_TR_root.mono SynClass.sub_TO_HTN_REG_root_TO_HTN_TR_root

/-- The same for `STRIPS`. -/
theorem spaceDecidableAdv_STRIPS : SpaceDecidableAdv codingSer SynClass.STRIPS :=
  spaceDecidableAdv_TO_HTN_TR_root.mono SynClass.sub_STRIPS_TO_HTN_TR_root

end Space

end HTN
