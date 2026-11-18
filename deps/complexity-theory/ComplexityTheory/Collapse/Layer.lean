import ComplexityTheory.Collapse.Quant
/-!
# Nesting the quantifiers

`ComplexityTheory/Collapse/Quant.lean` quantifies over the strings whose length is that of the
*first* argument, the body reading the bound variable as its first argument and the ambient
arguments after it.  Building a formula with several quantifiers therefore alternates two moves:

* quantify — `HTN.PSpace.psBigOr`, `HTN.PSpace.psBigAnd`, whose result again reads a fixed number
  of arguments (`HTN.PSpace.argDep_bigOr`, `HTN.PSpace.argDep_bigAnd`);
* substitute the template — `HTN.PSpace.psSubstFirst`, which replaces the first argument by a
  computed string, so that the quantifier runs over the strings of the length one wants.

This file provides the two moves together with the bookkeeping of "reads only its first `n`
arguments" (`HTN.PTime.ArgDep` for predicates, `HTN.PSpace.FnDep` for functions) that they need.
-/

namespace HTN

namespace PSpace

open PTime

/-- A function that reads only its first `n` arguments. -/
def FnDep (n : ℕ) (f : Fn) : Prop := ∀ args, f args = f (padArgs n args)

theorem getD_tail (args : Args) (i : ℕ) : args.tail.getD i [] = args.getD (i + 1) [] := by
  cases args with
  | nil => simp
  | cons a rest => simp

theorem tail_padArgs (n : ℕ) (args : Args) :
    (padArgs (n + 1) args).tail = padArgs n args.tail := by
  rw [padArgs, padArgs, List.range_succ_eq_map, List.map_cons, List.map_map, List.tail_cons]
  exact List.map_congr_left fun i _ => by simp [getD_tail, Nat.add_comm]

theorem argDep_bigAnd {P : Args → Bool} {n : ℕ} (hdep : ArgDep (n + 1) P) :
    ArgDep (n + 1) (fun args => allLenB (args.getD 0 []).length (fun y => P (y :: args.tail))) := by
  intro args
  simp only [getD_padArgs (Nat.succ_pos n), tail_padArgs]
  refine congrArg _ (funext fun y => ?_)
  rw [hdep (y :: args.tail), padArgs_cons]

theorem argDep_bigOr {P : Args → Bool} {n : ℕ} (hdep : ArgDep (n + 1) P) :
    ArgDep (n + 1) (fun args => anyLen (args.getD 0 []).length (fun y => P (y :: args.tail))) := by
  intro args
  simp only [getD_padArgs (Nat.succ_pos n), tail_padArgs]
  refine congrArg _ (funext fun y => ?_)
  rw [hdep (y :: args.tail), padArgs_cons]

/-- **Substituting a computed string for the first argument.** -/
theorem psSubstFirst {P : Args → Bool} {n : ℕ} (hP : PSpaceB P) (hdep : ArgDep (n + 1) P)
    {f : Fn} (hf : PSpaceF f) : PSpaceB (fun args => P (f args :: args)) := by
  have hcomp : PSpaceF (compFn (fun args => [P args]) (f :: (List.range n).map (fun i => proj i))) := by
    refine PSpaceF.comp hP ?_
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hf
    · exact psSpace_relay n 0 g (by simpa using hg)
  refine PSpaceF.of_eq hcomp fun args => ?_
  show [P ((f :: (List.range n).map (fun i => proj i)).map (fun h => h args))] = _
  rw [List.map_cons]
  have h0 : ((List.range n).map (fun i => proj i)).map (fun h => h args) = padArgs n args := by
    have := map_relay n 0 args
    simpa using this
  rw [h0, ← padArgs_cons, ← hdep]

theorem argDep_substFirst {P : Args → Bool} {n : ℕ} (hdep : ArgDep (n + 1) P) {f : Fn}
    (hf : FnDep n f) : ArgDep n (fun args => P (f args :: args)) := by
  intro args
  show P (f args :: args) = P (f (padArgs n args) :: padArgs n args)
  rw [hdep (f args :: args), padArgs_cons, ← hf args]

/-! ### Functions that read only their first arguments -/

theorem fnDep_proj {n i : ℕ} (h : i < n) : FnDep n (proj i) := by
  intro args
  show args.getD i [] = (padArgs n args).getD i []
  rw [getD_padArgs h]

theorem fnDep_comp {n : ℕ} {g : Fn} {hs : List Fn} (hhs : ∀ h ∈ hs, FnDep n h) :
    FnDep n (compFn g hs) := by
  intro args
  simp only [compFn]
  exact congrArg g (List.map_congr_left fun h hh => hhs h hh args)

theorem fnDep_const {n : ℕ} (z : List Bool) : FnDep n (fun _ => z) := fun _ => rfl

end PSpace

end HTN
