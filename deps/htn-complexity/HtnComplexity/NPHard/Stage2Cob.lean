import HtnComplexity.NPHard.Stage2
/-!
# The numerical stage is polynomial time

Tactics `cobn`, `cobb`, `cobl` discharge membership in Cobham's class for arithmetic expressions
and loops; with them, `polyTimeFun_stage2` shows that the numerical stage runs in polynomial time.
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM Merge

theorem getD_drop_args (args : Args) (k i : ℕ) : (args.drop k).getD i [] = args.getD (k + i) [] := by
  simp [List.getD_eq_getElem?_getD]

theorem cobN_pair {f g : Args → ℕ} (hf : CobN f) (hg : CobN g) :
    CobN fun args => Nat.pair (f args) (g args) :=
  (cobN_ite (cobB_lt hf hg) (cobN_add (cobN_mul hg hg) hf)
    (cobN_add (cobN_add (cobN_mul hf hf) hf) hg)).of_eq fun args => by
    simp only [Nat.pair, decide_eq_true_eq]

/-- Discharges goals `CobN f` for arithmetic expressions `f` in argument lengths. -/
syntax "cobn" : tactic
/-- Discharges goals `CobB p` for comparisons of arithmetic expressions. -/
syntax "cobb" : tactic
macro_rules
  | `(tactic| cobb) => `(tactic| first
    | with_reducible exact cobB_const _
    | (with_reducible apply cobB_eq) <;> cobn
    | (with_reducible apply cobB_le) <;> cobn
    | (with_reducible apply cobB_lt) <;> cobn)
macro_rules
  | `(tactic| cobn) => `(tactic| first
    | with_reducible exact cobN_const _
    | with_reducible exact cobN_arg _
    | with_reducible assumption
    | ((with_reducible apply CobN.dropN); with_reducible assumption)
    | ((with_reducible apply CobN.drop1); with_reducible assumption)
    | (with_reducible apply cobN_radix) <;> cobn
    | (with_reducible apply cobN_pair) <;> cobn
    | (with_reducible apply cobN_length) <;>
        first | with_reducible assumption | ((with_reducible apply CobList.dropN); with_reducible assumption)
    | (with_reducible apply cobN_getD) <;>
        first | cobn | with_reducible assumption | ((with_reducible apply CobList.dropN); with_reducible assumption)
    | (with_reducible apply cobN_valTrip) <;> cobn
    | (with_reducible apply cobN_valW) <;> cobn
    | (with_reducible apply cobN_valX) <;> cobn
    | (with_reducible apply cobN_valY) <;> cobn
    | (with_reducible apply cobN_lit) <;> first | cobn | cobb
    | (with_reducible apply cobN_ite) <;> first | cobn | cobb
    | (with_reducible apply cobN_add) <;> cobn
    | (with_reducible apply cobN_sub) <;> cobn
    | (with_reducible apply cobN_mul) <;> cobn
    | (with_reducible apply cobN_mod) <;> cobn
    | (with_reducible apply cobN_div) <;> cobn)

/-- Discharges goals `CobList L` for loops emitting arithmetic expressions. -/
syntax "cobl" : tactic
macro_rules
  | `(tactic| cobl) => `(tactic| first
    | with_reducible exact cobList_nil
    | (with_reducible refine cobList_append ?_ ?_) <;> cobl
    | (with_reducible refine cobList_cons ?_ ?_) <;> first | cobn | cobl
    | (with_reducible refine cobList_single ?_) <;> cobn
    | (with_reducible refine cobList_ite ?_ ?_ ?_) <;> first | cobb | cobl
    | ((with_reducible refine cobList_loop ?_ ?_) <;> first | cobn | (beta_reduce; simp only [← List.drop_one, List.drop_drop, getD_drop_args]; cobl))
    | ((with_reducible refine cobList_tokLoop ?_ ?_) <;>
        first | with_reducible assumption | (beta_reduce; (try simp only [decLit]); cobl)))

theorem cobList_numsFlat {N M : Args → ℕ} (hN : CobN N) (hM : CobN M) {T : Args → List ℕ}
    (hT : CobList T) : CobList fun args => numsFlat (N args) (M args) (T args) := by
  unfold numsFlat tT tF
  cobl

theorem cobN_nZeros {T : Args → List ℕ} (hT : CobList T) : CobN fun args => nZeros (T args) := by
  unfold nZeros zerosBefore
  refine (cobN_count (cobN_length hT) (p := fun args =>
    decide ((T args.tail).getD (args.getD 0 []).length 0 = 0))
    (cobB_eq (cobN_getD hT.drop1 (cobN_arg 0)) (cobN_const 0))).of_eq fun args => ?_
  simp

/-- **The numerical stage is computable in polynomial time.** -/
theorem polyTimeFun_stage2 : PolyTimeFun stage2 := by
  have hL : CobList fun args => parseUnl (args.getD 0 []) := cobList_parse (Cobham.proj 0)
  have hN : CobN fun args => (parseUnl (args.getD 0 [])).getD 0 0 := cobN_getD hL (cobN_const 0)
  have hT := cobList_tail hL
  have hM := cobN_nZeros hT
  have hn := cobList_numsFlat hN hM hT
  have h : CobList fun args => s2List (parseUnl (args.getD 0 [])) := by
    unfold s2List bigB
    refine cobList_cons ?_ (cobList_cons ?_ hn)
    · apply cobN_hor <;> cobn
    · refine cobN_add (cobN_add ?_ (cobN_sub (cobN_length hT) hM)) ?_ <;> cobn
  exact PolyTimeFun.of_cobham h fun x => rfl

end HTN.NPHard
