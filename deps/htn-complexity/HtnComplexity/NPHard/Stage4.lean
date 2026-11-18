import HtnComplexity.NPHard.Stage2Cob
import HtnComplexity.Complexity.SerPos
/-!
# The serialisation stage in polynomial time

The stage mapping the unary code `unl (B :: m :: as)` of a numerical instance to the serialised
partition instance `instSer (partInst as B m)` is polynomial time (`polyTimeFun_stage4`) and
computes the right thing (`stage4_code`).
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM Merge HTN.Syn

/-- The length of the row `i` of the grid of a partition instance. -/
def gLen (B m : ℕ) (as : List ℕ) (i : ℕ) : ℕ :=
  if i < as.length then 2 * as.getD i 0 else 2 * B * m

/-- The name of the action in column `j` of row `i`. -/
def gName (B : ℕ) (as : List ℕ) (i j : ℕ) : ℕ :=
  if i < as.length then (if j < as.getD i 0 then 0 else 1) else (if j % (2 * B) < B then 2 else 3)

/-- The serialised partition instance, written as loops. -/
def s4 (B m : ℕ) (as : List ℕ) : List Bool :=
  serNatList [0] ++ serNatList [0] ++
  (((List.range (as.length + 1)).flatMap fun i => (List.range (gLen B m as i)).flatMap fun j =>
      true :: serNat (Nat.pair i j)) ++ [false]) ++
  (((List.range (as.length + 1)).flatMap fun i =>
      (List.range (gLen B m as i - 1)).flatMap fun j =>
        true :: bstr (serNat (Nat.pair i j) ++ serNat (Nat.pair i (j + 1)))) ++ [false]) ++
  (((List.range (as.length + 1)).flatMap fun i => (List.range (gLen B m as i)).flatMap fun j =>
      true :: bstr (serNat (Nat.pair i j) ++ false :: serNat (gName B as i j))) ++ [false])

/-! ### Cobham's class -/

theorem cobham_serNat {f : Args → ℕ} (hf : CobN f) : Cobham fun args => serNat (f args) :=
  (cobham_bstr (HTN.PTime.cobham_c1 cobham_lenFnArgs hf)).of_fun_eq fun args => by
    simp only [compFn, List.map_cons, List.map_nil, serNat]
    rw [show lenFnArgs [un (f args)] = lenFn (un (f args)) from rfl, lenFn_eq, length_un]

theorem cobham_loop {N : Args → ℕ} (hN : CobN N) {F : ℕ → Args → List Bool}
    (hF : Cobham fun args => F (args.getD 0 []).length args.tail) :
    Cobham fun args => (List.range (N args)).flatMap fun i => F i args :=
  (cobham_forRange hN hF).of_fun_eq fun args => by simp

/-- Discharges goals `Cobham f` for loops emitting serialised numbers. -/
syntax "cobs" : tactic
macro_rules
  | `(tactic| cobs) => `(tactic| first
    | with_reducible exact cobham_const _
    | (with_reducible refine cobham_append' ?_ ?_) <;> cobs
    | (with_reducible refine cobham_cons' _ ?_) <;> cobs
    | (with_reducible refine cobham_serNat ?_) <;> cobn
    | ((with_reducible refine cobham_loop ?_ ?_) <;>
        first | cobn | (beta_reduce; simp only [← List.drop_one, List.drop_drop, getD_drop_args]; cobs)))

theorem cobham_s4 {B M : Args → ℕ} (hB : CobN B) (hM : CobN M) {As : Args → List ℕ}
    (hA : CobList As) : Cobham fun args => s4 (B args) (M args) (As args) := by
  have hI : CobN fun a : Args => (a.getD 0 []).length := cobN_arg 0
  have hN : CobN fun a : Args => (if (a.getD 0 []).length < (As a.tail).length then
      2 * (As a.tail).getD (a.getD 0 []).length 0 else 2 * B a.tail * M a.tail) :=
    cobN_ite (cobB_lt hI (cobN_length hA.drop1)) (cobN_mul (cobN_const 2)
      (cobN_getD hA.drop1 hI)) (cobN_mul (cobN_mul (cobN_const 2) hB.drop1) hM.drop1)
      |>.of_eq fun _ => by simp only [decide_eq_true_eq]
  have hL : CobN fun a : Args => (As a).length + 1 := cobN_add (cobN_length hA) (cobN_const 1)
  unfold s4 gLen gName
  repeat' (with_reducible refine cobham_append' ?_ ?_)
  all_goals try cobs
  · refine cobham_loop hL (cobham_loop hN ?_)
    exact cobham_cons' true (cobham_serNat (cobN_pair (cobN_arg 0).drop1 (cobN_arg 0)))
  · refine cobham_loop hL (cobham_loop (cobN_sub hN (cobN_const 1)) ?_)
    exact cobham_cons' true (cobham_bstr (cobham_append' (cobham_serNat (cobN_pair
      (cobN_arg 0).drop1 (cobN_arg 0))) (cobham_serNat (cobN_pair (cobN_arg 0).drop1
      (cobN_add (cobN_arg 0) (cobN_const 1))))))
  · refine cobham_loop hL (cobham_loop hN ?_)
    refine cobham_cons' true (cobham_bstr (cobham_append' (cobham_serNat (cobN_pair
      (cobN_arg 0).drop1 (cobN_arg 0))) (cobham_cons' false (cobham_serNat ?_))))
    have hI' : CobN fun a : Args => (a.tail.getD 0 []).length := (cobN_arg 0).drop1
    have hA' := hA.drop1.drop1
    exact cobN_ite (cobB_lt hI' (cobN_length hA')) (cobN_ite (cobB_lt (cobN_arg 0)
      (cobN_getD hA' hI')) (cobN_const 0) (cobN_const 1)) (cobN_ite (cobB_lt (cobN_mod
      (cobN_arg 0) (cobN_mul (cobN_const 2) hB.drop1.drop1)) hB.drop1.drop1) (cobN_const 2)
      (cobN_const 3)) |>.of_eq fun _ => by simp only [decide_eq_true_eq]

/-! ### The serialised instance is `s4` -/

/-- The rows of the grid of a partition instance, in closed form. -/
def rowsP (B m : ℕ) (as : List ℕ) : List (List (Bool × ℕ)) :=
  (List.range (as.length + 1)).map fun i => (List.range (gLen B m as i)).map fun j =>
    (false, gName B as i j)

theorem length_zoBlocks (B m : ℕ) : (zoBlocks B m).length = 2 * B * m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [zoBlocks, zoWord, ih]; ring

theorem getElem_zoBlocks (B m j : ℕ) (hj : j < (zoBlocks B m).length) :
    (zoBlocks B m)[j] = !decide (j % (2 * B) < B) := by
  induction m generalizing j with
  | zero => simp [zoBlocks] at hj
  | succ m ih =>
    simp only [zoBlocks]
    rw [List.getElem_append]
    split_ifs with h
    · simp only [zoWord, List.length_append, List.length_replicate] at h
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [zoWord, List.getElem_append, List.length_replicate, List.getElem_replicate]
      split_ifs with h2 <;> simp [h2]
    · simp only [zoWord, List.length_append, List.length_replicate] at h
      rw [ih]
      congr 2
      have hz : (zoWord B).length = 2 * B := by simp [zoWord]; omega
      rw [hz, Nat.mod_eq_sub_mod (show 2 * B ≤ j by omega)]

theorem rows_partInst (B m : ℕ) (as : List ℕ) :
    ((chains (as.map zoWord) (zoBlocks B m)).map fun row => row.map (encLabel id id)) =
      rowsP B m as := by
  unfold chains letters primChain rowsP
  rw [List.range_succ, List.map_append]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  congr 1
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h2
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply, gLen, gName, h2,
      if_true]
    rw [show as.getD i 0 = as[i] by simp [List.getD_eq_getElem?_getD, h2]]
    refine List.ext_getElem (by simp [aWord, zoWord]; omega) fun j g1 g2 => ?_
    simp only [List.length_map, List.length_range] at g2
    simp only [aWord, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
    simp only [zoWord, List.getElem_append, List.length_replicate, List.getElem_replicate]
    split_ifs <;> rfl
  · congr 1
    simp only [gLen, gName, lt_irrefl, if_false]
    refine List.ext_getElem (by simp [bWord, length_zoBlocks]) fun j g1 g2 => ?_
    simp only [bWord, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [getElem_zoBlocks]
    by_cases h : j % (2 * B) < B <;> simp [h, encLabel, bName]

theorem blist_eq (l : List (List Bool)) :
    blist l = l.flatMap (fun x => true :: bstr x) ++ [false] := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [blist, List.foldr] at ih ⊢; rw [← ih]

theorem gridRow_rowsP (B m : ℕ) (as : List ℕ) {i : ℕ} (hi : i < as.length + 1) :
    gridRow (rowsP B m as) i = (List.range (gLen B m as i)).map fun j => (false, gName B as i j) := by
  simp [gridRow, rowsP, List.getD_eq_getElem?_getD, hi]

theorem instSer_partInst (as : List ℕ) (B m : ℕ) : instSer (partInst as B m) = s4 B m as := by
  have hlen : (rowsP B m as).length = as.length + 1 := by simp [rowsP]
  simp only [instSer, partInst, mergeInst, gridDescOf, rows_partInst, InstDesc.initList,
    InstDesc.goalList, InstDesc.tnI, tnSer, gridDesc, TnDesc.ids, TnDesc.ordList, TnDesc.lbl,
    s4, serPairList, serLblList, serNatList, blist_eq, List.flatMap_map, cellIds, cellOrd,
    cellLbl, hlen, List.map_flatMap, List.flatMap_assoc, List.append_assoc]
  have e1 : ((List.range (as.length + 1)).flatMap fun x =>
      (List.range (gridRow (rowsP B m as) x).length).flatMap fun a =>
        true :: bstr (bitsOfNat (Nat.pair x a))) =
      (List.range (as.length + 1)).flatMap fun i =>
        (List.range (gLen B m as i)).flatMap fun j => true :: serNat (Nat.pair i j) := by
    refine List.flatMap_congr fun i hi => ?_
    rw [gridRow_rowsP _ _ _ (List.mem_range.1 hi)]
    simp [serNat]
  have e2 : ((List.range (as.length + 1)).flatMap fun x =>
      (List.range ((gridRow (rowsP B m as) x).length - 1)).flatMap fun a =>
        true :: bstr (serPair (Nat.pair x a, Nat.pair x (a + 1)))) =
      (List.range (as.length + 1)).flatMap fun i =>
        (List.range (gLen B m as i - 1)).flatMap fun j =>
          true :: bstr (serNat (Nat.pair i j) ++ serNat (Nat.pair i (j + 1))) := by
    refine List.flatMap_congr fun i hi => ?_
    rw [gridRow_rowsP _ _ _ (List.mem_range.1 hi)]
    simp [serPair, serNat]
  have e3 : ((List.range (as.length + 1)).flatMap fun x =>
      (List.range (gridRow (rowsP B m as) x).length).flatMap fun a =>
        true :: bstr (serLbl (Nat.pair x a, (gridRow (rowsP B m as) x).getD a (false, 0)))) =
      (List.range (as.length + 1)).flatMap fun i =>
        (List.range (gLen B m as i)).flatMap fun j =>
          true :: bstr (serNat (Nat.pair i j) ++ false :: serNat (gName B as i j)) := by
    refine List.flatMap_congr fun i hi => ?_
    rw [gridRow_rowsP _ _ _ (List.mem_range.1 hi)]
    simp only [List.length_map, List.length_range]
    refine List.flatMap_congr fun j hj => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.1 hj)]
    simp [serLbl, serNat]
  rw [e1, e2, e3]

/-! ### The stage -/

/-- **The serialisation stage**: from the unary code of `B :: m :: as` to the serialised
partition instance. -/
def stage4 (x : List Bool) : List Bool :=
  s4 ((parseUnl x).getD 0 0) ((parseUnl x).getD 1 0) (parseUnl x).tail.tail

theorem stage4_code (B m : ℕ) (as : List ℕ) :
    stage4 (unl (B :: m :: as)) = codingSer.code (partInst as B m) := by
  rw [stage4, parseUnl_unl]
  exact (instSer_partInst as B m).symm

theorem polyTimeFun_stage4 : PolyTimeFun stage4 := by
  have hL : CobList fun args => parseUnl (args.getD 0 []) := cobList_parse (Cobham.proj 0)
  exact PolyTimeFun.of_cobham (cobham_s4 (cobN_getD hL (cobN_const 0))
    (cobN_getD hL (cobN_const 1)) (cobList_tail (cobList_tail hL))) fun x => rfl

end HTN.NPHard
