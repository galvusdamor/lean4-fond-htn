import HtnComplexity.Space.RegRename
import HtnComplexity.Complexity.Serial
/-!
# The facts of a compiled instance are small when its code is short

The target-side machine of `HtnComplexity/Space/TblSolver.lean` is correct only on table
problems whose initial state and goal mention facts below `2 ^ L`, and the advice may depend on
`L`.  This file supplies the missing link for regular HTN: the facts of the renamed compiled
problem of an instance description `q` are below `2 ^ (|instSer q| + 2)`.

The reason is that every numeral occurring in a description is written out in its serialisation,
so a number occurring in `q` is below `2 ^ |instSer q|`, and the compilation multiplies it by
`4` and adds at most `1`.  Three numerals have to be covered: the facts of the initial state,
the facts of the goal, and the name of the initial compound task `HTN.Syn.rootName`, which the
label list of the initial task network carries.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Two constant bits prefixed to a numeral -/

/-- The numeral of `4 v + 2` is the numeral of `v` with `false, true` in front.  This holds at
`v = 0` as well, which is why the renaming of `HtnComplexity/Space/Rename.lean` uses the
residues `2` and `3` modulo `4`. -/
theorem bitsOfNat_four_add_two (v : ℕ) : bitsOfNat (4 * v + 2) = false :: true :: bitsOfNat v := by
  have h1 : bitsOfNat (4 * v + 2) = decide ((4 * v + 2) % 2 = 1) :: bitsOfNat ((4 * v + 2) / 2) := by
    rw [show 4 * v + 2 = (4 * v + 1) + 1 by ring, bitsOfNat_succ]
  have h2 : bitsOfNat (2 * v + 1) = decide ((2 * v + 1) % 2 = 1) :: bitsOfNat ((2 * v + 1) / 2) := by
    rw [show 2 * v + 1 = (2 * v) + 1 by ring, bitsOfNat_succ]
  rw [h1, show (4 * v + 2) / 2 = 2 * v + 1 by omega, h2]
  simp [Nat.mul_add_div]
  omega

/-- The numeral of `4 v + 3` is the numeral of `v` with `true, true` in front. -/
theorem bitsOfNat_four_add_three (v : ℕ) :
    bitsOfNat (4 * v + 3) = true :: true :: bitsOfNat v := by
  have h1 : bitsOfNat (4 * v + 3) = decide ((4 * v + 3) % 2 = 1) :: bitsOfNat ((4 * v + 3) / 2) := by
    rw [show 4 * v + 3 = (4 * v + 2) + 1 by ring, bitsOfNat_succ]
  have h2 : bitsOfNat (2 * v + 1) = decide ((2 * v + 1) % 2 = 1) :: bitsOfNat ((2 * v + 1) / 2) := by
    rw [show 2 * v + 1 = (2 * v) + 1 by ring, bitsOfNat_succ]
  rw [h1, show (4 * v + 3) / 2 = 2 * v + 1 by omega, h2]
  simp [Nat.mul_add_div]
  omega

/-! ### A number is below two to the length of its numeral -/

theorem natOfBits_lt (x : List Bool) : natOfBits x < 2 ^ x.length := by
  induction x with
  | nil => simp
  | cons b x ih =>
    rw [natOfBits_cons, List.length_cons, pow_succ]
    cases b <;> simp only [if_true, if_false, Bool.false_eq_true] <;> omega

theorem lt_two_pow_of_length_bitsOfNat_le {n L : ℕ} (h : (bitsOfNat n).length ≤ L) :
    n < 2 ^ L :=
  lt_of_lt_of_le
    (by simpa only [natOfBits_bitsOfNat] using natOfBits_lt (bitsOfNat n))
    (Nat.pow_le_pow_right (by norm_num) h)

/-! ### Every numeral of a description is written out in its serialisation -/

theorem le_length_blist_of_mem {x : List Bool} {l : List (List Bool)} (h : x ∈ l) :
    2 * x.length + 2 ≤ (blist l).length := by
  have h1 : 2 * x.length + 2 ≤ (l.map fun y => 2 * y.length + 2).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem h)
  rw [length_blist]
  omega

theorem two_length_bitsOfNat_le_serNatList {v : ℕ} {l : List ℕ} (h : v ∈ l) :
    2 * (bitsOfNat v).length + 2 ≤ (serNatList l).length := by
  have := le_length_blist_of_mem (x := bitsOfNat v) (l := l.map bitsOfNat)
    (List.mem_map_of_mem h)
  rw [serNatList]
  omega

theorem length_bitsOfNat_le_serNatList {v : ℕ} {l : List ℕ} (h : v ∈ l) :
    (bitsOfNat v).length ≤ (serNatList l).length := by
  have := two_length_bitsOfNat_le_serNatList h
  omega

theorem length_bitsOfNat_le_of_mem_initList {q : InstDesc} {v : ℕ} (h : v ∈ q.initList) :
    (bitsOfNat v).length ≤ (instSer q).length := by
  have h1 := length_bitsOfNat_le_serNatList h
  have h2 : (serNatList q.initList).length ≤ (instSer q).length := by
    simp [instSer]
  omega

theorem length_bitsOfNat_le_of_mem_goalList {q : InstDesc} {v : ℕ} (h : v ∈ q.goalList) :
    (bitsOfNat v).length ≤ (instSer q).length := by
  have h1 := length_bitsOfNat_le_serNatList h
  have h2 : (serNatList q.goalList).length ≤ (instSer q).length := by
    simp [instSer]
    omega
  omega

theorem length_bitsOfNat_add_two_le_of_mem_initList {q : InstDesc} {v : ℕ}
    (h : v ∈ q.initList) : (bitsOfNat v).length + 2 ≤ (instSer q).length := by
  have h1 := two_length_bitsOfNat_le_serNatList h
  have h2 : (serNatList q.initList).length ≤ (instSer q).length := by
    simp [instSer]
  omega

theorem length_bitsOfNat_add_two_le_of_mem_goalList {q : InstDesc} {v : ℕ}
    (h : v ∈ q.goalList) : (bitsOfNat v).length + 2 ≤ (instSer q).length := by
  have h1 := two_length_bitsOfNat_le_serNatList h
  have h2 : (serNatList q.goalList).length ≤ (instSer q).length := by
    simp [instSer]
    omega
  omega

/-! ### The name of the initial compound task -/

theorem two_le_length_instSer (q : InstDesc) : 2 ≤ (instSer q).length := by
  have h1 : 1 ≤ (serNatList q.initList).length := by
    rw [serNatList, length_blist]; omega
  have h2 : 1 ≤ (serNatList q.goalList).length := by
    rw [serNatList, length_blist]; omega
  rw [instSer]
  simp only [List.length_append]
  omega

theorem length_bitsOfNat_rootName_add_two_le (q : InstDesc) :
    (bitsOfNat (rootName q)).length + 2 ≤ (instSer q).length := by
  rcases hc : q.tnI.compoundNames with _ | ⟨c, cs⟩
  · simpa [rootName, hc] using two_le_length_instSer q
  · have hmem : c ∈ q.tnI.compoundNames := by rw [hc]; exact List.mem_cons_self
    obtain ⟨i, -, hlab⟩ := TnDesc.mem_compoundNames.1 hmem
    have hlook : q.tnI.lbl.lookup i = some (true, c) := by
      rcases hl : q.tnI.lbl.lookup i with _ | ⟨b, n⟩
      · rw [TnDesc.label, hl] at hlab; exact absurd hlab (by simp)
      · cases b
        · rw [TnDesc.label, hl] at hlab; exact absurd hlab (by simp)
        · rw [TnDesc.label, hl] at hlab
          simp only [Sum.inr.injEq] at hlab
          subst hlab
          rfl
    have hin : (i, true, c) ∈ q.tnI.lbl := mem_of_lookup_eq_some hlook
    have h1 : 2 * (serLbl (i, true, c)).length + 2 ≤ (serLblList q.tnI.lbl).length := by
      have := le_length_blist_of_mem (x := serLbl (i, true, c))
        (l := q.tnI.lbl.map serLbl) (List.mem_map_of_mem hin)
      rw [serLblList]
      omega
    have h2 : 2 * (bitsOfNat c).length + 1 ≤ (serLbl (i, true, c)).length := by
      simp [serLbl, serNat]
      omega
    have h3 : (serLblList q.tnI.lbl).length ≤ (instSer q).length := by
      simp [instSer, tnSer]
      omega
    rw [rootName, hc]
    simp only [List.headI]
    omega

theorem length_bitsOfNat_rootName_le (q : InstDesc) :
    (bitsOfNat (rootName q)).length ≤ (instSer q).length := by
  have := length_bitsOfNat_rootName_add_two_le q
  omega

/-! ### The facts of the renamed compiled problem -/

theorem mem_regInitR_lt {q : InstDesc} {f L : ℕ} (hL : (instSer q).length ≤ L)
    (h : f ∈ regInitR q) : f < 2 ^ (L + 2) := by
  have hpow : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by ring
  rcases List.mem_append.1 h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    have := lt_two_pow_of_length_bitsOfNat_le
      ((length_bitsOfNat_le_of_mem_initList hv).trans hL)
    omega
  · rw [List.mem_singleton.1 h]
    have := lt_two_pow_of_length_bitsOfNat_le
      ((length_bitsOfNat_rootName_le q).trans hL)
    omega

theorem mem_regGoalR_lt {q : InstDesc} {f L : ℕ} (hL : (instSer q).length ≤ L)
    (h : f ∈ regGoalR q) : f < 2 ^ (L + 2) := by
  have hpow : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by ring
  have hone : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  rcases List.mem_append.1 h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    have := lt_two_pow_of_length_bitsOfNat_le
      ((length_bitsOfNat_le_of_mem_goalList hv).trans hL)
    omega
  · rw [List.mem_singleton.1 h]
    omega


/-! ### The compiled problem is small enough for the machine -/

theorem length_bitsOfNat_le_of_mem_regInitR {q : InstDesc} {f : ℕ} (h : f ∈ regInitR q) :
    (bitsOfNat f).length ≤ (instSer q).length := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    have := length_bitsOfNat_add_two_le_of_mem_initList hv
    rw [bitsOfNat_four_add_two]
    simp only [List.length_cons]
    omega
  · rw [List.mem_singleton.1 h, bitsOfNat_four_add_three]
    have := length_bitsOfNat_rootName_add_two_le q
    simp only [List.length_cons]
    omega

theorem length_bitsOfNat_le_of_mem_regGoalR {q : InstDesc} {f : ℕ} (h : f ∈ regGoalR q) :
    (bitsOfNat f).length ≤ (instSer q).length := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    have := length_bitsOfNat_add_two_le_of_mem_goalList hv
    rw [bitsOfNat_four_add_two]
    simp only [List.length_cons]
    omega
  · rw [List.mem_singleton.1 h]
    simp

theorem length_succ_le_length_blist (l : List (List Bool)) :
    l.length + 1 ≤ (blist l).length := by
  rw [length_blist]
  have h : l.length ≤ (l.map fun x => 2 * x.length + 2).sum := by
    induction l with
    | nil => simp
    | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
  omega

theorem length_regInitR_le (q : InstDesc) : (regInitR q).length ≤ (instSer q).length := by
  have h1 : q.initList.length + 1 ≤ (serNatList q.initList).length := by
    have := length_succ_le_length_blist (q.initList.map bitsOfNat)
    rw [serNatList]
    simpa using this
  have h2 : (serNatList q.initList).length ≤ (instSer q).length := by
    simp [instSer]
  rw [regInitR]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

end Space

end HTN
