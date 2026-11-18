import HtnComplexity.Complexity.RecMemSim
import HtnComplexity.Complexity.AltMemPrimrec
/-!
# The recursive encoding: its size, and that it is produced by an algorithm

The description `HTN.Syn.rmDom M n` of `HtnComplexity/Complexity/RecMemDom.lean` has

* a size that depends on the **machine only** (`HTN.Syn.size_rmDom_le`): unlike
  `HTN.Syn.amDom`, whose size is linear in the number of steps the machine is allowed, it lists
  one action per transition and one method per transition, whatever the length of the input and
  however long the computation runs;
* and it is primitive recursive in the input length, for a machine that may itself grow with the
  input length (`HTN.Syn.computable_rmDom_fam`).

Together with the correctness theorem `HTN.Syn.solvable_rmDom_iff` these are the three things a
polynomial-time hardness family needs of its fixed part; the family itself is assembled in
`HtnComplexity/Complexity/RecMemUniform.lean`.
-/

namespace HTN

namespace Syn

open Binarise

variable {M : RecAltMem}

/-! ### Size -/

/-- A bound on the size of every action of the encoding. -/
def rmBudget (M : RecAltMem) : ℕ :=
  4 + M.mem + (M.ex.map fun t => t.inG.length + t.memG.length).sum
    + (M.un.map fun t => t.inG.length + t.memG.length).sum
    + (M.acc.map fun c => c.inG.length + c.memG.length).sum

theorem rm_length_guard_ex_le (i : ℕ) :
    (M.ex.getI i).inG.length + (M.ex.getI i).memG.length ≤
      (M.ex.map fun t => t.inG.length + t.memG.length).sum := by
  by_cases hi : i < M.ex.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.ex) hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem rm_length_guard_un_le (j : ℕ) :
    (M.un.getI j).inG.length + (M.un.getI j).memG.length ≤
      (M.un.map fun t => t.inG.length + t.memG.length).sum := by
  by_cases hj : j < M.un.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.un) hj]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem rm_length_guard_acc_le (a : ℕ) :
    (M.acc.getI a).inG.length + (M.acc.getI a).memG.length ≤
      (M.acc.map fun c => c.inG.length + c.memG.length).sum := by
  by_cases ha : a < M.acc.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.acc) ha]
    exact List.mem_map_of_mem (List.getElem_mem ha)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem size_rmActData_le (n j : ℕ) :
    ActionDesc.size (j, rmActData M n j) ≤ rmBudget M := by
  have he := rm_length_guard_ex_le (M := M) (j / 4)
  have hu := rm_length_guard_un_le (M := M) (j / 4)
  have ha := rm_length_guard_acc_le (M := M) (j / 4)
  rw [ActionDesc.size, rmActData, rmBudget]
  by_cases h0 : j % 4 = 0
  · simp only [if_pos h0, rmFwdData, List.length_append, List.length_cons, List.length_map,
      List.length_nil]
    omega
  · rw [if_neg h0]
    by_cases h1 : j % 4 = 1
    · simp only [if_pos h1, rmUndoData, List.length_cons, List.length_nil]
      omega
    · rw [if_neg h1]
      by_cases h2 : j % 4 = 2
      · simp only [if_pos h2, rmGrdData, List.length_append, List.length_map, List.length_nil]
        omega
      · rw [if_neg h2]
        by_cases h3 : j / 4 < M.acc.length
        · simp only [if_pos h3, rmAccData, List.length_append, List.length_map, List.length_nil]
          omega
        · simp only [if_neg h3, rmInitData, List.length_map, List.length_range, List.length_nil]
          omega

theorem size_rmActions_le (n : ℕ) :
    ((rmActions M n).map ActionDesc.size).sum ≤ rmNumActs M * rmBudget M := by
  have hb : ∀ x ∈ (rmActions M n).map ActionDesc.size, x ≤ rmBudget M := by
    intro x hx
    simp only [List.mem_map, rmActions] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simp only [List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact size_rmActData_le n j
  have h := List.sum_le_card_nsmul _ (rmBudget M) hb
  rwa [List.length_map, rmActions, List.length_map, List.length_range, smul_eq_mul] at h

theorem size_rmRootMethods : ((rmRootMethods M).map MethodDesc.size).sum = 6 := by
  simp [rmRootMethods, MethodDesc.size]

theorem size_rmExMethods_le : ((rmExMethods M).map MethodDesc.size).sum ≤ 6 * M.ex.length := by
  have hb : ∀ x ∈ (rmExMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨i, -, rfl⟩ := mem_rmExMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (rmExMethods M).length = M.ex.length := by simp [rmExMethods]
  omega

theorem size_rmDMethods_le : ((rmDMethods M).map MethodDesc.size).sum ≤ 6 * M.ex.length := by
  have hb : ∀ x ∈ (rmDMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨i, -, rfl⟩ := mem_rmDMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (rmDMethods M).length = M.ex.length := by simp [rmDMethods]
  omega

theorem size_rmUnMethods_le : ((rmUnMethods M).map MethodDesc.size).sum ≤ 6 * M.un.length := by
  have hb : ∀ x ∈ (rmUnMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := mem_rmUnMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (rmUnMethods M).length = M.un.length := by simp [rmUnMethods]
  omega

theorem size_rmBrMethods_le : ((rmBrMethods M).map MethodDesc.size).sum ≤ 6 * M.un.length := by
  have hb : ∀ x ∈ (rmBrMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := mem_rmBrMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (rmBrMethods M).length = M.un.length := by simp [rmBrMethods]
  omega

theorem size_rmAccMethods_le : ((rmAccMethods M).map MethodDesc.size).sum ≤ 6 * M.acc.length := by
  have hb : ∀ x ∈ (rmAccMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨a, -, rfl⟩ := mem_rmAccMethods he
    simp [MethodDesc.size, TnDesc.size, singleBody, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (rmAccMethods M).length = M.acc.length := by simp [rmAccMethods]
  omega

/-- The bound on the size of the description: it depends on the machine alone. -/
def rmConst (M : RecAltMem) : ℕ :=
  rmNumActs M * rmBudget M + 6 * (2 * M.ex.length + 2 * M.un.length + M.acc.length + 1)

/-- **The description has a size that does not depend on the length of the input word** — nor,
therefore, on the number of steps the machine makes. -/
theorem size_rmDom_le (n : ℕ) : (rmDom M n).size ≤ rmConst M := by
  have ha := size_rmActions_le (M := M) n
  have h0 := size_rmRootMethods (M := M)
  have h1 := size_rmExMethods_le (M := M)
  have h2 := size_rmDMethods_le (M := M)
  have h3 := size_rmUnMethods_le (M := M)
  have h4 := size_rmBrMethods_le (M := M)
  have h5 := size_rmAccMethods_le (M := M)
  simp only [DomDesc.size, rmDom_actions, rmDom_methods, List.map_append, List.sum_append,
    rmConst]
  omega

/-! ### The description is produced by an algorithm

The statement is proved for a machine that may itself depend on the input length, which is what
a uniform family needs. -/

/-- **The components of a family of recursive alternating machines are primitive recursive.** -/
structure RecMachFamPrimrec (Mf : ℕ → RecAltMem) : Prop where
  /-- The number of memory bits. -/
  mem : Primrec fun n => (Mf n).mem
  /-- The initial state. -/
  start : Primrec fun n => (Mf n).start
  /-- The accepting conditions. -/
  acc : Primrec fun n => (Mf n).acc
  /-- The existential transitions. -/
  ex : Primrec fun n => (Mf n).ex
  /-- The universal transitions. -/
  un : Primrec fun n => (Mf n).un

variable {Mf : ℕ → RecAltMem}

theorem primrec_rmInFact : Primrec rmInFact := primrec_posFactPair

theorem primrec_rmActData_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun p : ℕ × ℕ => rmActData (Mf p.1) p.1 p.2 := by
  have hn : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hex : Primrec fun p : ℕ × ℕ => (Mf p.1).ex := h.ex.comp Primrec.fst
  have hun : Primrec fun p : ℕ × ℕ => (Mf p.1).un := h.un.comp Primrec.fst
  have hacc : Primrec fun p : ℕ × ℕ => (Mf p.1).acc := h.acc.comp Primrec.fst
  have hmem : Primrec fun p : ℕ × ℕ => (Mf p.1).mem := h.mem.comp Primrec.fst
  have hacclen : Primrec fun p : ℕ × ℕ => (Mf p.1).acc.length := Primrec.list_length.comp hacc
  have hd4 : Primrec fun p : ℕ × ℕ => p.2 / 4 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hm4 : Primrec fun p : ℕ × ℕ => p.2 % 4 :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hmapof : Primrec₂ fun (p : ℕ × ℕ) (l : MemLit) => amRailOf p.1 l :=
    primrec_amRailOf.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hmapin : Primrec₂ fun (_ : ℕ × ℕ) (l : InLit) => rmInFact l :=
    primrec_rmInFact.comp Primrec.snd
  have hfwd : Primrec fun p : ℕ × ℕ => rmFwdData (Mf p.1) p.1 (p.2 / 4) := by
    have htex := Primrec.list_getI.comp hex hd4
    have h2 := Primrec.snd.comp htex
    have hinL := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hmemL := Primrec.fst.comp h3
    have h4 := Primrec.snd.comp h3
    have hwr := Primrec.fst.comp h4
    have hidx := Primrec.fst.comp hwr
    have hwr2 := Primrec.snd.comp hwr
    have hold := Primrec.fst.comp hwr2
    have hnew := Primrec.snd.comp hwr2
    have hrailold := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hold))
    have hrailnew := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hnew))
    have hinmap := Primrec.list_map hinL hmapin
    have hmemmap := Primrec.list_map hmemL hmapof
    exact Primrec.pair
      (Primrec.list_append.comp hinmap (Primrec.list_cons.comp hrailold hmemmap))
      (Primrec.pair (Primrec.list_cons.comp hrailnew (Primrec.const []))
        (Primrec.list_cons.comp hrailold (Primrec.const [])))
  have hundo : Primrec fun p : ℕ × ℕ => rmUndoData (Mf p.1) p.1 (p.2 / 4) := by
    have htex := Primrec.list_getI.comp hex hd4
    have h2 := Primrec.snd.comp htex
    have h3 := Primrec.snd.comp h2
    have h4 := Primrec.snd.comp h3
    have hwr := Primrec.fst.comp h4
    have hidx := Primrec.fst.comp hwr
    have hwr2 := Primrec.snd.comp hwr
    have hold := Primrec.fst.comp hwr2
    have hnew := Primrec.snd.comp hwr2
    have hrailold := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hold))
    have hrailnew := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hnew))
    exact Primrec.pair (Primrec.list_cons.comp hrailnew (Primrec.const []))
      (Primrec.pair (Primrec.list_cons.comp hrailold (Primrec.const []))
        (Primrec.list_cons.comp hrailnew (Primrec.const [])))
  have hgrd : Primrec fun p : ℕ × ℕ => rmGrdData (Mf p.1) p.1 (p.2 / 4) := by
    have htun := Primrec.list_getI.comp hun hd4
    have h2 := Primrec.snd.comp htun
    have hinL := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hmemL := Primrec.fst.comp h3
    have hinmap := Primrec.list_map hinL hmapin
    have hmemmap := Primrec.list_map hmemL hmapof
    exact Primrec.pair (Primrec.list_append.comp hinmap hmemmap)
      (Primrec.pair (Primrec.const []) (Primrec.const []))
  have haccd : Primrec fun p : ℕ × ℕ => rmAccData (Mf p.1) p.1 (p.2 / 4) := by
    have htacc := Primrec.list_getI.comp hacc hd4
    have h2 := Primrec.snd.comp htacc
    have hinL := Primrec.fst.comp h2
    have hmemL := Primrec.snd.comp h2
    have hinmap := Primrec.list_map hinL hmapin
    have hmemmap := Primrec.list_map hmemL hmapof
    exact Primrec.pair (Primrec.list_append.comp hinmap hmemmap)
      (Primrec.pair (Primrec.const []) (Primrec.const []))
  have hinit : Primrec fun p : ℕ × ℕ => rmInitData (Mf p.1) p.1 := by
    have hmapinit : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) => amRail p.1 i false :=
      primrec_amRailTriple.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.const false)))
    have hrange : Primrec fun p : ℕ × ℕ => List.range (Mf p.1).mem :=
      Primrec.list_range.comp hmem
    have hmap := Primrec.list_map hrange hmapinit
    exact Primrec.pair (Primrec.const []) (Primrec.pair hmap (Primrec.const []))
  refine (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 0)
    (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 0)) hfwd
    (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 1)
      (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 1)) hundo
      (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 2)
        (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 2)) hgrd
        (Primrec.ite (c := fun p : ℕ × ℕ => p.2 / 4 < (Mf p.1).acc.length)
          (PrimrecRel.comp Primrec.nat_lt hd4 hacclen)
          haccd hinit)))).of_eq fun p => rfl

theorem primrec_rmActions_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmActions (Mf n) n := by
  refine Primrec.list_map (Primrec.list_range.comp ?_) ?_
  · have hnum : Primrec fun n : ℕ =>
        4 * ((Mf n).ex.length + (Mf n).un.length + (Mf n).acc.length + 1) :=
      Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp (Primrec.list_length.comp h.ex)
              (Primrec.list_length.comp h.un))
            (Primrec.list_length.comp h.acc))
          (Primrec.const 1))
    exact hnum.of_eq fun n => rfl
  · exact Primrec.pair Primrec.snd (primrec_rmActData_fam h)

/-- The root method, with the two-task body written out. -/
theorem rmRootMethods_raw (M : RecAltMem) :
    rmRootMethods M = [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
      ([(0, false, 4 * M.acc.length + 3), (1, true, 4 * M.start + 1)] :
        List (ℕ × Bool × ℕ))))] := rfl

theorem primrec_rmRootMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmRootMethods (Mf n) := by
  have key : Primrec fun n : ℕ =>
      [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * (Mf n).acc.length + 3), (1, true, 4 * (Mf n).start + 1)] :
          List (ℕ × Bool × ℕ))))] := by
    have hinit : Primrec fun n : ℕ => 4 * (Mf n).acc.length + 3 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.list_length.comp h.acc))
        (Primrec.const 3)
    have hname : Primrec fun n : ℕ => 4 * (Mf n).start + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) h.start) (Primrec.const 1)
    refine Primrec.list_cons.comp ?_ (Primrec.const [])
    refine Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const [0, 1]) (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hinit))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hname))
        (Primrec.const []))
  exact key.of_eq fun n => (rmRootMethods_raw (Mf n)).symm

/-- The existential methods, with the two-task bodies written out. -/
theorem rmExMethods_raw (M : RecAltMem) :
    rmExMethods M = (List.range M.ex.length).map fun i =>
      ((4 * (M.ex.getI i).src + 1 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * i), (1, true, 4 * i + 3)] : List (ℕ × Bool × ℕ)))) := rfl

theorem primrec_rmExMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmExMethods (Mf n) := by
  have key : Primrec fun n : ℕ => (List.range (Mf n).ex.length).map fun i =>
      ((4 * ((Mf n).ex.getI i).src + 1 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * i), (1, true, 4 * i + 3)] : List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.ex)) ?_
    have ii : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (h.ex.comp Primrec.fst) ii
    have hsrc := Primrec.fst.comp hget
    have hname : Primrec fun w : ℕ × ℕ => 4 * ((Mf w.1).ex.getI w.2).src + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hsrc) (Primrec.const 1)
    have hfwd : Primrec fun w : ℕ × ℕ => 4 * w.2 :=
      Primrec.nat_mul.comp (Primrec.const 4) ii
    have hd : Primrec fun w : ℕ × ℕ => 4 * w.2 + 3 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ii) (Primrec.const 3)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hfwd))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hd))
        (Primrec.const []))
  exact key.of_eq fun n => (rmExMethods_raw (Mf n)).symm

/-- The undoing methods, with the two-task bodies written out. -/
theorem rmDMethods_raw (M : RecAltMem) :
    rmDMethods M = (List.range M.ex.length).map fun i =>
      ((4 * i + 3 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, true, 4 * (M.ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
          List (ℕ × Bool × ℕ)))) := rfl

theorem primrec_rmDMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmDMethods (Mf n) := by
  have key : Primrec fun n : ℕ => (List.range (Mf n).ex.length).map fun i =>
      ((4 * i + 3 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, true, 4 * ((Mf n).ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
          List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.ex)) ?_
    have ii : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (h.ex.comp Primrec.fst) ii
    have htgt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget)))
    have hname : Primrec fun w : ℕ × ℕ => 4 * w.2 + 3 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ii) (Primrec.const 3)
    have hc := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) htgt)
      (Primrec.const 1)
    have hu : Primrec fun w : ℕ × ℕ => 4 * w.2 + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ii) (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const false) hu))
        (Primrec.const []))
  exact key.of_eq fun n => (rmDMethods_raw (Mf n)).symm

/-- The universal methods, with the two-task bodies written out. -/
theorem rmUnMethods_raw (M : RecAltMem) :
    rmUnMethods M = (List.range M.un.length).map fun j =>
      ((4 * (M.un.getI j).src + 1 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * j + 2), (1, true, 4 * j + 2)] : List (ℕ × Bool × ℕ)))) := rfl

theorem primrec_rmUnMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmUnMethods (Mf n) := by
  have key : Primrec fun n : ℕ => (List.range (Mf n).un.length).map fun j =>
      ((4 * ((Mf n).un.getI j).src + 1 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * j + 2), (1, true, 4 * j + 2)] : List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.un)) ?_
    have jj : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (h.un.comp Primrec.fst) jj
    have hsrc := Primrec.fst.comp hget
    have hname : Primrec fun w : ℕ × ℕ => 4 * ((Mf w.1).un.getI w.2).src + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hsrc) (Primrec.const 1)
    have hgb : Primrec fun w : ℕ × ℕ => 4 * w.2 + 2 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) jj) (Primrec.const 2)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hgb))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hgb))
        (Primrec.const []))
  exact key.of_eq fun n => (rmUnMethods_raw (Mf n)).symm

/-- The branching methods, with the two-task bodies written out. -/
theorem rmBrMethods_raw (M : RecAltMem) :
    rmBrMethods M = (List.range M.un.length).map fun j =>
      ((4 * j + 2 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, true, 4 * (M.un.getI j).tgt₁ + 1), (1, true, 4 * (M.un.getI j).tgt₂ + 1)] :
          List (ℕ × Bool × ℕ)))) := rfl

theorem primrec_rmBrMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmBrMethods (Mf n) := by
  have key : Primrec fun n : ℕ => (List.range (Mf n).un.length).map fun j =>
      ((4 * j + 2 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, true, 4 * ((Mf n).un.getI j).tgt₁ + 1),
          (1, true, 4 * ((Mf n).un.getI j).tgt₂ + 1)] : List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.un)) ?_
    have jj : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (h.un.comp Primrec.fst) jj
    have hrest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    have ht1 := Primrec.fst.comp hrest
    have ht2 := Primrec.snd.comp hrest
    have hname : Primrec fun w : ℕ × ℕ => 4 * w.2 + 2 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) jj) (Primrec.const 2)
    have hc1 := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ht1)
      (Primrec.const 1)
    have hc2 := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ht2)
      (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc1))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hc2))
        (Primrec.const []))
  exact key.of_eq fun n => (rmBrMethods_raw (Mf n)).symm

/-- The accepting methods, with the one-task bodies written out. -/
theorem rmAccMethods_raw (M : RecAltMem) :
    rmAccMethods M = (List.range M.acc.length).map fun a =>
      ((4 * (M.acc.getI a).st + 1 : ℕ), (([0] : List ℕ), ([] : List (ℕ × ℕ)),
        ([(0, false, 4 * a + 3)] : List (ℕ × Bool × ℕ)))) := rfl

theorem primrec_rmAccMethods_fam (h : RecMachFamPrimrec Mf) :
    Primrec fun n => rmAccMethods (Mf n) := by
  have key : Primrec fun n : ℕ => (List.range (Mf n).acc.length).map fun a =>
      ((4 * ((Mf n).acc.getI a).st + 1 : ℕ), (([0] : List ℕ), ([] : List (ℕ × ℕ)),
        ([(0, false, 4 * a + 3)] : List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.acc)) ?_
    have aa : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (h.acc.comp Primrec.fst) aa
    have hst := Primrec.fst.comp hget
    have hname : Primrec fun w : ℕ × ℕ => 4 * ((Mf w.1).acc.getI w.2).st + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hst) (Primrec.const 1)
    have hact : Primrec fun w : ℕ × ℕ => 4 * w.2 + 3 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) aa) (Primrec.const 3)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0])
      (Primrec.pair (Primrec.const []) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.const [])
  exact key.of_eq fun n => (rmAccMethods_raw (Mf n)).symm

/-- **The description of the recursive encoding is produced by an algorithm**, uniformly in the
input length and for a machine that may itself depend on it. -/
theorem computable_rmDom_fam (h : RecMachFamPrimrec Mf) :
    Computable fun n => rmDom (Mf n) n :=
  (Primrec.pair (primrec_rmActions_fam h)
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp (primrec_rmRootMethods_fam h) (primrec_rmExMethods_fam h))
            (primrec_rmDMethods_fam h))
          (primrec_rmUnMethods_fam h))
        (primrec_rmBrMethods_fam h))
      (primrec_rmAccMethods_fam h))).to_comp

end Syn

end HTN
