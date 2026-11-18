import HtnComplexity.Complexity.AltMemSim
/-!
# Alternation with a memory: size, computability, and the hardness family

The domain description `HTN.Syn.amDom` of `HtnComplexity/Complexity/AltMemDom.lean` has size
linear in the length of the input word and is primitive recursive in it, so — with the
correctness theorem `HTN.Syn.solvable_amDom_iff` of `HtnComplexity/Complexity/AltMemSim.lean`
— it gives a polynomial-time hardness family

    HTN.Syn.amFamily M : Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root M.Accepts

for the language of an **alternating machine with a memory**, in `TO-HTN-AC` with a rooted
instance, hence in each of the three source classes `TO-HTN`, `HTN-TR`, `HTN-AC` of the eight
open cells of the compilability table.
-/

namespace HTN

namespace Syn

open Binarise

variable {M : BitAltMem}

/-! ### Size -/

/-- A bound on the size of every action of the encoding. -/
def amBudget (M : BitAltMem) : ℕ :=
  5 + M.mem + (M.ex.map fun t => t.guard.length).sum + (M.un.map fun t => t.guard.length).sum
    + (M.acc.map fun c => c.guard.length).sum

theorem length_guard_ex_le (i : ℕ) :
    (M.ex.getI i).guard.length ≤ (M.ex.map fun t => t.guard.length).sum := by
  by_cases hi : i < M.ex.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.ex) hi]
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem length_guard_un_le (j : ℕ) :
    (M.un.getI j).guard.length ≤ (M.un.map fun t => t.guard.length).sum := by
  by_cases hj : j < M.un.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.un) hj]
    exact List.mem_map_of_mem (List.getElem_mem hj)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem length_guard_acc_le (a : ℕ) :
    (M.acc.getI a).guard.length ≤ (M.acc.map fun c => c.guard.length).sum := by
  by_cases ha : a < M.acc.length
  · refine List.single_le_sum (fun x _ => Nat.zero_le x) _ ?_
    rw [List.getI_eq_getElem (l := M.acc) ha]
    exact List.mem_map_of_mem (List.getElem_mem ha)
  · rw [List.getI_eq_default _ (by omega)]
    exact Nat.zero_le _

theorem size_amActData_le (n j : ℕ) :
    ActionDesc.size (j, amActData M n j) ≤ amBudget M := by
  have he := length_guard_ex_le (M := M) (j / 4 % M.ex.length)
  have hu := length_guard_un_le (M := M) (j / 4 % M.un.length)
  have ha := length_guard_acc_le (M := M) (j / 4)
  rw [ActionDesc.size, amActData, amBudget]
  by_cases h0 : j % 4 = 0
  · simp only [if_pos h0, amFwdData, List.length_cons, List.length_map, List.length_nil]
    omega
  · rw [if_neg h0]
    by_cases h1 : j % 4 = 1
    · simp only [if_pos h1, amUndoData, List.length_cons, List.length_nil]
      omega
    · rw [if_neg h1]
      by_cases h2 : j % 4 = 2
      · simp only [if_pos h2, amGrdData, List.length_cons, List.length_map, List.length_nil]
        omega
      · rw [if_neg h2]
        by_cases h3 : j / 4 < M.acc.length
        · simp only [if_pos h3, amAccData, List.length_map, List.length_nil]
          omega
        · simp only [if_neg h3, amInitData, List.length_map, List.length_range, List.length_nil]
          omega

theorem size_amActions_le (n : ℕ) :
    ((amActions M n).map ActionDesc.size).sum ≤ amNumActs M n * amBudget M := by
  have hb : ∀ x ∈ (amActions M n).map ActionDesc.size, x ≤ amBudget M := by
    intro x hx
    simp only [List.mem_map, amActions] at hx
    obtain ⟨e, he, rfl⟩ := hx
    simp only [List.mem_range] at he
    obtain ⟨j, -, rfl⟩ := he
    exact size_amActData_le n j
  have h := List.sum_le_card_nsmul _ (amBudget M) hb
  rwa [List.length_map, amActions, List.length_map, List.length_range, smul_eq_mul] at h

theorem size_amRootMethods (n : ℕ) :
    ((amRootMethods M n).map MethodDesc.size).sum = 6 := by
  simp [amRootMethods, MethodDesc.size]

theorem size_amExMethods_le (n : ℕ) :
    ((amExMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.ex.length) := by
  have hlen : (amExMethods M n).length ≤ n * M.ex.length := by
    have h := length_flatMap_le (List.range n)
      (fun k => (List.range M.ex.length).map fun i =>
        (amCName (k + 1) (M.ex.getI i).src,
          pairBody (Sum.inl (amFwd M k i)) (Sum.inr (amDName k i))))
      M.ex.length (fun _ _ => by simp)
    simp only [amExMethods, List.length_range] at h ⊢
    exact h
  have hb : ∀ x ∈ (amExMethods M n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, i, -, rfl⟩ := mem_amExMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((amExMethods M n).map MethodDesc.size).sum ≤ (amExMethods M n).length * 6 := h
    _ ≤ (n * M.ex.length) * 6 := Nat.mul_le_mul_right _ hlen
    _ = 6 * (n * M.ex.length) := Nat.mul_comm _ _

theorem size_amDMethods_le (n : ℕ) :
    ((amDMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.ex.length) := by
  have hlen : (amDMethods M n).length ≤ n * M.ex.length := by
    have h := length_flatMap_le (List.range n)
      (fun k => (List.range M.ex.length).map fun i =>
        (amDName k i,
          pairBody (Sum.inr (amCName k (M.ex.getI i).tgt)) (Sum.inl (amUndo i))))
      M.ex.length (fun _ _ => by simp)
    simp only [amDMethods, List.length_range] at h ⊢
    exact h
  have hb : ∀ x ∈ (amDMethods M n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, i, -, rfl⟩ := mem_amDMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((amDMethods M n).map MethodDesc.size).sum ≤ (amDMethods M n).length * 6 := h
    _ ≤ (n * M.ex.length) * 6 := Nat.mul_le_mul_right _ hlen
    _ = 6 * (n * M.ex.length) := Nat.mul_comm _ _

theorem size_amUnMethods_le (n : ℕ) :
    ((amUnMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.un.length) := by
  have hlen : (amUnMethods M n).length ≤ n * M.un.length := by
    have h := length_flatMap_le (List.range n)
      (fun k => (List.range M.un.length).map fun j =>
        (amCName (k + 1) (M.un.getI j).src,
          pairBody (Sum.inl (amGrd M k j))
            (Sum.inr (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂))))
      M.un.length (fun _ _ => by simp)
    simp only [amUnMethods, List.length_range] at h ⊢
    exact h
  have hb : ∀ x ∈ (amUnMethods M n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, j, -, rfl⟩ := mem_amUnMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((amUnMethods M n).map MethodDesc.size).sum ≤ (amUnMethods M n).length * 6 := h
    _ ≤ (n * M.un.length) * 6 := Nat.mul_le_mul_right _ hlen
    _ = 6 * (n * M.un.length) := Nat.mul_comm _ _

theorem size_amBrMethods_le (n : ℕ) :
    ((amBrMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.un.length) := by
  have hlen : (amBrMethods M n).length ≤ n * M.un.length := by
    have h := length_flatMap_le (List.range n)
      (fun k => (List.range M.un.length).map fun j =>
        (amBrName k (M.un.getI j).tgt₁ (M.un.getI j).tgt₂,
          pairBody (Sum.inr (amCName k (M.un.getI j).tgt₁))
            (Sum.inr (amCName k (M.un.getI j).tgt₂))))
      M.un.length (fun _ _ => by simp)
    simp only [amBrMethods, List.length_range] at h ⊢
    exact h
  have hb : ∀ x ∈ (amBrMethods M n).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨k, -, j, -, rfl⟩ := mem_amBrMethods he
    simp [MethodDesc.size]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  calc ((amBrMethods M n).map MethodDesc.size).sum ≤ (amBrMethods M n).length * 6 := h
    _ ≤ (n * M.un.length) * 6 := Nat.mul_le_mul_right _ hlen
    _ = 6 * (n * M.un.length) := Nat.mul_comm _ _

theorem size_amAccMethods_le :
    ((amAccMethods M).map MethodDesc.size).sum ≤ 6 * M.acc.length := by
  have hb : ∀ x ∈ (amAccMethods M).map MethodDesc.size, x ≤ 6 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨a, -, rfl⟩ := mem_amAccMethods he
    simp [MethodDesc.size, TnDesc.size, singleBody, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h := List.sum_le_card_nsmul _ 6 hb
  rw [List.length_map, smul_eq_mul] at h
  have hl : (amAccMethods M).length = M.acc.length := by
    simp [amAccMethods]
  calc ((amAccMethods M).map MethodDesc.size).sum ≤ (amAccMethods M).length * 6 := h
    _ = M.acc.length * 6 := by rw [hl]
    _ = 6 * M.acc.length := Nat.mul_comm _ _

/-- The coefficient of the linear size bound. -/
def amCoef (M : BitAltMem) : ℕ :=
  4 * (M.ex.length + M.un.length) * amBudget M + 12 * (M.ex.length + M.un.length)

/-- The constant of the linear size bound. -/
def amConst (M : BitAltMem) : ℕ :=
  4 * (M.ex.length + M.acc.length + 1) * amBudget M + 6 * M.acc.length + 6

/-- **The description has size linear in the length of the input word.** -/
theorem size_amDom_le (n : ℕ) : (amDom M n).size ≤ amCoef M * n + amConst M := by
  have hsplit : (amDom M n).size = ((amActions M n).map ActionDesc.size).sum
      + (((amRootMethods M n).map MethodDesc.size).sum
        + (((amExMethods M n).map MethodDesc.size).sum
          + (((amDMethods M n).map MethodDesc.size).sum
            + (((amUnMethods M n).map MethodDesc.size).sum
              + (((amBrMethods M n).map MethodDesc.size).sum
                + ((amAccMethods M).map MethodDesc.size).sum))))) := by
    simp [DomDesc.size, amDom, DomDesc.actions, DomDesc.methods, List.map_append,
      List.sum_append]
  have h1 := size_amActions_le (M := M) n
  have h2 := size_amRootMethods (M := M) n
  have h3 := size_amExMethods_le (M := M) n
  have h4 := size_amDMethods_le (M := M) n
  have h5 := size_amUnMethods_le (M := M) n
  have h6 := size_amBrMethods_le (M := M) n
  have h7 := size_amAccMethods_le (M := M)
  have hnum : amNumActs M n * amBudget M
      ≤ 4 * (M.ex.length + M.un.length) * amBudget M * n
        + 4 * (M.ex.length + M.acc.length + 1) * amBudget M :=
    Nat.le_of_eq (by simp only [amNumActs]; ring)
  rw [hsplit, h2, amCoef, amConst]
  nlinarith [h1, h3, h4, h5, h6, h7, hnum]

/-! ### Computability -/

theorem primrec_amRailOf : Primrec fun x : ℕ × MemLit => amRailOf x.1 x.2 := by
  have h : Primrec fun x : ℕ × MemLit => 2 * (x.1 + x.2.1 + 1) + x.2.2.toNat :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.const 1)))
      (primrec_toNat.comp (Primrec.snd.comp Primrec.snd))
  refine h.of_eq fun x => ?_
  obtain ⟨n, i, b⟩ := x
  cases b <;> simp [amRailOf, amRail, posFact]

theorem primrec_posFactPair : Primrec fun x : ℕ × Bool => posFact x.1 x.2 := by
  have h : Primrec fun x : ℕ × Bool => 2 * (x.1 + 1) + x.2.toNat :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)))
      (primrec_toNat.comp Primrec.snd)
  refine h.of_eq fun x => ?_
  obtain ⟨k, b⟩ := x
  cases b <;> simp [posFact]

theorem primrec_amRailTriple : Primrec fun x : ℕ × ℕ × Bool => amRail x.1 x.2.1 x.2.2 :=
  primrec_amRailOf.comp (Primrec.pair Primrec.fst Primrec.snd)

theorem primrec_amActData : Primrec (fun p : ℕ × ℕ => amActData M p.1 p.2) := by
  have hn : Primrec fun p : ℕ × ℕ => p.1 := Primrec.fst
  have hd4 : Primrec fun p : ℕ × ℕ => p.2 / 4 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hm4 : Primrec fun p : ℕ × ℕ => p.2 % 4 :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hkex : Primrec fun p : ℕ × ℕ => p.2 / 4 / M.ex.length :=
    Primrec.nat_div.comp hd4 (Primrec.const M.ex.length)
  have hiex : Primrec fun p : ℕ × ℕ => p.2 / 4 % M.ex.length :=
    Primrec.nat_mod.comp hd4 (Primrec.const M.ex.length)
  have hkun : Primrec fun p : ℕ × ℕ => p.2 / 4 / M.un.length :=
    Primrec.nat_div.comp hd4 (Primrec.const M.un.length)
  have hiun : Primrec fun p : ℕ × ℕ => p.2 / 4 % M.un.length :=
    Primrec.nat_mod.comp hd4 (Primrec.const M.un.length)
  have hmapof : Primrec₂ fun (p : ℕ × ℕ) (l : MemLit) => amRailOf p.1 l :=
    primrec_amRailOf.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hfwd : Primrec fun p : ℕ × ℕ =>
      amFwdData M p.1 (p.2 / 4 / M.ex.length) (p.2 / 4 % M.ex.length) := by
    have htex := Primrec.list_getI.comp (Primrec.const M.ex) hiex
    have h2 := Primrec.snd.comp htex
    have hbitB := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hguardL := Primrec.fst.comp h3
    have h4 := Primrec.snd.comp h3
    have hwr := Primrec.fst.comp h4
    have hidx := Primrec.fst.comp hwr
    have hwr2 := Primrec.snd.comp hwr
    have hold := Primrec.fst.comp hwr2
    have hnew := Primrec.snd.comp hwr2
    have hbit := primrec_posFactPair.comp (Primrec.pair hkex hbitB)
    have hrailold := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hold))
    have hrailnew := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hnew))
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair (Primrec.list_cons.comp hbit (Primrec.list_cons.comp hrailold hguard))
      (Primrec.pair (Primrec.list_cons.comp hrailnew (Primrec.const []))
        (Primrec.list_cons.comp hrailold (Primrec.const [])))
  have hundo : Primrec fun p : ℕ × ℕ => amUndoData M p.1 (p.2 / 4) := by
    have htex := Primrec.list_getI.comp (Primrec.const M.ex) hd4
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
  have hgrd : Primrec fun p : ℕ × ℕ =>
      amGrdData M p.1 (p.2 / 4 / M.un.length) (p.2 / 4 % M.un.length) := by
    have htun := Primrec.list_getI.comp (Primrec.const M.un) hiun
    have h2 := Primrec.snd.comp htun
    have hbitB := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hguardL := Primrec.fst.comp h3
    have hbit := primrec_posFactPair.comp (Primrec.pair hkun hbitB)
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair (Primrec.list_cons.comp hbit hguard)
      (Primrec.pair (Primrec.const []) (Primrec.const []))
  have hacc : Primrec fun p : ℕ × ℕ => amAccData M p.1 (p.2 / 4) := by
    have htacc := Primrec.list_getI.comp (Primrec.const M.acc) hd4
    have hguardL := Primrec.snd.comp htacc
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair hguard (Primrec.pair (Primrec.const []) (Primrec.const []))
  have hinit : Primrec fun p : ℕ × ℕ => amInitData M p.1 := by
    have hmapinit : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) => amRail p.1 i false :=
      primrec_amRailTriple.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.const false)))
    have hmap := Primrec.list_map (Primrec.const (List.range M.mem)) hmapinit
    exact Primrec.pair (Primrec.const []) (Primrec.pair hmap (Primrec.const []))
  refine (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 0)
    (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 0)) hfwd
    (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 1)
      (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 1)) hundo
      (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 2)
        (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 2)) hgrd
        (Primrec.ite (c := fun p : ℕ × ℕ => p.2 / 4 < M.acc.length)
          (PrimrecRel.comp Primrec.nat_lt hd4 (Primrec.const M.acc.length))
          hacc hinit)))).of_eq fun p => rfl

theorem primrec_amActions : Primrec (amActions M) := by
  refine Primrec.list_map (Primrec.list_range.comp ?_) ?_
  · have h : Primrec fun n : ℕ =>
        4 * (n * M.ex.length + n * M.un.length + M.ex.length + M.acc.length + 1) :=
      Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp Primrec.id (Primrec.const M.ex.length))
                (Primrec.nat_mul.comp Primrec.id (Primrec.const M.un.length)))
              (Primrec.const M.ex.length))
            (Primrec.const M.acc.length))
          (Primrec.const 1))
    exact h.of_eq fun n => rfl
  · exact Primrec.pair Primrec.snd primrec_amActData

/-- The root method, with the two-task body written out. -/
theorem amRootMethods_raw (n : ℕ) :
    amRootMethods M n = [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
      ([(0, false, 4 * M.acc.length + 3), (1, true, 4 * Nat.pair n M.start + 1)] :
        List (ℕ × Bool × ℕ))))] := rfl

theorem primrec_amRootMethods : Primrec (amRootMethods M) := by
  have key : Primrec fun n : ℕ =>
      [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * M.acc.length + 3), (1, true, 4 * Nat.pair n M.start + 1)] :
          List (ℕ × Bool × ℕ))))] := by
    have hname : Primrec fun n : ℕ => 4 * Nat.pair n M.start + 1 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp Primrec.id (Primrec.const M.start)))
        (Primrec.const 1)
    refine Primrec.list_cons.comp ?_ (Primrec.const [])
    refine Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const [0, 1]) (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp (Primrec.const (0, false, 4 * M.acc.length + 3))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hname))
        (Primrec.const []))
  exact key.of_eq fun n => (amRootMethods_raw n).symm

/-- The existential methods, with the two-task bodies written out. -/
theorem amExMethods_raw (n : ℕ) :
    amExMethods M n = List.flatMap (fun k => (List.range M.ex.length).map fun i =>
      ((4 * Nat.pair (k + 1) (M.ex.getI i).src + 1 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 4 * (i + M.ex.length * k)), (1, true, 4 * Nat.pair k i + 3)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := rfl

theorem primrec_amExMethods : Primrec (amExMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => (List.range M.ex.length).map fun i =>
      ((4 * Nat.pair (k + 1) (M.ex.getI i).src + 1 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 4 * (i + M.ex.length * k)), (1, true, 4 * Nat.pair k i + 3)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const (List.range M.ex.length)) ?_
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have ii : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (Primrec.const M.ex) ii
    have hsrc := Primrec.fst.comp hget
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) hsrc))
      (Primrec.const 1)
    have hfwd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * (w.2 + M.ex.length * w.1.2) :=
      Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.nat_add.comp ii (Primrec.nat_mul.comp (Primrec.const M.ex.length) kk))
    have hd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * Nat.pair w.1.2 w.2 + 3 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ii))
        (Primrec.const 3)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hfwd))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hd))
        (Primrec.const []))
  exact key.of_eq fun n => (amExMethods_raw n).symm

/-- The undoing methods, with the two-task bodies written out. -/
theorem amDMethods_raw (n : ℕ) :
    amDMethods M n = List.flatMap (fun k => (List.range M.ex.length).map fun i =>
      ((4 * Nat.pair k i + 3 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, 4 * Nat.pair k (M.ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := rfl

theorem primrec_amDMethods : Primrec (amDMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => (List.range M.ex.length).map fun i =>
      ((4 * Nat.pair k i + 3 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, 4 * Nat.pair k (M.ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const (List.range M.ex.length)) ?_
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have ii : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (Primrec.const M.ex) ii
    have htgt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget)))
    have hname : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * Nat.pair w.1.2 w.2 + 3 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ii))
        (Primrec.const 3)
    have hc := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk htgt))
      (Primrec.const 1)
    have hu : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * w.2 + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ii) (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const false) hu))
        (Primrec.const []))
  exact key.of_eq fun n => (amDMethods_raw n).symm

/-- The universal methods, with the two-task bodies written out. -/
theorem amUnMethods_raw (n : ℕ) :
    amUnMethods M n = List.flatMap (fun k => (List.range M.un.length).map fun j =>
      ((4 * Nat.pair (k + 1) (M.un.getI j).src + 1 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 4 * (j + M.un.length * k) + 2),
            (1, true, 4 * Nat.pair k (Nat.pair (M.un.getI j).tgt₁ (M.un.getI j).tgt₂) + 2)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := rfl

theorem primrec_amUnMethods : Primrec (amUnMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => (List.range M.un.length).map fun j =>
      ((4 * Nat.pair (k + 1) (M.un.getI j).src + 1 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 4 * (j + M.un.length * k) + 2),
            (1, true, 4 * Nat.pair k (Nat.pair (M.un.getI j).tgt₁ (M.un.getI j).tgt₂) + 2)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const (List.range M.un.length)) ?_
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have jj : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (Primrec.const M.un) jj
    have hsrc := Primrec.fst.comp hget
    have hrest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    have ht1 := Primrec.fst.comp hrest
    have ht2 := Primrec.snd.comp hrest
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) hsrc))
      (Primrec.const 1)
    have hgrd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * (w.2 + M.un.length * w.1.2) + 2 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec.nat_add.comp jj (Primrec.nat_mul.comp (Primrec.const M.un.length) kk)))
        (Primrec.const 2)
    have hbr := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp ht1 ht2)))
      (Primrec.const 2)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hgrd))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hbr))
        (Primrec.const []))
  exact key.of_eq fun n => (amUnMethods_raw n).symm

/-- The branching methods, with the two-task bodies written out. -/
theorem amBrMethods_raw (n : ℕ) :
    amBrMethods M n = List.flatMap (fun k => (List.range M.un.length).map fun j =>
      ((4 * Nat.pair k (Nat.pair (M.un.getI j).tgt₁ (M.un.getI j).tgt₂) + 2 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, 4 * Nat.pair k (M.un.getI j).tgt₁ + 1),
            (1, true, 4 * Nat.pair k (M.un.getI j).tgt₂ + 1)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := rfl

theorem primrec_amBrMethods : Primrec (amBrMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => (List.range M.un.length).map fun j =>
      ((4 * Nat.pair k (Nat.pair (M.un.getI j).tgt₁ (M.un.getI j).tgt₂) + 2 : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, 4 * Nat.pair k (M.un.getI j).tgt₁ + 1),
            (1, true, 4 * Nat.pair k (M.un.getI j).tgt₂ + 1)] :
            List (ℕ × Bool × ℕ))))) (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const (List.range M.un.length)) ?_
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have jj : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hget := Primrec.list_getI.comp (Primrec.const M.un) jj
    have hrest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    have ht1 := Primrec.fst.comp hrest
    have ht2 := Primrec.snd.comp hrest
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp ht1 ht2)))
      (Primrec.const 2)
    have hc1 := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ht1))
      (Primrec.const 1)
    have hc2 := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ht2))
      (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc1))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hc2))
        (Primrec.const []))
  exact key.of_eq fun n => (amBrMethods_raw n).symm

theorem computable_amDom : Computable (amDom M) :=
  (Primrec.pair primrec_amActions
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp primrec_amRootMethods primrec_amExMethods)
            primrec_amDMethods)
          primrec_amUnMethods)
        primrec_amBrMethods)
      (Primrec.const (amAccMethods M)))).to_comp


/-! ### An example that really uses both alternation and the memory

The machine `HTN.Syn.twoCheck` has one memory bit.  Reading a `true` it branches universally into
two copies of the state `1`, and each branch then reads a `true` and **writes** the memory bit,
which it may only do while that bit is still `false`.  The second branch can therefore only
succeed because the write of the first one has been undone — which is exactly what the encoding
guarantees (`HTN.Syn.accFrom_of_yieldSeq_amDom`: a refinement of a configuration task restores
the state it started in). -/

/-- One memory bit, one universal transition, one writing existential transition. -/
def twoCheck : BitAltMem where
  mem := 1
  start := 0
  acc := [(2, [(0, true)])]
  ex := [(1, true, [], (0, false, true), 2)]
  un := [(0, true, [], 1, 1)]

theorem twoCheck_accFrom_one : twoCheck.AccFrom 1 [true] (fun _ => false) := by
  refine BitAltMem.AccFrom.ex (t := (1, true, [], (0, false, true), 2)) (by simp [twoCheck])
    rfl rfl (by intro p hp; simp [AmExTr.guard] at hp)
    (by simp [twoCheck, AmExTr.wr, MemWrite.idx]) rfl ?_
  refine BitAltMem.AccFrom.nil (c := (2, [(0, true)])) (by simp [twoCheck]) rfl ?_
  intro p hp
  simp only [AmAcc.guard, List.mem_singleton] at hp
  subst hp
  exact ⟨by simp [twoCheck], by simp [memUpd, AmExTr.wr, MemWrite.idx, MemWrite.new]⟩

theorem twoCheck_accepts : twoCheck.Accepts [true, true] :=
  BitAltMem.AccFrom.un (t := (0, true, [], 1, 1)) (by simp [twoCheck]) rfl rfl
    (by intro p hp; simp [AmUnTr.guard] at hp) twoCheck_accFrom_one twoCheck_accFrom_one

theorem twoCheck_not_accepts : ¬ twoCheck.Accepts [true, false] := by
  intro h
  cases h with
  | ex ht hq hb hg hw hu h' =>
    rename_i t
    simp only [twoCheck, List.mem_singleton] at ht
    subst ht
    exact absurd hq (by simp [AmExTr.src, twoCheck])
  | un ht hq hb hg h₁ h₂ =>
    rename_i t
    simp only [twoCheck, List.mem_singleton] at ht
    subst ht
    cases h₁ with
    | ex ht' hq' hb' =>
      rename_i t'
      simp only [twoCheck, List.mem_singleton] at ht'
      subst ht'
      exact absurd hb' (by simp [AmExTr.bit])
    | un ht' hq' =>
      rename_i t'
      simp only [twoCheck, List.mem_singleton] at ht'
      subst ht'
      exact absurd hq' (by simp [AmUnTr.src, AmUnTr.tgt₁])

/-- The encoded problem of the example is solvable … -/
theorem solvable_twoCheck :
    Solvable (amDom twoCheck [true, true].length) (posEnc [true, true]) :=
  (solvable_amDom_iff [true, true]).2 twoCheck_accepts

/-- … and the one for a word the machine rejects is not. -/
theorem not_solvable_twoCheck :
    ¬ Solvable (amDom twoCheck [true, false].length) (posEnc [true, false]) := fun h =>
  twoCheck_not_accepts ((solvable_amDom_iff [true, false]).1 h)

/-! ### The family -/

variable (M)

/-- **A polynomial-time hardness family whose fixed part is an alternating machine with a
memory**, reading its input from the initial state, in `TO-HTN-AC` with a rooted instance. -/
noncomputable def amFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root M.Accepts where
  dom := amDom M
  inst := posEnc
  bound := Polynomial.C (amCoef M + 1) * Polynomial.X + Polynomial.C (amConst M + 2)
  dom_size := fun n => by
    have h := size_amDom_le (M := M) n
    have h2 : amCoef M * n ≤ (amCoef M + 1) * n := Nat.mul_le_mul_right _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  inst_size := fun w => by
    have h := size_posEnc w
    have h2 : w.length ≤ (amCoef M + 1) * w.length := Nat.le_mul_of_pos_left _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  dom_ok := fun _ => amDom_domOk _
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_amDom_iff
  dom_computable := computable_amDom
  inst_polyTime := polyTimeCode_posEnc

/-- **The alternating-with-memory family, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_altMem_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root M.Accepts) :=
  ⟨(amFamily M).mono ⟨fun _ h => h.1, fun _ h => h⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_altMem_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root M.Accepts) :=
  ⟨(amFamily M).mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h.2, fun _ h => h⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_altMem_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root M.Accepts) :=
  ⟨(amFamily M).mono ⟨fun _ h => h.2, fun _ h => h⟩⟩

end Syn

end HTN
