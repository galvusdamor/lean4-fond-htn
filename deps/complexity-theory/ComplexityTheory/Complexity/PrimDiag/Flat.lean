import ComplexityTheory.Complexity.CobhamTM.ProgTM
/-!
# A flat machine for compiled stack programs

`ComplexityTheory/Complexity/CobhamTM/ProgTM.lean` compiles a structured stack program to a flat
list of instructions (`Prog.compile`).  Here the flat list is run directly, by a step function on
pairs "program counter, list of stacks" (`Prog.fstep`).  The step function is primitive recursive
*jointly in the instruction list* (`ComplexityTheory/Complexity/PrimDiag/Universal.lean`), which is
what makes a universal evaluator for the functions of Cobham's class primitive recursive.

* `Prog.fstep` — one instruction; a program counter outside the list leaves the configuration
  unchanged (the machine has halted);
* `Prog.flat_compile` — a run of a program in `t` steps is a run of the flat machine in at most
  `2 * t` steps, from the start of its code to the address just after it.
-/

namespace HTN.PTime.CobhamTM

namespace Prog

/-! ### Stores as lists -/

/-- Stack `k` of a list of stacks (empty beyond the list). -/
def getS (T : List (List Bool)) (k : ℕ) : List Bool := T.getD k []

/-- Replace stack `k` (no effect beyond the list). -/
def setS (T : List (List Bool)) (k : ℕ) (v : List Bool) : List (List Bool) :=
  (List.range T.length).map fun i => if i = k then v else T.getD i []

/-- The first `M` stacks of a store, as a list. -/
def toL (M : ℕ) (S : Store) : List (List Bool) := (List.range M).map S

theorem getS_toL {M k : ℕ} (hk : k < M) (S : Store) : getS (toL M S) k = S k := by
  simp [getS, toL, List.getD_eq_getElem?_getD, hk]

theorem setS_toL {M k : ℕ} (hk : k < M) (S : Store) (v : List Bool) :
    setS (toL M S) k v = toL M (Function.update S k v) := by
  simp only [setS, toL, List.length_map, List.length_range]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  by_cases h : i = k
  · subst h; simp
  · simp [h, List.getD_eq_getElem?_getD, hi]

/-! ### The step function -/

/-- The branch target of `br k a₀ aF aT` on a stack. -/
def brTarget (l : List Bool) (a₀ aF aT : ℕ) : ℕ :=
  match l with
  | [] => a₀
  | false :: _ => aF
  | true :: _ => aT

/-- One instruction of the flat machine. -/
def execI (pc : ℕ) (T : List (List Bool)) : Instr → ℕ × List (List Bool)
  | .push k b => (pc + 1, setS T k (b :: getS T k))
  | .pop k => (pc + 1, setS T k (getS T k).tail)
  | .br k a₀ aF aT => (brTarget (getS T k) a₀ aF aT, T)
  | .jmp a => (a, T)

/-- One step of the flat machine: execute the instruction at the program counter, or stay
(halted) if there is none. -/
def fstep (C : List Instr) (c : ℕ × List (List Bool)) : ℕ × List (List Bool) :=
  match C[c.1]? with
  | none => c
  | some i => execI c.1 c.2 i

theorem fstep_of_le {C : List Instr} {c : ℕ × List (List Bool)} (h : C.length ≤ c.1) :
    fstep C c = c := by
  simp [fstep, List.getElem?_eq_none h]

theorem iterate_fstep_of_le {C : List Instr} {c : ℕ × List (List Bool)} (h : C.length ≤ c.1)
    (k : ℕ) : (fstep C)^[k] c = c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, fstep_of_le h, ih]

/-! ### Correctness of the flat machine on compiled programs -/

/-- Reachability of the flat machine in at most `k` steps. -/
def FReach (C : List Instr) (a b : ℕ × List (List Bool)) (k : ℕ) : Prop :=
  ∃ k' ≤ k, (fstep C)^[k'] a = b

theorem FReach.refl (C : List Instr) (a : ℕ × List (List Bool)) : FReach C a a 0 :=
  ⟨0, le_rfl, rfl⟩

theorem FReach.trans {C : List Instr} {a b c : ℕ × List (List Bool)} {k₁ k₂ : ℕ}
    (h₁ : FReach C a b k₁) (h₂ : FReach C b c k₂) : FReach C a c (k₁ + k₂) := by
  obtain ⟨k₁', hk₁, e₁⟩ := h₁
  obtain ⟨k₂', hk₂, e₂⟩ := h₂
  exact ⟨k₂' + k₁', by omega, by rw [Function.iterate_add_apply, e₁, e₂]⟩

theorem FReach.mono {C : List Instr} {a b : ℕ × List (List Bool)} {k k' : ℕ}
    (h : FReach C a b k) (hk : k ≤ k') : FReach C a b k' :=
  let ⟨j, hj, e⟩ := h; ⟨j, le_trans hj hk, e⟩

theorem FReach.single {C : List Instr} {a b : ℕ × List (List Bool)} (h : fstep C a = b) :
    FReach C a b 1 := ⟨1, le_rfl, by simpa using h⟩

theorem fstep_at {C : List Instr} {o : ℕ} {ins : Instr} {c : List Instr}
    (h : At C o (ins :: c)) (T : List (List Bool)) : fstep C (o, T) = execI o T ins := by
  obtain ⟨ho, hC⟩ := At.get h
  simp [fstep, List.getElem?_eq_getElem ho, hC]

/-- **The flat machine runs compiled programs**: a run of `p` in `t` steps is a run of the flat
machine in at most `2 * t` steps, the stores being represented by their first `M` stacks. -/
theorem flat_compile {C : List Instr} {M : ℕ} :
    ∀ {p : Prog} {S S' : Store} {t : ℕ}, Eval p S S' t → ∀ {o : ℕ}, maxStack p < M →
      At C o (compile p o) →
        FReach C (o, toL M S) (o + size p, toL M S') (2 * t) := by
  intro p S S' t e
  induction e with
  | skip S => intro o _ _; simpa [size] using FReach.refl C _
  | push k b S =>
    intro o hN hat
    refine (FReach.single ?_).mono (by omega)
    rw [fstep_at (c := []) hat]
    simp only [execI, size]
    rw [getS_toL (by simpa [maxStack] using hN), setS_toL (by simpa [maxStack] using hN)]
  | pop k S =>
    intro o hN hat
    refine (FReach.single ?_).mono (by omega)
    rw [fstep_at (c := []) hat]
    simp only [execI, size]
    rw [getS_toL (by simpa [maxStack] using hN), setS_toL (by simpa [maxStack] using hN)]
  | @seq p q S S₁ S₂ t₁ t₂ _ _ ih₁ ih₂ =>
    intro o hN hat
    simp only [maxStack, max_lt_iff] at hN
    simp only [compile] at hat
    have hat₁ := hat.append_left
    have hat₂ := hat.append_right
    rw [length_compile] at hat₂
    have r₁ := ih₁ hN.1 hat₁
    have r₂ := ih₂ hN.2 hat₂
    rw [show o + size (Prog.seq p q) = o + size p + size q by simp only [size]; omega]
    exact (r₁.trans r₂).mono (by omega)
  | @ifNil k p₀ pF pT S S' t hk _ ih =>
    intro o hN hat
    simp only [maxStack, max_lt_iff] at hN
    simp only [compile] at hat
    have hat0 := hat.append_left.append_left.append_left.append_left.append_left
    have hat₀ : At C (o + 1) (compile p₀ (o + 1)) :=
      hat.append_left.append_left.append_left.append_left.append_right.congr (by simp)
    have hjmp : At C (o + 1 + size p₀) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have r₀ : FReach C (o, toL M S) (o + 1, toL M S) 1 := by
      refine FReach.single ?_
      rw [fstep_at hat0]
      simp [execI, getS_toL hN.1, hk, brTarget]
    have r₁ := ih hN.2.1 hat₀
    have r₂ : FReach C (o + 1 + size p₀, toL M S')
        (o + size (ifTop k p₀ pF pT), toL M S') 1 := by
      refine FReach.single ?_
      rw [fstep_at (c := []) hjmp]
      simp only [execI, size]
      congr 1; omega
    exact ((r₀.trans r₁).trans r₂).mono (by omega)
  | @ifF k p₀ pF pT S S' t r hk _ ih =>
    intro o hN hat
    simp only [maxStack, max_lt_iff] at hN
    simp only [compile] at hat
    have hat0 := hat.append_left.append_left.append_left.append_left.append_left
    have hatF : At C (o + size p₀ + 2) (compile pF (o + size p₀ + 2)) :=
      hat.append_left.append_left.append_right.congr (by simp [length_compile]; omega)
    have hjmp : At C (o + size p₀ + 2 + size pF) [.jmp (o + size p₀ + size pF + size pT + 3)] :=
      hat.append_left.append_right.congr (by simp [length_compile]; omega)
    have r₀ : FReach C (o, toL M S) (o + size p₀ + 2, toL M S) 1 := by
      refine FReach.single ?_
      rw [fstep_at hat0]
      simp [execI, getS_toL hN.1, hk, brTarget]
    have r₁ := ih hN.2.2.1 hatF
    have r₂ : FReach C (o + size p₀ + 2 + size pF, toL M S')
        (o + size (ifTop k p₀ pF pT), toL M S') 1 := by
      refine FReach.single ?_
      rw [fstep_at (c := []) hjmp]
      simp only [execI, size]
      congr 1; omega
    exact ((r₀.trans r₁).trans r₂).mono (by omega)
  | @ifT k p₀ pF pT S S' t r hk _ ih =>
    intro o hN hat
    simp only [maxStack, max_lt_iff] at hN
    simp only [compile] at hat
    have hat0 := hat.append_left.append_left.append_left.append_left.append_left
    have hatT : At C (o + size p₀ + size pF + 3) (compile pT (o + size p₀ + size pF + 3)) :=
      hat.append_right.congr (by simp [length_compile]; omega)
    have r₀ : FReach C (o, toL M S) (o + size p₀ + size pF + 3, toL M S) 1 := by
      refine FReach.single ?_
      rw [fstep_at hat0]
      simp [execI, getS_toL hN.1, hk, brTarget]
    have r₁ := ih hN.2.2.2 hatT
    have e : o + size p₀ + size pF + 3 + size pT = o + size (ifTop k p₀ pF pT) := by
      simp only [size]; omega
    rw [e] at r₁
    exact (r₀.trans r₁).mono (by omega)
  | @loopNil k p S hk =>
    intro o hN hat
    simp only [maxStack, max_lt_iff] at hN
    simp only [compile] at hat
    have hat0 := hat.append_left.append_left
    refine (FReach.single ?_).mono (by omega)
    rw [fstep_at hat0]
    simp only [execI, getS_toL hN.1, hk, brTarget, size]
    rw [Nat.add_assoc]
  | @loopCons k p S S₁ S₂ t₁ t₂ hk _ _ ih₁ ih₂ =>
    intro o hN hat
    have hN' := hN
    simp only [maxStack, max_lt_iff] at hN
    have hat' := hat
    simp only [compile] at hat
    have hat0 := hat.append_left.append_left
    have hatb : At C (o + 1) (compile p (o + 1)) :=
      hat.append_left.append_right.congr (by simp)
    have hjmp : At C (o + 1 + size p) [.jmp o] :=
      hat.append_right.congr (by simp [length_compile]; omega)
    obtain ⟨b, r, hkr⟩ := List.exists_cons_of_ne_nil hk
    have r₀ : FReach C (o, toL M S) (o + 1, toL M S) 1 := by
      refine FReach.single ?_
      rw [fstep_at hat0]
      cases b <;> simp [execI, getS_toL hN.1, hkr, brTarget]
    have r₁ := ih₁ hN.2 hatb
    have r₂ : FReach C (o + 1 + size p, toL M S₁) (o, toL M S₁) 1 := by
      refine FReach.single ?_
      rw [fstep_at (c := []) hjmp]
      simp [execI]
    have r₃ := ih₂ hN' hat'
    exact (((r₀.trans r₁).trans r₂).trans r₃).mono (by omega)

end Prog

end HTN.PTime.CobhamTM
