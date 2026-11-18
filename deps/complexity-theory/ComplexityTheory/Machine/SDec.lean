import ComplexityTheory.Machine.SRealize
import ComplexityTheory.Collapse.Fun
/-!
# Decrementing a binary counter on a stack

The counter is a bit string on stack `C`, least significant bit on top (`HTN.PSpace.val`).
`HTN.Mach.decP C D G FL` decrements it, using a guard stack `G` and a stack `D` that collects the
bits the borrow runs through:

* if the counter is `0` (all bits `false`, `k` of them), the program pops them all and leaves `k`
  copies of `true` on `D` (`HTN.Mach.dec_zero`);
* otherwise (`k` bits `false`, then `true`, then `rest`) it leaves `false :: rest` on `C`, `k`
  copies of `true` on `D` and pushes `true` on the flag stack `FL` (`HTN.Mach.dec_pos`); moving
  `D` back onto `C` (`HTN.Mach.restore`) gives the counter decremented by one
  (`HTN.Mach.val_dec`).
-/

namespace HTN

namespace Mach

open TM PTime CobhamTM Prog PSpace

theorem _root_.HTN.PTime.CobhamTM.Prog.Eval.of_eq {p : Prog} {S S' S'' : Store} {t : ℕ} (e : Eval p S S' t) (h : S' = S'') :
    Eval p S S'' t := h ▸ e

variable (C D G FL : ℕ)

/-- One round of the borrow. -/
def decBody : Prog :=
  ifTop C (pop G) (seq (pop C) (push D true))
    (seq (pop C) (seq (push C false) (seq (pop G) (push FL true))))

/-- The decrement. -/
def decP : Prog := seq (push G true) (loop G (decBody C D G FL))

/-- Moving the borrowed bits back. -/
def restoreP : Prog := loop D (seq (pop D) (push C true))

variable {C D G FL}

theorem val_dec (k : ℕ) (rest : List Bool) :
    val (List.replicate k true ++ false :: rest) + 1 = val (List.replicate k false ++ true :: rest) := by
  induction k with
  | zero => simp; omega
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, val_cons_true, val_cons_false]
    omega

theorem val_replicate_false (k : ℕ) : val (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-- A bit string is all `false`, or has a first `true`. -/
theorem falses_or_true (c : List Bool) :
    (∃ k, c = List.replicate k false) ∨ ∃ k rest, c = List.replicate k false ++ true :: rest := by
  induction c with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b c ih =>
    cases b
    · rcases ih with ⟨k, rfl⟩ | ⟨k, rest, rfl⟩
      · exact Or.inl ⟨k + 1, rfl⟩
      · exact Or.inr ⟨k + 1, rest, rfl⟩
    · exact Or.inr ⟨0, c, rfl⟩

section

variable (hCD : C ≠ D) (hCG : C ≠ G) (hCF : C ≠ FL) (hDG : D ≠ G) (hDF : D ≠ FL) (hGF : G ≠ FL)
include hCD hCG hCF hDG hDF hGF

theorem dec_zero_loop : ∀ (k : ℕ) (S : Store), S C = List.replicate k false → S G = [true] →
    ∃ t ≤ 4 * k + 4, Eval (loop G (decBody C D G FL)) S
      (Function.update (Function.update (Function.update S C []) D
        (List.replicate k true ++ S D)) G []) t := by
  intro k
  induction k with
  | zero =>
    intro S hC hG
    have e : Eval (loop G (decBody C D G FL)) S (Function.update S G (S G).tail) _ :=
      .loopCons (by simp [hG]) (.ifNil (by simpa using hC) (.pop G S))
        (.loopNil (by simp [hG]))
    refine ⟨_, by norm_num, e.of_eq ?_⟩
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | succ k ih =>
    intro S hC hG
    set S₁ := Function.update (Function.update S C (S C).tail) D
      (true :: Function.update S C (S C).tail D) with hS₁
    have hC₁ : S₁ C = List.replicate k false := by
      simp [hS₁, Function.update_of_ne hCD, hC, List.replicate_succ]
    have hG₁ : S₁ G = [true] := by
      simp [hS₁, Function.update_of_ne hDG.symm, Function.update_of_ne hCG.symm, hG]
    obtain ⟨t, ht, e⟩ := ih S₁ hC₁ hG₁
    have eb : Eval (decBody C D G FL) S S₁ (1 + 1 + 1) :=
      .ifF (r := List.replicate k false) (by simpa [List.replicate_succ] using hC)
        (.seq (.pop C S) (.push D true _))
    have e' := Eval.loopCons (by simp [hG]) eb e
    refine ⟨_, by omega, e'.of_eq ?_⟩
    funext j
    simp only [hS₁, Function.update_apply]
    split_ifs <;> simp_all [List.replicate_succ']

theorem dec_pos_loop : ∀ (k : ℕ) (rest : List Bool) (S : Store),
    S C = List.replicate k false ++ true :: rest → S G = [true] →
    ∃ t ≤ 4 * k + 7, Eval (loop G (decBody C D G FL)) S
      (Function.update (Function.update (Function.update (Function.update S C (false :: rest)) D
        (List.replicate k true ++ S D)) G []) FL (true :: S FL)) t := by
  intro k
  induction k with
  | zero =>
    intro rest S hC hG
    simp only [List.replicate_zero, List.nil_append] at hC
    have eb : Eval (decBody C D G FL) S _ _ :=
      .ifT (r := rest) hC (.seq (.pop C S) (.seq (.push C false _) (.seq (.pop G _) (.push FL true _))))
    have e := Eval.loopCons (by simp [hG]) eb (.loopNil (k := G) (p := decBody C D G FL) (by
      rw [Function.update_of_ne hGF, Function.update_self, Function.update_of_ne hCG.symm,
        Function.update_of_ne hCG.symm, hG]; rfl))
    refine ⟨_, by norm_num, e.of_eq ?_⟩
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | succ k ih =>
    intro rest S hC hG
    set S₁ := Function.update (Function.update S C (S C).tail) D
      (true :: Function.update S C (S C).tail D) with hS₁
    have hC₁ : S₁ C = List.replicate k false ++ true :: rest := by
      simp [hS₁, Function.update_of_ne hCD, hC, List.replicate_succ]
    have hG₁ : S₁ G = [true] := by
      simp [hS₁, Function.update_of_ne hDG.symm, Function.update_of_ne hCG.symm, hG]
    obtain ⟨t, ht, e⟩ := ih rest S₁ hC₁ hG₁
    have eb : Eval (decBody C D G FL) S S₁ (1 + 1 + 1) :=
      .ifF (r := List.replicate k false ++ true :: rest) (by simpa [List.replicate_succ] using hC)
        (.seq (.pop C S) (.push D true _))
    have e' := Eval.loopCons (by simp [hG]) eb e
    refine ⟨_, by omega, e'.of_eq ?_⟩
    funext j
    simp only [hS₁, Function.update_apply]
    split_ifs <;> simp_all [List.replicate_succ']

/-- **Decrementing zero.** -/
theorem dec_zero {k : ℕ} {S : Store} (hC : S C = List.replicate k false) (hG : S G = []) :
    ∃ t ≤ 4 * k + 5, Eval (decP C D G FL) S
      (Function.update (Function.update S C []) D (List.replicate k true ++ S D)) t := by
  obtain ⟨t, ht, e⟩ := dec_zero_loop hCD hCG hCF hDG hDF hGF k (Function.update S G (true :: S G))
    (by simp [Function.update_of_ne hCG, hC]) (by simp [hG])
  have e' := Eval.seq (.push G true S) e
  refine ⟨_, by omega, e'.of_eq ?_⟩
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **Decrementing a positive counter.** -/
theorem dec_pos {k : ℕ} {rest : List Bool} {S : Store}
    (hC : S C = List.replicate k false ++ true :: rest) (hG : S G = []) :
    ∃ t ≤ 4 * k + 8, Eval (decP C D G FL) S
      (Function.update (Function.update (Function.update S C (false :: rest)) D
        (List.replicate k true ++ S D)) FL (true :: S FL)) t := by
  obtain ⟨t, ht, e⟩ := dec_pos_loop hCD hCG hCF hDG hDF hGF k rest
    (Function.update S G (true :: S G)) (by simp [Function.update_of_ne hCG, hC]) (by simp [hG])
  have e' := Eval.seq (.push G true S) e
  refine ⟨_, by omega, e'.of_eq ?_⟩
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end

theorem restore_loop {C D : ℕ} (hCD : C ≠ D) : ∀ (k : ℕ) (S : Store), S D = List.replicate k true →
    ∃ t ≤ 4 * k + 1, Eval (restoreP C D) S
      (Function.update (Function.update S D []) C (List.replicate k true ++ S C)) t := by
  intro k
  induction k with
  | zero =>
    intro S hD
    have e := Eval.loopNil (k := D) (p := seq (pop D) (push C true)) (S := S) (by simpa using hD)
    refine ⟨_, by norm_num, e.of_eq ?_⟩
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | succ k ih =>
    intro S hD
    set S₁ := Function.update (Function.update S D (S D).tail) C
      (true :: Function.update S D (S D).tail C) with hS₁
    have hD₁ : S₁ D = List.replicate k true := by
      simp [hS₁, Function.update_of_ne hCD.symm, hD, List.replicate_succ]
    obtain ⟨t, ht, e⟩ := ih S₁ hD₁
    have e' := Eval.loopCons (k := D) (p := seq (pop D) (push C true)) (by simp [hD, List.replicate_succ])
      (.seq (.pop D S) (.push C true _)) e
    refine ⟨_, by omega, e'.of_eq ?_⟩
    funext j
    simp only [hS₁, Function.update_apply]
    split_ifs <;> simp_all [List.replicate_succ']

end Mach

end HTN
