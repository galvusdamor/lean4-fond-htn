import ComplexityTheory.Complexity.CobhamTM.Kit
/-!
# Structured stack programs

A small structured language over infinitely many stacks of bits (`Store := ℕ → List Bool`),
used as an intermediate language between Cobham's class and TM2 machines:

* `Prog` — `skip`, `push k b`, `pop k`, sequencing, a three-way branch on the top of a stack
  (`ifTop`), and a loop that runs while a stack is nonempty (`loop`);
* `Eval p S S' t` — big-step semantics with a step count `t`;
* `Runs p S S' T` — `p` takes `S` to `S'` in at most `T` steps.

The basic programs `clear`, `moveRev` and `copy` (copying a stack through a temporary stack)
come with their exact effect and a linear time bound.
-/

namespace HTN.PTime.CobhamTM

/-- The memory of a stack program: infinitely many stacks of bits. -/
abbrev Store : Type := ℕ → List Bool

/-- Structured stack programs. -/
inductive Prog where
  | skip
  | push (k : ℕ) (b : Bool)
  | pop (k : ℕ)
  | seq (p q : Prog)
  | ifTop (k : ℕ) (pNil pF pT : Prog)
  | loop (k : ℕ) (body : Prog)

namespace Prog

/-- Big-step semantics with a step count. -/
inductive Eval : Prog → Store → Store → ℕ → Prop
  | skip (S : Store) : Eval skip S S 0
  | push (k : ℕ) (b : Bool) (S : Store) : Eval (push k b) S (Function.update S k (b :: S k)) 1
  | pop (k : ℕ) (S : Store) : Eval (pop k) S (Function.update S k (S k).tail) 1
  | seq {p q : Prog} {S S₁ S₂ : Store} {t₁ t₂ : ℕ} :
      Eval p S S₁ t₁ → Eval q S₁ S₂ t₂ → Eval (seq p q) S S₂ (t₁ + t₂)
  | ifNil {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} {t : ℕ} :
      S k = [] → Eval p₀ S S' t → Eval (ifTop k p₀ pF pT) S S' (t + 1)
  | ifF {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} {t : ℕ} {r : List Bool} :
      S k = false :: r → Eval pF S S' t → Eval (ifTop k p₀ pF pT) S S' (t + 1)
  | ifT {k : ℕ} {p₀ pF pT : Prog} {S S' : Store} {t : ℕ} {r : List Bool} :
      S k = true :: r → Eval pT S S' t → Eval (ifTop k p₀ pF pT) S S' (t + 1)
  | loopNil {k : ℕ} {p : Prog} {S : Store} : S k = [] → Eval (loop k p) S S 1
  | loopCons {k : ℕ} {p : Prog} {S S₁ S₂ : Store} {t₁ t₂ : ℕ} :
      S k ≠ [] → Eval p S S₁ t₁ → Eval (loop k p) S₁ S₂ t₂ → Eval (loop k p) S S₂ (t₁ + t₂ + 1)

/-- `p` takes `S` to `S'` in at most `T` steps. -/
def Runs (p : Prog) (S S' : Store) (T : ℕ) : Prop := ∃ t ≤ T, Eval p S S' t

theorem Runs.mono {p : Prog} {S S' : Store} {T T' : ℕ} (h : Runs p S S' T) (hT : T ≤ T') :
    Runs p S S' T' := let ⟨t, ht, e⟩ := h; ⟨t, le_trans ht hT, e⟩

theorem Runs.of_eq {p : Prog} {S S' S'' : Store} {T : ℕ} (h : Runs p S S' T) (e : S' = S'') :
    Runs p S S'' T := e ▸ h

theorem Runs.seq {p q : Prog} {S S₁ S₂ : Store} {T₁ T₂ : ℕ} (h₁ : Runs p S S₁ T₁)
    (h₂ : Runs q S₁ S₂ T₂) : Runs (Prog.seq p q) S S₂ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, e₁⟩ := h₁
  obtain ⟨t₂, ht₂, e₂⟩ := h₂
  exact ⟨t₁ + t₂, by omega, Eval.seq e₁ e₂⟩

theorem Runs.skip (S : Store) : Runs Prog.skip S S 0 := ⟨0, le_rfl, Eval.skip S⟩

theorem Runs.push (k : ℕ) (b : Bool) (S : Store) :
    Runs (Prog.push k b) S (Function.update S k (b :: S k)) 1 := ⟨1, le_rfl, Eval.push k b S⟩

theorem Runs.pop (k : ℕ) (S : Store) :
    Runs (Prog.pop k) S (Function.update S k (S k).tail) 1 := ⟨1, le_rfl, Eval.pop k S⟩

/-- A sequence of programs. -/
def seqList : List Prog → Prog
  | [] => skip
  | p :: ps => seq p (seqList ps)

/-! ### Store algebra -/

@[simp] theorem update_same' (S : Store) (k : ℕ) (l : List Bool) :
    Function.update S k l k = l := Function.update_self k l S

theorem update_ne' (S : Store) {k j : ℕ} (h : j ≠ k) (l : List Bool) :
    Function.update S k l j = S j := Function.update_of_ne h l S

theorem update_eq_self' (S : Store) (k : ℕ) : Function.update S k (S k) = S :=
  Function.update_eq_self k S

/-! ### Clearing a stack -/

/-- Pop a stack until it is empty. -/
def clear (k : ℕ) : Prog := loop k (pop k)

theorem runs_clear (k : ℕ) (S : Store) :
    Runs (clear k) S (Function.update S k []) (2 * (S k).length + 1) := by
  generalize hl : S k = l
  induction l generalizing S with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    have : Function.update S k [] = S := by rw [← hl]; exact update_eq_self' S k
    rw [this]; exact Eval.loopNil hl
  | cons b l ih =>
    have h1 := ih (Function.update S k (S k).tail) (by simp [hl])
    obtain ⟨t, ht, e⟩ := h1
    refine ⟨1 + t + 1, by simp; omega, ?_⟩
    have := Eval.loopCons (p := pop k) (by rw [hl]; simp) (Eval.pop k S) e
    simpa [Function.update_idem] using this

/-! ### Moving a stack onto another one, reversing it -/

/-- Move the top bit of `src` to `dst`. -/
def move1 (src dst : ℕ) : Prog :=
  ifTop src skip (seq (pop src) (push dst false)) (seq (pop src) (push dst true))

/-- Move the whole of `src` onto `dst` (reversing it). -/
def moveRev (src dst : ℕ) : Prog := loop src (move1 src dst)

theorem runs_moveRev {src dst : ℕ} (hne : src ≠ dst) (S : Store) :
    Runs (moveRev src dst) S
      (Function.update (Function.update S src []) dst ((S src).reverse ++ S dst))
      (4 * (S src).length + 1) := by
  generalize hl : S src = l
  induction l generalizing S with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update S src []) dst ([].reverse ++ S dst) = S := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← hl, update_eq_self', update_eq_self']
    rw [this]; exact Eval.loopNil hl
  | cons b l ih =>
    set S₁ := Function.update (Function.update S src l) dst (b :: S dst) with hS₁
    have h1 := ih S₁ (by rw [hS₁, update_ne' _ hne, update_same'])
    obtain ⟨t, ht, e⟩ := h1
    have hstep : Eval (move1 src dst) S S₁ 3 := by
      cases b
      · refine Eval.ifF hl ?_
        have := Eval.seq (Eval.pop src S) (Eval.push dst false (Function.update S src (S src).tail))
        simpa [hl, hS₁, update_ne' _ (Ne.symm hne)] using this
      · refine Eval.ifT hl ?_
        have := Eval.seq (Eval.pop src S) (Eval.push dst true (Function.update S src (S src).tail))
        simpa [hl, hS₁, update_ne' _ (Ne.symm hne)] using this
    refine ⟨3 + t + 1, by simp; omega, ?_⟩
    have := Eval.loopCons (by rw [hl]; simp) hstep e
    convert this using 1
    rw [hS₁]
    funext j
    by_cases hj : j = dst
    · subst hj; simp
    · by_cases hj' : j = src
      · subst hj'; simp [update_ne' _ hne]
      · simp [update_ne' _ hj, update_ne' _ hj']

/-! ### Copying a stack -/

/-- Move the top bit of `src` to both `d₁` and `d₂`. -/
def move2 (src d₁ d₂ : ℕ) : Prog :=
  ifTop src skip (seq (pop src) (seq (push d₁ false) (push d₂ false)))
    (seq (pop src) (seq (push d₁ true) (push d₂ true)))

/-- Move the whole of `src` onto both `d₁` and `d₂` (reversing it). -/
def moveRev2 (src d₁ d₂ : ℕ) : Prog := loop src (move2 src d₁ d₂)

theorem runs_moveRev2 {src d₁ d₂ : ℕ} (h1 : src ≠ d₁) (h2 : src ≠ d₂) (h12 : d₁ ≠ d₂)
    (S : Store) :
    Runs (moveRev2 src d₁ d₂) S
      (Function.update (Function.update (Function.update S src []) d₁ ((S src).reverse ++ S d₁))
        d₂ ((S src).reverse ++ S d₂))
      (5 * (S src).length + 1) := by
  generalize hl : S src = l
  induction l generalizing S with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    have : Function.update (Function.update (Function.update S src []) d₁ ([].reverse ++ S d₁))
        d₂ ([].reverse ++ S d₂) = S := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← hl, update_eq_self', update_eq_self', update_eq_self']
    rw [this]; exact Eval.loopNil hl
  | cons b l ih =>
    set S₁ := Function.update (Function.update (Function.update S src l) d₁ (b :: S d₁))
      d₂ (b :: S d₂) with hS₁
    have h1' := ih S₁ (by rw [hS₁, update_ne' _ h2, update_ne' _ h1, update_same'])
    obtain ⟨t, ht, e⟩ := h1'
    have hstep : Eval (move2 src d₁ d₂) S S₁ 4 := by
      cases b
      · refine Eval.ifF hl ?_
        have := Eval.seq (Eval.pop src S) (Eval.seq
          (Eval.push d₁ false (Function.update S src (S src).tail))
          (Eval.push d₂ false _))
        simpa [hl, hS₁, update_ne' _ (Ne.symm h1), update_ne' _ (Ne.symm h2),
          update_ne' _ (Ne.symm h12)] using this
      · refine Eval.ifT hl ?_
        have := Eval.seq (Eval.pop src S) (Eval.seq
          (Eval.push d₁ true (Function.update S src (S src).tail))
          (Eval.push d₂ true _))
        simpa [hl, hS₁, update_ne' _ (Ne.symm h1), update_ne' _ (Ne.symm h2),
          update_ne' _ (Ne.symm h12)] using this
    refine ⟨4 + t + 1, by simp; omega, ?_⟩
    have := Eval.loopCons (by rw [hl]; simp) hstep e
    convert this using 1
    rw [hS₁]
    funext j
    by_cases hj2 : j = d₂
    · subst hj2; simp
    · by_cases hj1 : j = d₁
      · subst hj1; simp [update_ne' _ hj2]
      · by_cases hjs : j = src
        · subst hjs; simp [update_ne' _ hj2, update_ne' _ hj1]
        · simp [update_ne' _ hj2, update_ne' _ hj1, update_ne' _ hjs]

/-- Copy `src` onto `dst` through the empty temporary stack `tmp`. -/
def copy (src dst tmp : ℕ) : Prog := seq (moveRev src tmp) (moveRev2 tmp src dst)

theorem runs_copy {src dst tmp : ℕ} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (S : Store) (htmp : S tmp = []) :
    Runs (copy src dst tmp) S (Function.update S dst (S src ++ S dst))
      (9 * (S src).length + 2) := by
  have r1 := runs_moveRev h2 S
  set S₁ := Function.update (Function.update S src []) tmp ((S src).reverse ++ S tmp) with hS₁
  have r2 := runs_moveRev2 (Ne.symm h2) (Ne.symm h3) h1 S₁
  have e1 : S₁ tmp = (S src).reverse := by simp [hS₁, htmp]
  have e2 : S₁ src = [] := by simp [hS₁, update_ne' _ h2]
  have e3 : S₁ dst = S dst := by simp [hS₁, update_ne' _ h3, update_ne' _ h1.symm]
  refine (Runs.seq r1 r2).mono (by rw [e1, List.length_reverse]; omega) |>.of_eq ?_
  rw [e1, e2, e3, List.reverse_reverse, List.append_nil]
  funext j
  by_cases hjd : j = dst
  · subst hjd; simp
  · by_cases hjs : j = src
    · subst hjs; simp [update_ne' _ hjd]
    · by_cases hjt : j = tmp
      · subst hjt; simp [update_ne' _ hjd, update_ne' _ hjs, hS₁, htmp]
      · simp [update_ne' _ hjd, update_ne' _ hjs, update_ne' _ hjt, hS₁]

end Prog

end HTN.PTime.CobhamTM
