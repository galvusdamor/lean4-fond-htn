import HtnComplexity.ToHtnAc.ToHtnAc
import HtnPlanning.Computable.Syntax
/-!
# Numbering the signature of the compiled acyclic domain

The compilation of totally ordered problems into acyclic ones
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) produces a domain over the signature

* `HTN.ToAc.AcFact F A C` — facts,
* `HTN.ToAc.AcAct F A C` — action names,
* `HTN.ToAc.AcTask F A C` — compound task names,
* `ℕ × ℕ` — task identifiers,

where `(F, A, C)` is the signature of the source problem.  A *description*
(`HtnPlanning/Computable/Syntax.lean`) uses `ℕ` for all four components, so lifting the
construction to descriptions needs an injective numbering of those three types (and of
`ℕ × ℕ`, for which `Nat.pairEquiv` is used).

This file supplies it.  Given injections `f : F → ℕ`, `a : A → ℕ`, `c : C → ℕ` it defines

* `HTN.ToAc.encFact f a c`, `HTN.ToAc.encAct f a c`, `HTN.ToAc.encTask f a c`

and proves them injective.  Each constructor gets a tag (the residue modulo the number of
constructors), and its arguments are packed linearly — the copy index of a fact is a `Fin 5`,
so `5 * f v + i` is injective.  The encoding of a compound task name is recursive, since `cnt`
and `cntPar` carry a task name; there the two arguments are packed with `Nat.pair`.
-/

namespace HTN

namespace ToAc

variable {F A C : Type}

/-- The two channels, numbered. -/
def encRW : RW → ℕ
  | RW.read => 0
  | RW.write => 1

theorem encRW_injective : Function.Injective encRW := by
  intro x y h
  cases x <;> cases y <;> simp_all [encRW]

/-- A task name of the source signature, numbered. -/
def encName (a : A → ℕ) (c : C → ℕ) : A ⊕ C → ℕ
  | Sum.inl x => 2 * a x
  | Sum.inr y => 2 * c y + 1

theorem encName_injective {a : A → ℕ} {c : C → ℕ} (ha : Function.Injective a)
    (hc : Function.Injective c) :
    Function.Injective (encName a c) := by
  rintro (x | x) (y | y) h <;> simp only [encName] at h
  · exact congrArg Sum.inl (ha (by omega))
  · omega
  · omega
  · exact congrArg Sum.inr (hc (by omega))

/-- **The facts of the compiled domain, numbered.** -/
def encFact (f : F → ℕ) (a : A → ℕ) (c : C → ℕ) : AcFact F A C → ℕ
  | AcFact.key0 => 0
  | AcFact.key1 x => 6 * encRW x + 1
  | AcFact.key2 x => 6 * encRW x + 2
  | AcFact.pos v i => 6 * (5 * f v + (i : ℕ)) + 3
  | AcFact.neg v i => 6 * (5 * f v + (i : ℕ)) + 4
  | AcFact.task t => 6 * encName a c t + 5

/-- **The actions of the compiled domain, numbered.** -/
def encAct (f : F → ℕ) (a : A → ℕ) (c : C → ℕ) : AcAct F A C → ℕ
  | AcAct.setV v i => 13 * (5 * f v + (i : ℕ))
  | AcAct.delV v i => 13 * (5 * f v + (i : ℕ)) + 1
  | AcAct.prePV v i j => 13 * (25 * f v + 5 * (i : ℕ) + (j : ℕ)) + 2
  | AcAct.preNV v i j => 13 * (25 * f v + 5 * (i : ℕ) + (j : ℕ)) + 3
  | AcAct.setC t => 13 * encName a c t + 4
  | AcAct.preC t => 13 * encName a c t + 5
  | AcAct.lock => 6
  | AcAct.unlock => 7
  | AcAct.ask x => 13 * encRW x + 8
  | AcAct.accept x => 13 * encRW x + 9
  | AcAct.doneA x => 13 * encRW x + 10
  | AcAct.waitA x => 13 * encRW x + 11
  | AcAct.op2 o => 13 * a o + 12

/-- **The compound task names of the compiled domain, numbered.** -/
def encTask (f : F → ℕ) (a : A → ℕ) (c : C → ℕ) : AcTask F A C → ℕ
  | AcTask.SEL i => 13 * (i : ℕ)
  | AcTask.SELn n i => 13 * (5 * n + (i : ℕ)) + 1
  | AcTask.EQ i j => 13 * (5 * (i : ℕ) + (j : ℕ)) + 2
  | AcTask.EQn n i j => 13 * (25 * n + 5 * (i : ℕ) + (j : ℕ)) + 3
  | AcTask.STATE1 n => 13 * n + 4
  | AcTask.STATE3 n => 13 * n + 5
  | AcTask.MEM => 6
  | AcTask.WRITE => 7
  | AcTask.READ => 8
  | AcTask.TUPLE => 9
  | AcTask.cnt t k => 13 * Nat.pair (encTask f a c t) k + 10
  | AcTask.cntPar t k => 13 * Nat.pair (encTask f a c t) k + 11
  | AcTask.tI => 12

variable {f : F → ℕ} {a : A → ℕ} {c : C → ℕ}

private lemma pair_inj {x y z w : ℕ} (h : Nat.pair x y = Nat.pair z w) : x = z ∧ y = w := by
  have h1 := congrArg Nat.unpair h
  simpa using h1

theorem encFact_injective (hf : Function.Injective f) (ha : Function.Injective a)
    (hc : Function.Injective c) : Function.Injective (encFact f a c) := by
  intro x y h
  cases x <;> cases y <;> simp only [encFact] at h <;>
    first
      | omega
      | (congr 1 <;>
          first
            | omega
            | (refine hf ?_; omega)
            | (refine encRW_injective ?_; omega)
            | (refine encName_injective ha hc ?_; omega))

theorem encAct_injective (hf : Function.Injective f) (ha : Function.Injective a)
    (hc : Function.Injective c) : Function.Injective (encAct f a c) := by
  intro x y h
  cases x <;> cases y <;> simp only [encAct] at h <;>
    first
      | omega
      | (congr 1 <;>
          first
            | omega
            | (refine hf ?_; omega)
            | (refine ha ?_; omega)
            | (refine encRW_injective ?_; omega)
            | (refine encName_injective ha hc ?_; omega))

theorem encTask_injective : Function.Injective (encTask f a c) := by
  intro x
  induction x with
  | SEL i => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1; omega)
  | SELn n i =>
    intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1 <;> omega)
  | EQ i j =>
    intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1 <;> omega)
  | EQn n i j =>
    intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1 <;> omega)
  | STATE1 n =>
    intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1; omega)
  | STATE3 n =>
    intro y h; cases y <;> simp only [encTask] at h <;> first | omega | (congr 1; omega)
  | MEM => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | rfl
  | WRITE => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | rfl
  | READ => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | rfl
  | TUPLE => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | rfl
  | cnt t k ih =>
    intro y h
    cases y <;> simp only [encTask] at h <;> try omega
    rename_i t' k'
    obtain ⟨h1, h2⟩ :=
      pair_inj (show Nat.pair (encTask f a c t) k = Nat.pair (encTask f a c t') k' by omega)
    rw [ih h1, h2]
  | cntPar t k ih =>
    intro y h
    cases y <;> simp only [encTask] at h <;> try omega
    rename_i t' k'
    obtain ⟨h1, h2⟩ :=
      pair_inj (show Nat.pair (encTask f a c t) k = Nat.pair (encTask f a c t') k' by omega)
    rw [ih h1, h2]
  | tI => intro y h; cases y <;> simp only [encTask] at h <;> first | omega | rfl

end ToAc

end HTN
