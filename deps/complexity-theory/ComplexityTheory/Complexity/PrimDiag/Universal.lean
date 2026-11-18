import ComplexityTheory.Complexity.PrimDiag.Flat
import ComplexityTheory.Complexity.CobhamTM.CobhamToTM
/-!
# A primitive recursive universal evaluator for Cobham's class

`uevalB C M A T args` runs the flat instruction list `C` (`Prog.fstep`) for `T` steps on `M`
stacks, the first `A` of which hold the arguments, and reads the first bit of stack `A`.

* `primrec_uevalB` — `uevalB` is primitive recursive **jointly in the program `C`**, the numbers
  `M`, `A`, `T` and the arguments;
* `exists_uevalB` — every predicate of Cobham's class is `uevalB C M A` for suitable `C`, `M`,
  `A`, with a running time `(|args| + m) ^ m`.

Together they give a primitive recursive enumeration of all polynomial-time predicates, the
ingredient of the diagonal argument of `ComplexityTheory/Complexity/PrimDiag/Diag.lean`.
-/

namespace HTN.PTime.CobhamTM

namespace Prog

/-! ### Coding instructions -/

/-- Instructions as a sum of products of numbers and Booleans. -/
def instrEquiv : Instr ≃ (ℕ × Bool) ⊕ (ℕ ⊕ ((ℕ × ℕ × ℕ × ℕ) ⊕ ℕ)) where
  toFun
    | .push k b => .inl (k, b)
    | .pop k => .inr (.inl k)
    | .br k a b c => .inr (.inr (.inl (k, a, b, c)))
    | .jmp a => .inr (.inr (.inr a))
  invFun
    | .inl (k, b) => .push k b
    | .inr (.inl k) => .pop k
    | .inr (.inr (.inl (k, a, b, c))) => .br k a b c
    | .inr (.inr (.inr a)) => .jmp a
  left_inv := by intro i; cases i <;> rfl
  right_inv := by intro s; rcases s with ⟨k, b⟩ | k | ⟨k, a, b, c⟩ | a <;> rfl

instance : Primcodable Instr := Primcodable.ofEquiv _ instrEquiv

/-! ### Primitive recursiveness of the machine -/

theorem primrec_getS : Primrec₂ getS := Primrec.list_getD []

theorem primrec_setS : Primrec fun x : List (List Bool) × ℕ × List Bool => setS x.1 x.2.1 x.2.2 := by
  unfold setS
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) ?_
  refine Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    ((Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

theorem brTarget_eq (l : List Bool) (a₀ aF aT : ℕ) :
    brTarget l a₀ aF aT = Option.casesOn l.head? a₀ (fun b => cond b aT aF) := by
  rcases l with _ | ⟨_ | _, _⟩ <;> rfl

theorem primrec_brTarget :
    Primrec fun x : List Bool × ℕ × ℕ × ℕ => brTarget x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  refine Primrec.of_eq ?_ fun x => (brTarget_eq _ _ _ _).symm
  refine Primrec.option_casesOn (Primrec.list_head?.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd) ?_
  exact Primrec.cond Primrec.snd
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))

/-- The coded instructions. -/
abbrev ISum : Type := (ℕ × Bool) ⊕ (ℕ ⊕ ((ℕ × ℕ × ℕ × ℕ) ⊕ ℕ))
/-- A tail of the coding. -/
abbrev ISum₁ : Type := ℕ ⊕ ((ℕ × ℕ × ℕ × ℕ) ⊕ ℕ)
/-- A tail of the coding. -/
abbrev ISum₂ : Type := (ℕ × ℕ × ℕ × ℕ) ⊕ ℕ

/-- `execI` through the coding of instructions. -/
def execS (x : (ℕ × List (List Bool)) × ISum) :
    ℕ × List (List Bool) :=
  Sum.casesOn x.2 (fun kb => (x.1.1 + 1, setS x.1.2 kb.1 (kb.2 :: getS x.1.2 kb.1)))
    (fun s => Sum.casesOn s (fun k => (x.1.1 + 1, setS x.1.2 k (getS x.1.2 k).tail))
      (fun s => Sum.casesOn s (fun q => (brTarget (getS x.1.2 q.1) q.2.1 q.2.2.1 q.2.2.2, x.1.2))
        (fun a => (a, x.1.2))))

/-- Configurations of the flat machine. -/
abbrev Cfg : Type := ℕ × List (List Bool)

theorem primrec_push : Primrec fun y : Cfg × (ℕ × Bool) =>
    ((y.1.1 + 1, setS y.1.2 y.2.1 (y.2.2 :: getS y.1.2 y.2.1)) : Cfg) :=
  Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (primrec_setS.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd)
          (primrec_getS.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))))))

theorem primrec_pop : Primrec fun y : Cfg × ℕ =>
    ((y.1.1 + 1, setS y.1.2 y.2 (getS y.1.2 y.2).tail) : Cfg) :=
  Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
    (primrec_setS.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.pair Primrec.snd
        (Primrec.list_tail.comp (primrec_getS.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))))

theorem primrec_br : Primrec fun y : Cfg × (ℕ × ℕ × ℕ × ℕ) =>
    ((brTarget (getS y.1.2 y.2.1) y.2.2.1 y.2.2.2.1 y.2.2.2.2, y.1.2) : Cfg) := by
  refine Primrec.pair ?_ (Primrec.snd.comp Primrec.fst)
  exact primrec_brTarget.comp (Primrec.pair
    (primrec_getS.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd))

theorem primrec_jmp : Primrec fun y : Cfg × ℕ => ((y.2, y.1.2) : Cfg) :=
  Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)

theorem primrec_execS : Primrec execS := by
  unfold execS
  refine Primrec.sumCasesOn Primrec.snd
    (primrec_push.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂ ?_
  refine Primrec.sumCasesOn Primrec.snd
    (primrec_pop.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      Primrec.snd)).to₂ ?_
  exact Primrec.sumCasesOn Primrec.snd
    (primrec_br.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂
    (primrec_jmp.comp (Primrec.pair
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)).to₂

theorem execI_eq (pc : ℕ) (T : List (List Bool)) (i : Instr) :
    execI pc T i = execS ((pc, T), instrEquiv i) := by
  cases i <;> rfl

theorem primrec_execI :
    Primrec fun x : (ℕ × List (List Bool)) × Instr => execI x.1.1 x.1.2 x.2 := by
  refine Primrec.of_eq ?_ fun x => (execI_eq x.1.1 x.1.2 x.2).symm
  exact primrec_execS.comp (Primrec.pair Primrec.fst
    ((Primrec.of_equiv (e := instrEquiv)).comp Primrec.snd))

theorem primrec_fstep :
    Primrec fun x : List Instr × (ℕ × List (List Bool)) => fstep x.1 x.2 := by
  unfold fstep
  have : Primrec fun x : List Instr × (ℕ × List (List Bool)) =>
      @Option.casesOn Instr (fun _ => ℕ × List (List Bool)) (x.1[x.2.1]?) x.2
        (fun i => execI x.2.1 x.2.2 i) :=
    Primrec.option_casesOn (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      Primrec.snd (primrec_execI.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  refine this.of_eq fun x => ?_
  cases x.1[x.2.1]? <;> rfl

/-! ### The universal evaluator -/

/-- The initial list of `M` stacks: the arguments on stacks `0, …, A - 1`, the others empty. -/
def initL (M A : ℕ) (args : Args) : List (List Bool) :=
  (List.range M).map fun j => if j < A then args.getD j [] else []

/-- **The universal evaluator**: run `C` for `T` steps from `initL M A args`, read the first bit of
stack `A`. -/
def uevalB (C : List Instr) (M A T : ℕ) (args : Args) : Bool :=
  ((getS ((fstep C)^[T] (0, initL M A args)).2 A).head?).getD false

theorem primrec_initL : Primrec fun x : (ℕ × ℕ) × Args => initL x.1.1 x.1.2 x.2 := by
  unfold initL
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) ?_
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
    ((Primrec.list_getD []).comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const [])

theorem primrec_uevalB :
    Primrec fun x : (List Instr × ℕ × ℕ) × ℕ × Args =>
      uevalB x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2 := by
  unfold uevalB
  have hit : Primrec fun x : (List Instr × ℕ × ℕ) × ℕ × Args =>
      (fstep x.1.1)^[x.2.1] (0, initL x.1.2.1 x.1.2.2 x.2.2) :=
    Primrec.nat_iterate (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.const 0) (primrec_initL.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) (Primrec.snd.comp Primrec.snd))))
      (primrec_fstep.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).to₂
  exact Primrec.option_getD.comp (Primrec.list_head?.comp (primrec_getS.comp
    (Primrec.snd.comp hit) (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
    (Primrec.const false)

/-! ### Every predicate of Cobham's class is evaluated -/

/-- Every polynomial is bounded by `(s + m) ^ m` for some `m ≥ 1`. -/
theorem exists_powSelf_bound (p : Polynomial ℕ) : ∃ m, 1 ≤ m ∧ ∀ s, p.eval s ≤ (s + m) ^ m := by
  set d := p.natDegree
  set c := ∑ i ∈ Finset.range (d + 1), p.coeff i
  refine ⟨c + d + 1, by omega, fun s => ?_⟩
  have hs : 1 ≤ s + (c + d + 1) := by omega
  rw [Polynomial.eval_eq_sum_range]
  calc ∑ i ∈ Finset.range (d + 1), p.coeff i * s ^ i
      ≤ ∑ i ∈ Finset.range (d + 1), p.coeff i * (s + (c + d + 1)) ^ d := by
        refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
        rw [Finset.mem_range] at hi
        calc s ^ i ≤ (s + (c + d + 1)) ^ i := Nat.pow_le_pow_left (by omega) _
          _ ≤ (s + (c + d + 1)) ^ d := Nat.pow_le_pow_right hs (by omega)
    _ = c * (s + (c + d + 1)) ^ d := by rw [← Finset.sum_mul]
    _ ≤ (s + (c + d + 1)) * (s + (c + d + 1)) ^ d := Nat.mul_le_mul_right _ (by omega)
    _ = (s + (c + d + 1)) ^ (d + 1) := by ring
    _ ≤ (s + (c + d + 1)) ^ (c + d + 1) := Nat.pow_le_pow_right hs (by omega)

/-- `(s + m) ^ m` is monotone in `m` (for `m ≥ 1`). -/
theorem pow_bound_mono {s m m' : ℕ} (h1 : 1 ≤ m) (h : m ≤ m') : (s + m) ^ m ≤ (s + m') ^ m' :=
  calc (s + m) ^ m ≤ (s + m') ^ m := Nat.pow_le_pow_left (by omega) _
    _ ≤ (s + m') ^ m' := Nat.pow_le_pow_right (by omega) h

/-- **Universality**: every predicate of Cobham's class is computed by the universal evaluator,
for a suitable program, within `(|args| + m) ^ m` steps. -/
theorem exists_uevalB {V : Args → Bool} (hV : CobhamB V) :
    ∃ (C : List Instr) (M A m : ℕ), 1 ≤ m ∧
      ∀ (args : Args) (T : ℕ), (argSize args + m) ^ m ≤ T → uevalB C M A T args = V args := by
  obtain ⟨R⟩ := nonempty_realizer hV
  obtain ⟨m, hm1, hm⟩ := exists_powSelf_bound (2 * R.time)
  refine ⟨compile (R.P id R.A (R.A + 1)) 0, max (maxStack (R.P id R.A (R.A + 1))) R.A + 1, R.A, m, hm1, fun args T hT => ?_⟩
  set S : Store := fun j => if j < R.A then args.getD j [] else [] with hS
  have hspec := R.spec id R.A (R.A + 1) S (fun i hi => by simp; omega) (by omega)
    (fun i hi => by simp; omega) (by simp [S]) (fun j hj => by simp [S]; omega)
  obtain ⟨t, ht, e⟩ := hspec
  have hreach := flat_compile (C := compile (R.P id R.A (R.A + 1)) 0) (M := max (maxStack (R.P id R.A (R.A + 1))) R.A + 1) e (o := 0)
    (by omega) (fun i _ => by simp)
  obtain ⟨k, hk, hke⟩ := hreach
  have hsz : argSize (argsOf R.A id S) ≤ argSize args :=
    argSize_argsOf_le_of_getD fun i hi => by simp [S, hi]
  have htime : 2 * t ≤ T := by
    have h1 := hm (argSize (argsOf R.A id S))
    have h2 : (argSize (argsOf R.A id S) + m) ^ m ≤ (argSize args + m) ^ m :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : (2 * R.time).eval (argSize (argsOf R.A id S)) =
        2 * R.time.eval (argSize (argsOf R.A id S)) := by simp
    omega
  have hinit : initL (max (maxStack (R.P id R.A (R.A + 1))) R.A + 1) R.A args = toL (max (maxStack (R.P id R.A (R.A + 1))) R.A + 1) S := rfl
  have hrun : (fstep (compile (R.P id R.A (R.A + 1)) 0))^[T] (0, initL (max (maxStack (R.P id R.A (R.A + 1))) R.A + 1) R.A args) =
      (0 + size (R.P id R.A (R.A + 1)), toL (max (maxStack (R.P id R.A (R.A + 1))) R.A + 1)
        (Function.update S R.A [V (argsOf R.A id S)])) := by
    rw [hinit, show T = (T - k) + k by omega, Function.iterate_add_apply, hke]
    exact iterate_fstep_of_le (by simp [length_compile]) _
  have hargs : argsOf R.A id S = padArgs R.A args := by
    simp only [argsOf, padArgs, id]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp [S, hi]
  have hV' : V (padArgs R.A args) = V args := by
    have := R.reads args
    simp only [List.cons.injEq, and_true] at this
    exact this.symm
  unfold uevalB
  rw [hrun, getS_toL (by omega)]
  simp [hargs, hV']

end Prog

end HTN.PTime.CobhamTM
