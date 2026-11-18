import ComplexityTheory.Complexity.Cobham
/-!
# Cobham's class is not degenerate: some functions it contains

`ComplexityTheory/Complexity/Cobham.lean` defines the class and proves the two inclusions the
compilability argument needs.  Those say what the class does *not* contain; this file exercises
the two non-trivial closure rules — composition and bounded recursion on notation — on concrete
functions, which is what one wants in order to believe that the class is a genuine class of
polynomial-time functions rather than a vacuous one:

* `HTN.PTime.cobham_tail` — the tail of a bit string;
* `HTN.PTime.cobham_append` — concatenation, the first function that really needs the recursion
  rule together with a bound: the bound is the smash function of the two arguments, each
  lengthened by one bit;
* `HTN.PTime.cobhamFun_tail`, `HTN.PTime.cobhamFun_appendConst` — the same, as unary
  polynomial-time functions on bit strings.
-/

namespace HTN

namespace PTime

/-! ### The tail of a bit string -/

theorem brnFn_tail :
    brnFn (fun _ => []) (proj 0) (proj 0) = fun args => (args.getD 0 []).tail := by
  funext args
  rw [brnFn]
  cases hx : args.getD 0 [] with
  | nil => simp [brnAux]
  | cons b x => cases b <;> simp [brnAux, proj]

/-- **The tail function belongs to Cobham's class.** -/
theorem cobham_tail : Cobham (fun args => (args.getD 0 []).tail) := by
  have hb : ∀ args : Args,
      (brnFn (fun _ => []) (proj 0) (proj 0) args).length ≤ (proj 0 args).length := by
    intro args
    rw [brnFn_tail]
    simp [proj]
  simpa [brnFn_tail] using
    Cobham.brn Cobham.empty (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 0) hb

/-! ### Concatenation -/

/-- The step function of the recursion for concatenation: prefix the recursive value with `b`.
The recursive value is the second argument the recursion supplies. -/
def consRec (b : Bool) : Fn := compFn (consFn b) [proj 1]

theorem consRec_apply (b : Bool) (args : Args) :
    consRec b args = b :: args.getD 1 [] := by
  simp [consRec, compFn, consFn, proj]

/-- The bound used for concatenation: the smash of the two arguments, each lengthened by one
bit, has length `(|x| + 1) * (|y| + 1) ≥ |x| + |y|`. -/
def appendBound : Fn :=
  compFn smashFn [compFn (consFn false) [proj 0], compFn (consFn false) [proj 1]]

theorem length_appendBound (args : Args) :
    (appendBound args).length = ((args.getD 0 []).length + 1) * ((args.getD 1 []).length + 1) := by
  simp [appendBound, compFn, smashFn, consFn, proj]

theorem cobham_appendBound : Cobham appendBound := by
  refine Cobham.comp Cobham.smash ?_
  intro h hh
  rcases List.mem_cons.1 hh with rfl | hh
  · exact Cobham.comp (Cobham.cons false) (by
      intro k hk
      rw [List.mem_singleton.1 hk]
      exact Cobham.proj 0)
  · rw [List.mem_singleton.1 hh]
    exact Cobham.comp (Cobham.cons false) (by
      intro k hk
      rw [List.mem_singleton.1 hk]
      exact Cobham.proj 1)

theorem brnAux_append (v : Args) : ∀ x : List Bool,
    brnAux (proj 0) (consRec false) (consRec true) x v = x ++ v.getD 0 [] := by
  intro x
  induction x with
  | nil => simp [brnAux, proj]
  | cons b x ih =>
    cases b <;> simp [brnAux, consRec_apply, ih]

theorem brnFn_append :
    brnFn (proj 0) (consRec false) (consRec true) =
      fun args => args.getD 0 [] ++ args.getD 1 [] := by
  funext args
  rw [brnFn, brnAux_append]
  cases args with
  | nil => simp
  | cons x xs => simp

theorem cobham_consRec (b : Bool) : Cobham (consRec b) :=
  Cobham.comp (Cobham.cons b) (by
    intro k hk
    rw [List.mem_singleton.1 hk]
    exact Cobham.proj 1)

/-- **Concatenation belongs to Cobham's class.** -/
theorem cobham_append : Cobham (fun args => args.getD 0 [] ++ args.getD 1 []) := by
  have hb : ∀ args : Args,
      (brnFn (proj 0) (consRec false) (consRec true) args).length ≤
        (appendBound args).length := by
    intro args
    rw [brnFn_append, length_appendBound]
    simp only [List.length_append]
    nlinarith [(args.getD 0 []).length, (args.getD 1 []).length,
      Nat.zero_le ((args.getD 0 []).length * (args.getD 1 []).length)]
  simpa [brnFn_append] using
    Cobham.brn (Cobham.proj 0) (cobham_consRec false) (cobham_consRec true) cobham_appendBound hb

/-! ### As unary polynomial-time functions -/

/-- The tail function is polynomial time. -/
theorem cobhamFun_tail : CobhamFun (fun x : List Bool => x.tail) :=
  ⟨_, cobham_tail, fun _ => rfl⟩

/-- Every constant belongs to Cobham's class. -/
theorem cobham_const : ∀ y : List Bool, Cobham (fun _ : Args => y)
  | [] => Cobham.empty
  | b :: y => by
    have h : Cobham (compFn (consFn b) [fun _ : Args => y]) :=
      Cobham.comp (Cobham.cons b) (by
        intro k hk
        rw [List.mem_singleton.1 hk]
        exact cobham_const y)
    simpa [compFn, consFn, proj] using h

/-- Appending a fixed string on the right is polynomial time. -/
theorem cobhamFun_appendConst (y : List Bool) : CobhamFun (fun x : List Bool => x ++ y) := by
  refine ⟨compFn (fun args => args.getD 0 [] ++ args.getD 1 [])
    [proj 0, fun _ => y], Cobham.comp cobham_append ?_, fun x => by simp [compFn, proj]⟩
  intro k hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact Cobham.proj 0
  · rw [List.mem_singleton.1 hk]
    exact cobham_const y

end PTime

end HTN
