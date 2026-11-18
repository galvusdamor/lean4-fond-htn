import Mathlib.Computability.Partrec
import ComplexityTheory.Complexity.Basic
/-!
# Polynomial time as a concrete class: Cobham's class of bit-string functions

`HtnCompilability/Computable/PaperKarpLipton.lean` formalises the Karp–Lipton argument behind
the eight remaining cells of the paper's table, but has to leave *polynomial time* as a
parameter

    Eff : (InstDesc → InstDesc) → Prop

because this development had no formalised notion of it: the argument needs the instance
translation to be computable **in polynomial time**, and `HTN.Syn.CompSyn` only asks it to be
computable, which (as that file proves) makes the argument vacuous.

This file removes the parameter by defining polynomial time the machine-independent way, as
**Cobham's class**: the smallest class of functions on bit strings that contains the constant
empty string, the projections, the two successors `x ↦ b :: x` and the smash function, and is
closed under composition and under *bounded recursion on notation*.  Formalised here is
everything the Karp–Lipton argument needs of the class, and the two inclusions that make it a
sensible notion:

* `HTN.PTime.Cobham.primrec` — every function of the class is primitive recursive, hence
  `HTN.PTime.Cobham.computable` computable.  This is the inclusion the compilability argument
  uses: it is what makes `¬ CompSynEff` a *weaker* statement than `¬ CompSyn`;
* `HTN.PTime.Cobham.poly_length` — every function of the class has output length bounded by a
  fixed polynomial in the length of its longest argument.  Together the two say that the class
  sits inside the primitive recursive, polynomially bounded functions, which is the sanity
  check one wants of a definition of `FP`.

**Cobham's theorem is formalised** (in `ComplexityTheory/Complexity/CobhamTM/`, which builds on this file):
the class is exactly the class of functions computable in polynomial time by a Turing machine.
For unary functions `F : List Bool → List Bool` (the unary restriction `HTN.PTime.CobhamFun`
defined at the end of this file),

    HTN.PTime.CobhamTM.cobhamFun_iff_tm2ComputableInPolyTime :
      CobhamFun F ↔ Nonempty (Turing.TM2ComputableInPolyTime finEncodingListBool
        finEncodingListBool F)

where `Turing.TM2ComputableInPolyTime` is Mathlib's notion of polynomial-time computability by a
multi-stack Turing machine and `finEncodingListBool` encodes a bit string by itself over the
alphabet `Bool`.  The two directions are `cobhamFun_of_tm2ComputableInPolyTime`
(`ComplexityTheory/Complexity/CobhamTM/TMToCobham.lean`, simulation of the machine inside the class) and
`tm2ComputableInPolyTime_of_cobhamFun` (`ComplexityTheory/Complexity/CobhamTM/CobhamToTM.lean`, compilation
of the class to machines).

Because of this, the official notion of a polynomial-time function of the development,
`HTN.PTime.PolyTimeFun` (`ComplexityTheory/Complexity/PolyTimeTM.lean`), is *defined* by
Mathlib's Turing machines, and every polynomial-time reduction (`HTN.Syn.PolyTimeMap`,
`HTN.Syn.InP`, `HTN.Syn.ReducesToPartition`, …) is phrased through it; Cobham's class is the
tool used to *prove* that concrete functions are polynomial time
(`HTN.PTime.PolyTimeFun.of_cobham`).

Conventions.  Arguments are collected in a `List (List Bool)` rather than in a vector, so that
arity is implicit: a function reads the arguments it wants with `HTN.PTime.proj` and a missing
argument reads as the empty string.  The smash function is taken in its length form,
`|smash x y| = |x| * |y|`; this is the usual `2 ^ (|x| * |y|)` transcribed to strings, and it is
what makes the class closed under the polynomial bounds that bounded recursion needs.
-/

namespace HTN

namespace PTime

/-! ### Every function of the class is primitive recursive -/

theorem primrec_proj (n : ℕ) : Primrec (proj n) :=
  (Primrec.list_getD []).comp Primrec.id (Primrec.const n)

theorem primrec_consFn (b : Bool) : Primrec (consFn b) :=
  Primrec.list_cons.comp (Primrec.const b) ((Primrec.list_getD []).comp Primrec.id
    (Primrec.const 0))

theorem primrec_replicate_false : Primrec (fun n : ℕ => List.replicate n false) := by
  have h : Primrec (fun n : ℕ => (List.range n).map (fun _ => false)) :=
    Primrec.list_map Primrec.list_range (Primrec.const false).to₂
  exact h.of_eq fun n => by rw [List.map_const', List.length_range]

theorem primrec_smashFn : Primrec smashFn :=
  primrec_replicate_false.comp (Primrec.nat_mul.comp
    (Primrec.list_length.comp ((Primrec.list_getD []).comp Primrec.id (Primrec.const 0)))
    (Primrec.list_length.comp ((Primrec.list_getD []).comp Primrec.id (Primrec.const 1))))

theorem primrec_map_apply {hs : List Fn} (h : ∀ f ∈ hs, Primrec f) :
    Primrec (fun args : Args => hs.map fun f => f args) := by
  induction hs with
  | nil => simpa using (Primrec.const ([] : List (List Bool)))
  | cons f hs ih =>
    have hf : Primrec f := h f (by simp)
    have ihs := ih fun g hg => h g (by simp [hg])
    simpa using Primrec.list_cons.comp hf ihs

theorem cond_fn_apply (b : Bool) (h0 h1 : Fn) (args : Args) :
    (bif b then h1 else h0) args = bif b then h1 args else h0 args := by
  cases b <;> rfl

theorem primrec_brnAux {g h0 h1 : Fn} (hg : Primrec g) (hh0 : Primrec h0) (hh1 : Primrec h1) :
    Primrec₂ (brnAux g h0 h1) := by
  have harg : Primrec (fun r : (List Bool × Args) × (Bool × List Bool × List Bool) =>
      r.2.2.1 :: r.2.2.2 :: r.1.2) :=
    Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
  have hh : Primrec₂ (fun (p : List Bool × Args) (q : Bool × List Bool × List Bool) =>
      (bif q.1 then h1 else h0) (q.2.1 :: q.2.2 :: p.2)) := by
    have := Primrec.cond (Primrec.fst.comp Primrec.snd) (hh1.comp harg) (hh0.comp harg)
    exact (this.of_eq fun r => (cond_fn_apply r.2.1 h0 h1 _).symm).to₂
  have key := Primrec.list_rec (f := fun p : List Bool × Args => p.1)
    (g := fun p : List Bool × Args => g p.2) Primrec.fst (hg.comp Primrec.snd) hh
  refine key.of_eq fun p => ?_
  obtain ⟨x, v⟩ := p
  induction x with
  | nil => rfl
  | cons b x ih => simpa [brnAux] using congrArg (fun z => (bif b then h1 else h0) (x :: z :: v)) ih

theorem primrec_brnFn {g h0 h1 : Fn} (hg : Primrec g) (hh0 : Primrec h0) (hh1 : Primrec h1) :
    Primrec (brnFn g h0 h1) :=
  (primrec_brnAux hg hh0 hh1).comp
    ((Primrec.list_getD []).comp Primrec.id (Primrec.const 0)) Primrec.list_tail

/-- **Every function of Cobham's class is primitive recursive.** -/
theorem Cobham.primrec {f : Fn} (hf : Cobham f) : Primrec f := by
  induction hf with
  | empty => exact Primrec.const []
  | proj n => exact primrec_proj n
  | cons b => exact primrec_consFn b
  | smash => exact primrec_smashFn
  | comp _ _ ihg ihs => exact ihg.comp (primrec_map_apply ihs)
  | brn _ _ _ _ _ ihg ihh0 ihh1 _ => exact primrec_brnFn ihg ihh0 ihh1

/-- **Every function of Cobham's class is computable.**  This is the inclusion the
compilability argument uses. -/
theorem Cobham.computable {f : Fn} (hf : Cobham f) : Computable f := hf.primrec.to_comp

/-! ### Every function of the class is polynomially bounded -/

/-- The size of an argument list: the length of its longest string. -/
def argSize (args : Args) : ℕ := (args.map List.length).foldr max 0

@[simp] theorem argSize_nil : argSize [] = 0 := rfl

theorem argSize_cons (x : List Bool) (args : Args) :
    argSize (x :: args) = max x.length (argSize args) := rfl

theorem length_le_argSize {x : List Bool} {args : Args} (h : x ∈ args) :
    x.length ≤ argSize args := by
  induction args with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [argSize_cons]
    · exact le_trans (ih h) (by simp [argSize_cons])

theorem length_getD_le_argSize (args : Args) (n : ℕ) :
    (args.getD n []).length ≤ argSize args := by
  by_cases h : n < args.length
  · exact length_le_argSize (by
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h)
  · rw [List.getD, List.getElem?_eq_none (by omega)]
    simp

theorem argSize_tail_le (args : Args) : argSize args.tail ≤ argSize args := by
  cases args with
  | nil => simp
  | cons x xs => simp [argSize_cons]

/-- A finite family of polynomially bounded functions has a common polynomial bound. -/
theorem exists_common_bound {hs : List Fn}
    (h : ∀ f ∈ hs, ∃ p : Polynomial ℕ, ∀ args, (f args).length ≤ p.eval (argSize args)) :
    ∃ q : Polynomial ℕ, ∀ f ∈ hs, ∀ args, (f args).length ≤ q.eval (argSize args) := by
  induction hs with
  | nil => exact ⟨0, by simp⟩
  | cons f hs ih =>
    obtain ⟨q, hq⟩ := ih fun k hk => h k (by simp [hk])
    obtain ⟨pf, hpf⟩ := h f (by simp)
    refine ⟨q + pf, fun k hk args => ?_⟩
    rcases List.mem_cons.1 hk with rfl | hk
    · simpa using le_trans (hpf args) (by simp)
    · simpa using le_trans (hq k hk args) (by simp)

/-- The argument list produced by a family of functions with a common bound is bounded. -/
theorem argSize_map_le {hs : List Fn} {q : Polynomial ℕ}
    (hq : ∀ f ∈ hs, ∀ args, (f args).length ≤ q.eval (argSize args)) (args : Args) :
    argSize (hs.map fun f => f args) ≤ q.eval (argSize args) := by
  induction hs with
  | nil => simp
  | cons f hs ih =>
    rw [List.map_cons, argSize_cons]
    exact max_le (hq f (by simp) args) (ih fun k hk => hq k (by simp [hk]))

/-- **Every function of Cobham's class is polynomially bounded**: its output is no longer than
a fixed polynomial in the length of its longest argument. -/
theorem Cobham.poly_length {f : Fn} (hf : Cobham f) :
    ∃ p : Polynomial ℕ, ∀ args, (f args).length ≤ p.eval (argSize args) := by
  induction hf with
  | empty => exact ⟨0, by simp⟩
  | proj n => exact ⟨Polynomial.X, fun args => by simpa using length_getD_le_argSize args n⟩
  | cons b =>
    exact ⟨Polynomial.X + Polynomial.C 1, fun args => by
      simpa [consFn] using Nat.succ_le_succ (length_getD_le_argSize args 0)⟩
  | smash =>
    refine ⟨Polynomial.X ^ 2, fun args => ?_⟩
    have h0 := length_getD_le_argSize args 0
    have h1 := length_getD_le_argSize args 1
    calc (smashFn args).length = (args.getD 0 []).length * (args.getD 1 []).length := by
            simp [smashFn]
      _ ≤ argSize args * argSize args := Nat.mul_le_mul h0 h1
      _ = (Polynomial.X ^ 2 : Polynomial ℕ).eval (argSize args) := by simp [sq]
  | @comp g hs _ _ ihg ihs =>
    obtain ⟨pg, hpg⟩ := ihg
    obtain ⟨q, hq⟩ := exists_common_bound ihs
    refine ⟨pg.comp q, fun args => ?_⟩
    have hsize : argSize (hs.map fun h => h args) ≤ q.eval (argSize args) :=
      argSize_map_le hq args
    calc (compFn g hs args).length ≤ pg.eval (argSize (hs.map fun h => h args)) := hpg _
      _ ≤ pg.eval (q.eval (argSize args)) := Polynomial.eval_mono_nat pg hsize
      _ = (pg.comp q).eval (argSize args) := by simp
  | @brn g h0 h1 bd _ _ _ _ hbound _ _ _ ihbd =>
    obtain ⟨p, hp⟩ := ihbd
    exact ⟨p, fun args => le_trans (hbound args) (hp args)⟩

/-! ### The unary functions of the class -/

/-- **The unary functions of Cobham's class**: the unary restriction of a function of Cobham's
class.  By Cobham's theorem (`HTN.PTime.CobhamTM.cobhamFun_iff_tm2ComputableInPolyTime`) these
are exactly the functions computed in polynomial time by a Turing machine, which is how the
official notion `HTN.PTime.PolyTimeFun` is defined. -/
def CobhamFun (F : List Bool → List Bool) : Prop := ∃ f : Fn, Cobham f ∧ ∀ x, F x = f [x]

theorem CobhamFun.computable {F : List Bool → List Bool} (hF : CobhamFun F) :
    Computable F := by
  obtain ⟨f, hf, hFf⟩ := hF
  exact (hf.computable.comp (Computable.list_cons.comp Computable.id
    (Computable.const []))).of_eq fun x => (hFf x).symm

theorem CobhamFun.poly_length {F : List Bool → List Bool} (hF : CobhamFun F) :
    ∃ p : Polynomial ℕ, ∀ x, (F x).length ≤ p.eval x.length := by
  obtain ⟨f, hf, hFf⟩ := hF
  obtain ⟨p, hp⟩ := hf.poly_length
  exact ⟨p, fun x => by simpa [hFf x, argSize_cons] using hp [x]⟩

/-- The identity is a unary function of Cobham's class. -/
theorem cobhamFun_id : CobhamFun _root_.id :=
  ⟨proj 0, Cobham.proj 0, fun _ => rfl⟩

/-- The unary functions of Cobham's class are closed under composition. -/
theorem CobhamFun.comp {F G : List Bool → List Bool} (hF : CobhamFun F)
    (hG : CobhamFun G) : CobhamFun (fun x => F (G x)) := by
  obtain ⟨f, hf, hFf⟩ := hF
  obtain ⟨g, hg, hGg⟩ := hG
  refine ⟨compFn f [g], Cobham.comp hf ?_, fun x => ?_⟩
  · intro h hh
    rw [List.mem_singleton.1 hh]
    exact hg
  · simp [compFn, hFf, hGg]

end PTime

end HTN
