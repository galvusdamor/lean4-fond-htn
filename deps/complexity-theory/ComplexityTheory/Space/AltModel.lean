import ComplexityTheory.Space.Model
import ComplexityTheory.Complexity.PolyTimeTM
import ComplexityTheory.Complexity.Basic
/-!
# Alternating polynomial space with advice: the class `EXPTIME/poly`

Cells 3 and 5 of Table 3 have the target `TO-HTN-1`, whose plan-existence problem is
`EXPTIME`-complete.  The target-side upper bound they need is therefore an *exponential-time*
algorithm with the domain description as advice, and the complexity hypothesis they run on is
`NEXPTIME ⊄ EXPTIME/poly`.

As for the closed cells (`HTN.Space.ExptimeNePspace`), `EXPTIME` is read here as **alternating
polynomial space** (Chandra–Kozen–Stockmeyer: `APSPACE = EXPTIME`, and the simulation is uniform
in an extra advice string, so `APSPACE/poly = EXPTIME/poly`).  The model is the alternating
counterpart of `HTN.Space.NSpace`:

* a configuration is a tuple of `k` bit strings, each of length polynomial in the length of the
  input and of the advice;
* the initial-configuration test, the acceptance test, the classification of a configuration as
  universal or existential, and the transition relation are predicates of Cobham's class;
* acceptance is the **least fixpoint** of the alternating acceptance rule (no step bound): an
  accepting configuration accepts, a universal one accepts when all its successors do, an
  existential one when some successor does.

Since there are only exponentially many configurations of polynomial size, the least fixpoint is
computable in exponential time; conversely every exponential-time machine is simulated in this
model.  Tests receive their arguments in the order `x, a, c` (input, advice, configuration) and
`x, a, c', c` for the transition relation.

## Main definitions and results

* `HTN.Space.AltSpace`, `HTN.Space.AltSpace.Acc`, `HTN.Space.AltSpace.Accepts` — the model;
* `HTN.Space.InAltSpacePoly` — the class `EXPTIME/poly` (advice of polynomial length depending on
  the length of the input only);
* `HTN.Space.AltSpace.pre`, `HTN.Space.AltSpace.accepts_pre` — the input may be pre-processed by
  any function of Cobham's class;
* `HTN.Space.inAltSpacePoly_of_precomp` — the packaged form the target bridge uses.
-/

namespace HTN

namespace Space

open PTime

/-! ### Substituting a computed string for the first argument -/

/-- The argument list with its first entry replaced by `f` of it, cut or padded to exactly
`m + 1` entries. -/
def preArgs (f : Fn) (m : ℕ) (args : Args) : Args :=
  f [args.getD 0 []] :: (List.range m).map fun i => args.getD (i + 1) []

theorem range_map_getD (l : List (List Bool)) :
    (List.range l.length).map (fun i => l.getD i []) = l := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

theorem preArgs_cons (f : Fn) (x : List Bool) (rest : Args) :
    preArgs f rest.length (x :: rest) = f [x] :: rest := by
  simp only [preArgs, List.getD_cons_zero, List.getD_cons_succ, range_map_getD]

theorem cobhamB_preArgs {p : Args → Bool} (hp : CobhamB p) {f : Fn} (hf : Cobham f) (m : ℕ) :
    CobhamB fun args => p (preArgs f m args) := by
  have hc : Cobham (compFn (fun args => [p args])
      (compFn f [proj 0] :: (List.range m).map fun i => proj (i + 1))) := by
    refine Cobham.comp hp ?_
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact cobham_c1 hf (Cobham.proj 0)
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hh
      exact Cobham.proj _
  refine hc.of_eq' fun args => ?_
  simp [compFn, preArgs, proj, List.map_map, Function.comp_def]

/-! ### The model -/

namespace AltSpace

variable (M : AltSpace)

end AltSpace

/-! ### Pre-processing the input -/

namespace AltSpace

variable (M : AltSpace) (f : Fn) (p : Polynomial ℕ)

/-- **The input of a machine may be pre-processed by a function of Cobham's class**, given a
polynomial bound on the length of its value. -/
noncomputable def pre (hf : Cobham f)
    (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length) : AltSpace where
  k := M.k
  initB := fun args => M.initB (preArgs f (M.k + 1) args)
  accB := fun args => M.accB (preArgs f (M.k + 1) args)
  univB := fun args => M.univB (preArgs f (M.k + 1) args)
  stepB := fun args => M.stepB (preArgs f (M.k + M.k + 1) args)
  cobham_initB := cobhamB_preArgs M.cobham_initB hf _
  cobham_accB := cobhamB_preArgs M.cobham_accB hf _
  cobham_univB := cobhamB_preArgs M.cobham_univB hf _
  cobham_stepB := cobhamB_preArgs M.cobham_stepB hf _
  bound := M.bound.comp (p + Polynomial.X)
  initB_length := by
    intro x a c hc h w hw
    have hlen : (a :: c).length = M.k + 1 := by simp [hc]
    rw [← hlen, preArgs_cons] at h
    refine (M.initB_length (f [x]) a c hc h w hw).trans ?_
    have h1 : (f [x]).length + a.length ≤ (p + Polynomial.X).eval (x.length + a.length) := by
      have := (hp x).trans (Polynomial.eval_mono_nat p (Nat.le_add_right x.length a.length))
      simp only [Polynomial.eval_add, Polynomial.eval_X]
      omega
    simpa using Polynomial.eval_mono_nat M.bound h1
  stepB_length := by
    intro x a c' c hc' hc h w hw
    have hlen : (a :: (c' ++ c)).length = M.k + M.k + 1 := by simp [hc, hc']
    rw [← hlen, preArgs_cons] at h
    refine (M.stepB_length (f [x]) a c' c hc' hc h w hw).trans ?_
    have h1 : (f [x]).length + a.length ≤ (p + Polynomial.X).eval (x.length + a.length) := by
      have := (hp x).trans (Polynomial.eval_mono_nat p (Nat.le_add_right x.length a.length))
      simp only [Polynomial.eval_add, Polynomial.eval_X]
      omega
    simpa using Polynomial.eval_mono_nat M.bound h1

variable {M f p}

section PreLemmas

variable (hf : Cobham f) (hp : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length)

theorem pre_test1 (t : Args → Bool) (x a : List Bool) {c : Args} (hc : c.length = M.k) :
    t (preArgs f (M.k + 1) (x :: a :: c)) = t (f [x] :: a :: c) := by
  have hlen : (a :: c).length = M.k + 1 := by simp [hc]
  rw [← hlen, preArgs_cons]

theorem pre_test2 (t : Args → Bool) (x a : List Bool) {c c' : Args} (hc : c.length = M.k)
    (hc' : c'.length = M.k) :
    t (preArgs f (M.k + M.k + 1) (x :: a :: (c' ++ c))) = t (f [x] :: a :: (c' ++ c)) := by
  have hlen : (a :: (c' ++ c)).length = M.k + M.k + 1 := by simp [hc, hc']
  rw [← hlen, preArgs_cons]

theorem pre_acc_iff (x a : List Bool) (c : Args) :
    (M.pre f p hf hp).Acc x a c ↔ M.Acc (f [x]) a c := by
  constructor
  · intro h
    induction h with
    | acc hc hacc =>
      exact Acc.acc hc (by rw [← pre_test1 (M := M) M.accB x a hc]; exact hacc)
    | univ hc hu _ ih =>
      refine Acc.univ hc (by rw [← pre_test1 (M := M) M.univB x a hc]; exact hu) fun c' hc' hs => ?_
      exact ih c' hc' (by
        show M.stepB _ = true
        rw [pre_test2 (M := M) M.stepB x a hc hc']; exact hs)
    | ex hc hu hc' hs _ ih =>
      refine Acc.ex hc (by rw [← pre_test1 (M := M) M.univB x a hc]; exact hu) hc' ?_ ih
      rw [← pre_test2 (M := M) M.stepB x a hc hc']; exact hs
  · intro h
    induction h with
    | acc hc hacc =>
      exact Acc.acc hc (by show M.accB _ = true; rw [pre_test1 (M := M) M.accB x a hc]; exact hacc)
    | univ hc hu _ ih =>
      refine Acc.univ hc (by show M.univB _ = true; rw [pre_test1 (M := M) M.univB x a hc]; exact hu)
        fun c' hc' hs => ih c' hc' ?_
      have hs' : M.stepB (preArgs f (M.k + M.k + 1) (x :: a :: (c' ++ _))) = true := hs
      rw [pre_test2 (M := M) M.stepB x a hc hc'] at hs'
      exact hs'
    | ex hc hu hc' hs _ ih =>
      refine Acc.ex hc (by show M.univB _ = false; rw [pre_test1 (M := M) M.univB x a hc]; exact hu)
        hc' ?_ ih
      show M.stepB _ = true
      rw [pre_test2 (M := M) M.stepB x a hc hc']; exact hs

/-- **The pre-processed machine accepts `x` exactly when the original one accepts `f [x]`.** -/
theorem accepts_pre (x a : List Bool) :
    (M.pre f p hf hp).Accepts x a ↔ M.Accepts (f [x]) a := by
  constructor
  · rintro ⟨c, hc, hinit, hacc⟩
    refine ⟨c, hc, ?_, (pre_acc_iff hf hp x a c).1 hacc⟩
    have h : M.initB (preArgs f (M.k + 1) (x :: a :: c)) = true := hinit
    rwa [pre_test1 (M := M) M.initB x a hc] at h
  · rintro ⟨c, hc, hinit, hacc⟩
    refine ⟨c, hc, ?_, (pre_acc_iff hf hp x a c).2 hacc⟩
    show M.initB _ = true
    rw [pre_test1 (M := M) M.initB x a hc]
    exact hinit

end PreLemmas

end AltSpace

/-- **A machine reached through a polynomial-time pre-processing of the word, with advice
depending on the length of the word only, puts the language into `EXPTIME/poly`.** -/
theorem inAltSpacePoly_of_precomp {L : List Bool → Prop} (M : AltSpace)
    {F : List Bool → List Bool} (hF : PolyTimeFun F) (adv : ℕ → List Bool) (r : Polynomial ℕ)
    (hadv : ∀ n, (adv n).length ≤ r.eval n)
    (h : ∀ w, L w ↔ M.Accepts (F w) (adv w.length)) : InAltSpacePoly L := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  obtain ⟨p, hp⟩ := hf.poly_length
  have hp' : ∀ y : List Bool, (f [y]).length ≤ p.eval y.length := by
    intro y
    simpa [argSize_cons] using hp [y]
  refine ⟨M.pre f p hf hp', adv, r, hadv, fun w => ?_⟩
  rw [AltSpace.accepts_pre, ← hFf w]
  exact h w

end Space

end HTN
