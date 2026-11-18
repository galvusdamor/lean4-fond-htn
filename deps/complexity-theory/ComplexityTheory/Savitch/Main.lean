import ComplexityTheory.Savitch.Loop
import ComplexityTheory.Collapse.Layer
/-!
# Savitch's theorem: the target bridge of cells 1 and 2 of Table 3

This file assembles the pieces of `ComplexityTheory/Savitch/` into

    HTN.Savitch.inPSpacePoly_of_inNSpacePoly :
      HTN.Space.InNSpacePoly L → HTN.PSpace.InPSpacePoly L,

that is, **Savitch's theorem with advice**: a language a *nondeterministic* polynomial-space
machine accepts with polynomial advice is decided by a *deterministic* polynomial-space predicate
with the same advice.  It is the target bridge `HTN.Space.SavitchAdvice` that cells 1 and 2 of
Table 3 carry (`HtnCompilability/Space/Table3Sep.lean`).

## The formula

On input `x` with advice `a` the deterministic predicate evaluates

    ∃ e₀ of width E,  ∃ e of width E,
      `e₀` decodes to an initial configuration  ∧  `e` decodes to an accepting one
      ∧  the depth-first search, run for `2 ^ ((E + 3) * (E + 1) + 1) - 1` steps from the call
         `(e₀, e)` at level `E`, returns `true`.

The width `E` is twice a polynomial bound `W` on the length of a configuration; the templates
recording `W`, `E`, the width `frW E` of a frame, the height `E * frW E` of a full stack and the
counter are computed from `x` and `a` by functions of Cobham's class, which is how the
polynomial-space class gets hold of the numerical parameters.  The two quantifiers are the
existential quantification over strings of the length of a computed template
(`HTN.PSpace.psBigOr` and `HTN.PSpace.psSubstFirst`); the search itself is the bounded
exponential iteration of the class.
-/

namespace HTN

namespace Savitch

open PTime PSpace Space

/-! ### The templates -/

section Templates

variable (f0 px pa : Fn)

/-- The template recording the width `W` of a configuration. -/
def twF : Fn := fun args => f0 [px args ++ pa args]

/-- The template recording the width `E = 2 * W` of a node. -/
def teF : Fn := fun args => twF f0 px pa args ++ twF f0 px pa args

/-- The template recording the width `frW E` of a frame. -/
def tfF : Fn := fun args =>
  [false, false] ++ (teF f0 px pa args ++ (teF f0 px pa args ++ teF f0 px pa args))

/-- The template recording the height `E * frW E` of a full stack. -/
def tkfF : Fn := fun args => smashFn [teF f0 px pa args, tfF f0 px pa args]

/-- The length of the counter: `(E + 3) * (E + 1) + 1`. -/
def tcpreF : Fn := fun args =>
  smashFn [teF f0 px pa args ++ [false, false, false], teF f0 px pa args ++ [false]] ++ [false]

/-- The counter of the iteration: that many ones. -/
def tcF : Fn := fun args => ones (tcpreF f0 px pa args).length

variable {f0 px pa}

theorem length_teF (args : Args) :
    (teF f0 px pa args).length = 2 * (twF f0 px pa args).length := by
  simp only [teF, List.length_append]; ring

theorem length_tfF (args : Args) :
    (tfF f0 px pa args).length = frW (teF f0 px pa args).length := by
  simp only [tfF, frW, List.length_append, List.length_cons, List.length_nil]; ring

theorem length_tkfF (args : Args) :
    (tkfF f0 px pa args).length
      = (teF f0 px pa args).length * frW (teF f0 px pa args).length := by
  simp only [tkfF, smashFn, List.length_replicate, List.getD_cons_zero, List.getD_cons_succ,
    length_tfF]

theorem length_tcF (args : Args) :
    (tcF f0 px pa args).length
      = ((teF f0 px pa args).length + 3) * ((teF f0 px pa args).length + 1) + 1 := by
  simp only [tcF, length_ones, tcpreF, smashFn, List.length_append, List.length_replicate,
    List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.length_nil]

theorem cobham_twF (hf0 : Cobham f0) (hx : Cobham px) (ha : Cobham pa) :
    Cobham (twF f0 px pa) :=
  (cobham_c1 hf0 (cobham_app2 hx ha)).of_eq' fun args => by simp [compFn, twF]

theorem cobham_teF (hf0 : Cobham f0) (hx : Cobham px) (ha : Cobham pa) :
    Cobham (teF f0 px pa) :=
  cobham_app2 (cobham_twF hf0 hx ha) (cobham_twF hf0 hx ha)

theorem cobham_tfF (hf0 : Cobham f0) (hx : Cobham px) (ha : Cobham pa) :
    Cobham (tfF f0 px pa) :=
  cobham_app2 (cobham_const [false, false])
    (cobham_app2 (cobham_teF hf0 hx ha)
      (cobham_app2 (cobham_teF hf0 hx ha) (cobham_teF hf0 hx ha)))

theorem cobham_tkfF (hf0 : Cobham f0) (hx : Cobham px) (ha : Cobham pa) :
    Cobham (tkfF f0 px pa) :=
  (cobham_c2 Cobham.smash (cobham_teF hf0 hx ha) (cobham_tfF hf0 hx ha)).of_eq' fun args => by
    simp [compFn, tkfF]

theorem cobham_tcF (hf0 : Cobham f0) (hx : Cobham px) (ha : Cobham pa) :
    Cobham (tcF f0 px pa) := by
  have hpre : Cobham (tcpreF f0 px pa) :=
    cobham_app2 (cobham_c2 Cobham.smash
      (cobham_app2 (cobham_teF hf0 hx ha) (cobham_const [false, false, false]))
      (cobham_app2 (cobham_teF hf0 hx ha) (cobham_const [false]))
      |>.of_eq' fun args => by simp [compFn]) (cobham_const [false])
  exact (cobham_c1 cobham_onesLenFn hpre).of_eq' fun args => by
    simp [compFn, onesLenFn_apply, tcF]

theorem fnDep_twF {n : ℕ} (hx : FnDep n px) (ha : FnDep n pa) : FnDep n (twF f0 px pa) := by
  intro args
  simp only [twF, hx args, ha args]

theorem fnDep_teF {n : ℕ} (hx : FnDep n px) (ha : FnDep n pa) : FnDep n (teF f0 px pa) := by
  intro args
  simp only [teF, fnDep_twF (f0 := f0) hx ha args]

end Templates

/-! ### The body: the two decoded tests and the search -/

variable (M : NSpace) (f0 : Fn)

/-- The state the search starts in: the call of the recursion on the pair `(e₀, e)`. -/
def st0F : Fn := fun args =>
  callSt (teF f0 (proj 2) (proj 3) args).length (args.getD 1 []) (args.getD 0 []) []

/-- **The body of the two quantifiers**, on the argument list `[e, e₀, x, a]`. -/
def qBody : Args → Bool := fun args =>
  (M.initB [dec (twF f0 (proj 2) (proj 3) args).length (args.getD 1 []),
      args.getD 2 [], args.getD 3 []] &&
    M.accB [dec (twF f0 (proj 2) (proj 3) args).length (args.getD 0 []),
      args.getD 2 [], args.getD 3 []]) &&
  ((loopFn (svStepFn M) [tcF f0 (proj 2) (proj 3) args, st0F f0 args,
      twF f0 (proj 2) (proj 3) args, teF f0 (proj 2) (proj 3) args,
      tfF f0 (proj 2) (proj 3) args, tkfF f0 (proj 2) (proj 3) args,
      args.getD 2 [], args.getD 3 []]).drop 1).headD false

variable {M f0}

theorem cobham_st0F (hf0 : Cobham f0) : Cobham (st0F f0) := by
  have hte : Cobham (teF f0 (proj 2) (proj 3)) :=
    cobham_teF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have hz : Cobham (fun args : Args => zeros (teF f0 (proj 2) (proj 3) args).length) :=
    (cobham_c1 cobham_zerosFn hte).of_eq' fun args => by simp [compFn, zerosFn_apply]
  exact cobham_app2 (cobham_const [false, false])
    (cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 (cobham_const [false, false])
      (Cobham.proj 1)) (Cobham.proj 0)) hz) (cobham_const []))

theorem psQBody (hf0 : Cobham f0) : PSpaceB (qBody M f0) := by
  have htw : Cobham (twF f0 (proj 2) (proj 3)) :=
    cobham_twF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have hte : Cobham (teF f0 (proj 2) (proj 3)) :=
    cobham_teF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have htf : Cobham (tfF f0 (proj 2) (proj 3)) :=
    cobham_tfF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have htkf : Cobham (tkfF f0 (proj 2) (proj 3)) :=
    cobham_tkfF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have htc : Cobham (tcF f0 (proj 2) (proj 3)) :=
    cobham_tcF hf0 (Cobham.proj 2) (Cobham.proj 3)
  have hinit : PSpaceB (fun args : Args =>
      M.initB [dec (twF f0 (proj 2) (proj 3) args).length (args.getD 1 []),
        args.getD 2 [], args.getD 3 []]) :=
    PSpaceB.of_cobhamB ((M.cobham_initB.comp3 (cobham_decOf htw (Cobham.proj 1))
      (Cobham.proj 2) (Cobham.proj 3)).of_eq fun args => by simp [proj])
  have hacc : PSpaceB (fun args : Args =>
      M.accB [dec (twF f0 (proj 2) (proj 3) args).length (args.getD 0 []),
        args.getD 2 [], args.getD 3 []]) :=
    PSpaceB.of_cobhamB ((M.cobham_accB.comp3 (cobham_decOf htw (Cobham.proj 0))
      (Cobham.proj 2) (Cobham.proj 3)).of_eq fun args => by simp [proj])
  have hloop : PSpaceF (fun args : Args =>
      loopFn (svStepFn M) [tcF f0 (proj 2) (proj 3) args, st0F f0 args,
        twF f0 (proj 2) (proj 3) args, teF f0 (proj 2) (proj 3) args,
        tfF f0 (proj 2) (proj 3) args, tkfF f0 (proj 2) (proj 3) args,
        args.getD 2 [], args.getD 3 []]) := by
    refine PSpaceF.of_eq (PSpaceF.comp (psSvLoop M)
      (hs := [tcF f0 (proj 2) (proj 3), st0F f0, twF f0 (proj 2) (proj 3),
        teF f0 (proj 2) (proj 3), tfF f0 (proj 2) (proj 3), tkfF f0 (proj 2) (proj 3),
        proj 2, proj 3]) ?_) (fun args => by simp [compFn, proj])
    intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact PSpaceF.cobham htc
    · exact PSpaceF.cobham (cobham_st0F hf0)
    · exact PSpaceF.cobham htw
    · exact PSpaceF.cobham hte
    · exact PSpaceF.cobham htf
    · exact PSpaceF.cobham htkf
    · exact psProj 2
    · exact psProj 3
  have hbit : PSpaceB (fun args : Args =>
      ((loopFn (svStepFn M) [tcF f0 (proj 2) (proj 3) args, st0F f0 args,
        twF f0 (proj 2) (proj 3) args, teF f0 (proj 2) (proj 3) args,
        tfF f0 (proj 2) (proj 3) args, tkfF f0 (proj 2) (proj 3) args,
        args.getD 2 [], args.getD 3 []]).drop 1).headD false) := by
    refine psHead (PSpaceF.of_eq (psC2 (PSpaceF.cobham cobham_dropFn)
      (PSpaceF.cobham (cobham_const [false])) hloop) fun args => ?_)
    simp [compFn, dropFn_apply]
  exact (hinit.and hacc).and hbit

theorem argDep_qBody : ArgDep 4 (qBody M f0) := by
  intro args
  simp only [qBody, st0F, twF, teF, tfF, tkfF, tcF, tcpreF, proj,
    getD_padArgs (by omega : (0 : ℕ) < 4), getD_padArgs (by omega : (1 : ℕ) < 4),
    getD_padArgs (by omega : (2 : ℕ) < 4), getD_padArgs (by omega : (3 : ℕ) < 4)]

/-! ### The two quantifiers -/

variable (M f0)

/-- The inner quantifier, over the accepting node; the argument list is `[e₀, x, a]`. -/
def qEx1 : Args → Bool := fun args =>
  anyLen (teF f0 (proj 1) (proj 2) args).length (fun y => qBody M f0 (y :: args))

/-- The outer quantifier, over the initial node; the argument list is `[x, a]`. -/
def qEx2 : Args → Bool := fun args =>
  anyLen (teF f0 (proj 0) (proj 1) args).length (fun y => qEx1 M f0 (y :: args))

variable {M f0}

theorem psQEx1 (hf0 : Cobham f0) : PSpaceB (qEx1 M f0) := by
  have h := psSubstFirst (n := 3) (psBigOr (psQBody (M := M) hf0) argDep_qBody)
    (argDep_bigOr (argDep_qBody (M := M) (f0 := f0)))
    (f := teF f0 (proj 1) (proj 2))
    (PSpaceF.cobham (cobham_teF hf0 (Cobham.proj 1) (Cobham.proj 2)))
  refine h.of_eq fun args => ?_
  simp only [qEx1, List.getD_cons_zero, List.tail_cons]

theorem argDep_qEx1 : ArgDep 3 (qEx1 M f0) := by
  have h := argDep_substFirst (n := 3) (argDep_bigOr (P := qBody M f0) argDep_qBody)
    (f := teF f0 (proj 1) (proj 2))
    (fnDep_teF (fnDep_proj (by omega)) (fnDep_proj (by omega)))
  intro args
  have h1 := h args
  simpa only [qEx1, List.getD_cons_zero, List.tail_cons] using h1

theorem psQEx2 (hf0 : Cobham f0) : PSpaceB (qEx2 M f0) := by
  have h := psSubstFirst (n := 2) (psBigOr (psQEx1 (M := M) hf0) argDep_qEx1)
    (argDep_bigOr (argDep_qEx1 (M := M) (f0 := f0)))
    (f := teF f0 (proj 0) (proj 1))
    (PSpaceF.cobham (cobham_teF hf0 (Cobham.proj 0) (Cobham.proj 1)))
  refine h.of_eq fun args => ?_
  simp only [qEx2, List.getD_cons_zero, List.tail_cons]

/-! ### What the body computes -/

theorem tcF_eq (f0 px pa : Fn) (args : Args) :
    tcF f0 px pa args
      = ones (((teF f0 px pa args).length + 3) * ((teF f0 px pa args).length + 1) + 1) := by
  simp only [tcF, tcpreF, smashFn, List.length_append, List.length_replicate,
    List.getD_cons_zero, List.getD_cons_succ, List.length_cons, List.length_nil]

/-- **The search returns the value of the recursion.**  On a well-formed argument list the last
conjunct of the body is `Rec`, the halving recursion, at the top level. -/
theorem loop_bit_eq (M : NSpace) {x a e₀ e tw te tf tkf tc : List Bool} {W : ℕ}
    (htw : tw.length = W) (htf : tf.length = frW te.length)
    (htkf : tkf.length = te.length * frW te.length)
    (htc : cost te.length te.length ≤ val tc)
    (he₀ : e₀.length = te.length) (he : e.length = te.length) :
    ((loopFn (svStepFn M) [tc, callSt te.length e₀ e [], tw, te, tf, tkf, x,
      a]).drop 1).headD false = Rec (stpM M x a W) te.length te.length e₀ e := by
  have hrun : loopFn (svStepFn M) [tc, callSt te.length e₀ e [], tw, te, tf, tkf, x, a]
      = run te.length tkf.length (stpM M x a W) (val tc) (callSt te.length e₀ e []) := by
    show loopAux (svStepFn M) [tw, te, tf, tkf, x, a] (val tc) (callSt te.length e₀ e []) = _
    rw [loopAux_eq_run M [tw, te, tf, tkf, x, a] (by simpa using htf)]
    simp only [List.getD_cons_zero, List.getD_cons_succ, htw]
  rw [hrun, htkf]
  obtain ⟨j, hj, hrec⟩ := dfs_correct (stp := stpM M x a W) (E := te.length) te.length
    te.length le_rfl e₀ e [] he₀ he (by simp [AtLevel])
  have hstop : ∀ n : ℕ, run te.length (te.length * frW te.length) (stpM M x a W) n
      (retSt (Rec (stpM M x a W) te.length te.length e₀ e) []) =
      retSt (Rec (stpM M x a W) te.length te.length e₀ e) [] :=
    fun n => run_halted _ _ _ (by simp [retSt]) n
  have hsplit : val tc = j + (val tc - j) := by
    have : j ≤ val tc := le_trans hj htc
    omega
  rw [hsplit, run_add, hrec, hstop]
  simp [retSt]

/-! ### The predicate decides the language -/

/-- The last conjunct of the body is the halving recursion. -/
theorem qBody_bit (M : NSpace) (f0 : Fn) (args : Args)
    (h0 : (args.getD 0 []).length = (teF f0 (proj 2) (proj 3) args).length)
    (h1 : (args.getD 1 []).length = (teF f0 (proj 2) (proj 3) args).length) :
    ((loopFn (svStepFn M) [tcF f0 (proj 2) (proj 3) args, st0F f0 args,
      twF f0 (proj 2) (proj 3) args, teF f0 (proj 2) (proj 3) args,
      tfF f0 (proj 2) (proj 3) args, tkfF f0 (proj 2) (proj 3) args,
      args.getD 2 [], args.getD 3 []]).drop 1).headD false
      = Rec (stpM M (args.getD 2 []) (args.getD 3 []) (twF f0 (proj 2) (proj 3) args).length)
          (teF f0 (proj 2) (proj 3) args).length (teF f0 (proj 2) (proj 3) args).length
          (args.getD 1 []) (args.getD 0 []) :=
  loop_bit_eq M rfl (length_tfF args) (length_tkfF args)
    (by rw [tcF_eq]; exact cost_le_val_ones _ _) h1 h0

theorem qBody_iff (M : NSpace) (f0 : Fn) (x a e₀ e : List Bool)
    (he₀ : e₀.length = 2 * (f0 [x ++ a]).length)
    (he : e.length = 2 * (f0 [x ++ a]).length) :
    qBody M f0 [e, e₀, x, a] = true ↔
      (M.initB [dec (f0 [x ++ a]).length e₀, x, a] = true ∧
        M.accB [dec (f0 [x ++ a]).length e, x, a] = true ∧
        Rec (stpM M x a (f0 [x ++ a]).length) (2 * (f0 [x ++ a]).length)
          (2 * (f0 [x ++ a]).length) e₀ e = true) := by
  have htw : twF f0 (proj 2) (proj 3) [e, e₀, x, a] = f0 [x ++ a] := rfl
  have hte : (teF f0 (proj 2) (proj 3) [e, e₀, x, a]).length = 2 * (f0 [x ++ a]).length := by
    rw [length_teF, htw]
  rw [qBody, qBody_bit M f0 [e, e₀, x, a] (by rw [hte]; exact he) (by rw [hte]; exact he₀)]
  simp only [List.getD_cons_zero, List.getD_cons_succ, htw, hte, Bool.and_eq_true, and_assoc]

theorem qEx2_iff (M : NSpace) {f0 : Fn}
    (hf0 : ∀ y : List Bool, M.bound.eval y.length ≤ (f0 [y]).length) (x a : List Bool) :
    qEx2 M f0 [x, a] = true ↔ M.Accepts x a := by
  set W := (f0 [x ++ a]).length with hW
  have hWb : M.bound.eval (x.length + a.length) ≤ W := by
    have h := hf0 (x ++ a)
    simpa using h
  have hlen0 : (teF f0 (proj 0) (proj 1) [x, a]).length = 2 * W := by
    rw [length_teF]; rfl
  have hlen1 : ∀ e₀ : List Bool, (teF f0 (proj 1) (proj 2) [e₀, x, a]).length = 2 * W := by
    intro e₀
    rw [length_teF]; rfl
  rw [qEx2, anyLen_eq_true, accepts_iff M x a hWb]
  constructor
  · rintro ⟨e₀, he₀, h⟩
    rw [hlen0] at he₀
    rw [qEx1, anyLen_eq_true] at h
    obtain ⟨e, he, hb⟩ := h
    rw [hlen1 e₀] at he
    obtain ⟨h1, h2, h3⟩ := (qBody_iff M f0 x a e₀ e he₀ he).1 hb
    exact ⟨e₀, e, he₀, he, h1, h2, h3⟩
  · rintro ⟨e₀, e, he₀, he, h1, h2, h3⟩
    refine ⟨e₀, by rw [hlen0]; exact he₀, ?_⟩
    rw [qEx1, anyLen_eq_true]
    exact ⟨e, by rw [hlen1 e₀]; exact he, (qBody_iff M f0 x a e₀ e he₀ he).2 ⟨h1, h2, h3⟩⟩

/-- **Savitch\'s theorem, with advice**: a language a nondeterministic polynomial-space machine
accepts with polynomial advice is decided by a deterministic polynomial-space predicate with the
same advice. -/
theorem inPSpacePoly_of_inNSpacePoly {L : List Bool → Prop} (h : InNSpacePoly L) :
    PSpace.InPSpacePoly L := by
  obtain ⟨M, adv, r, hadv, hL⟩ := h
  obtain ⟨f0, hf0c, hf0⟩ := exists_cobham_len_ge M.bound
  refine ⟨qEx2 M f0, adv, r, psQEx2 hf0c, hadv, fun x => ?_⟩
  rw [hL x, qEx2_iff M hf0]

end Savitch

end HTN
