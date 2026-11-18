import ComplexityTheory.Collapse.Verify
import ComplexityTheory.Collapse.Layer
/-!
# The formula a polynomial-space machine evaluates to eliminate the advice

Fix an alternating machine `M` and a predicate `q` which, with the right advice, decides the
configuration questions of `M`.  The decider of `ComplexityTheory/Collapse/Collapse.lean`
evaluates, on input `x`,

    ∃ a,  "the table  c, t ↦ q (code of (c,t,x), decC a)  is consistent"
            ∧  q (code of (initial configuration, 1…1, x), decC a)

— an existential quantifier over the candidate advice strings, inside it two universal
quantifiers over the configurations and the counters, and inside those one more quantifier over
the successors of a configuration.  This file builds that formula layer by layer and proves that
it is a predicate of the polynomial-space class whenever `q` is: each layer is stated in the
explicit "reads its first `k` arguments" form that `ComplexityTheory/Collapse/Layer.lean`
needs, so that quantifying and substituting the template alternate without bookkeeping in the
proofs.

The meaning of the formula — that it decides the language of `M` — is
`ComplexityTheory/Collapse/Collapse.lean`.
-/

namespace HTN

namespace PSpace

open PTime

namespace ASpace

variable (M : ASpace) (q : Args → Bool)

/-! ### Reading the claimed table off the advice -/

/-- The value the advice `a` claims for "the configuration `c` accepts within `t` rounds on
`x`". -/
def claim (x a c t : List Bool) : Bool := q [encS (ones (M.w x)) c t x, decC a]

variable {M q}

theorem cobham_onesW {f : Fn} (hf : Cobham f) : Cobham (fun args => ones (M.w (f args))) :=
  (cobham_c1 cobham_onesLenFn (cobham_c1 M.cobham_widthF hf)).of_eq' fun args => by
    simp [compFn, onesLenFn_apply, ASpace.w]

theorem cobham_onesW1 {f : Fn} (hf : Cobham f) :
    Cobham (fun args => ones (M.w (f args) + 1)) :=
  (cobham_c1 cobham_onesLenFn
    (cobham_c1 (Cobham.cons false) (cobham_c1 M.cobham_widthF hf))).of_eq' fun args => by
    simp [compFn, onesLenFn_apply, consFn, ASpace.w]

theorem cobham_zerosW1 {f : Fn} (hf : Cobham f) :
    Cobham (fun args => zeros (M.w (f args) + 1)) :=
  (cobham_c1 cobham_zerosFn
    (cobham_c1 (Cobham.cons false) (cobham_c1 M.cobham_widthF hf))).of_eq' fun args => by
    simp [compFn, zerosFn_apply, consFn, ASpace.w]

theorem cobham_encQ {fc ft fx : Fn} (hc : Cobham fc) (ht : Cobham ft) (hx : Cobham fx) :
    Cobham (fun args => encS (ones (M.w (fx args))) (fc args) (ft args) (fx args)) :=
  cobham_encS (cobham_onesW hx) hc ht hx

theorem psClaim (hq : PSpaceB q) {fx fa fc ft : Fn} (hx : Cobham fx) (ha : Cobham fa)
    (hc : Cobham fc) (ht : Cobham ft) :
    PSpaceB (fun args => claim M q (fx args) (fa args) (fc args) (ft args)) :=
  PSpaceB.comp2 hq (PSpaceF.cobham (cobham_encQ hc ht hx))
    (PSpaceF.cobham (cobham_decC ha))

theorem psIte {b p r : Args → Bool} (hb : PSpaceB b) (hp : PSpaceB p) (hr : PSpaceB r) :
    PSpaceB (fun args => if b args = true then p args else r args) :=
  ((hb.and hp).or (hb.not.and hr)).of_eq fun args => by
    cases hb' : b args <;> simp

variable (M q)

/-! ### Layer 0: the body of the quantifier over the successors

The argument list is `[c', c, t', a, x]`. -/

/-- The body of the universal quantifier over the successors of `c`. -/
def allBody : Args → Bool := fun args =>
  !M.stepB [args.getD 0 [], args.getD 1 [], args.getD 4 []] ||
    claim M q (args.getD 4 []) (args.getD 3 []) (args.getD 0 []) (args.getD 2 [])

/-- The body of the existential quantifier over the successors of `c`. -/
def exBody : Args → Bool := fun args =>
  M.stepB [args.getD 0 [], args.getD 1 [], args.getD 4 []] &&
    claim M q (args.getD 4 []) (args.getD 3 []) (args.getD 0 []) (args.getD 2 [])

variable {M q}

theorem psAllBody (hq : PSpaceB q) : PSpaceB (allBody M q) :=
  ((PSpaceB.of_cobhamB (M.cobhamB_stepB.comp3 (Cobham.proj 0) (Cobham.proj 1)
    (Cobham.proj 4))).not.or
      (psClaim (M := M) hq (Cobham.proj 4) (Cobham.proj 3) (Cobham.proj 0) (Cobham.proj 2))).of_eq
    fun _ => rfl

theorem psExBody (hq : PSpaceB q) : PSpaceB (exBody M q) :=
  ((PSpaceB.of_cobhamB (M.cobhamB_stepB.comp3 (Cobham.proj 0) (Cobham.proj 1)
    (Cobham.proj 4))).and
      (psClaim (M := M) hq (Cobham.proj 4) (Cobham.proj 3) (Cobham.proj 0) (Cobham.proj 2))).of_eq
    fun _ => rfl

theorem argDep_allBody : ArgDep 5 (allBody M q) := by
  intro args
  simp only [allBody, claim, getD_padArgs (by omega : (0:ℕ) < 5),
    getD_padArgs (by omega : (1:ℕ) < 5), getD_padArgs (by omega : (2:ℕ) < 5),
    getD_padArgs (by omega : (3:ℕ) < 5), getD_padArgs (by omega : (4:ℕ) < 5)]

theorem argDep_exBody : ArgDep 5 (exBody M q) := by
  intro args
  simp only [exBody, claim, getD_padArgs (by omega : (0:ℕ) < 5),
    getD_padArgs (by omega : (1:ℕ) < 5), getD_padArgs (by omega : (2:ℕ) < 5),
    getD_padArgs (by omega : (3:ℕ) < 5), getD_padArgs (by omega : (4:ℕ) < 5)]

variable (M q)

/-! ### Layer 1: the quantifiers over the successors

The argument list is `[c, t', a, x]`. -/

/-- All the successors of `c` accept, according to the claimed table. -/
def allQ : Args → Bool := fun args =>
  allLenB (M.w (args.getD 3 [])) (fun c' => allBody M q (c' :: args))

/-- Some successor of `c` accepts, according to the claimed table. -/
def exQ : Args → Bool := fun args =>
  anyLen (M.w (args.getD 3 [])) (fun c' => exBody M q (c' :: args))

variable {M q}

theorem psAllQ (hq : PSpaceB q) : PSpaceB (allQ M q) := by
  have h := psSubstFirst (n := 4) (psBigAnd (psAllBody (M := M) hq) (argDep_allBody (M := M) (q := q)))
    (argDep_bigAnd (argDep_allBody (M := M) (q := q)))
    (f := compFn M.widthF [proj 3]) (PSpaceF.cobham (cobham_c1 M.cobham_widthF (Cobham.proj 3)))
  refine h.of_eq fun args => ?_
  simp only [allQ, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w]

theorem psExQ (hq : PSpaceB q) : PSpaceB (exQ M q) := by
  have h := psSubstFirst (n := 4) (psBigOr (psExBody (M := M) hq) (argDep_exBody (M := M) (q := q)))
    (argDep_bigOr (argDep_exBody (M := M) (q := q)))
    (f := compFn M.widthF [proj 3]) (PSpaceF.cobham (cobham_c1 M.cobham_widthF (Cobham.proj 3)))
  refine h.of_eq fun args => ?_
  simp only [exQ, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w]

theorem argDep_allQ : ArgDep 4 (allQ M q) := by
  have h := argDep_substFirst (n := 4) (argDep_bigAnd (P := allBody M q) argDep_allBody)
    (f := compFn M.widthF [proj 3]) (fnDep_comp (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      exact fnDep_proj (by omega)))
  intro args
  have h1 := h args
  simpa only [allQ, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w] using h1

theorem argDep_exQ : ArgDep 4 (exQ M q) := by
  have h := argDep_substFirst (n := 4) (argDep_bigOr (P := exBody M q) argDep_exBody)
    (f := compFn M.widthF [proj 3]) (fnDep_comp (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      exact fnDep_proj (by omega)))
  intro args
  have h1 := h args
  simpa only [exQ, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w] using h1

variable (M q)

/-! ### Layer 2: the local check at one configuration and one counter

The argument list is `[c, t', a, x]`. -/

/-- The two local equations, checked at the configuration `c` and the counter `t'`. -/
def chkCT : Args → Bool := fun args =>
  (!decide (args.getD 1 [] = zeros (M.w (args.getD 3 []) + 1)) ||
      (claim M q (args.getD 3 []) (args.getD 2 []) (args.getD 0 [])
        (zeros (M.w (args.getD 3 []) + 1)) == M.accB [args.getD 0 [], args.getD 3 []])) &&
  (decide (args.getD 1 [] = ones (M.w (args.getD 3 []) + 1)) ||
      (claim M q (args.getD 3 []) (args.getD 2 []) (args.getD 0 []) (succB (args.getD 1 [])) ==
        (M.accB [args.getD 0 [], args.getD 3 []] ||
          (if M.univB [args.getD 0 [], args.getD 3 []] = true then allQ M q args
            else exQ M q args))))

variable {M q}

theorem psChkCT (hq : PSpaceB q) : PSpaceB (chkCT M q) := by
  have hzero : PSpaceB (fun args : Args =>
      decide (args.getD 1 [] = zeros (M.w (args.getD 3 []) + 1))) :=
    PSpaceB.of_cobhamB ((cobhamB_eqStr (Cobham.proj 1) (cobham_zerosW1 (M := M) (Cobham.proj 3))).of_eq
      fun args => by simp [proj])
  have hone : PSpaceB (fun args : Args =>
      decide (args.getD 1 [] = ones (M.w (args.getD 3 []) + 1))) :=
    PSpaceB.of_cobhamB ((cobhamB_eqStr (Cobham.proj 1) (cobham_onesW1 (M := M) (Cobham.proj 3))).of_eq
      fun args => by simp [proj])
  have hacc : PSpaceB (fun args : Args => M.accB [args.getD 0 [], args.getD 3 []]) :=
    PSpaceB.of_cobhamB ((M.cobhamB_accB.comp2 (Cobham.proj 0) (Cobham.proj 3)).of_eq
      fun args => by simp [proj])
  have huniv : PSpaceB (fun args : Args => M.univB [args.getD 0 [], args.getD 3 []]) :=
    PSpaceB.of_cobhamB ((M.cobhamB_univB.comp2 (Cobham.proj 0) (Cobham.proj 3)).of_eq
      fun args => by simp [proj])
  have hclaim0 : PSpaceB (fun args : Args => claim M q (args.getD 3 []) (args.getD 2 [])
      (args.getD 0 []) (zeros (M.w (args.getD 3 []) + 1))) :=
    psClaim hq (Cobham.proj 3) (Cobham.proj 2) (Cobham.proj 0) (cobham_zerosW1 (M := M) (Cobham.proj 3))
  have hclaim1 : PSpaceB (fun args : Args => claim M q (args.getD 3 []) (args.getD 2 [])
      (args.getD 0 []) (succB (args.getD 1 []))) :=
    psClaim hq (Cobham.proj 3) (Cobham.proj 2) (Cobham.proj 0)
      ((cobham_c1 cobham_succFn (Cobham.proj 1)).of_eq' fun args => by
        simp [compFn, succFn_apply, proj])
  exact ((hzero.not.or (hclaim0.op2 hacc (· == ·))).and
    (hone.or (hclaim1.op2 (hacc.or (psIte huniv (psAllQ hq) (psExQ hq))) (· == ·)))).of_eq
      fun args => rfl

theorem argDep_chkCT : ArgDep 4 (chkCT M q) := by
  intro args
  have h1 := argDep_allQ (M := M) (q := q) args
  have h2 := argDep_exQ (M := M) (q := q) args
  simp only [chkCT, claim, getD_padArgs (by omega : (0:ℕ) < 4),
    getD_padArgs (by omega : (1:ℕ) < 4), getD_padArgs (by omega : (2:ℕ) < 4),
    getD_padArgs (by omega : (3:ℕ) < 4), ← h1, ← h2]

variable (M q)

/-! ### Layer 3: all configurations

The argument list is `[t', a, x]`. -/

/-- The local check, at every configuration. -/
def chkT : Args → Bool := fun args =>
  allLenB (M.w (args.getD 2 [])) (fun c => chkCT M q (c :: args))

variable {M q}

theorem psChkT (hq : PSpaceB q) : PSpaceB (chkT M q) := by
  have h := psSubstFirst (n := 3) (psBigAnd (psChkCT (M := M) hq) (argDep_chkCT (M := M) (q := q)))
    (argDep_bigAnd (argDep_chkCT (M := M) (q := q)))
    (f := compFn M.widthF [proj 2]) (PSpaceF.cobham (cobham_c1 M.cobham_widthF (Cobham.proj 2)))
  refine h.of_eq fun args => ?_
  simp only [chkT, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w]

theorem argDep_chkT : ArgDep 3 (chkT M q) := by
  have h := argDep_substFirst (n := 3) (argDep_bigAnd (P := chkCT M q) argDep_chkCT)
    (f := compFn M.widthF [proj 2]) (fnDep_comp (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      exact fnDep_proj (by omega)))
  intro args
  have h1 := h args
  simpa only [chkT, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, ASpace.w] using h1

variable (M q)

/-! ### Layer 4: all counters

The argument list is `[a, x]`. -/

/-- **The advice `a` is consistent**: the local check passes at every counter and every
configuration. -/
def consistentB : Args → Bool := fun args =>
  allLenB (M.w (args.getD 1 []) + 1) (fun t' => chkT M q (t' :: args))

variable {M q}

theorem psConsistentB (hq : PSpaceB q) : PSpaceB (consistentB M q) := by
  have hf : Cobham (compFn (consFn false) [compFn M.widthF [proj 1]]) :=
    cobham_c1 (Cobham.cons false) (cobham_c1 M.cobham_widthF (Cobham.proj 1))
  have h := psSubstFirst (n := 3) (psBigAnd (psChkT (M := M) hq) (argDep_chkT (M := M) (q := q))) (argDep_bigAnd (argDep_chkT (M := M) (q := q)))
    (f := compFn (consFn false) [compFn M.widthF [proj 1]]) (PSpaceF.cobham hf)
  refine h.of_eq fun args => ?_
  simp only [consistentB, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, consFn, List.length_cons, ASpace.w]

theorem argDep_consistentB : ArgDep 2 (consistentB M q) := by
  have h := argDep_substFirst (n := 2) (argDep_bigAnd (P := chkT M q) argDep_chkT)
    (f := compFn (consFn false) [compFn M.widthF [proj 1]]) (fnDep_comp (by
      intro g hg
      rw [List.mem_singleton.1 hg]
      exact fnDep_comp (by
        intro g' hg'
        rw [List.mem_singleton.1 hg']
        exact fnDep_proj (by omega))))
  intro args
  have h1 := h args
  simpa only [consistentB, compFn, List.map_cons, List.map_nil, proj, List.getD_cons_zero,
    List.tail_cons, consFn, List.length_cons, ASpace.w] using h1

variable (M q)

/-! ### Layer 5: the search over the candidate advice

The argument list is `[a, x]` for the body and `[x]` for the answer. -/

/-- The body of the search: a consistent advice which claims that the initial configuration
accepts within the largest counter. -/
def searchB : Args → Bool := fun args =>
  consistentB M q args &&
    claim M q (args.getD 1 []) (args.getD 0 []) (M.initF [args.getD 1 []])
      (ones (M.w (args.getD 1 []) + 1))

/-- **The formula the decider evaluates**, with `padF` supplying the template of the candidate
advice strings. -/
def answerB (padF : Fn) : Args → Bool := fun args =>
  anyLen (padF args).length (fun a => searchB M q (a :: args))

variable {M q}

theorem psSearchB (hq : PSpaceB q) : PSpaceB (searchB M q) := by
  have hclaim : PSpaceB (fun args : Args => claim M q (args.getD 1 []) (args.getD 0 [])
      (M.initF [args.getD 1 []]) (ones (M.w (args.getD 1 []) + 1))) :=
    psClaim hq (Cobham.proj 1) (Cobham.proj 0)
      ((cobham_c1 M.cobham_initF (Cobham.proj 1)).of_eq' fun args => by simp [compFn, proj])
      (cobham_onesW1 (M := M) (Cobham.proj 1))
  exact ((psConsistentB hq).and hclaim).of_eq fun args => rfl

theorem argDep_searchB : ArgDep 2 (searchB M q) := by
  intro args
  have h1 := argDep_consistentB (M := M) (q := q) args
  simp only [searchB, claim, getD_padArgs (by omega : (0:ℕ) < 2),
    getD_padArgs (by omega : (1:ℕ) < 2), ← h1]

theorem psAnswerB (hq : PSpaceB q) {padF : Fn} (hpad : Cobham padF) :
    PSpaceB (answerB M q (compFn padF [proj 0])) := by
  have h := psSubstFirst (n := 1) (psBigOr (psSearchB (M := M) hq) (argDep_searchB (M := M) (q := q)))
    (argDep_bigOr (argDep_searchB (M := M) (q := q)))
    (f := compFn padF [proj 0]) (PSpaceF.cobham (cobham_c1 hpad (Cobham.proj 0)))
  refine h.of_eq fun args => ?_
  simp only [answerB, List.getD_cons_zero, List.tail_cons]

end ASpace

end PSpace

end HTN
