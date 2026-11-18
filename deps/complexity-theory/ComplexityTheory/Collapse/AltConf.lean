import ComplexityTheory.Collapse.Collapse
/-!
# The configuration questions of an alternating machine are again alternating

`ComplexityTheory/Collapse/Collapse.lean` eliminates the advice of a machine `M` provided the
hypothesis is available *for the language of configuration questions* of `M`
(`HTN.PSpace.ASpace.confLang`).  For the hypothesis "every language of the class has polynomial
advice" to apply there, the configuration questions must themselves be a language of the class.
That is what this file proves: from `M` it builds a second alternating machine `M.confMach`
whose language is `M.confLang`.

The construction is the obvious one.  On input `z` the machine decodes `z` as a triple
`(c, t, x)` — the configuration, the step counter and the input — and checks that `z` is exactly
the code of that triple (`HTN.PSpace.ASpace.wfB`); if it is not, the machine rejects.  Otherwise
its configurations are the pairs `c ++ t` of a configuration and a counter of `M` on `x`, it is
accepting, universal and existential exactly as `M` is at `c`, and a step decrements the counter
and takes a step of `M`; at the counter `0…0` there is no step and the configuration is
existential, so acceptance there is the acceptance test of `M`.  The whole point of the counter
is that the simulation terminates, and the statement of the simulation
(`HTN.PSpace.ASpace.accWithin_confMach`) is that after *any* number of rounds at least the value
of the counter the simulating machine has the answer of `M.accWithin` at that counter.

The consequence is the class-level form of the collapse,
`HTN.PSpace.inPSpace_of_inPSpacePoly`: if every language of alternating polynomial space has a
polynomial advice for polynomial space, then every language of alternating polynomial space is
in polynomial space — that is, `EXPTIME ⊆ PSPACE/poly` implies `EXPTIME ⊆ PSPACE`.
-/

namespace HTN

namespace PSpace

open PTime

/-! ### Quantifying over a concatenation -/

theorem allLenB_append (m n : ℕ) (f : List Bool → Bool) :
    allLenB (m + n) f = allLenB m (fun u => allLenB n (fun v => f (u ++ v))) := by
  rw [Bool.eq_iff_iff, allLenB_eq_true, allLenB_eq_true]
  constructor
  · intro h u hu
    rw [allLenB_eq_true]
    intro v hv
    exact h (u ++ v) (by simp [hu, hv])
  · intro h y hy
    have h1 := h (y.take m) (by simp; omega)
    rw [allLenB_eq_true] at h1
    have h2 := h1 (y.drop m) (by simp; omega)
    rwa [List.take_append_drop] at h2

theorem anyLen_append (m n : ℕ) (f : List Bool → Bool) :
    anyLen (m + n) f = anyLen m (fun u => anyLen n (fun v => f (u ++ v))) := by
  rw [Bool.eq_iff_iff, anyLen_eq_true, anyLen_eq_true]
  constructor
  · rintro ⟨y, hy, hfy⟩
    refine ⟨y.take m, by simp; omega, ?_⟩
    rw [anyLen_eq_true]
    exact ⟨y.drop m, by simp; omega, by rwa [List.take_append_drop]⟩
  · rintro ⟨u, hu, hu'⟩
    obtain ⟨v, hv, hfv⟩ := anyLen_eq_true.1 hu'
    exact ⟨u ++ v, by simp [hu, hv], hfv⟩

/-- A universal quantifier all of whose instances but one are true. -/
theorem allLenB_eq_of_unique {n : ℕ} {g : List Bool → Bool} {t₀ : List Bool}
    (h0 : t₀.length = n) (h : ∀ t, t.length = n → t ≠ t₀ → g t = true) :
    allLenB n g = g t₀ := by
  cases hg : g t₀ with
  | true =>
    rw [allLenB_eq_true]
    intro t ht
    by_cases h1 : t = t₀
    · rw [h1, hg]
    · exact h t ht h1
  | false =>
    rw [Bool.eq_false_iff]
    intro hcon
    have := allLenB_eq_true.1 hcon t₀ h0
    rw [hg] at this
    exact Bool.noConfusion this

/-- An existential quantifier all of whose instances but one are false. -/
theorem anyLen_eq_of_unique {n : ℕ} {g : List Bool → Bool} {t₀ : List Bool}
    (h0 : t₀.length = n) (h : ∀ t, t.length = n → t ≠ t₀ → g t = false) :
    anyLen n g = g t₀ := by
  cases hg : g t₀ with
  | true => exact anyLen_eq_true.2 ⟨t₀, h0, hg⟩
  | false =>
    rw [Bool.eq_false_iff]
    intro hcon
    obtain ⟨y, hy, hgy⟩ := anyLen_eq_true.1 hcon
    by_cases h1 : y = t₀
    · rw [h1, hg] at hgy; exact Bool.noConfusion hgy
    · rw [h y hy h1] at hgy; exact Bool.noConfusion hgy

theorem anyLen_const_false (n : ℕ) (g : List Bool → Bool) (h : ∀ t, t.length = n → g t = false) :
    anyLen n g = false := by
  rw [Bool.eq_false_iff]
  intro hcon
  obtain ⟨y, hy, hgy⟩ := anyLen_eq_true.1 hcon
  rw [h y hy] at hgy
  exact Bool.noConfusion hgy

/-! ### The binary successor is injective on the strings of a fixed length -/

theorem succB_inj_len {n : ℕ} {s t : List Bool} (hs : s.length = n) (ht : t.length = n)
    (h : succB s = succB t) : s = t := by
  have h1 : val (succB s) = val (succB t) := by rw [h]
  rw [val_succB, val_succB, hs, ht] at h1
  have hbs := val_lt_two_pow s
  have hbt := val_lt_two_pow t
  rw [hs] at hbs
  rw [ht] at hbt
  refine val_inj_of_length_eq _ _ (by rw [hs, ht]) ?_
  rcases Nat.lt_or_ge (val s + 1) (2 ^ n) with h2 | h2
  · rcases Nat.lt_or_ge (val t + 1) (2 ^ n) with h3 | h3
    · rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at h1; omega
    · have ht' : val t + 1 = 2 ^ n := by omega
      rw [Nat.mod_eq_of_lt h2, ht', Nat.mod_self] at h1
      omega
  · have hs' : val s + 1 = 2 ^ n := by omega
    rcases Nat.lt_or_ge (val t + 1) (2 ^ n) with h3 | h3
    · rw [Nat.mod_eq_of_lt h3, hs', Nat.mod_self] at h1
      omega
    · omega

/-- The predecessor of a nonzero counter. -/
theorem exists_pred_succB {n k : ℕ} {t : List Bool} (ht : t.length = n) (hval : val t = k + 1) :
    ∃ s : List Bool, s.length = n ∧ val s = k ∧ succB s = t := by
  have hb := val_lt_two_pow t
  rw [ht] at hb
  obtain ⟨s, hs, hvs⟩ := exists_val_eq n k (by omega)
  refine ⟨s, hs, hvs, ?_⟩
  refine val_inj_of_length_eq _ _ (by rw [length_succB, hs, ht]) ?_
  rw [val_succB, hs, hvs, Nat.mod_eq_of_lt (by omega), hval]

theorem eq_zeros_of_val_eq_zero {n : ℕ} {t : List Bool} (ht : t.length = n) (h : val t = 0) :
    t = zeros n :=
  val_inj_of_length_eq _ _ (by simp [ht]) (by rw [h, val_zeros])

namespace ASpace

variable (M : ASpace)

/-! ### The components of the simulating machine -/

/-- The template of the width of a configuration of `M`, read off the argument `i`, which is a
configuration question. -/
def cwid (i : ℕ) : Fn := fun args => M.widthF [decX (args.getD i [])]

/-- The configuration part of the argument `j`, a pair of a configuration and a counter. -/
def ctake (i j : ℕ) : Fn := fun args => (args.getD j []).take (M.cwid i args).length

/-- The counter part of the argument `j`. -/
def cdrop (i j : ℕ) : Fn := fun args => (args.getD j []).drop (M.cwid i args).length

variable {M}

theorem cobham_cwid (i : ℕ) : Cobham (M.cwid i) :=
  (cobham_c1 M.cobham_widthF (cobham_decX (Cobham.proj i))).of_eq' fun args => by
    simp [compFn, cwid, proj]

theorem cobham_ctake (i j : ℕ) : Cobham (M.ctake i j) :=
  cobham_take (cobham_cwid i) (Cobham.proj j)

theorem cobham_cdrop (i j : ℕ) : Cobham (M.cdrop i j) :=
  cobham_drop (cobham_cwid i) (Cobham.proj j)

theorem cwid_length (i : ℕ) (args : Args) :
    (M.cwid i args).length = M.w (decX (args.getD i [])) := rfl

/-- Two strings have the same length: a predicate of Cobham's class. -/
theorem cobhamB_eqLen {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB (fun args => decide ((a args).length = (b args).length)) := by
  refine (cobhamB_eqStr (cobham_c1 cobham_zerosFn ha) (cobham_c1 cobham_zerosFn hb)).of_eq
    fun args => ?_
  simp only [compFn, List.map_cons, List.map_nil, zerosFn_apply, List.getD_cons_zero]
  by_cases h : (a args).length = (b args).length
  · simp [h]
  · have : zeros (a args).length ≠ zeros (b args).length := by
      intro hcon
      exact h (by simpa using congrArg List.length hcon)
    simp [h, this]

theorem cobhamB_comp1 {p : Args → Bool} (hp : CobhamB p) {a : Fn} (ha : Cobham a) :
    CobhamB fun args => p [a args] :=
  (cobham_c1 hp ha).of_eq' fun args => by simp [compFn]

variable (M)

/-- **The well-formedness test**: the argument is exactly the code of the triple it decodes
to. -/
def wfB : Args → Bool := fun args =>
  decide (args.getD 0 [] = encS (ones (M.w (decX (args.getD 0 []))))
      (decC (args.getD 0 [])) (decT (args.getD 0 [])) (decX (args.getD 0 []))) &&
    decide ((decC (args.getD 0 [])).length = M.w (decX (args.getD 0 []))) &&
    decide ((decT (args.getD 0 [])).length = M.w (decX (args.getD 0 [])) + 1)

variable {M}

theorem cobhamB_wfB : CobhamB M.wfB := by
  have hx : Cobham (fun args : Args => decX (args.getD 0 [])) := cobham_decX (Cobham.proj 0)
  have hc : Cobham (fun args : Args => decC (args.getD 0 [])) := cobham_decC (Cobham.proj 0)
  have ht : Cobham (fun args : Args => decT (args.getD 0 [])) := cobham_decT (Cobham.proj 0)
  have h1 : CobhamB (fun args : Args => decide (args.getD 0 [] =
      encS (ones (M.w (decX (args.getD 0 [])))) (decC (args.getD 0 [])) (decT (args.getD 0 []))
        (decX (args.getD 0 [])))) :=
    cobhamB_eqStr (Cobham.proj 0) (cobham_encS (cobham_onesW (M := M) hx) hc ht hx)
  have h2 : CobhamB (fun args : Args =>
      decide ((decC (args.getD 0 [])).length = M.w (decX (args.getD 0 [])))) :=
    (cobhamB_eqLen hc (cobham_cwid (M := M) 0)).of_eq fun args => rfl
  have h3 : CobhamB (fun args : Args =>
      decide ((decT (args.getD 0 [])).length = M.w (decX (args.getD 0 [])) + 1)) := by
    refine (cobhamB_eqLen ht (cobham_c1 (Cobham.cons false) (cobham_cwid (M := M) 0))).of_eq
      fun args => ?_
    simp only [compFn, List.map_cons, List.map_nil, consFn, List.getD_cons_zero,
      List.length_cons, cwid, ASpace.w]
  exact ((h1.and h2).and h3).of_eq fun args => rfl

/-- The well-formedness test only reads the code. -/
theorem wfB_eq (z : List Bool) : M.wfB [z] =
    (decide (z = encS (ones (M.w (decX z))) (decC z) (decT z) (decX z)) &&
      decide ((decC z).length = M.w (decX z)) &&
      decide ((decT z).length = M.w (decX z) + 1)) := rfl

variable (M)

/-- The width of a configuration of the simulating machine: a configuration and a counter. -/
def confWidthF : Fn := fun args => M.cwid 0 args ++ M.cwid 0 args ++ [false]

/-- The initial configuration of the simulating machine: the decoded configuration and
counter, truncated to the right width so that the length is right even on a code that is not
well formed. -/
def confInitF : Fn := fun args =>
  (decC (args.getD 0 []) ++ decT (args.getD 0 []) ++ M.confWidthF args).take
    (M.confWidthF args).length

/-- The acceptance test of the simulating machine. -/
def confAccB : Args → Bool := fun args =>
  M.wfB [args.getD 1 []] && M.accB [M.ctake 1 0 args, decX (args.getD 1 [])]

/-- The classification test of the simulating machine: a configuration whose counter is `0…0`
is made existential, so that it has no successor and accepts exactly when `M` does. -/
def confUnivB : Args → Bool := fun args =>
  M.wfB [args.getD 1 []] &&
    !decide (M.cdrop 1 0 args = zeros ((M.cwid 1 args).length + 1)) &&
    M.univB [M.ctake 1 0 args, decX (args.getD 1 [])]

/-- The transition of the simulating machine: decrement the counter and take a step of `M`. -/
def confStepB : Args → Bool := fun args =>
  M.wfB [args.getD 2 []] &&
    !decide (M.cdrop 2 1 args = zeros ((M.cwid 2 args).length + 1)) &&
    decide (succB (M.cdrop 2 0 args) = M.cdrop 2 1 args) &&
    M.stepB [M.ctake 2 0 args, M.ctake 2 1 args, decX (args.getD 2 [])]

variable {M}

theorem cobham_confWidthF : Cobham M.confWidthF :=
  cobham_app2 (cobham_app2 (cobham_cwid (M := M) 0) (cobham_cwid (M := M) 0))
    (cobham_const [false])

theorem confWidthF_length (args : Args) :
    (M.confWidthF args).length = 2 * M.w (decX (args.getD 0 [])) + 1 := by
  simp only [confWidthF, List.length_append, List.length_singleton, cwid_length]
  omega

theorem cobham_confInitF : Cobham M.confInitF :=
  cobham_take cobham_confWidthF
    (cobham_app2 (cobham_app2 (cobham_decC (Cobham.proj 0)) (cobham_decT (Cobham.proj 0)))
      cobham_confWidthF)

theorem cobhamB_confAccB : CobhamB M.confAccB :=
  ((cobhamB_comp1 cobhamB_wfB (Cobham.proj 1)).and
    (M.cobhamB_accB.comp2 (cobham_ctake 1 0) (cobham_decX (Cobham.proj 1)))).of_eq fun _ => rfl

theorem cobhamB_confUnivB : CobhamB M.confUnivB := by
  have hz : Cobham (fun args : Args => zeros ((M.cwid 1 args).length + 1)) :=
    (cobham_c1 cobham_zerosFn (cobham_c1 (Cobham.cons false) (cobham_cwid (M := M) 1))).of_eq'
      fun args => by
        simp only [compFn, List.map_cons, List.map_nil, zerosFn_apply, consFn,
          List.getD_cons_zero, List.length_cons]
  exact (((cobhamB_comp1 cobhamB_wfB (Cobham.proj 1)).and
    (cobhamB_eqStr (cobham_cdrop 1 0) hz).not).and
      (M.cobhamB_univB.comp2 (cobham_ctake 1 0) (cobham_decX (Cobham.proj 1)))).of_eq fun _ => rfl

theorem cobhamB_confStepB : CobhamB M.confStepB := by
  have hz : Cobham (fun args : Args => zeros ((M.cwid 2 args).length + 1)) :=
    (cobham_c1 cobham_zerosFn (cobham_c1 (Cobham.cons false) (cobham_cwid (M := M) 2))).of_eq'
      fun args => by
        simp only [compFn, List.map_cons, List.map_nil, zerosFn_apply, consFn,
          List.getD_cons_zero, List.length_cons]
  have hsucc : Cobham (fun args : Args => succB (M.cdrop 2 0 args)) :=
    (cobham_c1 cobham_succFn (cobham_cdrop (M := M) 2 0)).of_eq' fun args => by
      simp [compFn, succFn_apply]
  exact ((((cobhamB_comp1 cobhamB_wfB (Cobham.proj 2)).and
    (cobhamB_eqStr (cobham_cdrop 2 1) hz).not).and
      (cobhamB_eqStr hsucc (cobham_cdrop 2 1))).and
        (M.cobhamB_stepB.comp3 (cobham_ctake 2 0) (cobham_ctake 2 1)
          (cobham_decX (Cobham.proj 2)))).of_eq fun _ => rfl

variable (M)

/-- **The machine deciding the configuration questions of `M`.** -/
def confMach : ASpace where
  widthF := M.confWidthF
  initF := M.confInitF
  accB := M.confAccB
  univB := M.confUnivB
  stepB := M.confStepB
  cobham_widthF := cobham_confWidthF
  cobham_initF := cobham_confInitF
  cobhamB_accB := cobhamB_confAccB
  cobhamB_univB := cobhamB_confUnivB
  cobhamB_stepB := cobhamB_confStepB
  initF_length := by
    intro z
    simp only [confInitF, List.length_take, List.length_append]
    omega

variable {M}

theorem confMach_w (z : List Bool) : M.confMach.w z = 2 * M.w (decX z) + 1 :=
  confWidthF_length (M := M) [z]

/-! ### The simulation -/

/-- On a code that is not well formed the simulating machine rejects. -/
theorem accWithin_confMach_of_not_wf {z : List Bool} (hz : M.wfB [z] = false) :
    ∀ (r : ℕ) (g : List Bool), M.confMach.accWithin z r g = false := by
  intro r
  induction r with
  | zero =>
    intro g
    rw [accWithin_zero]
    simp [confMach, confAccB, hz]
  | succ r ih =>
    intro g
    rw [accWithin_succ]
    have hacc : M.confMach.accB [g, z] = false := by simp [confMach, confAccB, hz]
    have huniv : M.confMach.univB [g, z] = false := by simp [confMach, confUnivB, hz]
    rw [hacc, if_neg (by rw [huniv]; exact Bool.noConfusion)]
    simp only [Bool.false_or]
    refine anyLen_const_false _ _ fun t _ => ?_
    have : M.confMach.stepB [t, g, z] = false := by simp [confMach, confStepB, hz]
    rw [this, Bool.false_and]

section wellFormed

variable {z : List Bool} (hz : M.wfB [z] = true)

include hz

theorem wf_length_decC : (decC z).length = M.w (decX z) := by
  rw [wfB_eq] at hz
  have := (Bool.and_eq_true_iff.1 hz).1
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 this).2

theorem wf_length_decT : (decT z).length = M.w (decX z) + 1 := by
  rw [wfB_eq] at hz
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 hz).2

theorem wf_code : z = encS (ones (M.w (decX z))) (decC z) (decT z) (decX z) := by
  rw [wfB_eq] at hz
  have := (Bool.and_eq_true_iff.1 hz).1
  exact of_decide_eq_true (Bool.and_eq_true_iff.1 this).1

/-- The acceptance test of the simulating machine on a pair. -/
theorem confMach_accB_append {c t : List Bool} (hc : c.length = M.w (decX z)) :
    M.confMach.accB [c ++ t, z] = M.accB [c, decX z] := by
  have h : (c ++ t).take (M.w (decX z)) = c := take_eq_of_length c t hc.symm
  simp only [confMach, confAccB, hz, Bool.true_and, ctake, cwid, List.getD_cons_zero,
    List.getD_cons_succ, ASpace.w] at *
  rw [h]

theorem confMach_univB_append {c t : List Bool} (hc : c.length = M.w (decX z)) :
    M.confMach.univB [c ++ t, z] =
      (!decide (t = zeros (M.w (decX z) + 1)) && M.univB [c, decX z]) := by
  have h : (c ++ t).take (M.w (decX z)) = c := take_eq_of_length c t hc.symm
  have h' : (c ++ t).drop (M.w (decX z)) = t := drop_eq_of_length c t hc.symm
  simp only [confMach, confUnivB, hz, Bool.true_and, ctake, cdrop, cwid,
    List.getD_cons_zero, List.getD_cons_succ, ASpace.w] at *
  rw [h, h']

theorem confMach_stepB_append {c' t' c t : List Bool} (hc' : c'.length = M.w (decX z))
    (hc : c.length = M.w (decX z)) :
    M.confMach.stepB [c' ++ t', c ++ t, z] =
      (!decide (t = zeros (M.w (decX z) + 1)) && decide (succB t' = t) &&
        M.stepB [c', c, decX z]) := by
  have h1 : (c' ++ t').take (M.w (decX z)) = c' := take_eq_of_length c' t' hc'.symm
  have h2 : (c' ++ t').drop (M.w (decX z)) = t' := drop_eq_of_length c' t' hc'.symm
  have h3 : (c ++ t).take (M.w (decX z)) = c := take_eq_of_length c t hc.symm
  have h4 : (c ++ t).drop (M.w (decX z)) = t := drop_eq_of_length c t hc.symm
  simp only [confMach, confStepB, hz, Bool.true_and, ctake, cdrop, cwid,
    List.getD_cons_zero, List.getD_cons_succ, ASpace.w] at *
  rw [h1, h2, h3, h4]

/-- **The simulation**: after at least as many rounds as the value of the counter, the
simulating machine has the answer of `M.accWithin` at that counter. -/
theorem accWithin_confMach : ∀ (r : ℕ) (c t : List Bool), c.length = M.w (decX z) →
    t.length = M.w (decX z) + 1 → val t ≤ r →
      M.confMach.accWithin z r (c ++ t) = M.accWithin (decX z) (val t) c := by
  intro r
  induction r with
  | zero =>
    intro c t hc ht hval
    have h0 : val t = 0 := Nat.le_zero.1 hval
    rw [accWithin_zero, h0, accWithin_zero, confMach_accB_append hz hc]
  | succ r ih =>
    intro c t hc ht hval
    rw [accWithin_succ, confMach_accB_append hz hc]
    rcases Nat.eq_zero_or_pos (val t) with h0 | hpos
    · -- the counter is zero: no successor, and the configuration is existential
      have htz : t = zeros (M.w (decX z) + 1) := eq_zeros_of_val_eq_zero ht h0
      have huniv : M.confMach.univB [c ++ t, z] = false := by
        rw [confMach_univB_append hz hc, htz]
        simp
      rw [if_neg (by rw [huniv]; exact Bool.noConfusion), h0, accWithin_zero]
      have hnone : anyLen (M.confMach.w z)
          (fun g => M.confMach.stepB [g, c ++ t, z] && M.confMach.accWithin z r g) = false := by
        refine anyLen_const_false _ _ fun g hg => ?_
        have hg1 : (g.take (M.w (decX z))).length = M.w (decX z) := by
          rw [List.length_take]
          rw [confMach_w] at hg
          omega
        have hsplit : g = g.take (M.w (decX z)) ++ g.drop (M.w (decX z)) :=
          (List.take_append_drop _ _).symm
        rw [hsplit, confMach_stepB_append hz hg1 hc, htz]
        simp
      rw [hnone]
      simp
    · -- the counter is positive: one round of the simulation
      obtain ⟨k, hk⟩ : ∃ k, val t = k + 1 := ⟨val t - 1, by omega⟩
      obtain ⟨s, hs, hvs, hsucc⟩ := exists_pred_succB ht hk
      have hkr : k ≤ r := by omega
      have htz : t ≠ zeros (M.w (decX z) + 1) := by
        intro hcon
        rw [hcon, val_zeros] at hk
        omega
      have huniv : M.confMach.univB [c ++ t, z] = M.univB [c, decX z] := by
        rw [confMach_univB_append hz hc]
        simp [htz]
      -- the body of the quantifier, after splitting the configuration into its two parts
      have hbodyAll : ∀ c' : List Bool, c'.length = M.w (decX z) →
          allLenB (M.w (decX z) + 1) (fun t' =>
              !M.confMach.stepB [c' ++ t', c ++ t, z] ||
                M.confMach.accWithin z r (c' ++ t')) =
            (!M.stepB [c', c, decX z] || M.accWithin (decX z) k c') := by
        intro c' hc'
        rw [allLenB_eq_of_unique hs ?_]
        · rw [confMach_stepB_append hz hc' hc, hsucc]
          simp only [htz, decide_false, Bool.not_false, Bool.true_and, decide_true,
            Bool.true_and]
          rw [ih c' s hc' hs (by omega), hvs]
        · intro t' ht' hne
          have : M.confMach.stepB [c' ++ t', c ++ t, z] = false := by
            rw [confMach_stepB_append hz hc' hc]
            have : succB t' ≠ t := by
              intro hcon
              exact hne (succB_inj_len ht' hs (by rw [hcon, hsucc]))
            simp [this]
          rw [this]
          simp
      have hbodyEx : ∀ c' : List Bool, c'.length = M.w (decX z) →
          anyLen (M.w (decX z) + 1) (fun t' =>
              M.confMach.stepB [c' ++ t', c ++ t, z] &&
                M.confMach.accWithin z r (c' ++ t')) =
            (M.stepB [c', c, decX z] && M.accWithin (decX z) k c') := by
        intro c' hc'
        rw [anyLen_eq_of_unique hs ?_]
        · rw [confMach_stepB_append hz hc' hc, hsucc]
          simp only [htz, decide_false, Bool.not_false, Bool.true_and, decide_true,
            Bool.true_and]
          rw [ih c' s hc' hs (by omega), hvs]
        · intro t' ht' hne
          have : M.confMach.stepB [c' ++ t', c ++ t, z] = false := by
            rw [confMach_stepB_append hz hc' hc]
            have : succB t' ≠ t := by
              intro hcon
              exact hne (succB_inj_len ht' hs (by rw [hcon, hsucc]))
            simp [this]
          rw [this]
          simp
      rw [huniv, hk, accWithin_succ]
      have hw : M.confMach.w z = M.w (decX z) + (M.w (decX z) + 1) := by
        rw [confMach_w]; omega
      by_cases hu : M.univB [c, decX z] = true
      · rw [if_pos hu, if_pos hu, hw, allLenB_append]
        refine congrArg _ (allLenB_congr fun c' hc' => hbodyAll c' hc')
      · rw [if_neg hu, if_neg hu, hw, anyLen_append]
        refine congrArg _ (anyLen_congr fun c' hc' => hbodyEx c' hc')

end wellFormed

/-- **The simulating machine decides the configuration questions of `M`.** -/
theorem confMach_L (z : List Bool) : M.confMach.L z ↔ M.confLang z := by
  by_cases hz : M.wfB [z] = true
  · have hc := wf_length_decC hz
    have ht := wf_length_decT hz
    have hcode := wf_code hz
    have hinit : M.confMach.initF [z] = decC z ++ decT z := by
      have hlen : (decC z ++ decT z).length = (M.confWidthF [z]).length := by
        rw [List.length_append, hc, ht, confWidthF_length]
        simp only [List.getD_cons_zero]
        omega
      show (decC ([z].getD 0 []) ++ decT ([z].getD 0 []) ++ M.confWidthF [z]).take
          (M.confWidthF [z]).length = decC z ++ decT z
      simp only [List.getD_cons_zero]
      rw [← hlen]
      exact take_eq_of_length _ _ rfl
    have hhor : val (decT z) ≤ M.confMach.horizon z := by
      have h1 := val_lt_two_pow (decT z)
      rw [ht] at h1
      have h2 : 2 ^ (M.w (decX z) + 1) ≤ 2 ^ (M.confMach.w z + 1) :=
        Nat.pow_le_pow_right (by omega) (by rw [confMach_w]; omega)
      have : 1 ≤ 2 ^ (M.confMach.w z + 1) := Nat.one_le_two_pow
      unfold ASpace.horizon
      omega
    rw [ASpace.L, hinit, accWithin_confMach hz _ (decC z) (decT z) hc ht hhor]
    constructor
    · intro h
      exact ⟨decX z, decC z, decT z, hc, ht, hcode, h⟩
    · rintro ⟨x, c, t, hc', ht', hzz, hacc⟩
      have := (M.confLang_encS hc' ht').2 hacc
      rw [← hzz] at this
      exact (M.confLang_encS hc ht).1 (by rwa [← hcode])
  · have hz' : M.wfB [z] = false := by
      cases h : M.wfB [z] with
      | true => exact absurd h hz
      | false => rfl
    constructor
    · intro h
      rw [ASpace.L, accWithin_confMach_of_not_wf hz'] at h
      exact absurd h Bool.noConfusion
    · rintro ⟨x, c, t, hc, ht, rfl, hacc⟩
      exfalso
      have hdc : decC (encS (ones (M.w x)) c t x) = c := decC_encS hc
      have hdt : decT (encS (ones (M.w x)) c t x) = t := decT_encS hc ht
      have hdx : decX (encS (ones (M.w x)) c t x) = x := decX_encS hc ht
      rw [wfB_eq, hdc, hdt, hdx, hc, ht] at hz'
      simp at hz'

end ASpace

/-- **The configuration questions of an alternating machine are an alternating language.** -/
theorem inAPSpace_confLang (M : ASpace) : InAPSpace M.confLang :=
  ⟨M.confMach, fun z => (ASpace.confMach_L z).symm⟩

/-- Membership in polynomial space only depends on the language. -/
theorem InPSpace.congr {L L' : List Bool → Prop} (h : InPSpace L) (hL : ∀ x, L' x ↔ L x) :
    InPSpace L' := by
  obtain ⟨p, hp, hpL⟩ := h
  exact ⟨p, hp, fun x => (hL x).trans (hpL x)⟩

/-- **`EXPTIME ⊆ PSPACE/poly` implies `EXPTIME ⊆ PSPACE`**: if every language of alternating
polynomial space is decided in polynomial space with a polynomial advice, then every language of
alternating polynomial space is decided in polynomial space with no advice at all. -/
theorem inPSpace_of_inPSpacePoly (hyp : ∀ L : List Bool → Prop, InAPSpace L → InPSpacePoly L)
    {L : List Bool → Prop} (hL : InAPSpace L) : InPSpace L := by
  obtain ⟨M, hM⟩ := hL
  exact (inPSpace_of_confLang M (hyp M.confLang (inAPSpace_confLang M))).congr hM

/-- **The hypothesis a Karp–Lipton cell needs follows from the separation alone.**  If some
language of alternating polynomial space is not in polynomial space — that is, if `EXPTIME` and
`PSPACE` are distinct, `PSPACE ⊆ EXPTIME` being the easy inclusion — then some language of
alternating polynomial space is not even in polynomial space with polynomial advice.  This is
the weakening of the hypothesis of the cells from `EXPTIME ⊄ PSPACE/poly` to `EXPTIME ≠
PSPACE`. -/
theorem exists_not_inPSpacePoly_of_exists_not_inPSpace
    (h : ∃ L : List Bool → Prop, InAPSpace L ∧ ¬ InPSpace L) :
    ∃ L : List Bool → Prop, InAPSpace L ∧ ¬ InPSpacePoly L := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨L, hL, hnot⟩ := h
  exact hnot (inPSpace_of_inPSpacePoly (fun L' hL' => hcon L' hL') hL)

end PSpace

end HTN
