import ComplexityTheory.Hierarchy.Scale
/-!
# One exponential up: padding as a map of scales

"The exponential hierarchy is the polynomial hierarchy one exponential up" is, made precise, a
statement about *padding*: with

    pad x = x ++ 0…0   (`2 ^ |x|` zeros)

a deterministic exponential-time computation on `x` is a polynomial-time computation on `pad x`,
and an exponentially long quantified string at input `x` is a polynomially long one at input
`pad x`.  A `HTN.Hier.Transfer` between two scales records exactly this correspondence, and the
theorems of this file are the consequences that do **not** depend on the base classes:

* `HTN.Hier.Transfer.sigmaLevel_iff` — level `k` of the upper hierarchy is level `k` of the lower
  one, on padded languages: `L ∈ Σ_k^EXP ↔ pad L ∈ Σ_k^P`;
* `HTN.Hier.Transfer.inAdvice_iff` — the same for the advice classes:
  `L ∈ EXPTIME/2^poly ↔ pad L ∈ P/poly`.  Note *which* advice class this is: the faithful lift of
  `P/poly` allows advice of length polynomial in `|pad x| = 2^{O(|x|)}`, that is **exponentially
  long** advice.  Polynomial advice at the exponential scale (`EXPTIME/poly`, the hypothesis in
  the compilability tables) is a strictly smaller advice regime; `HTN.Hier.inAdvice_mono` records
  that it is a sub-hypothesis;
* `HTN.Hier.Transfer.collapseAt` — **the symmetric result the question asks for**: a collapse of
  the lower hierarchy to level `k` transports to a collapse of the upper hierarchy to level `k`.
  With the Karp–Lipton theorem as the input, `NP ⊆ P/poly` gives `EXPH = Σ₂^EXP`
  (`HTN.Hier.Transfer.collapseAt_of_karpLipton`);
* `HTN.Hier.Transfer.adviceHyp_iff` — **and the systematic problem**: the hypothesis
  "every `Σ₁` language of the *upper* scale has advice" is equivalent to the hypothesis
  "every *padded* `Σ₁` language of the lower scale has advice".  It is the Karp–Lipton
  hypothesis restricted to the padded languages, and padding translates *upwards* only, so it
  does not give the Karp–Lipton hypothesis itself: there is no route from `NEXPTIME ⊆ EXPTIME/poly`
  back down to `NP ⊆ P/poly`.  What an argument at the upper scale has to do instead is to run
  the Karp–Lipton proof there, and that is where the genuine obstruction sits — see
  `KarpLipton.lean`.
-/

namespace HTN

namespace Hier

/-- The padded language: the image of `L` under `pad`. -/
def padLang (pad : Word → Word) (L : Lang) : Lang :=
  fun w => ∃ x, pad x = w ∧ L x

/-- The padded relation: `R` read on padded inputs, false off the range of `pad`. -/
def padRel (pad : Word → Word) (R : Rel) : Rel :=
  fun w ys => ∃ x, pad x = w ∧ R x ys

/-- **A map of scales by padding.**

`small` is the lower scale (`P`, polynomially long quantified strings and advice), `big` the
upper one (`EXPTIME`, exponentially long quantified strings and advice); `pad` is the padding
that turns an input of the upper scale into an input of the lower one.  The fields say that
padding is length-determined and injective, that the base class of the upper scale is the base
class of the lower one on padded inputs, that the lower base class can test membership in the
range of `pad`, and that the two string budgets correspond. -/
structure Transfer (small big : Scale) where
  /-- The padding map. -/
  pad : Word → Word
  /-- The length of a padded word, as a function of the length of the word. -/
  padLen : ℕ → ℕ
  /-- Padding is length-determined. -/
  pad_length : ∀ x, (pad x).length = padLen x.length
  /-- Padding is injective. -/
  pad_inj : Function.Injective pad
  /-- Distinct lengths stay distinct under padding. -/
  padLen_inj : Function.Injective padLen
  /-- The base class of the upper scale is the base class of the lower one, on padded inputs. -/
  base_iff : ∀ R, big.base R ↔ small.base (padRel pad R)
  /-- The lower base class can restrict a relation to the range of the padding. -/
  base_restrict : ∀ R, small.base R →
    small.base (fun w ys => (∃ x, pad x = w) ∧ R w ys)
  /-- The quantifier budgets correspond. -/
  Q_iff : ∀ n y, big.Q n y ↔ small.Q (padLen n) y
  /-- The advice budgets correspond. -/
  A_iff : ∀ n c, big.A n c ↔ small.A (padLen n) c

namespace Transfer

variable {small big : Scale} (T : Transfer small big)

theorem padRel_pad (R : Rel) (x : Word) (ys : List Word) :
    padRel T.pad R (T.pad x) ys ↔ R x ys := by
  constructor
  · rintro ⟨x', hx, hR⟩
    rwa [T.pad_inj hx] at hR
  · intro hR
    exact ⟨x, rfl, hR⟩

theorem padLang_pad (L : Lang) (x : Word) :
    padLang T.pad L (T.pad x) ↔ L x := by
  constructor
  · rintro ⟨x', hx, hL⟩
    rwa [T.pad_inj hx] at hL
  · intro hL
    exact ⟨x, rfl, hL⟩

/-- Two relations that agree on a fixed input word give the same quantifier prefix there: the
input word is not touched by the prefix. -/
theorem qpre_congr {s : Scale} {R₁ R₂ : Rel} {w : Word} (h : ∀ ys, R₁ w ys ↔ R₂ w ys) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word), qpre s R₁ k b w ys ↔ qpre s R₂ k b w ys := by
  intro k
  induction k with
  | zero => intro b ys; exact h ys.reverse
  | succ k ih =>
      intro b ys
      cases b with
      | false =>
          simp only [qpre_succ_false]
          exact forall_congr' fun y => imp_congr_right fun _ => ih true (y :: ys)
      | true =>
          simp only [qpre_succ_true]
          exact exists_congr fun y => and_congr_right fun _ => ih false (y :: ys)

/-- The quantifier prefix of the upper scale at `x` is the quantifier prefix of the lower scale
at `pad x`. -/
theorem qpre_pad (R : Rel) (x : Word) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word),
      qpre small (padRel T.pad R) k b (T.pad x) ys ↔ qpre big R k b x ys := by
  intro k
  induction k with
  | zero => intro b ys; exact T.padRel_pad R x ys.reverse
  | succ k ih =>
      intro b ys
      cases b with
      | false =>
          simp only [qpre_succ_false, T.pad_length x]
          constructor
          · intro h y hy
            exact (ih true (y :: ys)).1 (h y ((T.Q_iff x.length y).1 hy))
          · intro h y hy
            exact (ih true (y :: ys)).2 (h y ((T.Q_iff x.length y).2 hy))
      | true =>
          simp only [qpre_succ_true, T.pad_length x]
          constructor
          · rintro ⟨y, hy, h⟩
            exact ⟨y, (T.Q_iff x.length y).2 hy, (ih false (y :: ys)).1 h⟩
          · rintro ⟨y, hy, h⟩
            exact ⟨y, (T.Q_iff x.length y).1 hy, (ih false (y :: ys)).2 h⟩

/-- Off the range of the padding, a padded relation makes every quantifier prefix false — the
universal quantifiers are not vacuous, because the empty string is always admissible. -/
theorem qpre_not_of_not_mem_range (R : Rel) {w : Word} (hw : ¬ ∃ x, T.pad x = w) :
    ∀ (k : ℕ) (b : Bool) (ys : List Word), ¬ qpre small (padRel T.pad R) k b w ys := by
  intro k
  induction k with
  | zero =>
      intro b ys h
      exact hw ⟨h.choose, h.choose_spec.1⟩
  | succ k ih =>
      intro b ys
      cases b with
      | false =>
          intro h
          exact ih true ([] :: ys) (h [] (small.Q_nil w.length))
      | true =>
          rintro ⟨y, _, h⟩
          exact ih false (y :: ys) h

/-- **Level transfer.**  A language is at level `k` of the upper hierarchy exactly when its
padding is at level `k` of the lower one. -/
theorem sigmaLevel_iff (k : ℕ) (L : Lang) :
    SigmaLevel big k L ↔ SigmaLevel small k (padLang T.pad L) := by
  constructor
  · rintro ⟨R, hR, hL⟩
    refine ⟨padRel T.pad R, (T.base_iff R).1 hR, fun w => ?_⟩
    by_cases hw : ∃ x, T.pad x = w
    · obtain ⟨x, rfl⟩ := hw
      rw [T.padLang_pad L x, hL x, T.qpre_pad R x k true []]
    · constructor
      · rintro ⟨x, hx, -⟩
        exact absurd ⟨x, hx⟩ hw
      · intro h
        exact absurd h (T.qpre_not_of_not_mem_range R hw k true [])
  · rintro ⟨R', hR', hL⟩
    refine ⟨fun x ys => R' (T.pad x) ys, ?_, fun x => ?_⟩
    · refine (T.base_iff _).2 ?_
      have hEq : padRel T.pad (fun x ys => R' (T.pad x) ys)
          = fun w ys => (∃ x, T.pad x = w) ∧ R' w ys := by
        funext w ys
        apply propext
        constructor
        · rintro ⟨x, rfl, h⟩
          exact ⟨⟨x, rfl⟩, h⟩
        · rintro ⟨⟨x, rfl⟩, h⟩
          exact ⟨x, rfl, h⟩
      rw [hEq]
      exact T.base_restrict R' hR'
    · have hcongr : ∀ ys, padRel T.pad (fun x ys => R' (T.pad x) ys) (T.pad x) ys ↔ R' (T.pad x) ys :=
        fun ys => T.padRel_pad (fun x ys => R' (T.pad x) ys) x ys
      rw [← T.padLang_pad L x, hL (T.pad x),
        ← T.qpre_pad (fun x ys => R' (T.pad x) ys) x k true [],
        qpre_congr (s := small) hcongr k true []]

/-- **Advice transfer.**  A language is in the advice class of the upper scale exactly when its
padding is in the advice class of the lower one.  With `pad x = x 0^{2^{|x|}}` and the lower
advice budget polynomial, the upper advice budget is polynomial in `2^{|x|}`, i.e. exponential:
the faithful lift of `P/poly` is `EXPTIME/2^poly`, not `EXPTIME/poly`. -/
theorem inAdvice_iff (L : Lang) :
    InAdvice big L ↔ InAdvice small (padLang T.pad L) := by
  constructor
  · rintro ⟨a, ha, R, hR, hL⟩
    classical
    refine ⟨fun m => if h : ∃ n, T.padLen n = m then a h.choose else [], fun m => ?_,
      padRel T.pad R, (T.base_iff R).1 hR, fun w => ?_⟩
    · by_cases h : ∃ n, T.padLen n = m
      · simp only [dif_pos h]
        have := (T.A_iff h.choose (a h.choose)).1 (ha h.choose)
        rwa [h.choose_spec] at this
      · simp only [dif_neg h]
        exact small.A_nil m
    · by_cases hw : ∃ x, T.pad x = w
      · obtain ⟨x, rfl⟩ := hw
        have hex : ∃ n, T.padLen n = (T.pad x).length := ⟨x.length, (T.pad_length x).symm⟩
        have hchoose : hex.choose = x.length := by
          apply T.padLen_inj
          rw [hex.choose_spec, T.pad_length x]
        rw [T.padLang_pad L x, hL x, T.padRel_pad R x]
        simp only [dif_pos hex, hchoose]
      · constructor
        · rintro ⟨x, hx, -⟩
          exact absurd ⟨x, hx⟩ hw
        · rintro ⟨x, hx, -⟩
          exact absurd ⟨x, hx⟩ hw
  · rintro ⟨a', ha', R', hR', hL⟩
    refine ⟨fun n => a' (T.padLen n), fun n => (T.A_iff n _).2 (ha' _),
      fun x ys => R' (T.pad x) ys, ?_, fun x => ?_⟩
    · refine (T.base_iff _).2 ?_
      have hEq : padRel T.pad (fun x ys => R' (T.pad x) ys)
          = fun w ys => (∃ x, T.pad x = w) ∧ R' w ys := by
        funext w ys
        apply propext
        constructor
        · rintro ⟨x, rfl, h⟩
          exact ⟨⟨x, rfl⟩, h⟩
        · rintro ⟨⟨x, rfl⟩, h⟩
          exact ⟨x, rfl, h⟩
      rw [hEq]
      exact T.base_restrict R' hR'
    · rw [← T.padLang_pad L x, hL (T.pad x), T.pad_length x]

include T in
/-- **The symmetric collapse, one step.**  If the lower hierarchy collapses from level `k + 1` to
level `k`, so does the upper one. -/
theorem collapseStep (k : ℕ) (h : CollapseStep small k) : CollapseStep big k := by
  intro L hL
  exact (T.sigmaLevel_iff k L).2 (h _ ((T.sigmaLevel_iff (k + 1) L).1 hL))

include T in
/-- **The symmetric collapse.**  If the lower hierarchy collapses to level `k`, so does the upper
one.  At `k = 2` and with the two scales `P` and `EXPTIME`: if the polynomial hierarchy collapses
to `Σ₂^P`, the exponential hierarchy collapses to `Σ₂^EXP`. -/
theorem collapseAt (k : ℕ) (h : CollapseAt small k) : CollapseAt big k := by
  intro j L hL
  exact (T.sigmaLevel_iff k L).2 (h j _ ((T.sigmaLevel_iff j L).1 hL))

include T in
/-- **Downward separation.**  If the upper hierarchy does not collapse from level `k + 1` to
level `k`, neither does the lower one.  This is the contrapositive of `collapseStep`, and it is
the direction a cell of the compilability table can use: a separation proved one exponential up
is at least as hard as the corresponding separation downstairs. -/
theorem not_collapseStep_small (k : ℕ) (h : ¬ CollapseStep big k) : ¬ CollapseStep small k :=
  fun hs => h (T.collapseStep k hs)

include T in
/-- **The exponential Karp–Lipton collapse, from the classical hypothesis.**  Given the classical
Karp–Lipton theorem at the lower scale — "if every `Σ₁` language has advice then the hierarchy
collapses to level `2`" — the classical hypothesis `NP ⊆ P/poly` collapses the *exponential*
hierarchy to its second level as well.

This is the symmetric result: it is the same statement one exponential up, and its proof is
padding.  What it does **not** do is derive the collapse from the exponential-level hypothesis
`NEXPTIME ⊆ EXPTIME/poly`; for that see `adviceHyp_iff` and `KarpLipton.lean`. -/
theorem collapseAt_of_karpLipton
    (kl : (∀ L, SigmaLevel small 1 L → InAdvice small L) → CollapseAt small 2)
    (h : ∀ L, SigmaLevel small 1 L → InAdvice small L) : CollapseAt big 2 :=
  T.collapseAt 2 (kl h)

/-- **Why the hypothesis does not travel downwards.**  The advice hypothesis at the upper scale —
`NEXPTIME ⊆ EXPTIME/2^poly` — is exactly the Karp–Lipton hypothesis of the lower scale
*restricted to padded languages*.  Padding translates upwards, so this is a genuinely weaker
assumption than `NP ⊆ P/poly`, and the collapse of the lower hierarchy cannot be obtained from
it. -/
theorem adviceHyp_iff :
    (∀ L, SigmaLevel big 1 L → InAdvice big L) ↔
      (∀ L, SigmaLevel small 1 (padLang T.pad L) → InAdvice small (padLang T.pad L)) := by
  constructor
  · intro h L hL
    exact (T.inAdvice_iff L).1 (h L ((T.sigmaLevel_iff 1 L).2 hL))
  · intro h L hL
    exact (T.inAdvice_iff L).2 (h L ((T.sigmaLevel_iff 1 L).1 hL))

end Transfer

/-- Enlarging the advice budget (or the base class) only weakens the advice hypothesis: the
table's hypothesis `NEXPTIME ⊆ EXPTIME/poly` implies the faithful lift
`NEXPTIME ⊆ EXPTIME/2^poly` of the Karp–Lipton hypothesis. -/
theorem inAdvice_mono {s t : Scale} {L : Lang} (hbase : ∀ R, s.base R → t.base R)
    (hA : ∀ n c, s.A n c → t.A n c) (h : InAdvice s L) : InAdvice t L := by
  obtain ⟨a, ha, R, hR, hL⟩ := h
  exact ⟨a, fun n => hA n _ (ha n), R, hbase R hR, hL⟩

end Hier

end HTN
