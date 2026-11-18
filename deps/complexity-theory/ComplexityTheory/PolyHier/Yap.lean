import ComplexityTheory.PolyHier.Pack
/-!
# Yap's theorem: `coNP ⊆ NP/poly` collapses the polynomial hierarchy to its third level

`HTN.PH.CoNPInNPPoly` is the hypothesis "*every `coNP` predicate is in `NP/poly`*", stated with
parameters: for every predicate `p` of Cobham's class, the universal statement
`∀ w, |w| ≤ q(|x|) → p(x, y₁, …, yₘ, w)` about an input `x` and parameters `yᵢ` of length at most
`q(|x|)` is equivalent to an existential statement `∃ v, |v| ≤ r(|x|) ∧ V(α(|x|), x, y₁, …, yₘ, v)`
with a predicate `V` of Cobham's class and an advice string `α(|x|)` of polynomial length that
depends on `|x|` only.

`HTN.PH.phCollapsesTo_three_of_coNPInNPPoly` is **Yap's theorem** (1983): under this hypothesis
`Π₃ᵖ ⊆ Σ₃ᵖ`, i.e. the polynomial hierarchy collapses to its third level.  The proof guesses the
advice existentially, and checks it *universally* for soundness only: an advice string `a` is
*sound* if every certificate it accepts is a genuine certificate of the universal statement.
Soundness is a `Π₁` condition and merges with the universal block; completeness is not needed for
the guessed advice, only for the true one.
-/

namespace HTN

namespace PH

open PTime PSpace

/-- **`coNP ⊆ NP/poly`, with parameters.**  For every predicate `p` of Cobham's class, every
polynomial `q` and every number `m` of parameters, there are a predicate `V` of Cobham's class, a
polynomial `r` and advice strings `α n` with `|α n| ≤ r(n)` such that for every input `x` and
parameters `y₁, …, yₘ` of length at most `q(|x|)`:
`(∀ w, |w| ≤ q(|x|) → p(x, y₁, …, yₘ, w)) ↔ ∃ v, |v| ≤ r(|x|) ∧ V(α(|x|), x, y₁, …, yₘ, v)`. -/
def CoNPInNPPoly : Prop :=
  ∀ (p : Args → Bool) (q : Polynomial ℕ) (m : ℕ), CobhamB p →
    ∃ (V : Args → Bool) (r : Polynomial ℕ) (α : ℕ → List Bool), CobhamB V ∧
      (∀ n, (α n).length ≤ r.eval n) ∧
      ∀ (x : List Bool) (ys : List (List Bool)), ys.length = m →
        (∀ y ∈ ys, y.length ≤ q.eval x.length) →
        ((∀ w : List Bool, w.length ≤ q.eval x.length → p (x :: (ys ++ [w])) = true) ↔
          ∃ v : List Bool, v.length ≤ r.eval x.length ∧
            V (α x.length :: x :: (ys ++ [v])) = true)

/-- A predicate of the class applied to a list of computed arguments. -/
theorem cobhamB_compL {p : Args → Bool} (hp : CobhamB p) {fs : List Fn}
    (hfs : ∀ f ∈ fs, Cobham f) : CobhamB fun args => p (fs.map fun f => f args) :=
  (Cobham.comp hp hfs).of_eq' fun args => by simp [compFn]

/-- The matrix of the `Σ₃` formula of Yap's theorem, on the arguments `[x, a, t, s]`: the advice
`a` is sound on the tuple packed in `t` (after the first component), and it certifies the tuple
formed by the first component of `t` and the tuple packed in `s`. -/
def yapP (V p : Args → Bool) (q r : Polynomial ℕ) (args : Args) : Bool :=
  (!V [args.getD 1 [], args.getD 0 [],
        (pfst (psnd (args.getD 2 []))).take (q.eval (args.getD 0 []).length),
        (pfst (psnd (psnd (args.getD 2 [])))).take (q.eval (args.getD 0 []).length),
        (pfst (psnd (psnd (psnd (args.getD 2 []))))).take (r.eval (args.getD 0 []).length)] ||
    !p [args.getD 0 [],
        (pfst (psnd (args.getD 2 []))).take (q.eval (args.getD 0 []).length),
        (pfst (psnd (psnd (args.getD 2 [])))).take (q.eval (args.getD 0 []).length),
        (psnd (psnd (psnd (psnd (args.getD 2 []))))).take (q.eval (args.getD 0 []).length)]) &&
  V [args.getD 1 [], args.getD 0 [],
      (pfst (args.getD 2 [])).take (q.eval (args.getD 0 []).length),
      (pfst (args.getD 3 [])).take (q.eval (args.getD 0 []).length),
      (psnd (args.getD 3 [])).take (r.eval (args.getD 0 []).length)]

theorem cobhamB_yapP {V p : Args → Bool} (hV : CobhamB V) (hp : CobhamB p) (q r : Polynomial ℕ) :
    CobhamB (yapP V p q r) := by
  have hx := Cobham.proj 0
  have ha := Cobham.proj 1
  have ht := Cobham.proj 2
  have hs := Cobham.proj 3
  have tq : ∀ {f : Fn}, Cobham f → Cobham fun args => (f args).take (q.eval (proj 0 args).length) :=
    fun hf => cobham_truncPoly q hx hf
  have tr : ∀ {f : Fn}, Cobham f → Cobham fun args => (f args).take (r.eval (proj 0 args).length) :=
    fun hf => cobham_truncPoly r hx hf
  have h1 := cobhamB_compL hV (fs := [proj 1, proj 0,
      fun args => (pfst (psnd (proj 2 args))).take (q.eval (proj 0 args).length),
      fun args => (pfst (psnd (psnd (proj 2 args)))).take (q.eval (proj 0 args).length),
      fun args => (pfst (psnd (psnd (psnd (proj 2 args))))).take (r.eval (proj 0 args).length)])
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      · exact ha
      · exact hx
      · exact tq (cobham_pfst (cobham_psnd ht))
      · exact tq (cobham_pfst (cobham_psnd (cobham_psnd ht)))
      · exact tr (cobham_pfst (cobham_psnd (cobham_psnd (cobham_psnd ht)))))
  have h2 := cobhamB_compL hp (fs := [proj 0,
      fun args => (pfst (psnd (proj 2 args))).take (q.eval (proj 0 args).length),
      fun args => (pfst (psnd (psnd (proj 2 args)))).take (q.eval (proj 0 args).length),
      fun args => (psnd (psnd (psnd (psnd (proj 2 args))))).take (q.eval (proj 0 args).length)])
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact hx
      · exact tq (cobham_pfst (cobham_psnd ht))
      · exact tq (cobham_pfst (cobham_psnd (cobham_psnd ht)))
      · exact tq (cobham_psnd (cobham_psnd (cobham_psnd (cobham_psnd ht)))))
  have h3 := cobhamB_compL hV (fs := [proj 1, proj 0,
      fun args => (pfst (proj 2 args)).take (q.eval (proj 0 args).length),
      fun args => (pfst (proj 3 args)).take (q.eval (proj 0 args).length),
      fun args => (psnd (proj 3 args)).take (r.eval (proj 0 args).length)])
    (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl
      · exact ha
      · exact hx
      · exact tq (cobham_pfst ht)
      · exact tq (cobham_pfst hs)
      · exact tr (cobham_psnd hs))
  exact ((h1.not.or h2.not).and h3).of_eq fun args => by simp [yapP, proj]

theorem take_of_length_le {u : List Bool} {B : ℕ} (h : u.length ≤ B) : u.take B = u :=
  List.take_of_length_le h

/-- **Yap's theorem.**  If every `coNP` predicate is in `NP/poly` (with parameters), then
`Π₃ᵖ ⊆ Σ₃ᵖ`: the polynomial hierarchy collapses to its third level. -/
theorem phCollapsesTo_three_of_coNPInNPPoly (H : CoNPInNPPoly) : PHCollapsesTo 3 := by
  rintro L ⟨p, q, hp, hL⟩
  obtain ⟨V, r, α, hV, hα, hH⟩ := H (fun args => !p args) q 2 hp.not
  refine ⟨yapP V p q r, 10 * (q + r) + 10, cobhamB_yapP hV hp q r, fun x => ?_⟩
  set n := x.length with hn
  set B := q.eval n with hB
  set R := r.eval n with hR
  have hQ : (10 * (q + r) + 10 : Polynomial ℕ).eval n = 10 * (B + R) + 10 := by
    simp [hB, hR]
  rw [hQ]
  -- the `Π₃` form of `L`
  have hLx : L x ↔ ∀ y : List Bool, y.length ≤ B → ∃ z : List Bool, z.length ≤ B ∧
      ∀ w : List Bool, w.length ≤ B → p [x, y, z, w] = false := by
    have h := hL x
    simp only [qblock_succ_true, qblock_succ_false, qblock_zero, List.nil_append,
      List.cons_append] at h
    constructor
    · intro hx y hy
      by_contra hcon
      push_neg at hcon
      refine (h.2 ⟨y, hy, fun z hz => ?_⟩) hx
      obtain ⟨w, hw, hpw⟩ := hcon z hz
      exact ⟨w, hw, by simpa using hpw⟩
    · intro hall
      by_contra hx
      obtain ⟨y, hy, hyz⟩ := h.1 hx
      obtain ⟨z, hz, hzw⟩ := hall y hy
      obtain ⟨w, hw, hpw⟩ := hyz z hz
      have := hzw w hw
      simp [this] at hpw
  -- the hypothesis, specialised
  have hH' : ∀ y z : List Bool, y.length ≤ B → z.length ≤ B →
      ((∀ w : List Bool, w.length ≤ B → p [x, y, z, w] = false) ↔
        ∃ v : List Bool, v.length ≤ R ∧ V [α n, x, y, z, v] = true) := by
    intro y z hy hz
    have h := hH x [y, z] rfl (by simp [hy, hz, ← hB, ← hn])
    simp only [List.cons_append, List.nil_append, Bool.not_eq_true'] at h
    exact h
  simp only [qblock_succ_true, qblock_succ_false, qblock_zero, List.nil_append,
    List.cons_append]
  constructor
  · intro hx
    refine ⟨α n, le_trans (hα n) (by omega), fun t _ => ?_⟩
    set y := (pfst t).take B with hy
    have hyl : y.length ≤ B := List.length_take_le _ _
    obtain ⟨z, hz, hzw⟩ := (hLx.1 hx) y hyl
    obtain ⟨v, hv, hVv⟩ := (hH' y z hyl hz).1 hzw
    refine ⟨pk z v, by simp; omega, ?_⟩
    simp only [yapP, List.getD_cons_zero, List.getD_cons_succ, pfst_pk, psnd_pk, ← hn, ← hB,
      ← hR, take_of_length_le hz, take_of_length_le hv, ← hy, hVv, Bool.and_true]
    set y' := (pfst (psnd t)).take B
    set z' := (pfst (psnd (psnd t))).take B
    set v' := (pfst (psnd (psnd (psnd t)))).take R
    set w' := (psnd (psnd (psnd (psnd t)))).take B
    cases hV' : V [α n, x, y', z', v']
    · simp
    · have hall := (hH' y' z' (List.length_take_le _ _) (List.length_take_le _ _)).2
        ⟨v', List.length_take_le _ _, hV'⟩
      simp [hall w' (List.length_take_le _ _)]
  · rintro ⟨a, -, hall⟩
    apply hLx.2
    intro y hy
    obtain ⟨s, -, hs⟩ := hall (pk y (pk [] (pk [] (pk [] [])))) (by simp; omega)
    simp only [yapP, List.getD_cons_zero, List.getD_cons_succ, pfst_pk, psnd_pk, ← hn, ← hB,
      ← hR, take_of_length_le hy, Bool.and_eq_true] at hs
    set z := (pfst s).take B with hz
    set v := (psnd s).take R with hv
    have hzl : z.length ≤ B := List.length_take_le _ _
    have hvl : v.length ≤ R := List.length_take_le _ _
    refine ⟨z, hzl, fun w hw => ?_⟩
    obtain ⟨s', -, hs'⟩ := hall (pk y (pk y (pk z (pk v w)))) (by simp; omega)
    simp only [yapP, List.getD_cons_zero, List.getD_cons_succ, pfst_pk, psnd_pk, ← hn, ← hB,
      ← hR, take_of_length_le hy, take_of_length_le hzl, take_of_length_le hvl,
      take_of_length_le hw, hs.2, Bool.and_eq_true, Bool.not_true, Bool.false_or,
      Bool.not_eq_true'] at hs'
    exact hs'.1

end PH

end HTN
