import HtnComplexity.PT.List
/-!
# Bounded iteration in the polynomial-time calculus

* `HTN.Syn.PolyDom.PT.pb` — every polynomial-time function has output of size polynomial in the
  size of its input;
* `HTN.Syn.PolyDom.PT.iterate` — **iteration** of a polynomial-time step polynomially many times,
  provided the iterates stay of polynomial size;
* `HTN.Syn.PolyDom.PT.foldl` — **a left fold whose step adds at most a polynomial amount** to the
  size of the accumulator is polynomial time; `HTN.Syn.PolyDom.PT.foldr` likewise.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

variable {α β γ δ σ : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc σ]

/-! ### Sizes -/

/-- The size of a value: the length of its encoding. -/
def sz (a : α) : ℕ := (enc a).length

theorem sz_prod (a : α) (b : β) : sz (a, b) = sz a + sz b := by
  simp [sz, enc_prod]

theorem sz_cons (a : α) (l : List α) : sz (a :: l) = sz l + 2 * sz a + 2 := by
  simp only [sz, enc_cons, List.length_cons, List.length_append, length_bstr]
  ring

theorem sz_nil : sz ([] : List α) = 1 := rfl

theorem length_le_sz (l : List α) : l.length ≤ sz l := by
  induction l with
  | nil => simp [sz_nil]
  | cons a l ih => rw [sz_cons, List.length_cons]; omega

theorem sz_le_of_mem {a : α} {l : List α} (h : a ∈ l) : sz a ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem sz_drop_le (l : List α) (k : ℕ) : sz (l.drop k) ≤ sz l := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k => rw [List.drop_succ_cons, sz_cons]; have := ih k; omega

theorem sz_append_single (l : List α) (b : α) : sz (l ++ [b]) = sz l + 2 * sz b + 2 := by
  induction l with
  | nil => simp [sz_cons, sz_nil]
  | cons a l ih => simp only [List.cons_append, sz_cons, ih]; ring

/-! ### Polynomial bounds -/

/-- `b` is bounded by `d * (n + 1) ^ c`. -/
def PolyBd (b : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, b n ≤ d * (n + 1) ^ c

theorem polyBd_poly (p : Polynomial ℕ) : PolyBd fun n => p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨c₁, d₁, h₁⟩ := hp
    obtain ⟨c₂, d₂, h₂⟩ := hq
    refine ⟨c₁ + c₂, d₁ + d₂, fun n => ?_⟩
    have e1 : (n + 1) ^ c₁ ≤ (n + 1) ^ (c₁ + c₂) := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (n + 1) ^ c₂ ≤ (n + 1) ^ (c₁ + c₂) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Polynomial.eval_add]
    have := h₁ n; have := h₂ n
    nlinarith
  | monomial k a =>
    refine ⟨k, a, fun n => ?_⟩
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem pow_le_pow_add {n c c' : ℕ} (h : c ≤ c') : (n + 1) ^ c ≤ (n + 1) ^ c' :=
  Nat.pow_le_pow_right (by omega) h

/-- **Every polynomial-time function is polynomially bounded.** -/
theorem PT.pb {f : α → β} (hf : PT f) : ∃ c d : ℕ, ∀ a, sz (f a) ≤ d * (sz a + 1) ^ c := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨p, hp⟩ := hF.poly_length
  obtain ⟨c, d, hcd⟩ := polyBd_poly p
  refine ⟨c, d, fun a => ?_⟩
  have := hp [enc a]
  simp only [List.getD_cons_zero, hFf, argSize_cons, argSize_nil] at this
  rw [sz]
  refine this.trans ?_
  simpa [sz] using hcd (enc a).length

/-! ### Strings of polynomial length -/

theorem cobham_padPow (m e : ℕ) :
    Cobham fun args : Args => List.replicate (m * ((args.getD 0 []).length + 1) ^ e) false := by
  induction e with
  | zero => simpa using cobham_const (List.replicate m false)
  | succ e ih =>
    refine (PH.cobham_smash ih (cobham_consTrue cobham_var0)).of_eq' fun args => ?_
    simp [pow_succ, mul_assoc]

/-! ### Iteration -/

/-- The clamped step on codes. -/
def clampStep (S : List Bool → List Bool) (L : ℕ) (x c : List Bool) : List Bool :=
  (S (x ++ c)).take L

/-- **Iteration of a polynomial-time step**, `m * (|a| + 1) ^ e` times, provided all iterates are
of polynomial size. -/
theorem PT.iterate {init : α → σ} {step : α → σ → σ} (hi : PT init) (hs : PT₂ step)
    {c d : ℕ} (hb : ∀ a k, sz ((step a)^[k] (init a)) ≤ d * (sz a + 1) ^ c) (m e : ℕ) :
    PT fun a => (step a)^[m * (sz a + 1) ^ e] (init a) := by
  obtain ⟨I, hI, hIi⟩ := hi
  obtain ⟨S, hS, hSs⟩ := hs
  set L : List Bool → ℕ := fun x => d * (x.length + 1) ^ c with hL
  have hbd : Cobham fun args : Args => List.replicate (L (args.getD 0 [])) false :=
    cobham_padPow d c
  have hcnt : Cobham fun args : Args => List.replicate (m * ((args.getD 0 []).length + 1) ^ e) false :=
    cobham_padPow m e
  have hinit : Cobham fun args : Args => (I (args.getD 0 [])).take (L (args.getD 0 [])) :=
    (cobham_take hbd hI).of_eq' fun args => by simp
  have hstep : Cobham fun args : Args =>
      (S (args.tail.getD 0 [] ++ args.getD 0 [])).take (L (args.tail.getD 0 [])) :=
    (cobham_take (cobham_tailArgs hbd)
      (hS.app (PH.cobham_app (cobham_tailArgs cobham_var0) cobham_var0))).of_eq' fun args => by simp
  have key := cobham_iterateC hinit hstep hcnt hbd
    (fun args => by simp) (fun c args => by simp)
  refine ⟨fun x => (fun c => (S (x ++ c)).take (L x))^[m * (x.length + 1) ^ e]
    ((I x).take (L x)), key.of_eq' fun args => by simp, fun a => ?_⟩
  have hk : ∀ k, (fun c => (S (enc a ++ c)).take (L (enc a)))^[k] ((I (enc a)).take (L (enc a))) =
      enc ((step a)^[k] (init a)) := by
    intro k
    induction k with
    | zero =>
      simp only [Function.iterate_zero, id, hIi]
      exact List.take_of_length_le (by simpa [sz] using hb a 0)
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      have := hSs (a, (step a)^[k] (init a))
      simp only [enc_prod] at this
      rw [this]
      exact List.take_of_length_le (by
        have := hb a (k + 1)
        rw [Function.iterate_succ_apply'] at this
        simpa [sz] using this)
  simpa [sz] using hk (m * ((enc a).length + 1) ^ e)

/-! ### Folds -/

/-- The step of a left fold, on the pair (remaining list, accumulator). -/
def foldStep [Inhabited β] (g : σ → β → σ) (p : List β × σ) : List β × σ :=
  bif p.1.isEmpty then p else (p.1.tail, g p.2 p.1.headI)

theorem foldStep_iterate [Inhabited β] (g : σ → β → σ) :
    ∀ (k : ℕ) (l : List β) (s : σ),
      (foldStep g)^[k] (l, s) = (l.drop k, (l.take k).foldl g s) := by
  intro k
  induction k with
  | zero => intro l s; simp
  | succ k ih =>
    intro l s
    cases l with
    | nil =>
      rw [Function.iterate_succ_apply']
      rw [ih]; simp [foldStep]
    | cons b l =>
      rw [Function.iterate_succ_apply, show foldStep g (b :: l, s) = (l, g s b) from rfl, ih]
      simp

theorem PT.foldStep [Inhabited β] {g : α → σ → β → σ}
    (hg : PT fun q : α × σ × β => g q.1 q.2.1 q.2.2) :
    PT₂ fun (a : α) (p : List β × σ) => PolyDom.foldStep (g a) p := by
  unfold PT₂ PolyDom.foldStep
  refine PT.cond (PT.isEmpty (PT.fst.comp PT.snd)) PT.snd ?_
  refine PT.pair (PT.tail (PT.fst.comp PT.snd)) ?_
  exact hg.comp (PT.pair PT.fst (PT.pair (PT.snd.comp PT.snd) (PT.headI (PT.fst.comp PT.snd))))

/-- **A left fold all of whose intermediate accumulators are of polynomial size.** -/
theorem PT.foldl' [Inhabited β] {l : α → List β} {init : α → σ} {g : α → σ → β → σ}
    (hl : PT l) (hi : PT init) (hg : PT fun q : α × σ × β => g q.1 q.2.1 q.2.2)
    {c d : ℕ} (hb : ∀ a j, j ≤ (l a).length →
      sz (((l a).take j).foldl (g a) (init a)) ≤ d * (sz a + 1) ^ c) :
    PT fun a => (l a).foldl (g a) (init a) := by
  obtain ⟨cl, dl, hl'⟩ := hl.pb
  have hstate : ∀ a k, sz ((PolyDom.foldStep (g a))^[k] (l a, init a)) ≤
      (dl + d) * (sz a + 1) ^ (cl + c) := by
    intro a k
    rw [foldStep_iterate, sz_prod]
    have h1 := (sz_drop_le (l a) k).trans (hl' a)
    have h2 : sz (((l a).take k).foldl (g a) (init a)) ≤ d * (sz a + 1) ^ c := by
      by_cases hk : k ≤ (l a).length
      · exact hb a k hk
      · rw [List.take_of_length_le (by omega)]
        simpa using hb a (l a).length le_rfl
    have e1 : (sz a + 1) ^ cl ≤ (sz a + 1) ^ (cl + c) := pow_le_pow_add (by omega)
    have e2 : (sz a + 1) ^ c ≤ (sz a + 1) ^ (cl + c) := pow_le_pow_add (by omega)
    nlinarith
  have hit := PT.iterate (PT.pair hl hi) (PT.foldStep hg) hstate dl cl
  refine (PT.snd.comp hit).of_eq fun a => ?_
  rw [foldStep_iterate, List.take_of_length_le ((length_le_sz _).trans (hl' a))]

/-- **A left fold whose step adds at most a polynomial amount to the accumulator.** -/
theorem PT.foldl [Inhabited β] {l : α → List β} {init : α → σ} {g : α → σ → β → σ}
    (hl : PT l) (hi : PT init) (hg : PT fun q : α × σ × β => g q.1 q.2.1 q.2.2)
    {c d : ℕ} (hb : ∀ a s, ∀ b ∈ l a, sz (g a s b) ≤ sz s + d * (sz a + 1) ^ c) :
    PT fun a => (l a).foldl (g a) (init a) := by
  obtain ⟨cl, dl, hl'⟩ := hl.pb
  obtain ⟨ci, di, hi'⟩ := hi.pb
  have hacc : ∀ a (j : ℕ) (s : σ), j ≤ (l a).length →
      sz (((l a).take j).foldl (g a) s) ≤ sz s + j * (d * (sz a + 1) ^ c) := by
    intro a j
    induction j with
    | zero => intro s _; simp
    | succ j ih =>
      intro s hj
      have hjl : j < (l a).length := by omega
      rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have h1 := hb a (((l a).take j).foldl (g a) s) _ (List.getElem_mem hjl)
      have h2 := ih s (by omega)
      rw [Nat.succ_mul]
      omega
  refine PT.foldl' hl hi hg (c := cl + ci + c) (d := di + dl * d) fun a j hj => ?_
  have hlen : (l a).length ≤ dl * (sz a + 1) ^ cl := (length_le_sz _).trans (hl' a)
  have h2 := hacc a j (init a) hj
  have e2 : (sz a + 1) ^ ci ≤ (sz a + 1) ^ (cl + ci + c) := pow_le_pow_add (by omega)
  have e3 : (sz a + 1) ^ cl * (sz a + 1) ^ c ≤ (sz a + 1) ^ (cl + ci + c) := by
    rw [← pow_add]; exact pow_le_pow_add (by omega)
  have h3 : j * (d * (sz a + 1) ^ c) ≤ dl * d * ((sz a + 1) ^ cl * (sz a + 1) ^ c) := by
    calc j * (d * (sz a + 1) ^ c) ≤ (dl * (sz a + 1) ^ cl) * (d * (sz a + 1) ^ c) :=
          Nat.mul_le_mul_right _ (hj.trans hlen)
      _ = dl * d * ((sz a + 1) ^ cl * (sz a + 1) ^ c) := by ring
  have h4 : dl * d * ((sz a + 1) ^ cl * (sz a + 1) ^ c) ≤ dl * d * (sz a + 1) ^ (cl + ci + c) :=
    Nat.mul_le_mul_left _ e3
  have h5 : di * (sz a + 1) ^ ci ≤ di * (sz a + 1) ^ (cl + ci + c) := Nat.mul_le_mul_left _ e2
  have := hi' a
  rw [add_mul]
  omega

/-- **A right fold whose step adds at most a polynomial amount to the accumulator.** -/
theorem PT.reverse [Inhabited β] {l : α → List β} (hl : PT l) : PT fun a => (l a).reverse := by
  obtain ⟨cl, dl, hl'⟩ := hl.pb
  have h := PT.foldl (β := β) (σ := List β) (l := l) (init := fun _ => [])
    (g := fun _ s b => b :: s) hl PT.nil
    (PT.cons (PT.snd.comp PT.snd) (PT.fst.comp PT.snd)) (c := cl) (d := 2 * dl + 2)
    (fun a s b hb => by
      rw [sz_cons]
      have := (sz_le_of_mem hb).trans (hl' a)
      have : 1 ≤ (sz a + 1) ^ cl := Nat.one_le_pow _ _ (by omega)
      nlinarith)
  refine h.of_eq fun a => ?_
  simp only
  rw [List.foldl_flip_cons_eq_append]
  simp

theorem PT.foldr [Inhabited β] {l : α → List β} {init : α → σ} {g : α → β → σ → σ}
    (hl : PT l) (hi : PT init) (hg : PT fun q : α × β × σ => g q.1 q.2.1 q.2.2)
    {c d : ℕ} (hb : ∀ a s, ∀ b ∈ l a, sz (g a b s) ≤ sz s + d * (sz a + 1) ^ c) :
    PT fun a => (l a).foldr (g a) (init a) := by
  have h := PT.foldl (l := fun a => (l a).reverse) (g := fun a s b => g a b s) (PT.reverse hl) hi
    (hg.comp (PT.pair PT.fst (PT.pair (PT.snd.comp PT.snd) (PT.fst.comp PT.snd))))
    (c := c) (d := d) (fun a s b hb' => hb a s b (List.mem_reverse.1 hb'))
  exact h.of_eq fun a => by simp [List.foldl_reverse]

end PolyDom

end Syn

end HTN
