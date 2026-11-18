import HtnPlanning.Interleave.InterleaveList
/-!
# Prefix sums of integer weights, and interleavings

The synchronisation analysis of a plan of the HTN-AC compilation
(`HtnComplexity/ToHtnAc/ToHtnAc.lean`) repeatedly needs invariants of the form

> at every point of the run, the number of `ask` actions so far never exceeds the number of
> `wait` actions so far by more than the number of open locks,

i.e. bounds on *prefix sums of integer weights* attached to the actions.  Such bounds are
convenient because they are additive: the weight sum of an interleaving is the sum of the weight
sums of its parts, and every prefix of an interleaving is an interleaving of prefixes
(`HTN.InterleaveList.exists_prefix`), so a prefix-sum bound that holds for each part holds for
the whole.

This file provides that little theory:

* `HTN.PSumNonneg w l` — every prefix of `l` has nonnegative weight sum;
* `HTN.PSumNonneg.append`, `HTN.psumNonneg_of_weights_zero`, … — the closure lemmas used to
  verify the property for the explicit action sequences of the compilation;
* `HTN.Interleave.sum_map`, `HTN.InterleaveList.sum_map`, `HTN.Interleave.psumNonneg`,
  `HTN.InterleaveList.psumNonneg` — additivity and the transfer to interleavings;
* `HTN.sum_map_eq_countP_sub` — the weight sum of a `±1`-weight is a difference of counts.
-/

namespace HTN

universe u

variable {α : Type u}

/-- The weight sum of a list. -/
abbrev wsum (w : α → ℤ) (l : List α) : ℤ := (l.map w).sum

@[simp] lemma wsum_nil (w : α → ℤ) : wsum w ([] : List α) = 0 := rfl

@[simp] lemma wsum_cons (w : α → ℤ) (a : α) (l : List α) :
    wsum w (a :: l) = w a + wsum w l := by simp [wsum]

lemma wsum_append (w : α → ℤ) (l₁ l₂ : List α) :
    wsum w (l₁ ++ l₂) = wsum w l₁ + wsum w l₂ := by simp [wsum]

lemma wsum_add (w₁ w₂ : α → ℤ) (l : List α) :
    wsum (fun a => w₁ a + w₂ a) l = wsum w₁ l + wsum w₂ l := by
  induction l with
  | nil => simp
  | cons a l ih => simp

lemma wsum_eq_zero_of_weights_zero {w : α → ℤ} {l : List α} (h : ∀ a ∈ l, w a = 0) :
    wsum w l = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih fun b hb => h b (by simp [hb]), h a (by simp)]

/-- The weight sum of a weight that is `+1` on `f`, `-1` on `g` and `0` elsewhere is the
difference of the two counts. -/
lemma sum_map_eq_countP_sub {w : α → ℤ} {f g : α → Bool}
    (h : ∀ a, w a = (if f a then (1 : ℤ) else 0) - (if g a then (1 : ℤ) else 0))
    (l : List α) : wsum w l = (l.countP f : ℤ) - (l.countP g : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [wsum_cons, ih, h a, List.countP_cons, List.countP_cons]
      by_cases hf : f a <;> by_cases hg : g a <;> simp [hf, hg] <;> try ring

/-- A prefix of a concatenation is either a prefix of the first part, or the first part followed
by a prefix of the second. -/
lemma prefix_append_cases :
    ∀ {l₁ l₂ p : List α}, p <+: l₁ ++ l₂ → p <+: l₁ ∨ ∃ r, p = l₁ ++ r ∧ r <+: l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ p hp; exact Or.inr ⟨p, by simp, by simpa using hp⟩
  | cons a t ih =>
      intro l₂ p hp
      cases p with
      | nil => exact Or.inl List.nil_prefix
      | cons b p =>
          obtain ⟨rfl, hp'⟩ := List.cons_prefix_cons.1 (by simpa using hp)
          rcases ih hp' with h | ⟨r, rfl, hr⟩
          · exact Or.inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
          · exact Or.inr ⟨r, by simp, hr⟩

/-- If the first element of a list is the only one counted so far, a prefix that counts nothing
is empty. -/
lemma prefix_eq_nil_of_countP_head {l l' : List α} {a : α} {p : α → Bool} {q : List α}
    (hl : l = a :: l') (hp : p a) (hq : q <+: l) (h : q.countP p = 0) : q = [] := by
  subst hl
  cases q with
  | nil => rfl
  | cons b q' =>
      obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hq
      rw [List.countP_cons, if_pos hp] at h
      omega

/-- If a list contains exactly one element counted by `p`, and that element is its last one,
then a prefix that already counts it is the whole list. -/
lemma prefix_eq_of_countP_last {l l' : List α} {a : α} {p : α → Bool} {q : List α}
    (hl : l = l' ++ [a]) (hp : p a) (hcount : l.countP p = 1) (hq : q <+: l)
    (h : 1 ≤ q.countP p) : q = l := by
  subst hl
  have hl' : l'.countP p = 0 := by
    rw [List.countP_append] at hcount
    have : ([a] : List α).countP p = 1 := by simp [hp]
    omega
  rcases prefix_append_cases hq with hq' | ⟨v, rfl, hv⟩
  · have := (hq'.sublist).countP_le (p := p)
    omega
  · cases v with
    | nil =>
        rw [List.countP_append, hl'] at h
        simp at h
    | cons b v' =>
        obtain ⟨rfl, hv'⟩ := List.cons_prefix_cons.1 hv
        rw [List.prefix_nil.1 hv']

/-! ### Locating a prefix by counting a marker

If `l = u ++ a :: v` and `a` is counted by `p`, then the number of `p`-elements of a prefix `q`
of `l` says on which side of that occurrence of `a` the prefix ends. -/

/-- A prefix that has not yet passed the marker `a` is a prefix of the part before it. -/
lemma prefix_of_countP_le {l u v q : List α} {a : α} {p : α → Bool} {n : ℕ}
    (hl : l = u ++ a :: v) (hp : p a) (hu : u.countP p = n) (hq : q <+: l)
    (h : q.countP p ≤ n) : q <+: u := by
  subst hl
  rcases prefix_append_cases hq with h' | ⟨r, rfl, hr⟩
  · exact h'
  · cases r with
    | nil => simp
    | cons b r' =>
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hr
        rw [List.countP_append, List.countP_cons, if_pos hp] at h
        omega

/-- A prefix that counts more markers than the part before the marker `a` has passed `a`. -/
lemma append_singleton_prefix_of_countP_gt {l u v q : List α} {a : α} {p : α → Bool} {n : ℕ}
    (hl : l = u ++ a :: v) (hu : u.countP p = n) (hq : q <+: l)
    (h : n < q.countP p) : (u ++ [a]) <+: q := by
  subst hl
  rcases prefix_append_cases hq with h' | ⟨r, rfl, hr⟩
  · have := (h'.sublist).countP_le (p := p)
    omega
  · cases r with
    | nil =>
        rw [List.countP_append, hu] at h
        simp at h
    | cons b r' =>
        obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hr
        exact ⟨r', by simp⟩

/-- **A prefix that has passed one marker but not the next ends between them.**  Here `a` is a
marker for `p` and the element `b` following it is a marker for `p'`: a prefix `q` of `l` that
counts more than `m` occurrences of `p` and at most `n` occurrences of `p'` is exactly the part
of `l` up to and including `a`. -/
lemma eq_append_singleton_of_countP {l u v q : List α} {a b : α} {p p' : α → Bool} {m n : ℕ}
    (hl : l = u ++ a :: b :: v) (hp' : p' b) (hu : u.countP p = m)
    (hua : (u ++ [a]).countP p' = n) (hq : q <+: l)
    (h₁ : m < q.countP p) (h₂ : q.countP p' ≤ n) : q = u ++ [a] := by
  have hge : (u ++ [a]) <+: q :=
    append_singleton_prefix_of_countP_gt (v := b :: v) hl hu hq h₁
  have hle : q <+: u ++ [a] :=
    prefix_of_countP_le (l := l) (u := u ++ [a]) (v := v) (a := b) (p := p')
      (by rw [hl]; simp) hp' hua hq h₂
  exact hle.eq_of_length (le_antisymm hle.length_le hge.length_le)

/-- `PSumGe w c l`: every prefix of `l` has weight sum at least `c`. -/
def PSumGe (w : α → ℤ) (c : ℤ) (l : List α) : Prop := ∀ p, p <+: l → c ≤ wsum w p

/-- `PSumNonneg w l`: every prefix of `l` has nonnegative weight sum. -/
def PSumNonneg (w : α → ℤ) (l : List α) : Prop := PSumGe w 0 l

namespace PSumGe

variable {w : α → ℤ} {c c' : ℤ} {l l₁ l₂ : List α}

lemma nil (hc : c ≤ 0) : PSumGe w c ([] : List α) := by
  intro p hp
  rw [List.prefix_nil] at hp
  simpa [hp] using hc

/-- The whole list is one of its prefixes. -/
lemma total (h : PSumGe w c l) : c ≤ wsum w l := h l List.prefix_rfl

lemma nonpos (h : PSumGe w c l) : c ≤ 0 := by simpa using h [] List.nil_prefix

lemma mono (h : PSumGe w c l) (hc : c' ≤ c) : PSumGe w c' l := fun p hp => hc.trans (h p hp)

lemma of_prefix (h : PSumGe w c l) {p : List α} (hp : p <+: l) : PSumGe w c p :=
  fun q hq => h q (hq.trans hp)

/-- Concatenation: the second part starts from the weight sum of the first. -/
lemma append (h₁ : PSumGe w c l₁) (h₂ : PSumGe w (c - wsum w l₁) l₂) :
    PSumGe w c (l₁ ++ l₂) := by
  intro p hp
  rcases prefix_append_cases hp with h | ⟨r, rfl, hr⟩
  · exact h₁ p h
  · have := h₂ r hr
    rw [wsum_append]
    omega

/-- Prefixing a single element. -/
lemma cons {a : α} (hc : c ≤ 0) (h : PSumGe w (c - w a) l) : PSumGe w c (a :: l) := by
  have hwa : c ≤ w a := by have := h.nonpos; omega
  have hsingle : PSumGe w c [a] := by
    intro p hp
    obtain ⟨t, ht⟩ := hp
    cases p with
    | nil => simpa using hc
    | cons b q =>
        simp only [List.cons_append, List.cons.injEq] at ht
        obtain ⟨rfl, hq⟩ := ht
        obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.1 hq
        simpa using hwa
  have hres := PSumGe.append hsingle (by simpa using h)
  simpa using hres

/-- Appending after a block of weight-`0` elements. -/
lemma append_zero (hz : ∀ a ∈ l₁, w a = 0) (h₂ : PSumGe w c l₂) : PSumGe w c (l₁ ++ l₂) := by
  refine PSumGe.append (fun p hp => ?_) ?_
  · rw [wsum_eq_zero_of_weights_zero (fun a ha => hz a (hp.subset ha))]
    exact h₂.nonpos
  · rw [wsum_eq_zero_of_weights_zero hz]
    simpa using h₂

end PSumGe

namespace PSumNonneg

variable {w : α → ℤ} {l l₁ l₂ : List α}

lemma nil : PSumNonneg w ([] : List α) := PSumGe.nil le_rfl

/-- The whole list has nonnegative weight sum. -/
lemma total (h : PSumNonneg w l) : 0 ≤ wsum w l := PSumGe.total h

lemma of_prefix (h : PSumNonneg w l) {p : List α} (hp : p <+: l) : PSumNonneg w p :=
  PSumGe.of_prefix h hp

/-- Concatenation preserves the property. -/
lemma append (h₁ : PSumNonneg w l₁) (h₂ : PSumNonneg w l₂) : PSumNonneg w (l₁ ++ l₂) :=
  PSumGe.append h₁ (PSumGe.mono h₂ (by have := h₁.total; omega))

end PSumNonneg

/-- A list whose elements all have weight `0` satisfies every prefix-sum bound. -/
lemma psumGe_of_weights_zero {w : α → ℤ} {c : ℤ} {l : List α} (h : ∀ a ∈ l, w a = 0)
    (hc : c ≤ 0) : PSumGe w c l := by
  intro p hp
  rw [wsum_eq_zero_of_weights_zero (fun a ha => h a (hp.subset ha))]
  exact hc

/-- A list whose elements all have weight `0` satisfies every prefix-sum bound. -/
lemma psumNonneg_of_weights_zero {w : α → ℤ} {l : List α} (h : ∀ a ∈ l, w a = 0) :
    PSumNonneg w l := psumGe_of_weights_zero h le_rfl

/-- A singleton with nonnegative weight. -/
lemma psumNonneg_singleton {w : α → ℤ} {a : α} (h : 0 ≤ w a) : PSumNonneg w [a] := by
  intro p hp
  obtain ⟨t, ht⟩ := hp
  cases p with
  | nil => simp
  | cons b q =>
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, hq⟩ := ht
      obtain ⟨rfl, -⟩ := List.append_eq_nil_iff.1 hq
      simpa using h

/-! ### Interleavings -/

namespace Interleave

lemma sum_map {xs ys zs : List α} (h : Interleave xs ys zs) (w : α → ℤ) :
    wsum w zs = wsum w xs + wsum w ys := by
  have := h.perm
  calc wsum w zs = wsum w (xs ++ ys) := by
        simpa [wsum] using (this.map w).sum_eq
    _ = wsum w xs + wsum w ys := wsum_append w xs ys

/-- **A prefix-sum bound transfers from the two parts of an interleaving to the whole.** -/
lemma psumNonneg {xs ys zs : List α} {w : α → ℤ} (h : Interleave xs ys zs)
    (hx : PSumNonneg w xs) (hy : PSumNonneg w ys) : PSumNonneg w zs := by
  intro p hp
  obtain ⟨px, py, hpx, hpy, hint⟩ := h.exists_prefix hp
  rw [hint.sum_map]
  have := hx px hpx
  have := hy py hpy
  omega

end Interleave

namespace InterleaveList

lemma sum_map {ls : List (List α)} {z : List α} (h : InterleaveList ls z) (w : α → ℤ) :
    wsum w z = (ls.map (fun l => wsum w l)).sum := by
  induction h with
  | nil => simp
  | cons h hint ih => rw [hint.sum_map, ih]; simp

/-- **A prefix-sum bound transfers from the parts of an interleaving to the whole.** -/
lemma psumNonneg {ls : List (List α)} {z : List α} {w : α → ℤ} (h : InterleaveList ls z)
    (hall : ∀ l ∈ ls, PSumNonneg w l) : PSumNonneg w z := by
  induction h with
  | nil => exact PSumNonneg.nil
  | @cons as bs cs ls h hint ih =>
      exact hint.psumNonneg (hall as (by simp)) (ih fun l hl => hall l (by simp [hl]))

end InterleaveList

end HTN
