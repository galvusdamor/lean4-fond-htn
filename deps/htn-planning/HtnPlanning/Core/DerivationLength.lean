import HtnPlanning.Regular.RegularNormalForm
/-!
# How many methods does a derivation of a regular problem need?

The normal form theorem `HTN.Problem.solvable_iff_derives` characterises solvability of a
totally ordered regular problem by the existence of a *derivation* `P.Derives c₀ as`: a chain of
methods, each continuing the compound task left open by the previous one, whose concatenated
action sequence is `as`.  The compilation of regular problems into STRIPS
(`HtnComplexity/Regular/RegularToStrips.lean`) uses **one action per method application**, so the
length of the compiled plan is the *number of methods of the derivation*, not the length of
`as`; a derivation may apply arbitrarily many methods with an empty body without producing a
single action.

This file proves the missing bound: a derivation can always be shortened so that it applies at
most `(|as| + 1) · (|C| + 1)` methods.

* `HTN.Problem.DerivesN n c as` — a derivation of `as` from `c` using exactly `n` methods;
  `HTN.Problem.derives_iff_exists_derivesN` relates it to `HTN.Problem.Derives`.
* `HTN.Problem.derivLen c as` — the least number of methods of a derivation of `as` from `c`.
* `HTN.Problem.derivLen_le` — **the bound**: for a finite type of compound task names,
  `derivLen c as ≤ (|as| + 1) · (|C| + 1)`.
* `HTN.Problem.exists_derivesN_le` — consequently every derivation can be replaced by one with
  at most that many method applications.

The argument is the expected cut-elimination one, organised so that no explicit surgery on
derivations is needed.  Write `g c` for `derivLen c as`.  A *shortest* derivation of `as` from
`c` either consists of a single method, or applies a method with body `os` and continues with a
shortest derivation of the remaining actions (`HTN.Problem.derivLen_step`).  If `os ≠ ∅` the
remaining action sequence is strictly shorter and induction on the length of `as` applies.  If
`os = ∅` the state of the derivation is unchanged except for the compound task, and
`g c = g c' + 1`; since all the values `g c''` lie in the image of `C` under `g`, a set of at
most `|C|` natural numbers, at most `|C|` such steps can occur in a row.
-/

namespace HTN

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x} [DecidableEq I]

/-- **Counted derivations.**  `P.DerivesN n c as` states that the compound task `c` can be
refined into the action sequence `as` by a chain of exactly `n` methods; it is the relation
`HTN.Problem.Derives` with the number of method applications recorded. -/
inductive Problem.DerivesN (P : Problem F A C I) : ℕ → C → List A → Prop
  /-- The last method of the derivation leaves no compound task. -/
  | last {c : C} {os : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBody os none) : P.DerivesN 1 c os
  /-- A method leaving the compound task `c'`, which is derived in turn by `n` methods. -/
  | cons {n : ℕ} {c c' : C} {os rest : List A} {m : Method I A C} (hm : m ∈ P.methods)
      (hc : m.abstractTask = c) (hb : m.HasBody os (some c')) (h : P.DerivesN n c' rest) :
      P.DerivesN (n + 1) c (os ++ rest)

namespace Problem

variable {P : Problem F A C I}

lemma Derives.of_derivesN {n : ℕ} {c : C} {as : List A} (h : P.DerivesN n c as) :
    P.Derives c as := by
  induction h with
  | last hm hc hb => exact Derives.last hm hc hb
  | cons hm hc hb _ ih => exact Derives.cons hm hc hb ih

lemma Derives.exists_derivesN {c : C} {as : List A} (h : P.Derives c as) :
    ∃ n, P.DerivesN n c as := by
  induction h with
  | last hm hc hb => exact ⟨1, Problem.DerivesN.last hm hc hb⟩
  | cons hm hc hb _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Problem.DerivesN.cons hm hc hb hn⟩

/-- A derivation exists exactly when a counted derivation does. -/
theorem derives_iff_exists_derivesN {c : C} {as : List A} :
    P.Derives c as ↔ ∃ n, P.DerivesN n c as :=
  ⟨Derives.exists_derivesN, fun ⟨_, h⟩ => Derives.of_derivesN h⟩

open scoped Classical in
/-- The least number of methods of a derivation of `as` from `c` (and `0` if there is none). -/
noncomputable def derivLen (P : Problem F A C I) (c : C) (as : List A) : ℕ :=
  if h : ∃ n, P.DerivesN n c as then Nat.find h else 0

open scoped Classical in
lemma derivesN_derivLen {c : C} {as : List A} (h : P.Derives c as) :
    P.DerivesN (P.derivLen c as) c as := by
  have hex : ∃ n, P.DerivesN n c as := h.exists_derivesN
  rw [derivLen, dif_pos hex]
  exact Nat.find_spec hex

open scoped Classical in
lemma derivLen_le_of_derivesN {n : ℕ} {c : C} {as : List A} (h : P.DerivesN n c as) :
    P.derivLen c as ≤ n := by
  have hex : ∃ n, P.DerivesN n c as := ⟨n, h⟩
  rw [derivLen, dif_pos hex]
  exact Nat.find_le h

/-- Inversion for counted derivations. -/
lemma derivesN_inv {n : ℕ} {c : C} {as : List A} (h : P.DerivesN n c as) :
    n = 1 ∨ ∃ (c' : C) (os rest : List A) (k : ℕ), as = os ++ rest ∧ P.DerivesN k c' rest ∧
      n = k + 1 ∧ ∀ j, P.DerivesN j c' rest → P.DerivesN (j + 1) c as := by
  cases h with
  | last hm hc hb => exact Or.inl rfl
  | @cons k c c' os rest m hm hc hb htail =>
      exact Or.inr ⟨c', os, rest, k, rfl, htail, rfl,
        fun j hj => Problem.DerivesN.cons hm hc hb hj⟩

/-- **The shape of a shortest derivation.**  It either consists of a single method, or applies
a method with body `os` and continues with a shortest derivation of the remaining actions. -/
lemma derivLen_step {c : C} {as : List A} (h : P.Derives c as) :
    P.derivLen c as = 1 ∨
      ∃ (c' : C) (os rest : List A), as = os ++ rest ∧ P.Derives c' rest ∧
        P.derivLen c as = P.derivLen c' rest + 1 := by
  rcases derivesN_inv (derivesN_derivLen h) with h1 | ⟨c', os, rest, k, hsplit, htail, hk, hbuild⟩
  · exact Or.inl h1
  · have hder : P.Derives c' rest := Derives.of_derivesN htail
    refine Or.inr ⟨c', os, rest, hsplit, hder, ?_⟩
    have h1 : P.derivLen c' rest ≤ k := derivLen_le_of_derivesN htail
    have h2 : P.derivLen c as ≤ P.derivLen c' rest + 1 :=
      derivLen_le_of_derivesN (hbuild _ (derivesN_derivLen hder))
    omega

section Finite

variable [Fintype C] [DecidableEq C]

open scoped Classical in
/-- The set of values of `derivLen · as`: at most `|C|` natural numbers. -/
noncomputable def derivLenImage (P : Problem F A C I) (as : List A) : Finset ℕ :=
  Finset.univ.image fun c => P.derivLen c as

omit [DecidableEq C] in
open scoped Classical in
lemma mem_derivLenImage (P : Problem F A C I) (c : C) (as : List A) :
    P.derivLen c as ∈ P.derivLenImage as :=
  Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩

omit [DecidableEq C] in
open scoped Classical in
lemma card_derivLenImage_le (P : Problem F A C I) (as : List A) :
    (P.derivLenImage as).card ≤ Fintype.card C :=
  le_trans Finset.card_image_le (le_of_eq (Finset.card_univ))

omit [DecidableEq C] in
open scoped Classical in
/-- The inner induction: a shortest derivation performs at most `|C|` body-free steps before
it either stops or produces an action. -/
lemma derivLen_le_aux (as : List A) (M : ℕ)
    (hM : ∀ c : C, P.Derives c as → P.derivLen c as = 1 ∨
      (∃ (c' : C) (os rest : List A), as = os ++ rest ∧ os ≠ [] ∧ P.Derives c' rest ∧
        P.derivLen c as = P.derivLen c' rest + 1) →
      P.derivLen c as ≤ M) :
    ∀ (n : ℕ) (c : C), P.Derives c as → P.derivLen c as = n →
      n ≤ M + ((P.derivLenImage as).filter fun v => v ≤ n).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro c hc hn
    rcases derivLen_step hc with h1 | ⟨c', os, rest, hsplit, hder, hlen⟩
    · have hle := hM c hc (Or.inl h1)
      omega
    · by_cases hos : os = []
      · -- a step that produces no action: the compound task changes, the actions do not
        subst hos
        rw [List.nil_append] at hsplit
        subst hsplit
        have hlt : P.derivLen c' as < n := by omega
        have hIH := IH _ hlt c' hder rfl
        have hsub : ((P.derivLenImage as).filter fun v => v ≤ P.derivLen c' as) ⊂
            ((P.derivLenImage as).filter fun v => v ≤ n) := by
          refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨n, ?_, ?_⟩
          · intro v hv
            rw [Finset.mem_filter] at hv ⊢
            exact ⟨hv.1, le_trans hv.2 (by omega)⟩
          · rw [Finset.mem_filter]
            exact ⟨hn ▸ mem_derivLenImage P c as, le_refl _⟩
          · rw [Finset.mem_filter]
            rintro ⟨-, hle⟩
            omega
        have hcard := Finset.card_lt_card hsub
        omega
      · -- a step that produces an action
        have hle := hM c hc (Or.inr ⟨c', os, rest, hsplit, hos, hder, hlen⟩)
        omega

omit [DecidableEq C] in
open scoped Classical in
/-- **A derivation never needs more than `(|as| + 1) · (|C| + 1)` methods.** -/
theorem derivLen_le : ∀ (as : List A) (c : C), P.Derives c as →
    P.derivLen c as ≤ (as.length + 1) * (Fintype.card C + 1) := by
  have key : ∀ (k : ℕ) (as : List A), as.length = k → ∀ c : C, P.Derives c as →
      P.derivLen c as ≤ (k + 1) * (Fintype.card C + 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro as hk c hc
      subst hk
      have hM : ∀ c : C, P.Derives c as → P.derivLen c as = 1 ∨
          (∃ (c' : C) (os rest : List A), as = os ++ rest ∧ os ≠ [] ∧ P.Derives c' rest ∧
            P.derivLen c as = P.derivLen c' rest + 1) →
          P.derivLen c as ≤ 1 + as.length * (Fintype.card C + 1) := by
        rintro c₁ hc₁ (h1 | ⟨c', os, rest, hsplit, hos, hder, hlen⟩)
        · have : 0 ≤ as.length * (Fintype.card C + 1) := Nat.zero_le _
          omega
        · have hlensum : as.length = os.length + rest.length := by rw [hsplit]; simp
          have hos' : 0 < os.length := List.length_pos_iff.2 hos
          have hIH := IHk rest.length (by omega) rest rfl c' hder
          have hle : (rest.length + 1) * (Fintype.card C + 1) ≤
              as.length * (Fintype.card C + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
      have hmain := derivLen_le_aux as (1 + as.length * (Fintype.card C + 1)) hM
        (P.derivLen c as) c hc rfl
      have hcard : ((P.derivLenImage as).filter fun v => v ≤ P.derivLen c as).card ≤
          Fintype.card C :=
        le_trans (Finset.card_filter_le _ _) (card_derivLenImage_le P as)
      have hexp : (as.length + 1) * (Fintype.card C + 1) =
          as.length * (Fintype.card C + 1) + (Fintype.card C + 1) := by ring
      omega
  intro as c hc
  exact key as.length as rfl c hc

omit [DecidableEq C] in
open scoped Classical in
/-- **Every derivation can be shortened to at most `(|as| + 1) · (|C| + 1)` methods.** -/
theorem exists_derivesN_le {c : C} {as : List A} (h : P.Derives c as) :
    ∃ n ≤ (as.length + 1) * (Fintype.card C + 1), P.DerivesN n c as :=
  ⟨P.derivLen c as, derivLen_le as c h, derivesN_derivLen h⟩

end Finite

end Problem

end HTN
