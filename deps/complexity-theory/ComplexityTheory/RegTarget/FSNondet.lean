import ComplexityTheory.Compress.Covering
/-!
# Fortnow–Santhanam for nondeterministic AND-compressions

`HTN.Syn.Compress.fs_cover` is the covering lemma behind the theorem of Fortnow and Santhanam:
a *deterministic* compression of OR-SAT puts UNSAT into `NP/poly`.  For targets whose plan
existence is an existential question once the domain is fixed (`HTN-REG`: choose a linearization
of the primitive prefix), a compilation only yields a **nondeterministic** compression, and
OR-SAT trivially has one.  The right source is then AND-UNSAT (all formulas of the tuple are
unsatisfiable), compressed nondeterministically:

  a tuple is all-unsatisfiable  ⟺  for some witness `w`, the compressed value `g tup w` lies in
  the set `A` of accepting values.

The same covering argument still gives short certificates: pick an accepting witness for every
all-unsatisfiable tuple and cover with the resulting deterministic map.

* `HTN.Syn.RegTarget.fs_cover_nondet` — the covering lemma with witnesses;
* `HTN.Syn.RegTarget.fs_nondet_certificates` — **the certificate form**: membership in `U` is
  equivalent to the existence of a tuple containing the element and a witness whose value lies in
  a small advice set `S`.  This is the `NP/poly` conclusion (the verifier checks `g tup w ∈ S`),
  before any uniformity is imposed on `g`.
-/

namespace HTN

namespace Syn

namespace RegTarget

open Finset

variable {X Y W : Type*} [DecidableEq X] [DecidableEq Y]

/-- **The covering lemma with witnesses.**  If every `t`-tuple over `U` has a witness `w` whose
value `g tup w` is accepting (in `A`) and lies in a set `T` of at most `2 ^ ℓ` values (`ℓ ≤ t`),
then a set `S` of accepting values with `2 ^ |S| ≤ 2 |U|` covers `U`. -/
theorem fs_cover_nondet {t ℓ : ℕ} (g : (Fin t → X) → W → Y) (A : Set Y) (U : Finset X)
    (hU : U.Nonempty) (T : Finset Y) (hT : T.card ≤ 2 ^ ℓ) (hℓ : ℓ ≤ t) (ht : 0 < t)
    (hacc : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => U), ∃ w, g tup w ∈ A ∧ g tup w ∈ T) :
    ∃ S ⊆ T, (∀ y ∈ S, y ∈ A) ∧ 2 ^ S.card ≤ 2 * U.card ∧
      ∀ x ∈ U, ∃ tup ∈ Fintype.piFinset (fun _ : Fin t => U), (∃ i, tup i = x) ∧
        ∃ w, g tup w ∈ S := by
  classical
  obtain ⟨x₀, hx₀⟩ := hU
  have htup₀ : (fun _ : Fin t => x₀) ∈ Fintype.piFinset (fun _ : Fin t => U) :=
    Fintype.mem_piFinset.2 fun _ => hx₀
  obtain ⟨w₀, -, -⟩ := hacc _ htup₀
  let wit : (Fin t → X) → W := fun tup =>
    if h : tup ∈ Fintype.piFinset (fun _ : Fin t => U) then (hacc tup h).choose else w₀
  have hwit : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => U),
      g tup (wit tup) ∈ A ∧ g tup (wit tup) ∈ T := by
    intro tup h
    simp only [wit, dif_pos h]
    exact (hacc tup h).choose_spec
  let T' : Finset Y := T.filter (· ∈ A)
  have hT' : T'.card ≤ 2 ^ ℓ := (card_filter_le _ _).trans hT
  obtain ⟨S, hST, hcard, hcov⟩ := Compress.fs_cover (fun tup => g tup (wit tup)) U ⟨x₀, hx₀⟩ T'
    hT' hℓ ht (fun tup h => mem_filter.2 ⟨(hwit tup h).2, (hwit tup h).1⟩)
  refine ⟨S, hST.trans (filter_subset _ _), fun y hy => (mem_filter.1 (hST hy)).2, hcard,
    fun x hx => ?_⟩
  obtain ⟨tup, htup, hi, hS⟩ := hcov x hx
  exact ⟨tup, htup, hi, wit tup, hS⟩

/-- **Fortnow–Santhanam, nondeterministic form (certificates).**  Suppose that

* accepting values only come from tuples all of whose entries lie in `U` (soundness), and
* every `t`-tuple over `U` has a witness whose value is accepting and lies in `T`,
  `|T| ≤ 2 ^ ℓ`, `ℓ ≤ t` (completeness).

Then there is a small set `S` of values (`2 ^ |S| ≤ 2 |U|`) such that an element `x` lies in `U`
iff some tuple containing `x` has a witness whose value lies in `S`. -/
theorem fs_nondet_certificates {t ℓ : ℕ} (g : (Fin t → X) → W → Y) (A : Set Y) (U : Finset X)
    (hU : U.Nonempty) (T : Finset Y) (hT : T.card ≤ 2 ^ ℓ) (hℓ : ℓ ≤ t) (ht : 0 < t)
    (hsound : ∀ (tup : Fin t → X) (w : W), g tup w ∈ A → ∀ i, tup i ∈ U)
    (hacc : ∀ tup ∈ Fintype.piFinset (fun _ : Fin t => U), ∃ w, g tup w ∈ A ∧ g tup w ∈ T) :
    ∃ S : Finset Y, 2 ^ S.card ≤ 2 * U.card ∧
      ∀ x, x ∈ U ↔ ∃ tup : Fin t → X, (∃ i, tup i = x) ∧ ∃ w, g tup w ∈ S := by
  obtain ⟨S, -, hSA, hcard, hcov⟩ := fs_cover_nondet g A U hU T hT hℓ ht hacc
  refine ⟨S, hcard, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨tup, -, hi, w, hw⟩ := hcov x hx
    exact ⟨tup, hi, w, hw⟩
  · rintro ⟨tup, ⟨i, rfl⟩, w, hw⟩
    exact hsound tup w (hSA _ hw) i

end RegTarget

end Syn

end HTN
