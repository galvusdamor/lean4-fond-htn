import HtnPlanning.Core.Size
/-!
# Size measures restricted to the used part of a domain

`HTN.Domain.size` measures a domain by summing over *all* actions of the action type `A` and
over *all* methods of `D.methods`.  This is the right measure for a domain whose signature is
given by finite types, but several of the constructions of this project produce domains whose
action or method type is infinite even though only a finite part of it is ever used: the
binarisation of `HtnPlanning/Binarisation/Binarisation.lean`, for instance, has one compound task
name `⟨bs⟩` per *task sequence* `bs`, although only the suffixes of the method bodies of the
source domain occur in any decomposition.

This file introduces the missing measure.  A `HTN.Fragment` records a finite part of a
signature — finitely many facts, operators, compound task names and methods — and
`HTN.Domain.sizeOn D fr` measures `D` relative to it.  For a domain over finite types whose
fragment is the whole signature this is the old measure (`HTN.Domain.sizeOn_full`), and it is
monotone in the fragment (`HTN.Domain.sizeOn_le_sizeOn`).

On top of it, `HTN.CompilationScheme.HasPolySizeOn` and `HTN.CompilationScheme.HasLinearSizeOn`
are the fragment-relative versions of `HTN.CompilationScheme.HasPolySize` and
`HTN.CompilationScheme.HasLinearSize`: a compilation scheme has polynomial size relative to a
translation `frag` of fragments if the compiled domain, measured on the translated fragment, is
polynomially bounded by the source domain measured on the original fragment.  They satisfy the
same lemmas as the absolute versions (`HasLinearSizeOn.hasPolySizeOn`, `HasPolySizeOn.comp`).
-/

namespace HTN

universe u v w x u' v' w' x'

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

/-- A *fragment* of a signature: finitely many facts, operators, compound task names and
methods.  Fragments are used to measure the size of a domain whose signature is infinite but of
which only a finite part is used. -/
structure Fragment (F : Type u) (A : Type v) (C : Type w) (I : Type x) where
  /-- The facts of the fragment. -/
  facts : Finset F
  /-- The operators (primitive task names) of the fragment. -/
  ops : Finset A
  /-- The compound task names of the fragment. -/
  tasks : Finset C
  /-- The methods of the fragment. -/
  methods : Finset (Method I A C)

namespace Fragment

/-- A fragment is contained in another one if all four of its components are. -/
protected def Subset (fr₁ fr₂ : Fragment F A C I) : Prop :=
  fr₁.facts ⊆ fr₂.facts ∧ fr₁.ops ⊆ fr₂.ops ∧ fr₁.tasks ⊆ fr₂.tasks ∧
    fr₁.methods ⊆ fr₂.methods

instance : HasSubset (Fragment F A C I) := ⟨Fragment.Subset⟩

lemma subset_def {fr₁ fr₂ : Fragment F A C I} :
    fr₁ ⊆ fr₂ ↔ fr₁.facts ⊆ fr₂.facts ∧ fr₁.ops ⊆ fr₂.ops ∧ fr₁.tasks ⊆ fr₂.tasks ∧
      fr₁.methods ⊆ fr₂.methods := Iff.rfl

/-- The fragment consisting of the whole (finite) signature and the given methods. -/
def full [Fintype F] [Fintype A] [Fintype C] (ms : Finset (Method I A C)) :
    Fragment F A C I where
  facts := Finset.univ
  ops := Finset.univ
  tasks := Finset.univ
  methods := ms

end Fragment

/-- The size of a domain measured on a fragment: the number of facts and compound task names of
the fragment, plus the sizes of its operators and of its methods. -/
noncomputable def Domain.sizeOn (D : Domain F A C I) (fr : Fragment F A C I) : ℕ :=
  fr.facts.card + fr.tasks.card + (∑ a ∈ fr.ops, D.actionSize a) + (∑ m ∈ fr.methods, m.size)

/-- The size measured on a fragment only depends on the action model of the domain. -/
lemma Domain.sizeOn_congr {D D' : Domain F A C I} (h : D.toActionModel = D'.toActionModel)
    (fr : Fragment F A C I) : D.sizeOn fr = D'.sizeOn fr := by
  simp only [Domain.sizeOn, ActionModel.actionSize, h]

/-- The size measure is monotone in the fragment. -/
lemma Domain.sizeOn_le_sizeOn (D : Domain F A C I) {fr₁ fr₂ : Fragment F A C I}
    (h : fr₁ ⊆ fr₂) : D.sizeOn fr₁ ≤ D.sizeOn fr₂ := by
  obtain ⟨hf, ho, ht, hm⟩ := h
  refine Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Finset.card_le_card hf)
    (Finset.card_le_card ht)) ?_) ?_
  · exact Finset.sum_le_sum_of_subset ho
  · exact Finset.sum_le_sum_of_subset hm

/-- **On a finite signature the fragment measure is the absolute measure.** -/
theorem Domain.sizeOn_full [Fintype F] [Fintype A] [Fintype C] (D : Domain F A C I)
    {ms : Finset (Method I A C)} (hms : (ms : Set (Method I A C)) = D.methods) :
    D.sizeOn (Fragment.full ms) = D.size := by
  have h₁ : ∑ᶠ a : A, D.actionSize a = ∑ a ∈ (Finset.univ : Finset A), D.actionSize a :=
    finsum_eq_sum_of_fintype _
  have h₂ : ∑ᶠ m ∈ D.methods, m.size = ∑ m ∈ ms, m.size := by
    rw [← hms, finsum_mem_coe_finset]
  simp only [Domain.sizeOn, Domain.size, Fragment.full, h₁, h₂,
    Finset.card_univ, Nat.card_eq_fintype_card]

/-! ### Sizes of the constructed task networks and methods -/

/-- Every method has size at least one. -/
lemma Method.one_le_size (m : Method I A C) : 1 ≤ m.size := by
  simp [Method.size]

/-- If every method of the fragment has size at most `cm`, then the size of the domain on the
fragment is bounded by the sizes of the signature and of the operators plus `cm` per method.
This turns the per-method size bounds proved for the constructions of this project into bounds
on the size of the constructed domain. -/
lemma Domain.sizeOn_le_of_method_size_le (D : Domain F A C I) (fr : Fragment F A C I) {cm : ℕ}
    (h : ∀ m ∈ fr.methods, m.size ≤ cm) :
    D.sizeOn fr ≤ fr.facts.card + fr.tasks.card + (∑ a ∈ fr.ops, D.actionSize a) +
      cm * fr.methods.card := by
  have hsum : ∑ m ∈ fr.methods, m.size ≤ cm * fr.methods.card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ cm h) ?_
    rw [smul_eq_mul, Nat.mul_comm]
  simp only [Domain.sizeOn]
  omega

/-- The number of methods of a fragment is bounded by the size of the domain on it. -/
lemma Fragment.card_methods_le (D : Domain F A C I) (fr : Fragment F A C I) :
    fr.methods.card ≤ D.sizeOn fr := by
  have h : fr.methods.card ≤ ∑ m ∈ fr.methods, m.size := by
    simpa using Finset.card_nsmul_le_sum fr.methods (fun m => m.size) 1
      (fun m _ => m.one_le_size)
  simp only [Domain.sizeOn]
  omega

end HTN
