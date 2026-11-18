import HtnPlanning.Core.SizeOn
import HtnPlanning.Binarisation.Binarisation
/-!
# The binarisation is a linear compilation

`HtnPlanning/Binarisation/Binarisation.lean` proves that binarising the methods of a totally ordered
HTN problem preserves and reflects solvability.  What is missing there is the claim of the
source that the binarisation is a *linear* compilation: the compiled domain has infinitely many
compound task names (one per task sequence) and infinitely many methods, so its size cannot be
measured by `HTN.Domain.size`.

Using the fragment-relative measure of `HtnPlanning/Core/SizeOn.lean` this file closes the
gap.  Given

* a *fragment* `fr` of the source signature listing the facts, operators, compound task names
  and methods of the source domain, together with a function `body` returning the (totally
  ordered) body of each of its methods, and
* the initial task sequence `xs₀`,

the compiled domain only ever uses the compound task names `⟨bs⟩` for `bs` a **suffix of a
method body or of the initial task sequence** (`HTN.Bin.tailsOf`), a finite set.  The main
results are

* `HTN.Bin.covers_tailsOf` — this set is adequate in the sense of `HTN.Bin.Covers`, so all the
  correctness results of `HtnPlanning/Binarisation/Binarisation.lean` apply to the binarisation
  restricted to it (`HTN.Bin.solvable_iff_tailsOf`);
* `HTN.Bin.fragment_methods_subset` — the compiled fragment consists of methods of the
  restricted binarised domain;
* `HTN.Bin.sizeOn_fragment_le` — **the compiled domain, measured on the compiled fragment, is
  linear in the size of the source domain** measured on `fr` (and in the length of the initial
  task sequence);
* `HTN.Bin.instance_size_le` — the compiled problem instance is not larger than the source
  instance either.
-/

namespace HTN

universe u v w x

open TaskNetwork

/-! ### Sizes of sequence networks and of their methods -/

variable {A : Type v} {C : Type w} {I : Type x}

/-- The size of a method is bounded by `1 + n + n²`, where `n` is its number of subtasks. -/
lemma Method.size_le (m : Method I A C) :
    m.size ≤ 1 + m.subtasks.T.card + m.subtasks.T.card * m.subtasks.T.card := by
  have := m.subtasks.size_le
  simp only [Method.size]
  omega

/-- The size of a method whose subtask network is a chain of `k` tasks. -/
lemma Method.size_seq_le [Inhabited A] (c : C) (l : List (A ⊕ C)) :
    (Method.mk c (seq l)).size ≤ 1 + l.length + l.length * l.length := by
  have h := (Method.mk c (seq l)).size_le
  simpa using h

/-- The number of subtasks of a method with a totally ordered body is the length of the
body. -/
lemma Method.card_subtasks_of_hasSeqBody {m : Method I A C} {bs : List (A ⊕ C)}
    (h : m.HasSeqBody bs) : m.subtasks.T.card = bs.length := by
  classical
  obtain ⟨l, ⟨hnodup, hmem, -⟩, hmap, -⟩ := h
  have hT : m.subtasks.T = l.toFinset := by
    ext t
    rw [List.mem_toFinset, hmem]
  rw [hT, List.toFinset_card_of_nodup hnodup, ← hmap, List.length_map]

/-- The length of the body of a method is smaller than the size of the method. -/
lemma Method.length_lt_size {m : Method I A C} {bs : List (A ⊕ C)} (h : m.HasSeqBody bs) :
    bs.length + 1 ≤ m.size := by
  have h1 : m.subtasks.T.card = bs.length := Method.card_subtasks_of_hasSeqBody h
  have h2 : m.subtasks.T.card ≤ m.subtasks.size := Nat.le_add_right _ _
  simp only [Method.size]
  omega

namespace Bin

variable {F : Type u} [Inhabited A]

/-! ### The task sequences used by the binarisation -/

open scoped Classical in
/-- The task sequences used by the binarisation of a domain fragment with initial task sequence
`xs₀`: the suffixes of the method bodies and of `xs₀`. -/
noncomputable def tailsOf (body : Method I A C → List (A ⊕ C)) (fr : Fragment F A C I)
    (xs₀ : List (A ⊕ C)) : Finset (List (A ⊕ C)) :=
  xs₀.tails.toFinset ∪ fr.methods.biUnion fun m => (body m).tails.toFinset

variable {body : Method I A C → List (A ⊕ C)} {fr : Fragment F A C I} {xs₀ : List (A ⊕ C)}

omit [Inhabited A] in
open scoped Classical in
lemma mem_tailsOf {bs : List (A ⊕ C)} :
    bs ∈ tailsOf body fr xs₀ ↔ bs <:+ xs₀ ∨ ∃ m ∈ fr.methods, bs <:+ body m := by
  simp [tailsOf, List.mem_tails]

omit [Inhabited A] in
open scoped Classical in
lemma self_mem_tailsOf : xs₀ ∈ tailsOf body fr xs₀ :=
  mem_tailsOf.2 (Or.inl (List.suffix_refl _))

omit [Inhabited A] in
open scoped Classical in
lemma body_mem_tailsOf {m : Method I A C} (hm : m ∈ fr.methods) :
    body m ∈ tailsOf body fr xs₀ :=
  mem_tailsOf.2 (Or.inr ⟨m, hm, List.suffix_refl _⟩)

omit [Inhabited A] in
open scoped Classical in
/-- **The suffixes of the method bodies form an adequate set of task sequences**, so all the
correctness results about the restricted binarisation apply to it. -/
theorem covers_tailsOf {D : Domain F A C I} (hfr : (fr.methods : Set (Method I A C)) = D.methods)
    (hwf : ∀ m ∈ D.methods, m.subtasks.WF) (hbody : ∀ m ∈ fr.methods, m.HasSeqBody (body m)) :
    Covers D (tailsOf body fr xs₀ : Set (List (A ⊕ C))) where
  nil := by
    exact Finset.mem_coe.2 (mem_tailsOf.2 (Or.inl List.nil_suffix))
  tail := by
    intro x bs h
    rcases mem_tailsOf.1 (Finset.mem_coe.1 h) with h | ⟨m, hm, h⟩
    · exact Finset.mem_coe.2 (mem_tailsOf.2 (Or.inl ((List.suffix_cons x bs).trans h)))
    · exact Finset.mem_coe.2 (mem_tailsOf.2 (Or.inr ⟨m, hm, (List.suffix_cons x bs).trans h⟩))
  body := by
    rintro c bs ⟨m, hm, -, hb⟩
    have hmfr : m ∈ fr.methods := by
      have : m ∈ (fr.methods : Set (Method I A C)) := by rw [hfr]; exact hm
      exact this
    have hbs : bs = body m :=
      (Method.hasSeqBody_iff_of_isSeqNet
        (Method.exists_isSeqNet_of_hasSeqBody (hwf m hm) (hbody m hmfr)).choose_spec).1 hb
    rw [hbs]
    exact Finset.mem_coe.2 (body_mem_tailsOf hmfr)

omit [Inhabited A] in
/-- The number of task sequences used by the binarisation is bounded by the size of the source
domain plus the length of the initial task sequence. -/
theorem card_tailsOf_le (D : Domain F A C I) (hbody : ∀ m ∈ fr.methods, m.HasSeqBody (body m)) :
    (tailsOf body fr xs₀).card ≤ xs₀.length + 1 + D.sizeOn fr := by
  classical
  have h₁ : (tailsOf body fr xs₀).card ≤
      xs₀.tails.toFinset.card + (fr.methods.biUnion fun m => (body m).tails.toFinset).card :=
    Finset.card_union_le _ _
  have h₂ : xs₀.tails.toFinset.card ≤ xs₀.length + 1 := by
    simpa using List.toFinset_card_le xs₀.tails
  have h₃ : (fr.methods.biUnion fun m => (body m).tails.toFinset).card ≤
      ∑ m ∈ fr.methods, ((body m).length + 1) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro m _
    simpa using List.toFinset_card_le (body m).tails
  have h₄ : ∑ m ∈ fr.methods, ((body m).length + 1) ≤ ∑ m ∈ fr.methods, m.size :=
    Finset.sum_le_sum fun m hm => Method.length_lt_size (hbody m hm)
  have h₅ : ∑ m ∈ fr.methods, m.size ≤ D.sizeOn fr := by
    simp only [Domain.sizeOn]; omega
  omega

/-! ### The fragment of the binarised domain -/

open scoped Classical in
/-- The fragment of the binarised signature that the binarisation of `fr` uses: the same facts
and operators, the compound task names of `fr` and one name per used task sequence, and the
methods of the binarisation. -/
noncomputable def fragment (body : Method I A C → List (A ⊕ C)) (fr : Fragment F A C I)
    (xs₀ : List (A ⊕ C)) : Fragment F A (Name A C) (ℕ × ℕ) where
  facts := fr.facts
  ops := fr.ops
  tasks := fr.tasks.image Sum.inl ∪ (tailsOf body fr xs₀).image Sum.inr
  methods := fr.methods.image
      (fun m => ⟨Sum.inl m.abstractTask, seq [Sum.inr (Sum.inr (body m))]⟩) ∪
    (tailsOf body fr xs₀).image methodOf

open scoped Classical in
/-- **The methods of the compiled fragment are methods of the restricted binarised domain.** -/
theorem fragment_methods_subset {D : Domain F A C I}
    (hfr : (fr.methods : Set (Method I A C)) = D.methods)
    (hbody : ∀ m ∈ fr.methods, m.HasSeqBody (body m)) :
    ((fragment body fr xs₀).methods : Set (Method (ℕ × ℕ) A (Name A C))) ⊆
      methodsOn D (tailsOf body fr xs₀ : Set (List (A ⊕ C))) := by
  intro m' hm'
  simp only [fragment, Finset.coe_union, Set.mem_union, Finset.coe_image, Set.mem_image,
    Finset.mem_coe] at hm'
  rcases hm' with ⟨m, hm, rfl⟩ | ⟨bs, hbs, rfl⟩
  · refine Or.inl ⟨m.abstractTask, body m, ⟨m, ?_, rfl, hbody m hm⟩, ?_, rfl⟩
    · rw [← hfr]; exact hm
    · exact Finset.mem_coe.2 (body_mem_tailsOf hm)
  · exact Or.inr ⟨bs, Finset.mem_coe.2 hbs, rfl⟩

open scoped Classical in
@[simp] lemma fragment_facts : (fragment body fr xs₀).facts = fr.facts := rfl

open scoped Classical in
@[simp] lemma fragment_ops : (fragment body fr xs₀).ops = fr.ops := rfl

open scoped Classical in
lemma fragment_tasks : (fragment body fr xs₀).tasks =
    fr.tasks.image Sum.inl ∪ (tailsOf body fr xs₀).image Sum.inr := rfl

open scoped Classical in
lemma fragment_methods : (fragment body fr xs₀).methods =
    fr.methods.image
      (fun m => (⟨Sum.inl m.abstractTask, seq [Sum.inr (Sum.inr (body m))]⟩ :
        Method (ℕ × ℕ) A (Name A C))) ∪
    (tailsOf body fr xs₀).image (methodOf (A := A) (C := C)) := rfl

open scoped Classical in
/-- The methods `⟨c⟩ ↦ ⟨bs⟩` of the binarisation have size at most three. -/
lemma sum_size_image_le :
    ∑ m' ∈ fr.methods.image
      (fun m => (⟨Sum.inl m.abstractTask, seq [Sum.inr (Sum.inr (body m))]⟩ :
        Method (ℕ × ℕ) A (Name A C))), m'.size ≤ 3 * fr.methods.card := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ 3 ?_) ?_
  · intro m' hm'
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hm'
    simpa using Method.size_seq_le (Sum.inl m.abstractTask)
      [(Sum.inr (Sum.inr (body m)) : A ⊕ Name A C)]
  · rw [smul_eq_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left 3 (Finset.card_image_le (s := fr.methods)
      (f := fun m => (⟨Sum.inl m.abstractTask, seq [Sum.inr (Sum.inr (body m))]⟩ :
        Method (ℕ × ℕ) A (Name A C))))

open scoped Classical in
/-- The methods `⟨x bs⟩ ↦ x ⟨bs⟩` of the binarisation have size at most seven. -/
lemma sum_size_image_methodOf_le (T : Finset (List (A ⊕ C))) :
    ∑ m' ∈ T.image (methodOf (A := A) (C := C)), m'.size ≤ 7 * T.card := by
  refine le_trans (Finset.sum_le_card_nsmul _ _ 7 ?_) ?_
  · intro m' hm'
    obtain ⟨bs, -, rfl⟩ := Finset.mem_image.1 hm'
    cases bs with
    | nil =>
        have h := Method.size_seq_le (Sum.inr ([] : List (A ⊕ C)))
          ([] : List (A ⊕ Name A C))
        norm_num at h
        simp only [methodOf]
        omega
    | cons x bs =>
        have := Method.size_seq_le (Sum.inr (x :: bs))
          [emb x, (Sum.inr (Sum.inr bs) : A ⊕ Name A C)]
        simpa [methodOf] using this
  · rw [smul_eq_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left 7
      (Finset.card_image_le (s := T) (f := methodOf (A := A) (C := C)))

open scoped Classical in
/-- **The binarisation is a linear compilation.**  Measured on the fragment it actually uses,
the binarised domain is at most `12 ‖D‖ + 8 |xs₀| + 8` large, where `‖D‖` is the size of the
source domain measured on the source fragment. -/
theorem sizeOn_fragment_le (D : Domain F A C I) (S : Set (List (A ⊕ C)))
    (hbody : ∀ m ∈ fr.methods, m.HasSeqBody (body m)) :
    (domainOn D S).sizeOn (fragment body fr xs₀) ≤
      12 * D.sizeOn fr + 8 * xs₀.length + 8 := by
  -- the number of compound task names
  have htasks : (fragment body fr xs₀).tasks.card ≤
      fr.tasks.card + (tailsOf body fr xs₀).card := by
    rw [fragment_tasks]
    exact le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  -- the sizes of the methods
  have hmeth : ∑ m' ∈ (fragment body fr xs₀).methods, m'.size ≤
      3 * fr.methods.card + 7 * (tailsOf body fr xs₀).card := by
    have hunion := Finset.sum_union_inter
      (s₁ := fr.methods.image
        (fun m => (⟨Sum.inl m.abstractTask, seq [Sum.inr (Sum.inr (body m))]⟩ :
          Method (ℕ × ℕ) A (Name A C))))
      (s₂ := (tailsOf body fr xs₀).image (methodOf (A := A) (C := C))) (f := Method.size)
    have h1 := sum_size_image_le (body := body) (fr := fr)
    have h2 := sum_size_image_methodOf_le (tailsOf body fr xs₀)
    rw [fragment_methods]
    omega
  -- the operators are unchanged
  have hops : ∑ a ∈ fr.ops, (domainOn D S).actionSize a = ∑ a ∈ fr.ops, D.actionSize a := rfl
  have hcard : fr.methods.card ≤ D.sizeOn fr := Fragment.card_methods_le D fr
  have hTcard : (tailsOf body fr xs₀).card ≤ xs₀.length + 1 + D.sizeOn fr :=
    card_tailsOf_le D hbody
  have hfacts : fr.facts.card + fr.tasks.card + ∑ a ∈ fr.ops, D.actionSize a ≤ D.sizeOn fr := by
    simp only [Domain.sizeOn]; omega
  rw [Domain.sizeOn, fragment_facts, fragment_ops, hops]
  omega

/-- **The binarisation preserves and reflects solvability, using only the suffixes of the
method bodies as new compound task names.** -/
theorem solvable_iff_tailsOf [DecidableEq I] [Infinite I] {P : Problem F A C I} (hwf : P.WF)
    (hto : P.IsTO_M) (hfr : (fr.methods : Set (Method I A C)) = P.methods)
    (hbody : ∀ m ∈ fr.methods, m.HasSeqBody (body m)) {l₀ : List I}
    (h₀ : P.tnI.IsSeqNet l₀ xs₀) :
    (problemOn P xs₀ (tailsOf body fr xs₀ : Set (List (A ⊕ C)))).Solvable ↔ P.Solvable := by
  classical
  refine solvableOn_iff hwf hto (covers_tailsOf hfr (fun m hm => hwf.methods m hm) hbody) ?_ h₀
  exact Finset.mem_coe.2 self_mem_tailsOf

/-! ### The size of the compiled problem instance -/

/-- The compiled problem instance — the single initial task `⟨xs₀⟩` — is not larger than the
source instance. -/
theorem instance_size_le (Q : Instance F A C I) :
    (Instance.mk Q.init Q.goal (seq [Sum.inr (Sum.inr xs₀)]) :
      Instance F A (Name A C) (ℕ × ℕ)).size ≤ Q.size + 2 := by
  have h : (seq [(Sum.inr (Sum.inr xs₀) : A ⊕ Name A C)]).size ≤ 2 := by
    have := (seq [(Sum.inr (Sum.inr xs₀) : A ⊕ Name A C)]).size_le
    simpa using this
  simp only [Instance.size]
  omega

end Bin

end HTN
