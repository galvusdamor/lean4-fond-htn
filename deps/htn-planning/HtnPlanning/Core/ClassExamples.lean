import HtnPlanning.Core.ClassHierarchy
/-!
# Examples separating the HTN problem classes

The inclusions proved in `HtnPlanning/Core/ClassHierarchy.lean` are all strict, and the
classes `REG` and `ACYC` / `MOSTLY-ACYC` are incomparable.  This file provides the witnessing
example problems and proves the corresponding statements of Section 3 of Bercher et al.:

* `noHTN ⊊ REG` and `noHTN ⊊ ACYC`  (Def. 3.3, "Because regular problems allow for compound
  tasks, we get noHTN ⊊ REG");
* `ACYC ∩ REG ≠ ∅`, `ACYC ⊉ REG`, `REG ⊉ ACYC`;
* `MOSTLY-ACYC ⊋ ACYC`;
* `TAIL-REC ⊋ MOSTLY-ACYC` and `TAIL-REC ⊋ REG`;
* `UNRES-REC ⊋ TAIL-REC`;
* `HTN ⊋ TO-HTN`.

All examples use `Unit` as the set of facts and actions (their state-space part is irrelevant
for the structural restrictions), natural numbers as task identifiers, and `Unit` or `Bool` as
compound task names.
-/

namespace HTN

namespace Examples

/-! ### Small task networks used by the examples -/

variable {A C : Type}

/-- The task network consisting of a single task labelled `v`. -/
def tnSingle (v : A ⊕ C) : TaskNetwork ℕ A C where
  T := {0}
  ord := fun _ _ => False
  α := fun _ => v

/-- The task network consisting of two tasks labelled `v` and `w`, with `v` ordered before
`w`. -/
def tnPairOrd (v w : A ⊕ C) : TaskNetwork ℕ A C where
  T := {0, 1}
  ord := fun a b => a = 0 ∧ b = 1
  α := fun i => if i = 0 then v else w

/-- The task network consisting of two unordered tasks labelled `v` and `w`. -/
def tnPairUnord (v w : A ⊕ C) : TaskNetwork ℕ A C where
  T := {0, 1}
  ord := fun _ _ => False
  α := fun i => if i = 0 then v else w

/-- The empty task network over `ℕ`. -/
def tnEmpty [Inhabited A] : TaskNetwork ℕ A C where
  T := ∅
  ord := fun _ _ => False
  α := fun _ => Sum.inl default

lemma tnSingle_wf (v : A ⊕ C) : (tnSingle v).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma tnPairOrd_wf (v w : A ⊕ C) : (tnPairOrd v w).WF where
  mem_left := by rintro a b ⟨rfl, -⟩; simp [tnPairOrd]
  mem_right := by rintro a b ⟨-, rfl⟩; simp [tnPairOrd]
  irrefl := by rintro a ⟨rfl, h⟩; exact absurd h (by simp)
  trans := by rintro a b c ⟨rfl, rfl⟩ ⟨h, -⟩; exact absurd h (by simp)

lemma tnPairUnord_wf (v w : A ⊕ C) : (tnPairUnord v w).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

lemma tnEmpty_wf [Inhabited A] : (tnEmpty (A := A) (C := C)).WF where
  mem_left := fun h => h.elim
  mem_right := fun h => h.elim
  irrefl := fun _ h => h
  trans := fun h _ => h.elim

/-- A no-op planning problem over `Unit` facts and actions, given by its initial task network
and its set of methods. -/
def mkProblem (tnI : TaskNetwork ℕ Unit C) (M : Set (Method ℕ Unit C)) :
    Problem Unit Unit C ℕ where
  prec := fun _ => ∅
  add := fun _ => ∅
  del := fun _ => ∅
  methods := M
  init := ∅
  goal := ∅
  tnI := tnI

@[simp] lemma mkProblem_tnI (tnI : TaskNetwork ℕ Unit C) (M : Set (Method ℕ Unit C)) :
    (mkProblem tnI M).tnI = tnI := rfl

@[simp] lemma mkProblem_methods (tnI : TaskNetwork ℕ Unit C) (M : Set (Method ℕ Unit C)) :
    (mkProblem tnI M).methods = M := rfl

/-- Every problem built by `mkProblem` has only no-op actions. -/
lemma mkProblem_isNoop (tnI : TaskNetwork ℕ Unit C) (M : Set (Method ℕ Unit C)) :
    (mkProblem tnI M).IsNoop := fun _ => ⟨rfl, rfl, rfl⟩

/-! ### The example problems -/

/-- `Prec`: a single compound task that can be decomposed into nothing.  It is regular and
acyclic, but has a hierarchy. -/
def Ptrivial : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnEmpty⟩}

/-- `Preg`: the regular but recursive problem `c ↦ a c`. -/
def Preg : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnPairOrd (Sum.inl ()) (Sum.inr ())⟩}

/-- `Pac`: the acyclic but non-regular problem `true ↦ false false`. -/
def Pac : Problem Unit Unit Bool ℕ :=
  mkProblem (tnSingle (Sum.inr true)) {⟨true, tnPairOrd (Sum.inr false) (Sum.inr false)⟩}

/-- `Pmostly`: the mostly-acyclic but not acyclic problem `true ↦ false`, `false ↦ true`. -/
def Pmostly : Problem Unit Unit Bool ℕ :=
  mkProblem (tnSingle (Sum.inr true))
    {⟨true, tnSingle (Sum.inr false)⟩, ⟨false, tnSingle (Sum.inr true)⟩}

/-- `Pnontr`: the problem `c ↦ c a`, whose recursion goes through a non-last task, so it is not
tail-recursive. -/
def Pnontr : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnPairOrd (Sum.inr ()) (Sum.inl ())⟩}

/-- `Pnonto`: the problem `c ↦ {a, a}` with an unordered method, which is regular but not
totally ordered. -/
def Pnonto : Problem Unit Unit Unit ℕ :=
  mkProblem (tnSingle (Sum.inr ())) {⟨(), tnPairUnord (Sum.inl ()) (Sum.inl ())⟩}

/-! ### Well-formedness -/

lemma Ptrivial_wf : Ptrivial.WF where
  tnI := tnSingle_wf _
  methods := by rintro m hm; simp only [Ptrivial, mkProblem_methods, Set.mem_singleton_iff] at hm
                subst hm; exact tnEmpty_wf

lemma Preg_wf : Preg.WF where
  tnI := tnSingle_wf _
  methods := by rintro m hm; simp only [Preg, mkProblem_methods, Set.mem_singleton_iff] at hm
                subst hm; exact tnPairOrd_wf _ _

lemma Pac_wf : Pac.WF where
  tnI := tnSingle_wf _
  methods := by rintro m hm; simp only [Pac, mkProblem_methods, Set.mem_singleton_iff] at hm
                subst hm; exact tnPairOrd_wf _ _

lemma Pmostly_wf : Pmostly.WF where
  tnI := tnSingle_wf _
  methods := by
    rintro m hm
    simp only [Pmostly, mkProblem_methods, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl <;> exact tnSingle_wf _

lemma Pnontr_wf : Pnontr.WF where
  tnI := tnSingle_wf _
  methods := by rintro m hm; simp only [Pnontr, mkProblem_methods, Set.mem_singleton_iff] at hm
                subst hm; exact tnPairOrd_wf _ _

/-! ### Reachability in the examples -/

lemma reachable_root {C : Type} (c : C) (M : Set (Method ℕ Unit C)) :
    (mkProblem (tnSingle (Sum.inr c)) M).ReachableName c :=
  Problem.ReachableName.tnI (t := 0) (by simp [tnSingle]) rfl

/-! ### The example problems are not without hierarchy -/

lemma Ptrivial_not_noHTN : ¬ Ptrivial.IsNoHTN := by
  intro h
  obtain ⟨a, ha⟩ := h 0 (by simp [Ptrivial, mkProblem, tnSingle])
  exact absurd ha (by simp [Ptrivial, mkProblem, tnSingle])

/-! ### `Ptrivial` is regular and acyclic -/

lemma Ptrivial_isRegular : Ptrivial.IsRegular := by
  refine ⟨TaskNetwork.isRegular_of_T_eq_singleton (t := 0) rfl, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [Ptrivial, mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  exact TaskNetwork.IsPrimitive.isRegular (by intro t ht; simp [tnEmpty] at ht)

lemma Ptrivial_isAcyclic : Ptrivial.IsAcyclic := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, ?_, ?_⟩⟩
  · rintro ⟨⟩ ⟨⟩ - - - -; rfl
  · rintro m ⟨hm, -⟩
    simp only [Ptrivial, mkProblem_methods, Set.mem_singleton_iff] at hm
    subst hm
    intro t ht
    simp [tnEmpty] at ht

/-! ### `Preg` is regular (hence tail-recursive) but not mostly-acyclic -/

lemma Preg_isRegular : Preg.IsRegular := by
  refine ⟨TaskNetwork.isRegular_of_T_eq_singleton (t := 0) rfl, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [Preg, mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  constructor
  · rintro t ht t' ht' ⟨c, hc⟩ ⟨c', hc'⟩
    simp only [tnPairOrd, Finset.mem_insert, Finset.mem_singleton] at ht ht'
    rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl <;> simp_all [tnPairOrd]
  · rintro t ht ⟨c, hc⟩ t' ht' hne
    simp only [tnPairOrd, Finset.mem_insert, Finset.mem_singleton] at ht ht'
    rcases ht with rfl | rfl
    · simp [tnPairOrd] at hc
    · rcases ht' with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · exact absurd rfl hne

lemma Preg_isTailRecursive : Preg.IsTailRecursive := Preg_isRegular.isTailRecursive

lemma Preg_not_isMostlyAcyclic : ¬ Preg.IsMostlyAcyclic := by
  rintro ⟨le, hle⟩
  have hm : Preg.ReachableMethod ⟨(), tnPairOrd (Sum.inl ()) (Sum.inr ())⟩ :=
    ⟨by simp [Preg], reachable_root _ _⟩
  have hcard : 1 < (tnPairOrd (Sum.inl ()) (Sum.inr ()) : TaskNetwork ℕ Unit Unit).T.card := by
    decide
  obtain ⟨h₁, h₂⟩ := hle.big _ hm hcard 1 (by simp [tnPairOrd]) () (by simp [tnPairOrd])
  exact h₂ h₁

lemma Preg_not_isAcyclic : ¬ Preg.IsAcyclic := fun h => Preg_not_isMostlyAcyclic h.isMostlyAcyclic

/-! ### `Pac` is acyclic but not regular -/

lemma Pac_isAcyclic : Pac.IsAcyclic := by
  classical
  refine ⟨fun x y => x = y ∨ (x = false ∧ y = true), ⟨⟨fun _ _ => Or.inl rfl, ?_, ?_⟩, ?_, ?_⟩⟩
  · intro c₁ c₂ c₃ h₁ h₂ h₃; clear h₁ h₂ h₃; revert c₁ c₂ c₃; decide
  · intro c₁ c₂ h₁ h₂; clear h₁ h₂; revert c₁ c₂; decide
  · intro c₁ c₂ h₁ h₂; clear h₁ h₂; revert c₁ c₂; decide
  · rintro m ⟨hm, -⟩
    simp only [Pac, mkProblem_methods, Set.mem_singleton_iff] at hm
    subst hm
    intro t ht c hc
    have : c = false := by
      simp only [tnPairOrd, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simpa [tnPairOrd] using hc.symm
    subst this
    exact ⟨Or.inr ⟨rfl, rfl⟩, by simp⟩

lemma Pac_not_isRegular : ¬ Pac.IsRegular := by
  intro h
  have hm : Pac.ReachableMethod ⟨true, tnPairOrd (Sum.inr false) (Sum.inr false)⟩ :=
    ⟨by simp [Pac], reachable_root _ _⟩
  have h0 : (0 : ℕ) = 1 :=
    (h.2 _ hm).1 0 (by simp [tnPairOrd]) 1 (by simp [tnPairOrd])
      ⟨false, by simp [tnPairOrd]⟩ ⟨false, by simp [tnPairOrd]⟩
  exact absurd h0 (by decide)

/-! ### `Pmostly` is mostly-acyclic but not acyclic -/

lemma Pmostly_isMostlyAcyclic : Pmostly.IsMostlyAcyclic := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, ?_, fun _ _ _ _ _ _ _ => trivial⟩⟩
  rintro m ⟨hm, -⟩ hcard
  simp only [Pmostly, mkProblem_methods, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl <;> exact absurd hcard (by decide +kernel)

lemma Pmostly_not_isAcyclic : ¬ Pmostly.IsAcyclic := by
  rintro ⟨le, hle⟩
  have hmt : Pmostly.ReachableMethod ⟨true, tnSingle (Sum.inr false)⟩ :=
    ⟨by simp [Pmostly], reachable_root _ _⟩
  have hfalse : Pmostly.ReachableName false :=
    Problem.ReachableName.method (m := ⟨true, tnSingle (Sum.inr false)⟩) (t := 0)
      (by simp [Pmostly]) (reachable_root _ _) (by simp [tnSingle]) rfl
  have hmf : Pmostly.ReachableMethod ⟨false, tnSingle (Sum.inr true)⟩ :=
    ⟨by simp [Pmostly], hfalse⟩
  obtain ⟨h₁, -⟩ := hle.decreasing _ hmt 0 (by simp [tnSingle]) false rfl
  obtain ⟨-, h₂⟩ := hle.decreasing _ hmf 0 (by simp [tnSingle]) true rfl
  exact h₂ h₁

/-! ### `Pnontr` is not tail-recursive -/

lemma Pnontr_not_isTailRecursive : ¬ Pnontr.IsTailRecursive := by
  rintro ⟨le, hle⟩
  have hm : Pnontr.ReachableMethod ⟨(), tnPairOrd (Sum.inr ()) (Sum.inl ())⟩ :=
    ⟨by simp [Pnontr], reachable_root _ _⟩
  have hnl : ¬ (tnPairOrd (Sum.inr ()) (Sum.inl ()) : TaskNetwork ℕ Unit Unit).IsLastId 0 := by
    rintro ⟨-, h⟩
    have := h 1 (by simp [tnPairOrd]) (by decide)
    simp [tnPairOrd] at this
  obtain ⟨h₁, h₂⟩ := hle.nonlast _ hm 0 (by simp [tnPairOrd]) hnl () (by simp [tnPairOrd])
  exact h₂ h₁

/-! ### `Pnonto` is regular but not totally ordered -/

lemma Pnonto_isRegular : Pnonto.IsRegular := by
  refine ⟨TaskNetwork.isRegular_of_T_eq_singleton (t := 0) rfl, ?_⟩
  rintro m ⟨hm, -⟩
  simp only [Pnonto, mkProblem_methods, Set.mem_singleton_iff] at hm
  subst hm
  refine TaskNetwork.IsPrimitive.isRegular ?_
  intro t ht
  simp only [tnPairUnord, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl <;> exact ⟨(), rfl⟩

lemma Pnonto_not_isTO : ¬ Pnonto.IsTO := by
  rintro ⟨-, hTO⟩
  have hm : Pnonto.ReachableMethod ⟨(), tnPairUnord (Sum.inl ()) (Sum.inl ())⟩ :=
    ⟨by simp [Pnonto], reachable_root _ _⟩
  rcases hTO _ hm 0 (by simp [tnPairUnord]) 1 (by simp [tnPairUnord]) (by decide) with h | h <;>
    exact h

/-! ### A problem with a genuine precondition (not a no-op problem) -/

/-- `Pprec`: a problem with a primitive initial task network whose action has a nonempty
precondition, hence not a no-op problem. -/
def Pprec : Problem Unit Unit Unit ℕ where
  prec := fun _ => Set.univ
  add := fun _ => ∅
  del := fun _ => ∅
  methods := ∅
  init := ∅
  goal := ∅
  tnI := tnSingle (Sum.inl ())

lemma Pprec_not_isNoop : ¬ Pprec.IsNoop := by
  intro h
  have := (h ()).1
  simp only [Pprec] at this
  exact absurd (this ▸ Set.mem_univ ()) (by simp)

lemma Pprec_isTO : Pprec.IsTO := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hne
    simp only [Pprec, tnSingle, Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hne
  · rintro m ⟨hm, -⟩
    exact absurd hm (by simp [Pprec])

/-! ### `Pnonto` is acyclic and tail-recursive, but not totally ordered -/

lemma Pnonto_isAcyclic : Pnonto.IsAcyclic := by
  refine ⟨fun _ _ => True, ⟨⟨fun _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ => Or.inl trivial⟩, ?_, ?_⟩⟩
  · rintro ⟨⟩ ⟨⟩ - - - -; rfl
  · rintro m ⟨hm, -⟩
    simp only [Pnonto, mkProblem_methods, Set.mem_singleton_iff] at hm
    subst hm
    intro t ht c hc
    simp only [tnPairUnord, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [tnPairUnord] at hc

lemma Pnonto_isTailRecursive : Pnonto.IsTailRecursive := Pnonto_isRegular.isTailRecursive

/-! ### The separation statements -/

namespace Classes

open HTN.Classes

/-- `noHTN ⊊ REG`. -/
theorem noHTN_ssubset_HTN_REG :
    noHTN Unit Unit Unit ℕ ⊂ HTN_REG Unit Unit Unit ℕ :=
  ⟨noHTN_subset_HTN_REG, fun h => Ptrivial_not_noHTN (h Ptrivial_isRegular)⟩

/-- `noHTN ⊊ ACYC`. -/
theorem noHTN_ssubset_HTN_AC :
    noHTN Unit Unit Unit ℕ ⊂ HTN_AC Unit Unit Unit ℕ :=
  ⟨noHTN_subset_HTN_AC, fun h => Ptrivial_not_noHTN (h Ptrivial_isAcyclic)⟩

/-- `ACYC ∩ REG ≠ ∅`. -/
theorem HTN_AC_inter_HTN_REG_nonempty :
    (HTN_AC Unit Unit Unit ℕ ∩ HTN_REG Unit Unit Unit ℕ).Nonempty :=
  ⟨Ptrivial, Ptrivial_isAcyclic, Ptrivial_isRegular⟩

/-- `REG ⊄ ACYC`: there are regular problems that are not acyclic. -/
theorem HTN_REG_not_subset_HTN_AC :
    ¬ HTN_REG Unit Unit Unit ℕ ⊆ HTN_AC Unit Unit Unit ℕ :=
  fun h => Preg_not_isAcyclic (h Preg_isRegular)

/-- `ACYC ⊄ REG`: there are acyclic problems that are not regular. -/
theorem HTN_AC_not_subset_HTN_REG :
    ¬ HTN_AC Unit Unit Bool ℕ ⊆ HTN_REG Unit Unit Bool ℕ :=
  fun h => Pac_not_isRegular (h Pac_isAcyclic)

/-- `ACYC ⊊ MOSTLY-ACYC`. -/
theorem HTN_AC_ssubset_MOSTLY_ACYC :
    HTN_AC Unit Unit Bool ℕ ⊂ MOSTLY_ACYC Unit Unit Bool ℕ :=
  ⟨HTN_AC_subset_MOSTLY_ACYC, fun h => Pmostly_not_isAcyclic (h Pmostly_isMostlyAcyclic)⟩

/-- `MOSTLY-ACYC ⊊ TAIL-REC`. -/
theorem MOSTLY_ACYC_ssubset_HTN_TR :
    MOSTLY_ACYC Unit Unit Unit ℕ ⊂ HTN_TR Unit Unit Unit ℕ :=
  ⟨MOSTLY_ACYC_subset_HTN_TR, fun h => Preg_not_isMostlyAcyclic (h Preg_isTailRecursive)⟩

/-- `REG ⊊ TAIL-REC`. -/
theorem HTN_REG_ssubset_HTN_TR :
    HTN_REG Unit Unit Bool ℕ ⊂ HTN_TR Unit Unit Bool ℕ := by
  refine ⟨HTN_REG_subset_HTN_TR, fun h => Pac_not_isRegular (h ?_)⟩
  exact Pac_isAcyclic.isTailRecursive

/-- `TAIL-REC ⊊ HTN`. -/
theorem HTN_TR_ssubset_HTN :
    HTN_TR Unit Unit Unit ℕ ⊂ HTN Unit Unit Unit ℕ :=
  ⟨HTN_TR_subset_HTN, fun h => Pnontr_not_isTailRecursive (h (show Pnontr ∈ HTN Unit Unit Unit ℕ from trivial))⟩

/-- `TO-HTN ⊊ HTN`. -/
theorem TO_HTN_ssubset_HTN :
    TO_HTN Unit Unit Unit ℕ ⊂ HTN Unit Unit Unit ℕ :=
  ⟨TO_HTN_subset_HTN, fun h => Pnonto_not_isTO (h (show Pnonto ∈ HTN Unit Unit Unit ℕ from trivial))⟩

/-- `HTN-NOOP ⊊ HTN`. -/
theorem HTN_NOOP_ssubset_HTN :
    HTN_NOOP Unit Unit Unit ℕ ⊂ HTN Unit Unit Unit ℕ :=
  ⟨HTN_NOOP_subset_HTN,
    fun h => Pprec_not_isNoop (h (show Pprec ∈ HTN Unit Unit Unit ℕ from trivial))⟩

/-- `TO-HTN-NOOP ⊊ TO-HTN`. -/
theorem TO_HTN_NOOP_ssubset_TO_HTN :
    TO_HTN_NOOP Unit Unit Unit ℕ ⊂ TO_HTN Unit Unit Unit ℕ :=
  ⟨TO_HTN_NOOP_subset_TO_HTN, fun h => Pprec_not_isNoop (h Pprec_isTO).2⟩

/-- `TO-HTN-NOOP ⊊ HTN-NOOP`. -/
theorem TO_HTN_NOOP_ssubset_HTN_NOOP :
    TO_HTN_NOOP Unit Unit Unit ℕ ⊂ HTN_NOOP Unit Unit Unit ℕ :=
  ⟨TO_HTN_NOOP_subset_HTN_NOOP,
    fun h => Pnonto_not_isTO (h (mkProblem_isNoop _ _)).1⟩

/-- `TO-HTN-REG ⊊ HTN-REG`. -/
theorem TO_HTN_REG_ssubset_HTN_REG :
    TO_HTN_REG Unit Unit Unit ℕ ⊂ HTN_REG Unit Unit Unit ℕ :=
  ⟨TO_HTN_REG_subset_HTN_REG, fun h => Pnonto_not_isTO (h Pnonto_isRegular).1⟩

/-- `TO-HTN-AC ⊊ HTN-AC`. -/
theorem TO_HTN_AC_ssubset_HTN_AC :
    TO_HTN_AC Unit Unit Unit ℕ ⊂ HTN_AC Unit Unit Unit ℕ :=
  ⟨TO_HTN_AC_subset_HTN_AC, fun h => Pnonto_not_isTO (h Pnonto_isAcyclic).1⟩

/-- `TO-HTN-TR ⊊ HTN-TR`. -/
theorem TO_HTN_TR_ssubset_HTN_TR :
    TO_HTN_TR Unit Unit Unit ℕ ⊂ HTN_TR Unit Unit Unit ℕ :=
  ⟨TO_HTN_TR_subset_HTN_TR, fun h => Pnonto_not_isTO (h Pnonto_isTailRecursive).1⟩

end Classes

end Examples

end HTN
