import HtnComplexity.Complexity.AutFamily
/-!
# Alternation: a hardness family whose fixed part is an *alternating* machine

`HtnComplexity/Complexity/AutFamily.lean` puts a nondeterministic finite automaton into the
fixed domain description: a refinement of the root task is a *run*, i.e. a single sequence of
configurations, because every method body contains at most one compound task.  The hardness
constructions of the literature for the classes `HTN-TR` and `HTN-AC` use **alternation** — a
configuration may branch universally, and *all* of its successors have to accept — and the note
in `NOTES.md` §5.5(1) records that as the missing shape.

This file supplies it.  The machine is an **alternating finite automaton over the bit alphabet**
(`HTN.Syn.BitAlt`): besides the existential transitions `(q, b, q')` of `BitAut` it has universal
transitions `(q, b, q₁, q₂)`, and

    M.AccFrom q (b :: v)

holds if *some* existential transition leads to a state accepting `v`, or *some* universal
transition leads to a pair of states which **both** accept `v`.

The encoding keeps the instance encoder `HTN.Syn.posEnc` of
`HtnComplexity/Complexity/PosFamily.lean` unchanged — the initial task network is the single
compound task `0`, the input is read from the initial state — and adds one intermediate compound
task per universal transition:

    altName M n (k+1) q  ⟶  aName k b · altName M n k q'          (existential transition)
    altName M n (k+1) q  ⟶  aName k b · brName M n k q₁ q₂        (universal transition)
    brName M n k q₁ q₂   ⟶  altName M n k q₁ · altName M n k q₂   (the universal branching)

The branching method is what carries alternation: both branches occur in the body, so both have
to be refined, and — because the guard actions `aName k b` of `HTN.Syn.autActions` have **no
effect** — both see the same state, namely the encoded input.  This is why the branching may be
written as an *ordered* body: a universal branch is not a parallel process here but a second
inspection of the same immutable input, so the domain stays totally ordered and the family stays
in all three source classes of the eight open cells.

The rank of `altName M n k q` is `3k` and the rank of `brName M n k q₁ q₂` is `3k + 1`, so the
domain is acyclic; it has `n · (|ex| + 2|un|) + |accept|` methods and `2n` actions, i.e. size
linear in `n`, and is primitive recursive in `n`.  The correctness statement is

    HTN.Syn.solvable_altDom_iff : Solvable (altDom M w.length) (posEnc w) ↔ M.Accepts w

and hence `HTN.Syn.altFamily M : Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root M.Accepts`,
transported to `TO-HTN`, `HTN-TR` and `HTN-AC`.  Every nondeterministic automaton is an
alternating one with no universal transitions (`HTN.Syn.BitAlt.ofAut`), so this family subsumes
`HTN.Syn.autFamily`.
-/

namespace HTN

namespace Syn

open Binarise

/-! ### Alternating automata over the bit alphabet -/

/-- An **alternating finite automaton over the alphabet `Bool`**: an initial state, a list of
accepting states, a list of existential transitions `(source, bit, target)` and a list of
universal transitions `(source, bit, target₁, target₂)`.  States are natural numbers; only the
finitely many mentioned in the lists matter. -/
structure BitAlt where
  /-- The initial state. -/
  start : ℕ
  /-- The accepting states. -/
  accept : List ℕ
  /-- The existential transitions `(source, bit, target)`. -/
  ex : List (ℕ × Bool × ℕ)
  /-- The universal transitions `(source, bit, target₁, target₂)`. -/
  un : List (ℕ × Bool × ℕ × ℕ)

namespace BitAlt

/-- **Acceptance of a word from a state.**  An existential transition needs one accepting
successor, a universal transition needs both. -/
inductive AccFrom (M : BitAlt) : ℕ → List Bool → Prop
  /-- The empty word is accepted from an accepting state. -/
  | nil {q : ℕ} (h : q ∈ M.accept) : AccFrom M q []
  /-- An existential transition consumes the first bit. -/
  | ex {q : ℕ} {b : Bool} {q' : ℕ} {v : List Bool} (h : (q, b, q') ∈ M.ex)
      (h' : AccFrom M q' v) : AccFrom M q (b :: v)
  /-- A universal transition consumes the first bit and both successors must accept. -/
  | un {q : ℕ} {b : Bool} {q₁ q₂ : ℕ} {v : List Bool} (h : (q, b, q₁, q₂) ∈ M.un)
      (h₁ : AccFrom M q₁ v) (h₂ : AccFrom M q₂ v) : AccFrom M q (b :: v)

/-- **The language of the alternating automaton.** -/
def Accepts (M : BitAlt) (w : List Bool) : Prop := M.AccFrom M.start w

/-- Every nondeterministic automaton is an alternating one without universal transitions. -/
def ofAut (A : BitAut) : BitAlt := ⟨A.start, A.accept, A.trans, []⟩

theorem accFrom_ofAut (A : BitAut) (q : ℕ) (v : List Bool) :
    (ofAut A).AccFrom q v ↔ A.AccFrom q v := by
  constructor
  · intro h
    induction h with
    | nil h => exact BitAut.AccFrom.nil h
    | ex h _ ih => exact BitAut.AccFrom.cons h ih
    | un h => exact absurd h (by simp [ofAut])
  · intro h
    induction h with
    | nil h => exact AccFrom.nil h
    | cons h _ ih => exact AccFrom.ex h ih

theorem accepts_ofAut (A : BitAut) (w : List Bool) : (ofAut A).Accepts w ↔ A.Accepts w :=
  accFrom_ofAut A A.start w

end BitAlt

/-! ### The names of the encoding -/

variable {M : BitAlt}

/-- The code of the initial configuration; the naming transposes it with `0`, the name of the
root task of `HTN.Syn.posEnc`. -/
def altRoot (M : BitAlt) (n : ℕ) : ℕ := 2 * Nat.pair n M.start

/-- **The compound task standing for the configuration `(k, q)`**: the automaton is in the state
`q` and `k` bits are still to be read.  Its code is even. -/
def altName (M : BitAlt) (n k q : ℕ) : ℕ := swapZero (altRoot M n) (2 * Nat.pair k q)

/-- **The compound task standing for a universal branching** into the states `q₁` and `q₂`, with
`k` bits still to be read.  Its code is odd, so it is never a configuration task. -/
def brName (M : BitAlt) (n k q₁ q₂ : ℕ) : ℕ :=
  swapZero (altRoot M n) (2 * Nat.pair k (Nat.pair q₁ q₂) + 1)

@[simp] theorem altName_root (n : ℕ) : altName M n n M.start = 0 := by
  simp [altName, altRoot, swapZero]

theorem altName_inj {n k q k' q' : ℕ} (h : altName M n k q = altName M n k' q') :
    k = k' ∧ q = q' := by
  have h' : 2 * Nat.pair k q = 2 * Nat.pair k' q' := swapZero_injective _ h
  exact Nat.pair_eq_pair.1 (by omega)

theorem brName_inj {n k q₁ q₂ k' q₁' q₂' : ℕ}
    (h : brName M n k q₁ q₂ = brName M n k' q₁' q₂') : k = k' ∧ q₁ = q₁' ∧ q₂ = q₂' := by
  have h' : 2 * Nat.pair k (Nat.pair q₁ q₂) + 1 = 2 * Nat.pair k' (Nat.pair q₁' q₂') + 1 :=
    swapZero_injective _ h
  obtain ⟨hk, hq⟩ := Nat.pair_eq_pair.1 (show Nat.pair k (Nat.pair q₁ q₂)
    = Nat.pair k' (Nat.pair q₁' q₂') by omega)
  obtain ⟨h₁, h₂⟩ := Nat.pair_eq_pair.1 hq
  exact ⟨hk, h₁, h₂⟩

theorem altName_ne_brName {n k q k' q₁ q₂ : ℕ} : altName M n k q ≠ brName M n k' q₁ q₂ := by
  intro h
  have h' : 2 * Nat.pair k q = 2 * Nat.pair k' (Nat.pair q₁ q₂) + 1 := swapZero_injective _ h
  omega

/-! ### The domain description -/

/-- The methods of the existential transitions. -/
def altExMethods (M : BitAlt) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => M.ex.map fun t =>
    (altName M n (k + 1) t.1, pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (altName M n k t.2.2)))

/-- The methods of the universal transitions: read the bit, then branch. -/
def altUnMethods (M : BitAlt) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => M.un.map fun t =>
    (altName M n (k + 1) t.1,
      pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (brName M n k t.2.2.1 t.2.2.2)))

/-- The branching methods: a universal branch is refined into *both* of its successors. -/
def altBrMethods (M : BitAlt) (n : ℕ) : List MethodDesc :=
  (List.range n).flatMap fun k => M.un.map fun t =>
    (brName M n k t.2.2.1 t.2.2.2,
      pairBody (Sum.inr (altName M n k t.2.2.1)) (Sum.inr (altName M n k t.2.2.2)))

/-- The accepting methods. -/
def altAccMethods (M : BitAlt) (n : ℕ) : List MethodDesc :=
  M.accept.map fun q => (altName M n 0 q, TnDesc.nil)

/-- **The domain description of the encoding** for the words of length `n`.  Its actions are the
guards `HTN.Syn.autActions` of `HtnComplexity/Complexity/AutFamily.lean`. -/
def altDom (M : BitAlt) (n : ℕ) : DomDesc :=
  (autActions n,
    altExMethods M n ++ altUnMethods M n ++ altBrMethods M n ++ altAccMethods M n)

@[simp] theorem altDom_actions (n : ℕ) : (altDom M n).actions = autActions n := rfl

@[simp] theorem altDom_methods (n : ℕ) :
    (altDom M n).methods =
      altExMethods M n ++ altUnMethods M n ++ altBrMethods M n ++ altAccMethods M n := rfl

theorem mem_altExMethods {n : ℕ} {e : MethodDesc} (he : e ∈ altExMethods M n) :
    ∃ k < n, ∃ t ∈ M.ex,
      e = (altName M n (k + 1) t.1,
        pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (altName M n k t.2.2))) := by
  simp only [altExMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, t, ht, rfl⟩ := he
  exact ⟨k, hk, t, ht, rfl⟩

theorem mem_altUnMethods {n : ℕ} {e : MethodDesc} (he : e ∈ altUnMethods M n) :
    ∃ k < n, ∃ t ∈ M.un,
      e = (altName M n (k + 1) t.1,
        pairBody (Sum.inl (aName k t.2.1)) (Sum.inr (brName M n k t.2.2.1 t.2.2.2))) := by
  simp only [altUnMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, t, ht, rfl⟩ := he
  exact ⟨k, hk, t, ht, rfl⟩

theorem mem_altBrMethods {n : ℕ} {e : MethodDesc} (he : e ∈ altBrMethods M n) :
    ∃ k < n, ∃ t ∈ M.un,
      e = (brName M n k t.2.2.1 t.2.2.2,
        pairBody (Sum.inr (altName M n k t.2.2.1)) (Sum.inr (altName M n k t.2.2.2))) := by
  simp only [altBrMethods, List.mem_flatMap, List.mem_range, List.mem_map] at he
  obtain ⟨k, hk, t, ht, rfl⟩ := he
  exact ⟨k, hk, t, ht, rfl⟩

theorem mem_altAccMethods {n : ℕ} {e : MethodDesc} (he : e ∈ altAccMethods M n) :
    ∃ q ∈ M.accept, e = (altName M n 0 q, TnDesc.nil) := by
  simp only [altAccMethods, List.mem_map] at he
  obtain ⟨q, hq, rfl⟩ := he
  exact ⟨q, hq, rfl⟩

theorem mem_altDom_methods {n : ℕ} {e : MethodDesc} (he : e ∈ (altDom M n).methods) :
    e ∈ altExMethods M n ∨ e ∈ altUnMethods M n ∨ e ∈ altBrMethods M n ∨
      e ∈ altAccMethods M n := by
  rw [altDom_methods, List.mem_append, List.mem_append, List.mem_append] at he
  tauto

theorem mem_altDom_of_ex {n : ℕ} {e : MethodDesc} (h : e ∈ altExMethods M n) :
    e ∈ (altDom M n).methods :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h))

theorem mem_altDom_of_un {n : ℕ} {e : MethodDesc} (h : e ∈ altUnMethods M n) :
    e ∈ (altDom M n).methods :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_altDom_of_br {n : ℕ} {e : MethodDesc} (h : e ∈ altBrMethods M n) :
    e ∈ (altDom M n).methods :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_altDom_of_acc {n : ℕ} {e : MethodDesc} (h : e ∈ altAccMethods M n) :
    e ∈ (altDom M n).methods :=
  List.mem_append_right _ h

/-! ### The domain is in the class -/

theorem altDom_methodsTO (n : ℕ) : (altDom M n).MethodsTO := by
  intro e he
  rcases mem_altDom_methods he with he | he | he | he
  · obtain ⟨k, -, t, -, rfl⟩ := mem_altExMethods he
    exact pairBody_isTO _ _
  · obtain ⟨k, -, t, -, rfl⟩ := mem_altUnMethods he
    exact pairBody_isTO _ _
  · obtain ⟨k, -, t, -, rfl⟩ := mem_altBrMethods he
    exact pairBody_isTO _ _
  · obtain ⟨q, -, rfl⟩ := mem_altAccMethods he
    exact nil_isTO

/-- The rank of a compound task name: three times the number of bits still to be read, plus one
for a branching task — so a branching task ranks above the configurations it branches into and
below the configuration that created it. -/
def altRank (M : BitAlt) (n c : ℕ) : ℕ :=
  3 * (Nat.unpair (swapZero (altRoot M n) c / 2)).1 + swapZero (altRoot M n) c % 2

@[simp] theorem altRank_altName (n k q : ℕ) : altRank M n (altName M n k q) = 3 * k := by
  have h : swapZero (altRoot M n) (altName M n k q) = 2 * Nat.pair k q := by
    simp [altName, swapZero_swapZero]
  have h2 : 2 * Nat.pair k q / 2 = Nat.pair k q := by omega
  have h3 : 2 * Nat.pair k q % 2 = 0 := by omega
  simp [altRank, h, h2, h3]

@[simp] theorem altRank_brName (n k q₁ q₂ : ℕ) :
    altRank M n (brName M n k q₁ q₂) = 3 * k + 1 := by
  have h : swapZero (altRoot M n) (brName M n k q₁ q₂)
      = 2 * Nat.pair k (Nat.pair q₁ q₂) + 1 := by
    simp [brName, swapZero_swapZero]
  have h2 : (2 * Nat.pair k (Nat.pair q₁ q₂) + 1) / 2 = Nat.pair k (Nat.pair q₁ q₂) := by omega
  have h3 : (2 * Nat.pair k (Nat.pair q₁ q₂) + 1) % 2 = 1 := by omega
  simp [altRank, h, h2, h3]

theorem altDom_isAcyclic (n : ℕ) : (altDom M n).IsAcyclic := by
  refine ⟨altRank M n, ?_⟩
  intro e he t ht c hc
  have hpair : ∀ x y : ℕ ⊕ ℕ, t ∈ (pairBody x y).toTaskNetwork.T → t = 0 ∨ t = 1 := by
    intro x y ht
    simpa [TnDesc.toTaskNetwork, pairBody, TnDesc.ids] using ht
  rcases mem_altDom_methods he with he | he | he | he
  · obtain ⟨k, -, tr, -, rfl⟩ := mem_altExMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp only [altRank_altName]
      omega
  · obtain ⟨k, -, tr, -, rfl⟩ := mem_altUnMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp [TnDesc.toTaskNetwork] at hc
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp only [altRank_altName, altRank_brName]
      omega
  · obtain ⟨k, -, tr, -, rfl⟩ := mem_altBrMethods he
    rcases hpair _ _ ht with rfl | rfl
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_zero, Sum.inr.injEq] at hc
      subst hc
      simp
    · simp only [TnDesc.toTaskNetwork_α, pairBody_label_one, Sum.inr.injEq] at hc
      subst hc
      simp
  · obtain ⟨q, -, rfl⟩ := mem_altAccMethods he
    simp [TnDesc.nil, TnDesc.toTaskNetwork, TnDesc.ids] at ht

theorem altDom_domOk (n : ℕ) : SynClass.TO_HTN_AC_root.domOk (altDom M n) :=
  ⟨altDom_methodsTO n, altDom_isAcyclic n⟩

/-! ### The bodies the domain offers -/

/-- **The bodies of a configuration task**: an existential step, a universal step, or the end of
an accepting run. -/
theorem seqBody_altDom_iff {n k q : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (altDom M n).toDomain.SeqBody (altName M n k q) xs ↔
      (∃ j, j < n ∧ k = j + 1 ∧ ∃ b : Bool, ∃ q' : ℕ, (q, b, q') ∈ M.ex ∧
        xs = [Sum.inl (aName j b), Sum.inr (altName M n j q')]) ∨
      (∃ j, j < n ∧ k = j + 1 ∧ ∃ b : Bool, ∃ q₁ q₂ : ℕ, (q, b, q₁, q₂) ∈ M.un ∧
        xs = [Sum.inl (aName j b), Sum.inr (brName M n j q₁ q₂)]) ∨
      (k = 0 ∧ q ∈ M.accept ∧ xs = []) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_altDom_methods he with he | he | he | he
    · obtain ⟨j, hj, t, ht, rfl⟩ := mem_altExMethods he
      obtain ⟨hk, hq⟩ := altName_inj hc
      subst hk
      refine Or.inl ⟨j, hj, rfl, t.2.1, t.2.2, ?_, ?_⟩
      · rw [← hq]
        exact ht
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody
    · obtain ⟨j, hj, t, ht, rfl⟩ := mem_altUnMethods he
      obtain ⟨hk, hq⟩ := altName_inj hc
      subst hk
      refine Or.inr (Or.inl ⟨j, hj, rfl, t.2.1, t.2.2.1, t.2.2.2, ?_, ?_⟩)
      · rw [← hq]
        exact ht
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody
    · obtain ⟨j, -, t, -, rfl⟩ := mem_altBrMethods he
      exact absurd hc.symm altName_ne_brName
    · obtain ⟨q₀, hq₀, rfl⟩ := mem_altAccMethods he
      obtain ⟨hk, hq⟩ := altName_inj hc
      subst hk
      refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
      · rw [← hq]
        exact hq₀
      · exact (Method.hasSeqBody_iff_of_isSeqNet nil_isSeqNet).1 hbody
  · rintro (⟨j, hj, rfl, b, q', ht, rfl⟩ | ⟨j, hj, rfl, b, q₁, q₂, ht, rfl⟩ |
      ⟨rfl, hq, rfl⟩)
    · refine ⟨(altName M n (j + 1) q,
        pairBody (Sum.inl (aName j b)) (Sum.inr (altName M n j q'))), ?_, rfl, ?_⟩
      · exact mem_altDom_of_ex (by
          simp only [altExMethods, List.mem_flatMap, List.mem_range, List.mem_map]
          exact ⟨j, hj, (q, b, q'), ht, rfl⟩)
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl
    · refine ⟨(altName M n (j + 1) q,
        pairBody (Sum.inl (aName j b)) (Sum.inr (brName M n j q₁ q₂))), ?_, rfl, ?_⟩
      · exact mem_altDom_of_un (by
          simp only [altUnMethods, List.mem_flatMap, List.mem_range, List.mem_map]
          exact ⟨j, hj, (q, b, q₁, q₂), ht, rfl⟩)
      · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl
    · refine ⟨(altName M n 0 q, TnDesc.nil), ?_, rfl, ?_⟩
      · exact mem_altDom_of_acc (by
          simp only [altAccMethods, List.mem_map]
          exact ⟨q, hq, rfl⟩)
      · exact (Method.hasSeqBody_iff_of_isSeqNet nil_isSeqNet).2 rfl

/-- **The bodies of a branching task**: its two successors, in either order of listing. -/
theorem seqBody_altDom_br_iff {n k q₁ q₂ : ℕ} {xs : List (ℕ ⊕ ℕ)} :
    (altDom M n).toDomain.SeqBody (brName M n k q₁ q₂) xs ↔
      (k < n ∧ (∃ q : ℕ, ∃ b : Bool, (q, b, q₁, q₂) ∈ M.un) ∧
        xs = [Sum.inr (altName M n k q₁), Sum.inr (altName M n k q₂)]) := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hc, hbody⟩
    rcases mem_altDom_methods he with he | he | he | he
    · obtain ⟨j, -, t, -, rfl⟩ := mem_altExMethods he
      exact absurd hc altName_ne_brName
    · obtain ⟨j, -, t, -, rfl⟩ := mem_altUnMethods he
      exact absurd hc altName_ne_brName
    · obtain ⟨j, hj, t, ht, rfl⟩ := mem_altBrMethods he
      obtain ⟨hk, h₁, h₂⟩ := brName_inj hc
      subst hk
      subst h₁
      subst h₂
      exact ⟨hj, ⟨t.1, t.2.1, ht⟩,
        (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).1 hbody⟩
    · obtain ⟨q₀, -, rfl⟩ := mem_altAccMethods he
      exact absurd hc altName_ne_brName
  · rintro ⟨hk, ⟨q, b, ht⟩, rfl⟩
    refine ⟨(brName M n k q₁ q₂,
      pairBody (Sum.inr (altName M n k q₁)) (Sum.inr (altName M n k q₂))), ?_, rfl, ?_⟩
    · exact mem_altDom_of_br (by
        simp only [altBrMethods, List.mem_flatMap, List.mem_range, List.mem_map]
        exact ⟨k, hk, (q, b, q₁, q₂), ht, rfl⟩)
    · exact (Method.hasSeqBody_iff_of_isSeqNet (pairBody_isSeqNet _ _)).2 rfl

/-! ### No action has an effect -/

theorem altDom_add (n a : ℕ) : (altDom M n).add a = ∅ := by
  simp only [DomDesc.add, altDom_actions, (lookup_autActions_eff n a).1]
  simp

theorem altDom_del (n a : ℕ) : (altDom M n).del a = ∅ := by
  simp only [DomDesc.del, altDom_actions, (lookup_autActions_eff n a).2]
  simp

theorem altDom_transition (n a : ℕ) (s : Set ℕ) :
    (altDom M n).toDomain.transition a s = s := by
  simp [ActionModel.transition, show (altDom M n).toDomain.del a = ∅ from altDom_del n a,
    show (altDom M n).toDomain.add a = ∅ from altDom_add n a]

theorem altDom_transitionSeq (n : ℕ) (as : List ℕ) (s : Set ℕ) :
    (altDom M n).toDomain.transitionSeq as s = s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => rw [ActionModel.transitionSeq_cons, altDom_transition, ih]

theorem altDom_seqApplicable_iff (n : ℕ) (as : List ℕ) (s : Set ℕ) :
    (altDom M n).toDomain.SeqApplicable as s ↔ ∀ a ∈ as, (altDom M n).prec a ⊆ s := by
  induction as generalizing s with
  | nil => simp [ActionModel.SeqApplicable]
  | cons a as ih =>
    rw [ActionModel.seqApplicable_cons, altDom_transition, ih]
    simp [ActionModel.Applicable]

/-- The precondition of a listed action is the single fact guarding it. -/
theorem prec_altDom {n k : ℕ} (hk : k < n) (b : Bool) :
    (altDom M n).prec (aName k b) = {posFact k b} := by
  have hlookup := lookup_range_map (n := 2 * n)
    (fun j => ([j + 2], ([] : List ℕ), ([] : List ℕ))) (aName_lt hk b)
  simp only [DomDesc.prec, altDom_actions, autActions]
  rw [hlookup]
  ext f
  simp [posFact_aName]

/-! ### The simulation -/

/-- **The refinements of a configuration task that are executable in the encoded word are the
accepting computations of the alternating automaton on the corresponding suffix.** -/
theorem yieldSeq_altDom_iff {W : List Bool} : ∀ {v : List Bool}, v <:+ W → ∀ q : ℕ,
    ((∃ as : List ℕ, (altDom M W.length).toDomain.YieldSeq
        [Sum.inr (altName M W.length v.length q)] as ∧
      ∀ a ∈ as, (altDom M W.length).prec a ⊆ {f | f ∈ posFacts W}) ↔ M.AccFrom q v) := by
  intro v
  induction v with
  | nil =>
    intro _ q
    constructor
    · rintro ⟨as, hy, -⟩
      cases hy with
      | comp hm h =>
        rcases seqBody_altDom_iff.1 hm with ⟨j, -, hj, -⟩ | ⟨j, -, hj, -⟩ | ⟨-, hq, -⟩
        · exact absurd hj (by simp)
        · exact absurd hj (by simp)
        · exact BitAlt.AccFrom.nil hq
    · intro h
      cases h with
      | nil hq =>
        refine ⟨[], ?_, by simp⟩
        exact Domain.YieldSeq.comp (bs := [])
          (seqBody_altDom_iff.2 (Or.inr (Or.inr ⟨rfl, hq, rfl⟩))) (by simp)
  | cons b v ih =>
    intro hv q
    have hvW : v <:+ W := (List.suffix_cons b v).trans hv
    have hlen : v.length < W.length := by
      have := hv.length_le
      simp only [List.length_cons] at this
      omega
    have hbit : ∀ b' : Bool, posFact v.length b' ∈ posFacts W → b' = b := by
      intro b' hmem
      obtain ⟨u, hu, hul⟩ := mem_posFacts_iff.1 hmem
      have hbu : b' :: u = b :: v := eq_of_suffix_of_length_eq hu hv (by simp [hul])
      exact (List.cons_eq_cons.1 hbu).1
    have hbr : ∀ (q₀ : ℕ) (b' : Bool) (q₁ q₂ : ℕ), (q₀, b', q₁, q₂) ∈ M.un →
        ((∃ as : List ℕ, (altDom M W.length).toDomain.YieldSeq
            [Sum.inr (brName M W.length v.length q₁ q₂)] as ∧
          ∀ a ∈ as, (altDom M W.length).prec a ⊆ {f | f ∈ posFacts W}) ↔
          (M.AccFrom q₁ v ∧ M.AccFrom q₂ v)) := by
      intro q₀ b' q₁ q₂ hun
      constructor
      · rintro ⟨as, hy, happ⟩
        cases hy with
        | comp hm h =>
          obtain ⟨-, -, rfl⟩ := seqBody_altDom_br_iff.1 hm
          rw [List.append_nil] at h
          obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ :=
            Domain.YieldSeq.split (xs := [Sum.inr (altName M W.length v.length q₁)])
              (ys := [Sum.inr (altName M W.length v.length q₂)]) h
          exact ⟨(ih hvW q₁).1 ⟨as₁, h₁, fun a ha => happ a (List.mem_append_left _ ha)⟩,
            (ih hvW q₂).1 ⟨as₂, h₂, fun a ha => happ a (List.mem_append_right _ ha)⟩⟩
      · rintro ⟨hacc₁, hacc₂⟩
        obtain ⟨as₁, hy₁, happ₁⟩ := (ih hvW q₁).2 hacc₁
        obtain ⟨as₂, hy₂, happ₂⟩ := (ih hvW q₂).2 hacc₂
        refine ⟨as₁ ++ as₂, ?_, ?_⟩
        · refine Domain.YieldSeq.comp
            (bs := [Sum.inr (altName M W.length v.length q₁),
              Sum.inr (altName M W.length v.length q₂)])
            (seqBody_altDom_br_iff.2 ⟨hlen, ⟨q₀, b', hun⟩, rfl⟩) ?_
          rw [List.append_nil]
          exact Domain.YieldSeq.append hy₁ hy₂
        · intro a ha
          rcases List.mem_append.1 ha with ha | ha
          · exact happ₁ a ha
          · exact happ₂ a ha
    constructor
    · rintro ⟨as, hy, happ⟩
      simp only [List.length_cons] at hy
      cases hy with
      | comp hm h =>
        rcases seqBody_altDom_iff.1 hm with ⟨j, hj, hjeq, b', q', htr, rfl⟩ |
          ⟨j, hj, hjeq, b', q₁, q₂, hun, rfl⟩ | ⟨hk, -, -⟩
        · have hjv : j = v.length := by omega
          subst hjv
          rw [List.cons_append, List.cons_append, List.nil_append] at h
          cases h with
          | prim h =>
            rename_i as'
            have hmem : posFact v.length b' ∈ posFacts W := by
              have := happ (aName v.length b') (by simp)
              rw [prec_altDom hlen] at this
              exact this rfl
            have hbb : b' = b := hbit b' hmem
            subst hbb
            refine BitAlt.AccFrom.ex htr ((ih hvW q').1 ⟨as', h, ?_⟩)
            exact fun a ha => happ a (List.mem_cons_of_mem _ ha)
        · have hjv : j = v.length := by omega
          subst hjv
          rw [List.cons_append, List.cons_append, List.nil_append] at h
          cases h with
          | prim h =>
            rename_i as'
            have hmem : posFact v.length b' ∈ posFacts W := by
              have := happ (aName v.length b') (by simp)
              rw [prec_altDom hlen] at this
              exact this rfl
            have hbb : b' = b := hbit b' hmem
            have happ' : ∀ a ∈ as', (altDom M W.length).prec a ⊆ {f | f ∈ posFacts W} :=
              fun a ha => happ a (List.mem_cons_of_mem _ ha)
            obtain ⟨hacc₁, hacc₂⟩ := (hbr q b' q₁ q₂ hun).1 ⟨as', h, happ'⟩
            rw [hbb] at hun
            exact BitAlt.AccFrom.un hun hacc₁ hacc₂
        · exact absurd hk (by simp)
    · intro h
      cases h with
      | ex htr h' =>
        rename_i q'
        obtain ⟨as', hy', happ'⟩ := (ih hvW q').2 h'
        refine ⟨aName v.length b :: as', ?_, ?_⟩
        · simp only [List.length_cons]
          refine Domain.YieldSeq.comp
            (bs := [Sum.inl (aName v.length b), Sum.inr (altName M W.length v.length q')])
            (seqBody_altDom_iff.2 (Or.inl ⟨v.length, hlen, rfl, b, q', htr, rfl⟩)) ?_
          rw [List.cons_append, List.cons_append, List.nil_append]
          exact Domain.YieldSeq.prim hy'
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · rw [prec_altDom hlen]
            intro f hf
            rw [Set.mem_singleton_iff] at hf
            subst hf
            exact mem_posFacts_iff.2 ⟨v, hv, rfl⟩
          · exact happ' a ha
      | un hun hacc₁ hacc₂ =>
        rename_i q₁ q₂
        obtain ⟨as', hy', happ'⟩ := (hbr q b q₁ q₂ hun).2 ⟨hacc₁, hacc₂⟩
        refine ⟨aName v.length b :: as', ?_, ?_⟩
        · simp only [List.length_cons]
          refine Domain.YieldSeq.comp
            (bs := [Sum.inl (aName v.length b),
              Sum.inr (brName M W.length v.length q₁ q₂)])
            (seqBody_altDom_iff.2
              (Or.inr (Or.inl ⟨v.length, hlen, rfl, b, q₁, q₂, hun, rfl⟩))) ?_
          rw [List.cons_append, List.cons_append, List.nil_append]
          exact Domain.YieldSeq.prim hy'
        · intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · rw [prec_altDom hlen]
            intro f hf
            rw [Set.mem_singleton_iff] at hf
            subst hf
            exact mem_posFacts_iff.2 ⟨v, hv, rfl⟩
          · exact happ' a ha

/-- **The encoded problem is solvable exactly when the alternating automaton accepts the
word.** -/
theorem solvable_altDom_iff (w : List Bool) :
    Solvable (altDom M w.length) (posEnc w) ↔ M.Accepts w := by
  have hseq : ((posEnc w).tnI).toTaskNetwork.IsSeqNet (TnDesc.lin (posEnc w).tnI)
      (TnDesc.seqBody (posEnc w).tnI) := TnDesc.isSeqNet_lin guardInst_isTO
  have hbody : TnDesc.seqBody (posEnc w).tnI = [Sum.inr 0] := rfl
  have hnorm := Problem.solvable_iff_yieldSeq (problem_wf (altDom M w.length) (posEnc w))
    (isTO_problem (altDom_methodsTO (M := M) w.length) guardInst_isTO).2 hseq
  rw [show Solvable (altDom M w.length) (posEnc w)
      = (problem (altDom M w.length) (posEnc w)).Solvable from rfl, hnorm, hbody]
  have key := yieldSeq_altDom_iff (M := M) (W := w) (List.suffix_refl w) M.start
  rw [altName_root] at key
  constructor
  · rintro ⟨as, hy, happ, -⟩
    exact key.1 ⟨as, hy,
      (altDom_seqApplicable_iff (M := M) w.length as {f | f ∈ posFacts w}).1 happ⟩
  · intro h
    obtain ⟨as, hy, happ⟩ := key.2 h
    refine ⟨as, hy,
      (altDom_seqApplicable_iff (M := M) w.length as {f | f ∈ posFacts w}).2 happ, ?_⟩
    intro f hf
    simp only [problem_goal, InstDesc.goalList, posEnc, guardInst, Set.mem_setOf_eq,
      List.not_mem_nil] at hf

/-! ### Size, computability, and the family -/

theorem sum_method_size_le {l : List MethodDesc} {L b : ℕ} (hlen : l.length ≤ L)
    (hb : ∀ e ∈ l, MethodDesc.size e ≤ b) : (l.map MethodDesc.size).sum ≤ b * L := by
  have h := List.sum_le_card_nsmul (l.map MethodDesc.size) b (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact hb e he)
  rw [List.length_map, smul_eq_mul] at h
  calc (l.map MethodDesc.size).sum ≤ l.length * b := h
    _ ≤ L * b := Nat.mul_le_mul_right _ hlen
    _ = b * L := Nat.mul_comm _ _

theorem size_altExMethods_le (n : ℕ) :
    ((altExMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.ex.length) := by
  refine sum_method_size_le ?_ ?_
  · simp [altExMethods]
  · intro e he
    obtain ⟨k, -, t, -, rfl⟩ := mem_altExMethods he
    simp [MethodDesc.size]

theorem size_altUnMethods_le (n : ℕ) :
    ((altUnMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.un.length) := by
  refine sum_method_size_le ?_ ?_
  · simp [altUnMethods]
  · intro e he
    obtain ⟨k, -, t, -, rfl⟩ := mem_altUnMethods he
    simp [MethodDesc.size]

theorem size_altBrMethods_le (n : ℕ) :
    ((altBrMethods M n).map MethodDesc.size).sum ≤ 6 * (n * M.un.length) := by
  refine sum_method_size_le ?_ ?_
  · simp [altBrMethods]
  · intro e he
    obtain ⟨k, -, t, -, rfl⟩ := mem_altBrMethods he
    simp [MethodDesc.size]

theorem size_altAccMethods_le (n : ℕ) :
    ((altAccMethods M n).map MethodDesc.size).sum ≤ M.accept.length := by
  have h : ((altAccMethods M n).map MethodDesc.size).sum ≤ 1 * M.accept.length := by
    refine sum_method_size_le (by simp [altAccMethods]) ?_
    intro e he
    obtain ⟨q, -, rfl⟩ := mem_altAccMethods he
    simp [MethodDesc.size, TnDesc.size, TnDesc.nil, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  omega

theorem size_altDom_le (n : ℕ) :
    (altDom M n).size
      ≤ (6 * M.ex.length + 12 * M.un.length + 4) * n + M.accept.length := by
  have hsplit : (altDom M n).size = ((autActions n).map ActionDesc.size).sum
      + (((altExMethods M n).map MethodDesc.size).sum
        + (((altUnMethods M n).map MethodDesc.size).sum
          + (((altBrMethods M n).map MethodDesc.size).sum
            + ((altAccMethods M n).map MethodDesc.size).sum))) := by
    simp [DomDesc.size, altDom, DomDesc.actions, DomDesc.methods, List.map_append,
      List.sum_append]
  have h1 := size_autActions_le n
  have h2 := size_altExMethods_le (M := M) n
  have h3 := size_altUnMethods_le (M := M) n
  have h4 := size_altBrMethods_le (M := M) n
  have h5 := size_altAccMethods_le (M := M) n
  rw [hsplit]
  nlinarith [h1, h2, h3, h4, h5]

/-- The existential methods, with the two-task bodies written out. -/
theorem altExMethods_raw (n : ℕ) :
    altExMethods M n = List.flatMap (fun k => M.ex.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := rfl

/-- The universal methods, with the two-task bodies written out. -/
theorem altUnMethods_raw (n : ℕ) :
    altUnMethods M n = List.flatMap (fun k => M.un.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (2 * Nat.pair n M.start)
              (2 * Nat.pair k (Nat.pair t.2.2.1 t.2.2.2) + 1))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := rfl

/-- The branching methods, with the two-task bodies written out. -/
theorem altBrMethods_raw (n : ℕ) :
    altBrMethods M n = List.flatMap (fun k => M.un.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k (Nat.pair t.2.2.1 t.2.2.2) + 1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2.1)),
            (1, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := rfl

theorem primrec_altExMethods : Primrec (altExMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => M.ex.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const M.ex) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.1.2 := Primrec.snd.comp Primrec.fst
    have t1 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.1 := Primrec.fst.comp Primrec.snd
    have tb : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have t2 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => w.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hbase : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => 2 * Nat.pair w.1.1 M.start :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp nn (Primrec.const M.start))
    have hhead : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start) (2 * Nat.pair (w.1.2 + 1) w.2.1) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) t1))
    have htail : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start) (2 * Nat.pair w.1.2 w.2.2.2) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp kk t2))
    have hact : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ) => 2 * w.1.2 + w.2.2.1.toNat :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) kk)
        (primrec_toNat.comp tb)
    refine Primrec.pair hhead (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) htail))
        (Primrec.const []))
  exact key.of_eq fun n => (altExMethods_raw n).symm

theorem primrec_altUnMethods : Primrec (altUnMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => M.un.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair (k + 1) t.1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, false, 2 * k + t.2.1.toNat),
            (1, true, swapZero (2 * Nat.pair n M.start)
              (2 * Nat.pair k (Nat.pair t.2.2.1 t.2.2.2) + 1))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const M.un) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have t1 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.1 :=
      Primrec.fst.comp Primrec.snd
    have tb : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have t2 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have t3 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hbase : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => 2 * Nat.pair w.1.1 M.start :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp nn (Primrec.const M.start))
    have hhead : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start) (2 * Nat.pair (w.1.2 + 1) w.2.1) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) t1))
    have htail : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start)
          (2 * Nat.pair w.1.2 (Nat.pair w.2.2.2.1 w.2.2.2.2) + 1) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2)
            (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp t2 t3)))
          (Primrec.const 1))
    have hact : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => 2 * w.1.2 + w.2.2.1.toNat :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) kk)
        (primrec_toNat.comp tb)
    refine Primrec.pair hhead (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) htail))
        (Primrec.const []))
  exact key.of_eq fun n => (altUnMethods_raw n).symm

theorem primrec_altBrMethods : Primrec (altBrMethods M) := by
  have key : Primrec fun n : ℕ => List.flatMap (fun k => M.un.map fun t =>
      ((swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k (Nat.pair t.2.2.1 t.2.2.2) + 1) : ℕ),
        (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
          ([(0, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2.1)),
            (1, true, swapZero (2 * Nat.pair n M.start) (2 * Nat.pair k t.2.2.2))] :
              List (ℕ × Bool × ℕ)))))
      (List.range n) := by
    refine Primrec.list_flatMap Primrec.list_range ?_
    refine Primrec.list_map (Primrec.const M.un) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have t2 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have t3 : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => w.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hbase : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) => 2 * Nat.pair w.1.1 M.start :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp nn (Primrec.const M.start))
    have hhead : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start)
          (2 * Nat.pair w.1.2 (Nat.pair w.2.2.2.1 w.2.2.2.2) + 1) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2)
            (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp t2 t3)))
          (Primrec.const 1))
    have hfst : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start) (2 * Nat.pair w.1.2 w.2.2.2.1) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp kk t2))
    have hsnd : Primrec fun w : (ℕ × ℕ) × (ℕ × Bool × ℕ × ℕ) =>
        swapZero (2 * Nat.pair w.1.1 M.start) (2 * Nat.pair w.1.2 w.2.2.2.2) :=
      primrec_swapZero.comp hbase
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp kk t3))
    refine Primrec.pair hhead (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hfst))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hsnd))
        (Primrec.const []))
  exact key.of_eq fun n => (altBrMethods_raw n).symm

theorem primrec_altAccMethods : Primrec (altAccMethods M) := by
  refine Primrec.list_map (Primrec.const M.accept) ?_
  refine Primrec.pair ?_ (Primrec.const TnDesc.nil)
  exact primrec_swapZero.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp Primrec.fst (Primrec.const M.start)))
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd))

theorem computable_altDom : Computable (altDom M) :=
  (Primrec.pair primrec_autActions
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp primrec_altExMethods primrec_altUnMethods)
        primrec_altBrMethods)
      primrec_altAccMethods)).to_comp

variable (M)

/-- **A polynomial-time hardness family whose fixed part is an alternating finite automaton
reading its input from the initial state**, for the language of that automaton, in `TO-HTN-AC`
with a rooted instance — hence in each of the three source classes of the eight open cells. -/
noncomputable def altFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root M.Accepts where
  dom := altDom M
  inst := posEnc
  bound := Polynomial.C (6 * M.ex.length + 12 * M.un.length + 4) * Polynomial.X +
    Polynomial.C (M.accept.length + 2)
  dom_size := fun n => by
    have h := size_altDom_le (M := M) n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  inst_size := fun w => by
    have h := size_posEnc w
    have h2 : w.length ≤ (6 * M.ex.length + 12 * M.un.length + 4) * w.length :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega
  dom_ok := fun _ => altDom_domOk _
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := posEnc_injective
  correct := solvable_altDom_iff
  dom_computable := computable_altDom
  inst_polyTime := polyTimeCode_posEnc

/-- **The alternating family, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_alt_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root M.Accepts) :=
  ⟨(altFamily M).mono ⟨fun _ h => h.1, fun _ h => h⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_alt_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root M.Accepts) :=
  ⟨(altFamily M).mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h.2, fun _ h => h⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_alt_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root M.Accepts) :=
  ⟨(altFamily M).mono ⟨fun _ h => h.2, fun _ h => h⟩⟩

/-! ### An example that really branches

The language `HTN.Syn.LAllTrue` of `HtnComplexity/Complexity/PosFamily.lean` — the words all
of whose bits are `true` — is also the language of an alternating automaton with **no**
existential transition: reading a `true` branches universally into two copies of the single
state, so a refinement of the root task is a binary tree of guards rather than a chain. -/

/-- The one-state alternating automaton whose only transition is universal. -/
def allTrueAlt : BitAlt := ⟨0, [0], [], [(0, true, 0, 0)]⟩

theorem accFrom_allTrueAlt (w : List Bool) :
    allTrueAlt.AccFrom 0 w ↔ ∀ b ∈ w, b = true := by
  induction w with
  | nil =>
    exact ⟨fun _ _ h => absurd h (by simp),
      fun _ => BitAlt.AccFrom.nil (by simp [allTrueAlt])⟩
  | cons b w ih =>
    constructor
    · intro h
      cases h with
      | ex h => exact absurd h (by simp [allTrueAlt])
      | un h h₁ _ =>
        simp only [allTrueAlt, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨-, hb, hq, -⟩ := h
        subst hb
        subst hq
        intro c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · rfl
        · exact ih.1 h₁ c hc
    · intro h
      have hw : ∀ c ∈ w, c = true := fun c hc => h c (List.mem_cons_of_mem _ hc)
      refine BitAlt.AccFrom.un (q₁ := 0) (q₂ := 0) ?_ (ih.2 hw) (ih.2 hw)
      rw [h b (by simp)]
      simp [allTrueAlt]

theorem allTrueAlt_accepts_iff (w : List Bool) : allTrueAlt.Accepts w ↔ LAllTrue w :=
  accFrom_allTrueAlt w

/-- **A polynomial-time hardness family for `LAllTrue` whose fixed part is an alternating
machine.** -/
theorem nonempty_hardFamilyPT_allTrue_alt :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root LAllTrue) := by
  have h : allTrueAlt.Accepts = LAllTrue := funext fun w => propext (allTrueAlt_accepts_iff w)
  exact h ▸ ⟨altFamily allTrueAlt⟩

end Syn

end HTN
