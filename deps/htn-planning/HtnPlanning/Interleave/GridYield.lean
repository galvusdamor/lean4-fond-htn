import HtnPlanning.Interleave.GridNet
/-!
# Refinement of grids: a syntactic description

For a domain whose method bodies are *grids* — parallel compositions of totally ordered chains,
as in the two large compilations formalised in this project — the refinements of a grid can be
described purely syntactically, without any reference to task identifiers.  This file introduces
the two mutually recursive relations

* `HTN.Domain.ChainYieldN D n xs as` — the chain of tasks `xs` refines into the action sequence
  `as` using `n` method applications: the leading task is either an action, which is executed, or
  a compound task, which is replaced by (a refinement of) the grid body of one of its methods;
  the actions coming from the leading task precede those of the rest of the chain;
* `HTN.Domain.GridYieldN D n ls as` — the grid `ls` refines into `as`: `as` is an *interleaving*
  of refinements of the individual chains.

The main result is the equivalence with the semantic refinement relation of
`HtnPlanning/Interleave/NetYield.lean`:

`HTN.Domain.netYieldN_grid_iff` — `D.NetYieldN n (grid ls) as ↔ D.GridYieldN n ls as`,
`HTN.Domain.netYieldN_seq_iff` — `D.NetYieldN n (seq xs) as ↔ D.ChainYieldN n xs as`,

for every domain all of whose methods have grid subtask networks.  Both are proved
simultaneously by induction on the number of decomposition steps, using the structural
decomposition of grids and chains of `HtnPlanning/Interleave/GridNet.lean`.
-/

namespace HTN

universe u v w

variable {F : Type u} {A : Type v} {C : Type w} [Inhabited A]

namespace Domain

open TaskNetwork

variable (D : Domain F A C (ℕ × ℕ))

/-- The domain has a method decomposing the compound task `c` into the grid `ls`. -/
def GridBody (c : C) (ls : List (List (A ⊕ C))) : Prop :=
  ∃ m ∈ D.methods, m.abstractTask = c ∧ m.subtasks = TaskNetwork.grid ls

/-! ### The refinement relations

Refinement of a chain of tasks and of a grid of chains, counted by the number of method
applications. -/

mutual

/-- `D.ChainYieldN n xs as`: the chain `xs` refines into the action sequence `as` using `n`
method applications. -/
inductive ChainYieldN : ℕ → List (A ⊕ C) → List A → Prop
  /-- The empty chain refines into the empty action sequence. -/
  | nil : ChainYieldN 0 [] []
  /-- A leading action is executed. -/
  | prim {n : ℕ} {xs : List (A ⊕ C)} {as : List A} (a : A) (h : ChainYieldN n xs as) :
      ChainYieldN n (Sum.inl a :: xs) (a :: as)
  /-- A leading compound task is replaced by the grid body of one of its methods; the actions
  it produces precede those of the rest of the chain. -/
  | comp {n k : ℕ} {c : C} {ls : List (List (A ⊕ C))} {xs : List (A ⊕ C)} {as bs cs : List A}
      (hm : GridBody D c ls) (hb : GridYieldN k ls bs) (ht : ChainYieldN n xs as)
      (hcs : cs = bs ++ as) : ChainYieldN (k + 1 + n) (Sum.inr c :: xs) cs

/-- `D.GridYieldN n ls as`: the grid `ls` refines into the action sequence `as` using `n` method
applications; the refinements of the individual chains are interleaved arbitrarily. -/
inductive GridYieldN : ℕ → List (List (A ⊕ C)) → List A → Prop
  /-- The empty grid refines into the empty action sequence. -/
  | nil : GridYieldN 0 [] []
  /-- The refinement of the first chain is interleaved with that of the remaining chains. -/
  | cons {n k : ℕ} {l : List (A ⊕ C)} {ls : List (List (A ⊕ C))} {as bs cs : List A}
      (hc : ChainYieldN n l as) (hg : GridYieldN k ls bs) (hint : Interleave as bs cs) :
      GridYieldN (n + k) (l :: ls) cs

end

/-- The chain `xs` refines into the action sequence `as`. -/
def ChainYield (xs : List (A ⊕ C)) (as : List A) : Prop := ∃ n, D.ChainYieldN n xs as

/-- The grid `ls` refines into the action sequence `as`. -/
def GridYield (ls : List (List (A ⊕ C))) (as : List A) : Prop := ∃ n, D.GridYieldN n ls as

variable {D}

/-! ### Inversion -/

@[simp] lemma chainYieldN_nil_iff {n : ℕ} {as : List A} :
    D.ChainYieldN n [] as ↔ n = 0 ∧ as = [] := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ChainYieldN.nil

lemma chainYieldN_cons_inl_iff {n : ℕ} {a : A} {xs : List (A ⊕ C)} {cs : List A} :
    D.ChainYieldN n (Sum.inl a :: xs) cs ↔ ∃ as, cs = a :: as ∧ D.ChainYieldN n xs as := by
  constructor
  · intro h
    cases h with
    | prim b h => exact ⟨_, rfl, h⟩
  · rintro ⟨as, rfl, h⟩
    exact ChainYieldN.prim a h

lemma chainYieldN_cons_inr_iff {n : ℕ} {c : C} {xs : List (A ⊕ C)} {cs : List A} :
    D.ChainYieldN n (Sum.inr c :: xs) cs ↔ ∃ (k n' : ℕ) (ls : List (List (A ⊕ C)))
      (bs as : List A), n = k + 1 + n' ∧ D.GridBody c ls ∧ D.GridYieldN k ls bs ∧
      D.ChainYieldN n' xs as ∧ cs = bs ++ as := by
  constructor
  · intro h
    cases h with
    | comp hm hb ht hcs => exact ⟨_, _, _, _, _, rfl, hm, hb, ht, hcs⟩
  · rintro ⟨k, n', ls, bs, as, rfl, hm, hb, ht, rfl⟩
    exact ChainYieldN.comp hm hb ht rfl

@[simp] lemma gridYieldN_nil_iff {n : ℕ} {as : List A} :
    D.GridYieldN n [] as ↔ n = 0 ∧ as = [] := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact GridYieldN.nil

lemma gridYieldN_cons_iff {n : ℕ} {l : List (A ⊕ C)} {ls : List (List (A ⊕ C))} {cs : List A} :
    D.GridYieldN n (l :: ls) cs ↔ ∃ (n₁ n₂ : ℕ) (as bs : List A), n = n₁ + n₂ ∧
      D.ChainYieldN n₁ l as ∧ D.GridYieldN n₂ ls bs ∧ Interleave as bs cs := by
  constructor
  · intro h
    cases h with
    | cons hc hg hint => exact ⟨_, _, _, _, rfl, hc, hg, hint⟩
  · rintro ⟨n₁, n₂, as, bs, rfl, hc, hg, hint⟩
    exact GridYieldN.cons hc hg hint

/-! ### The step-free relations -/

@[simp] lemma chainYield_nil_iff {as : List A} : D.ChainYield [] as ↔ as = [] := by
  simp [ChainYield]

lemma chainYield_cons_inl_iff {a : A} {xs : List (A ⊕ C)} {cs : List A} :
    D.ChainYield (Sum.inl a :: xs) cs ↔ ∃ as, cs = a :: as ∧ D.ChainYield xs as := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨as, rfl, h'⟩ := chainYieldN_cons_inl_iff.1 h
    exact ⟨as, rfl, n, h'⟩
  · rintro ⟨as, rfl, n, h⟩
    exact ⟨n, ChainYieldN.prim a h⟩

lemma chainYield_cons_inr_iff {c : C} {xs : List (A ⊕ C)} {cs : List A} :
    D.ChainYield (Sum.inr c :: xs) cs ↔ ∃ (ls : List (List (A ⊕ C))) (bs as : List A),
      D.GridBody c ls ∧ D.GridYield ls bs ∧ D.ChainYield xs as ∧ cs = bs ++ as := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨k, n', ls, bs, as, rfl, hm, hb, ht, rfl⟩ := chainYieldN_cons_inr_iff.1 h
    exact ⟨ls, bs, as, hm, ⟨k, hb⟩, ⟨n', ht⟩, rfl⟩
  · rintro ⟨ls, bs, as, hm, ⟨k, hb⟩, ⟨n', ht⟩, rfl⟩
    exact ⟨k + 1 + n', ChainYieldN.comp hm hb ht rfl⟩

/-- A chain consisting of a single compound task refines exactly like the grid bodies of its
methods. -/
lemma chainYield_singleton_inr_iff {c : C} {as : List A} :
    D.ChainYield [Sum.inr c] as ↔ ∃ ls, D.GridBody c ls ∧ D.GridYield ls as := by
  rw [chainYield_cons_inr_iff]
  constructor
  · rintro ⟨ls, bs, as', hm, hb, ht, rfl⟩
    rw [chainYield_nil_iff] at ht
    subst ht
    exact ⟨ls, hm, by simpa using hb⟩
  · rintro ⟨ls, hm, hb⟩
    exact ⟨ls, as, [], hm, hb, by simp, by simp⟩

@[simp] lemma gridYield_nil_iff {as : List A} : D.GridYield [] as ↔ as = [] := by
  simp [GridYield]

lemma gridYield_cons_iff {l : List (A ⊕ C)} {ls : List (List (A ⊕ C))} {cs : List A} :
    D.GridYield (l :: ls) cs ↔ ∃ as bs, D.ChainYield l as ∧ D.GridYield ls bs ∧
      Interleave as bs cs := by
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨n₁, n₂, as, bs, rfl, hc, hg, hint⟩ := gridYieldN_cons_iff.1 h
    exact ⟨as, bs, ⟨n₁, hc⟩, ⟨n₂, hg⟩, hint⟩
  · rintro ⟨as, bs, ⟨n₁, hc⟩, ⟨n₂, hg⟩, hint⟩
    exact ⟨n₁ + n₂, GridYieldN.cons hc hg hint⟩

/-- A grid with a single chain refines exactly like that chain. -/
lemma gridYield_singleton_iff {l : List (A ⊕ C)} {as : List A} :
    D.GridYield [l] as ↔ D.ChainYield l as := by
  rw [gridYield_cons_iff]
  constructor
  · rintro ⟨as', bs, hc, hg, hint⟩
    rw [gridYield_nil_iff] at hg
    subst hg
    rw [hint.eq_of_nil_right]
    exact hc
  · intro hc
    exact ⟨as, [], hc, by simp, Interleave.nil_right as⟩

/-- **Refinements of a concatenation of chains are the concatenations of refinements of the two
parts.** -/
lemma chainYield_append_iff {xs ys : List (A ⊕ C)} {cs : List A} :
    D.ChainYield (xs ++ ys) cs ↔ ∃ as bs, cs = as ++ bs ∧ D.ChainYield xs as ∧
      D.ChainYield ys bs := by
  induction xs generalizing cs with
  | nil =>
      simp only [List.nil_append, chainYield_nil_iff]
      constructor
      · intro h
        exact ⟨[], cs, rfl, rfl, h⟩
      · rintro ⟨as, bs, rfl, rfl, h⟩
        simpa using h
  | cons x xs ih =>
      cases x with
      | inl a =>
          rw [List.cons_append, chainYield_cons_inl_iff]
          constructor
          · rintro ⟨cs', rfl, h⟩
            obtain ⟨as, bs, rfl, h₁, h₂⟩ := ih.1 h
            exact ⟨a :: as, bs, rfl, chainYield_cons_inl_iff.2 ⟨as, rfl, h₁⟩, h₂⟩
          · rintro ⟨as, bs, rfl, h₁, h₂⟩
            obtain ⟨as', rfl, h₁'⟩ := chainYield_cons_inl_iff.1 h₁
            exact ⟨as' ++ bs, rfl, ih.2 ⟨as', bs, rfl, h₁', h₂⟩⟩
      | inr c =>
          rw [List.cons_append, chainYield_cons_inr_iff]
          constructor
          · rintro ⟨ls, bs, as, hm, hb, ht, rfl⟩
            obtain ⟨as₁, as₂, rfl, h₁, h₂⟩ := ih.1 ht
            exact ⟨bs ++ as₁, as₂, by simp, chainYield_cons_inr_iff.2
              ⟨ls, bs, as₁, hm, hb, h₁, rfl⟩, h₂⟩
          · rintro ⟨as, bs, rfl, h₁, h₂⟩
            obtain ⟨ls, bs', as', hm, hb, ht, rfl⟩ := chainYield_cons_inr_iff.1 h₁
            exact ⟨ls, bs', as' ++ bs, hm, hb, ih.2 ⟨as', bs, rfl, ht, h₂⟩, by simp⟩

/-- **Refinements of a concatenation of grids are the interleavings of refinements of the two
parts.** -/
lemma gridYield_append_iff {ls₁ ls₂ : List (List (A ⊕ C))} {cs : List A} :
    D.GridYield (ls₁ ++ ls₂) cs ↔ ∃ as bs, D.GridYield ls₁ as ∧ D.GridYield ls₂ bs ∧
      Interleave as bs cs := by
  induction ls₁ generalizing cs with
  | nil =>
      simp only [List.nil_append, gridYield_nil_iff]
      constructor
      · intro h
        exact ⟨[], cs, rfl, h, Interleave.nil_left cs⟩
      · rintro ⟨as, bs, rfl, h, hint⟩
        rw [hint.eq_of_nil_left]
        exact h
  | cons l ls₁ ih =>
      rw [List.cons_append, gridYield_cons_iff]
      constructor
      · rintro ⟨as, bs, hc, hg, hint⟩
        obtain ⟨bs₁, bs₂, hg₁, hg₂, hintb⟩ := ih.1 hg
        obtain ⟨x, hx₁, hx₂⟩ := Interleave.assoc' hintb hint
        exact ⟨x, bs₂, gridYield_cons_iff.2 ⟨as, bs₁, hc, hg₁, hx₁⟩, hg₂, hx₂⟩
      · rintro ⟨as, bs, hg₁, hg₂, hint⟩
        obtain ⟨as₁, as₂, hc, hg₁', hinta⟩ := gridYield_cons_iff.1 hg₁
        obtain ⟨y, hy₁, hy₂⟩ := Interleave.assoc hinta hint
        exact ⟨as₁, y, hc, ih.2 ⟨as₂, bs, hg₁', hg₂, hy₁⟩, hy₂⟩

/-! ### Equivalence with the semantic refinement relation -/

omit [Inhabited A] in
/-- A network without tasks refines only into the empty action sequence, in no steps. -/
lemma netYieldN_empty_iff {D : Domain F A C (ℕ × ℕ)} {n : ℕ} {tn : TaskNetwork (ℕ × ℕ) A C}
    {as : List A} (hT : tn.T = ∅) :
    D.NetYieldN n tn as ↔ n = 0 ∧ as = [] := by
  constructor
  · rintro ⟨sol, hsteps, hprim, l, hlin, has⟩
    have hn : n = 0 := by
      by_contra hn
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨tn₂, ⟨t, m, -, ht, -⟩, -⟩ := hsteps.exists_head
      rw [hT] at ht
      simp at ht
    subst hn
    cases hsteps with
    | refl =>
        have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons x l =>
              have := (hlin.2.1 x).1 (by simp)
              rw [hT] at this
              simp at this
        subst hl
        have : ([] : List (A ⊕ C)) = as.map Sum.inl := has
        exact ⟨rfl, by simpa using this.symm⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨tn, StepsN.refl _, ?_, [], ⟨by simp, ?_, by simp⟩, rfl⟩
    · intro x hx
      rw [hT] at hx
      simp at hx
    · intro t
      rw [hT]
      simp

/-- **The syntactic and the semantic refinement relations agree**, both for chains and for
grids, for every domain whose methods have grid subtask networks. -/
theorem netYieldN_grid_and_seq_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) (n : ℕ) :
    (∀ n' ≤ n, ∀ (xs : List (A ⊕ C)) (as : List A),
        D.NetYieldN n' (TaskNetwork.seq xs) as ↔ D.ChainYieldN n' xs as) ∧
      (∀ n' ≤ n, ∀ (ls : List (List (A ⊕ C))) (as : List A),
        D.NetYieldN n' (TaskNetwork.grid ls) as ↔ D.GridYieldN n' ls as) := by
  have hmwf : ∀ m ∈ D.methods, m.subtasks.WF := by
    intro m hm
    obtain ⟨ls, hls⟩ := hgrid m hm
    rw [hls]
    exact TaskNetwork.grid_wf
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    -- chains
    have hchain : ∀ (xs : List (A ⊕ C)), ∀ n' ≤ n, ∀ as : List A,
        (D.NetYieldN n' (TaskNetwork.seq xs) as ↔ D.ChainYieldN n' xs as) := by
      intro xs
      induction xs with
      | nil =>
          intro n' hn' as
          rw [netYieldN_empty_iff TaskNetwork.seq_nil_T, chainYieldN_nil_iff]
      | cons x xs ih =>
          intro n' hn' as
          rw [netYieldN_isSeries_iff (TaskNetwork.isSeries_seq_cons x xs)
            TaskNetwork.seq_wf TaskNetwork.seqShift_wf]
          constructor
          · rintro ⟨n₁, n₂, as₁, as₂, rfl, rfl, hy₁, hy₂⟩
            have hy₂' : D.NetYieldN n₂ (TaskNetwork.seq xs) as₂ :=
              hy₂.iso TaskNetwork.seqShift_wf TaskNetwork.seq_wf TaskNetwork.seqShift_iso
            have hrest : D.ChainYieldN n₂ xs as₂ := (ih n₂ (by omega) as₂).1 hy₂'
            cases x with
            | inl a =>
                rw [netYieldN_single_prim (TaskNetwork.isSingle_seq_singleton (Sum.inl a))
                  (TaskNetwork.seq_singleton_α (Sum.inl a))] at hy₁
                obtain ⟨rfl, rfl⟩ := hy₁
                simpa using ChainYieldN.prim a hrest
            | inr c =>
                rw [netYieldN_single_comp (TaskNetwork.isSingle_seq_singleton (Sum.inr c))
                  (TaskNetwork.seq_singleton_α (Sum.inr c)) hmwf] at hy₁
                obtain ⟨k, m, rfl, hm, hmc, hy⟩ := hy₁
                obtain ⟨ls, hls⟩ := hgrid m hm
                rw [hls] at hy
                have hk : k < n := by omega
                have hg : D.GridYieldN k ls as₁ := ((IH k hk).2 k le_rfl ls as₁).1 hy
                exact ChainYieldN.comp ⟨m, hm, hmc, hls⟩ hg hrest rfl
          · intro h
            cases x with
            | inl a =>
                obtain ⟨as', rfl, hrest⟩ := chainYieldN_cons_inl_iff.1 h
                refine ⟨0, n', [a], as', by omega, rfl, ?_, ?_⟩
                · exact (netYieldN_single_prim (TaskNetwork.isSingle_seq_singleton (Sum.inl a))
                    (TaskNetwork.seq_singleton_α (Sum.inl a))).2 ⟨rfl, rfl⟩
                · exact ((ih n' hn' as').2 hrest).iso TaskNetwork.seq_wf
                    TaskNetwork.seqShift_wf TaskNetwork.seqShift_iso.symm
            | inr c =>
                obtain ⟨k, n₂, ls, bs, as', rfl, ⟨m, hm, hmc, hls⟩, hg, hrest, rfl⟩ :=
                  chainYieldN_cons_inr_iff.1 h
                have hk : k < n := by omega
                have hy : D.NetYieldN k m.subtasks bs := by
                  rw [hls]
                  exact ((IH k hk).2 k le_rfl ls bs).2 hg
                refine ⟨k + 1, n₂, bs, as', by omega, rfl, ?_, ?_⟩
                · exact (netYieldN_single_comp (TaskNetwork.isSingle_seq_singleton (Sum.inr c))
                    (TaskNetwork.seq_singleton_α (Sum.inr c)) hmwf).2 ⟨k, m, rfl, hm, hmc, hy⟩
                · exact ((ih n₂ (by omega) as').2 hrest).iso TaskNetwork.seq_wf
                    TaskNetwork.seqShift_wf TaskNetwork.seqShift_iso.symm
    refine ⟨fun n' hn' xs as => hchain xs n' hn' as, ?_⟩
    -- grids
    intro n' hn' ls
    induction ls generalizing n' with
    | nil =>
        intro as
        rw [netYieldN_empty_iff TaskNetwork.grid_nil_T, gridYieldN_nil_iff]
    | cons l ls ih =>
        intro as
        rw [netYieldN_isPar_iff (TaskNetwork.isPar_grid_cons l ls)
          TaskNetwork.seq_wf TaskNetwork.gridShift_wf, gridYieldN_cons_iff]
        constructor
        · rintro ⟨n₁, n₂, as₁, as₂, rfl, hint, hy₁, hy₂⟩
          refine ⟨n₁, n₂, as₁, as₂, rfl, (hchain l n₁ (by omega) as₁).1 hy₁, ?_, hint⟩
          exact ih n₂ (by omega) as₂ |>.1
            (hy₂.iso TaskNetwork.gridShift_wf TaskNetwork.grid_wf TaskNetwork.gridShift_iso)
        · rintro ⟨n₁, n₂, as₁, as₂, rfl, hc, hg, hint⟩
          refine ⟨n₁, n₂, as₁, as₂, rfl, hint, (hchain l n₁ (by omega) as₁).2 hc, ?_⟩
          exact ((ih n₂ (by omega) as₂).2 hg).iso TaskNetwork.grid_wf
            TaskNetwork.gridShift_wf TaskNetwork.gridShift_iso.symm

/-- **Refinements of a grid are exactly the syntactic grid refinements.** -/
theorem netYieldN_grid_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {n : ℕ}
    {ls : List (List (A ⊕ C))} {as : List A} :
    D.NetYieldN n (TaskNetwork.grid ls) as ↔ D.GridYieldN n ls as :=
  (netYieldN_grid_and_seq_iff hgrid n).2 n le_rfl ls as

/-- **Refinements of a chain are exactly the syntactic chain refinements.** -/
theorem netYieldN_seq_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {n : ℕ}
    {xs : List (A ⊕ C)} {as : List A} :
    D.NetYieldN n (TaskNetwork.seq xs) as ↔ D.ChainYieldN n xs as :=
  (netYieldN_grid_and_seq_iff hgrid n).1 n le_rfl xs as

/-- Two presentations of the same grid have the same refinements, with the same number of
steps. -/
theorem gridYieldN_congr {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls) {n : ℕ}
    {ls ls' : List (List (A ⊕ C))} {as : List A}
    (h : TaskNetwork.grid ls = TaskNetwork.grid ls') :
    D.GridYieldN n ls as ↔ D.GridYieldN n ls' as := by
  rw [← netYieldN_grid_iff hgrid, ← netYieldN_grid_iff hgrid, h]

/-- The step-free version for grids. -/
theorem netYield_grid_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {ls : List (List (A ⊕ C))} {as : List A} :
    D.NetYield (TaskNetwork.grid ls) as ↔ D.GridYield ls as :=
  exists_congr fun _ => netYieldN_grid_iff hgrid

/-- The step-free version for chains. -/
theorem netYield_seq_iff {D : Domain F A C (ℕ × ℕ)}
    (hgrid : ∀ m ∈ D.methods, ∃ ls, m.subtasks = TaskNetwork.grid ls)
    {xs : List (A ⊕ C)} {as : List A} :
    D.NetYield (TaskNetwork.seq xs) as ↔ D.ChainYield xs as :=
  exists_congr fun _ => netYieldN_seq_iff hgrid

end Domain

end HTN
