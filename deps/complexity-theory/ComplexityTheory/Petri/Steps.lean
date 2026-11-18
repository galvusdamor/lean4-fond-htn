import ComplexityTheory.Petri.Walks
/-!
# Decomposition steps (c): pruning and splitting along a closed set of nodes

* `RunC C u v x es`: `es` is a walk of `C` from `u` to `v`, firing from `x` and agreeing with the
  labels.  Concatenation and sub-component lemmas.
* **Pruning** (`pruneAlts`, `prune_valid`): if `R` contains the entry and is closed under edges,
  the runs of the block are the runs of its restriction to `R`.
* **Splitting** (`splitAlts`, `split_valid`): if `S` contains the entry and is closed backwards
  under edges, a run either stays in `S` or leaves it once, through an edge from `S` to its
  complement, never to return.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*}

/-- A run of a component from `u` to `v`, starting with the marking `x`. -/
def RunC (C : Comp ι) (u v : ℕ) (x : ι → ℤ) (es : List (Edge ι)) : Prop :=
  TWalk C.edges u es v ∧ TFires (fun _ => True) x es ∧ TLab C (fun _ => True) u x es

theorem blockRun_iff_runC {b : Block ι} {M M' : ι → ℤ} :
    BlockRun b M M' ↔ Agree (M + b.pre) b.inp ∧ ∃ es, RunC b.comp b.comp.entry b.comp.exit
      (M + b.pre) es ∧ M' = M + b.pre + teff es ∧ Agree M' b.out := by
  unfold BlockRun RunC
  constructor
  · rintro ⟨h1, es, h2, h3, h4, h5, h6⟩; exact ⟨h1, es, ⟨h2, h3, h4⟩, h5, h6⟩
  · rintro ⟨h1, es, ⟨h2, h3, h4⟩, h5, h6⟩; exact ⟨h1, es, h2, h3, h4, h5, h6⟩

theorem runC_append {C : Comp ι} {u w : ℕ} {x : ι → ℤ} {es es' : List (Edge ι)} :
    RunC C u w x (es ++ es') ↔ ∃ v, RunC C u v x es ∧ RunC C v w (x + teff es) es' := by
  constructor
  · rintro ⟨hw, hf, hl⟩
    obtain ⟨v, hw1, hw2⟩ := twalk_append_iff.1 hw
    rw [tfires_append] at hf
    rw [tlab_append hw1] at hl
    exact ⟨v, ⟨hw1, hf.1, hl.1⟩, ⟨hw2, hf.2, hl.2⟩⟩
  · rintro ⟨v, ⟨hw1, hf1, hl1⟩, ⟨hw2, hf2, hl2⟩⟩
    exact ⟨twalk_append_iff.2 ⟨v, hw1, hw2⟩, (tfires_append _ _ _).2 ⟨hf1, hf2⟩,
      (tlab_append hw1).2 ⟨hl1, hl2⟩⟩

theorem runC_nil {C : Comp ι} {u v : ℕ} {x : ι → ℤ} :
    RunC C u v x [] ↔ u = v ∧ (∀ j, 0 ≤ x j) ∧ Agree x (C.lab u) := by
  constructor
  · rintro ⟨hw, hf, hl⟩
    exact ⟨hw.nil_inv, fun j => hf j trivial, fun j hj => hl j trivial hj⟩
  · rintro ⟨rfl, hf, hl⟩
    exact ⟨TWalk.nil _, fun j _ => hf j, fun j _ hj => hl j hj⟩

theorem runC_cons {C : Comp ι} {u w : ℕ} {x : ι → ℤ} {e : Edge ι} {es : List (Edge ι)} :
    RunC C u w x (e :: es) ↔ u = e.1 ∧ e ∈ C.edges ∧ (∀ j, 0 ≤ x j) ∧ Agree x (C.lab u) ∧
      RunC C e.2.2 w (x + e.2.1) es := by
  constructor
  · rintro ⟨hw, hf, hl⟩
    obtain ⟨rfl, he, hw⟩ := hw.cons_inv
    exact ⟨rfl, he, fun j => hf.1 j trivial, fun j hj => hl.1 j trivial hj, hw, hf.2, hl.2⟩
  · rintro ⟨rfl, he, hf, hl, hw, hf', hl'⟩
    exact ⟨TWalk.cons he hw, ⟨fun j _ => hf j, hf'⟩, ⟨fun j _ hj => hl j hj, hl'⟩⟩

theorem RunC.first {C : Comp ι} {u v : ℕ} {x : ι → ℤ} {es : List (Edge ι)} (h : RunC C u v x es) :
    (∀ j, 0 ≤ x j) ∧ Agree x (C.lab u) :=
  ⟨fun j => h.2.1.start j trivial, fun j hj => h.2.2.head j trivial hj⟩

theorem RunC.last {C : Comp ι} {u v : ℕ} {x : ι → ℤ} {es : List (Edge ι)} (h : RunC C u v x es) :
    (∀ j, 0 ≤ (x + teff es) j) ∧ Agree (x + teff es) (C.lab v) :=
  ⟨fun j => h.2.1.end_ok j trivial, fun j hj => h.2.2.last h.1 j trivial hj⟩

theorem runC_sub {C : Comp ι} {p : ℕ → Prop} [DecidablePred p] {q : Edge ι → Prop}
    [DecidablePred q] {s t u v : ℕ} {x : ι → ℤ} {es : List (Edge ι)} :
    RunC (C.sub p q s t) u v x es ↔ RunC C u v x es ∧ ∀ e ∈ es, q e := by
  unfold RunC
  rw [twalk_sub]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3, tlab_congr (C := C.sub p q s t) (C' := C) rfl h4⟩, h2⟩
  · rintro ⟨⟨h1, h3, h4⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3, tlab_congr (C := C) (C' := C.sub p q s t) rfl h4⟩

theorem listRun_singleton {b : Block ι} {M M' : ι → ℤ} :
    ListRun [b] M M' ↔ BlockRun b M M' := by
  simp [ListRun]

theorem listRun_pair {b b' : Block ι} {M M' : ι → ℤ} :
    ListRun [b, b'] M M' ↔ ∃ M₁, BlockRun b M M₁ ∧ BlockRun b' M₁ M' := by
  simp [ListRun]

/-! ### Pruning -/

section Prune

variable (b : Block ι) (R : ℕ → Prop) [DecidablePred R]

/-- The restriction of a block to a set of nodes. -/
def Block.restr (b : Block ι) (R : ℕ → Prop) [DecidablePred R] (s t : ℕ) : Comp ι :=
  b.comp.sub R (fun e => R e.1 ∧ R e.2.2) s t

/-- The alternatives of pruning a block to a forward-closed set `R`. -/
def pruneAlts : List (List (Block ι)) :=
  if R b.comp.exit then [[{ b with comp := b.restr R b.comp.entry b.comp.exit }]] else []

variable {b R}

theorem prune_valid (hent : R b.comp.entry) (hcl : ∀ e ∈ b.comp.edges, R e.1 → R e.2.2)
    (M M' : ι → ℤ) : BlockRun b M M' ↔ ∃ A ∈ pruneAlts b R, ListRun A M M' := by
  constructor
  · intro h
    obtain ⟨hA, es, hr, he, hA'⟩ := blockRun_iff_runC.1 h
    obtain ⟨hex, hall⟩ := hr.1.stay R hent hcl
    refine ⟨[{ b with comp := b.restr R b.comp.entry b.comp.exit }], by simp [pruneAlts, hex],
      listRun_singleton.2 (blockRun_iff_runC.2 ⟨hA, es, ?_, he, hA'⟩)⟩
    exact runC_sub.2 ⟨hr, hall⟩
  · rintro ⟨A, hA, hr⟩
    unfold pruneAlts at hA
    split_ifs at hA with hex
    · simp only [List.mem_singleton] at hA
      subst hA
      obtain ⟨h1, es, hr, he, hA'⟩ := blockRun_iff_runC.1 (listRun_singleton.1 hr)
      exact blockRun_iff_runC.2 ⟨h1, es, (runC_sub.1 hr).1, he, hA'⟩
    · simp at hA

end Prune

/-! ### Splitting -/

section Split

variable (b : Block ι) (S : ℕ → Prop) [DecidablePred S]

/-- The first block of a split through the edge `e`. -/
def splitFst (e : Edge ι) : Block ι :=
  ⟨b.pre, b.inp, b.restr S b.comp.entry e.1, b.comp.lab e.1⟩

/-- The second block of a split through the edge `e`. -/
def splitSnd (e : Edge ι) : Block ι :=
  ⟨e.2.1, b.comp.lab e.2.2, b.restr (fun v => ¬ S v) e.2.2 b.comp.exit, b.out⟩

/-- The alternatives of splitting a block along a backward-closed set `S`. -/
def splitAlts : List (List (Block ι)) :=
  if S b.comp.exit then [[{ b with comp := b.restr S b.comp.entry b.comp.exit }]]
  else (b.comp.edges.filter fun e => S e.1 ∧ ¬ S e.2.2).map fun e => [splitFst b S e, splitSnd b S e]

variable {b S}

theorem split_valid (hent : S b.comp.entry) (hcl : ∀ e ∈ b.comp.edges, S e.2.2 → S e.1)
    (M M' : ι → ℤ) : BlockRun b M M' ↔ ∃ A ∈ splitAlts b S, ListRun A M M' := by
  have hclN : ∀ e ∈ b.comp.edges, ¬ S e.1 → ¬ S e.2.2 := fun e he h1 h2 => h1 (hcl e he h2)
  constructor
  · intro h
    obtain ⟨hA, es, hr, he, hA'⟩ := blockRun_iff_runC.1 h
    rcases hr.1.split_exit S hent with hall | ⟨es₁, e, es₂, rfl, hall, h1, h2⟩
    · -- the run stays in `S`
      have hr' : RunC (b.restr S b.comp.entry b.comp.exit) b.comp.entry b.comp.exit
          (M + b.pre) es := runC_sub.2 ⟨hr, hall⟩
      have hex : S b.comp.exit := by
        refine (hr'.1.stay S hent fun e he _ => ?_).1
        have := (List.mem_filter.1 he).2
        simp only [decide_eq_true_eq] at this
        exact this.2
      refine ⟨[{ b with comp := b.restr S b.comp.entry b.comp.exit }], by simp [splitAlts, hex],
        listRun_singleton.2 ?_⟩
      exact blockRun_iff_runC.2 ⟨hA, es, hr', he, hA'⟩
    · -- the run leaves `S` through `e`
      obtain ⟨v, hr1, hr2⟩ := runC_append.1 hr
      obtain ⟨rfl, hemem, hpos, hag, hr3⟩ := runC_cons.1 hr2
      have hstay := hr3.1.stay (fun v => ¬ S v) h2 hclN
      have hex : ¬ S b.comp.exit := hstay.1
      refine ⟨[splitFst b S e, splitSnd b S e], ?_, listRun_pair.2 ⟨M + b.pre + teff es₁, ?_, ?_⟩⟩
      · simp only [splitAlts, if_neg hex, List.mem_map, List.mem_filter]
        exact ⟨e, ⟨hemem, by simp [h1, h2]⟩, rfl⟩
      · refine blockRun_iff_runC.2 ⟨hA, es₁, runC_sub.2 ⟨hr1, hall⟩, rfl, ?_⟩
        exact (hr1.last).2
      · refine blockRun_iff_runC.2 ⟨hr3.first.2, es₂, runC_sub.2 ⟨hr3, hstay.2⟩, ?_, ?_⟩
        · simp only [splitSnd]; rw [he, teff_append, teff_cons]; abel
        · exact hA'
  · rintro ⟨A, hA, hr⟩
    unfold splitAlts at hA
    split_ifs at hA with hex
    · simp only [List.mem_singleton] at hA
      subst hA
      obtain ⟨h1, es, hr, he, hA'⟩ := blockRun_iff_runC.1 (listRun_singleton.1 hr)
      exact blockRun_iff_runC.2 ⟨h1, es, (runC_sub.1 hr).1, he, hA'⟩
    · simp only [List.mem_map, List.mem_filter] at hA
      obtain ⟨e, ⟨hemem, -⟩, rfl⟩ := hA
      obtain ⟨M₁, r1, r2⟩ := listRun_pair.1 hr
      obtain ⟨h1, es₁, hr1, he1, -⟩ := blockRun_iff_runC.1 r1
      obtain ⟨h2, es₂, hr2, he2, hA'⟩ := blockRun_iff_runC.1 r2
      have hr1' := (runC_sub.1 hr1).1
      have hr2' := (runC_sub.1 hr2).1
      refine blockRun_iff_runC.2 ⟨h1, es₁ ++ e :: es₂, ?_, ?_, hA'⟩
      · refine runC_append.2 ⟨e.1, hr1', runC_cons.2 ⟨rfl, hemem, ?_, ?_, ?_⟩⟩
        · have := hr1'.last.1; simpa using this
        · have := hr1'.last.2; simpa using this
        · simp only [splitFst, splitSnd] at he1 hr2' ⊢
          rw [← he1]
          exact hr2'
      · simp only [splitFst, splitSnd] at he1 he2
        rw [he2, he1, teff_append, teff_cons]; abel

end Split

end KLM

end Petri

end HTN
