import HtnPlanning.Progression.Progression
import HtnPlanning.Core.DecompositionIso
/-!
# Splitting a task network into a progressed prefix and a remainder

A search node of progression search has already progressed some tasks and still holds the
others.  `HTN.TaskNetwork.Split tn₀ lP tn` says that the network `tn₀` consists exactly of the
tasks of the list `lP` — which are ordered among themselves as `lP` lists them, and none of
which has a predecessor in `tn` — together with the tasks of `tn`, whose mutual ordering and
labelling are those of `tn`.

The point of the definition is `HTN.TaskNetwork.Split.isLinearization`: a linearization of the
remainder, appended to the progressed prefix, is a linearization of the whole network, and the
action sequence it induces is the concatenation of the two.  This is what turns a run of
progression search into a solution of the planning problem.

The file also collects two auxiliary facts used with it: isomorphism is compatible with
progression (`HTN.TaskNetwork.iso_progress`), and the tasks of an action sequence are
primitive.
-/

namespace HTN

universe u v w

variable {I : Type u} {A : Type v} {C : Type w}

namespace TaskNetwork

/-- The ids of an action sequence are primitive. -/
lemma isPrimitiveId_of_isActionSeq {tn : TaskNetwork I A C} {l : List I} {as : List A}
    (h : tn.IsActionSeq l as) : ∀ x ∈ l, tn.IsPrimitiveId x := by
  induction l generalizing as with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    intro x hx
    cases as with
    | nil => exact absurd h (by simp [IsActionSeq])
    | cons a as =>
      simp only [IsActionSeq, List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨a, h.1⟩
      · exact ih h.2 x hx'

/-- **Progression is compatible with isomorphism.** -/
lemma iso_progress [DecidableEq I] {tn tn' : TaskNetwork I A C} {σ : I → I} {t : I}
    (hbij : Set.BijOn σ (tn.T : Set I) (tn'.T : Set I))
    (hord : ∀ x ∈ tn.T, ∀ y ∈ tn.T, (tn.ord x y ↔ tn'.ord (σ x) (σ y)))
    (hα : ∀ x ∈ tn.T, tn.α x = tn'.α (σ x)) (ht : t ∈ tn.T) :
    (tn.progress t).Iso (tn'.progress (σ t)) := by
  have hmaps : ∀ x ∈ tn.T, σ x ∈ tn'.T := fun x hx => by simpa using hbij.mapsTo (by simpa using hx)
  have hinj : ∀ x ∈ tn.T, ∀ y ∈ tn.T, σ x = σ y → x = y := fun x hx y hy h =>
    hbij.injOn (by simpa using hx) (by simpa using hy) h
  refine ⟨σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro x hx
    simp only [progress_T, Finset.coe_erase, Set.mem_diff,
      Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxT, hxt⟩ := hx
    refine ⟨hmaps x (by simpa using hxT), ?_⟩
    intro hcon
    exact hxt (hinj x (by simpa using hxT) t ht hcon)
  · intro x hx y hy hxy
    simp only [progress_T, Finset.coe_erase, Set.mem_diff,
      Set.mem_singleton_iff] at hx hy
    exact hinj x (by simpa using hx.1) y (by simpa using hy.1) hxy
  · intro y hy
    simp only [progress_T, Finset.coe_erase, Set.mem_diff,
      Set.mem_singleton_iff] at hy
    obtain ⟨x, hx, hxy⟩ := hbij.surjOn (by simpa using hy.1)
    refine ⟨x, ?_, hxy⟩
    simp only [progress_T, Finset.coe_erase, Set.mem_diff,
      Set.mem_singleton_iff]
    refine ⟨by simpa using hx, ?_⟩
    rintro rfl
    exact hy.2 hxy.symm
  · intro x hx y hy
    rw [mem_progress_T] at hx hy
    simp only [progress_ord]
    constructor
    · rintro ⟨h, -⟩
      refine ⟨(hord x hx.2 y hy.2).1 h, ?_⟩
      intro hcon
      exact hx.1 (hinj x hx.2 t ht hcon)
    · rintro ⟨h, -⟩
      exact ⟨(hord x hx.2 y hy.2).2 h, hx.1⟩
  · intro x hx
    rw [mem_progress_T] at hx
    simp only [progress_α]
    exact hα x hx.2

/-- `Split tn₀ lP tn`: the network `tn₀` is the already progressed prefix `lP` followed by the
remaining network `tn`. -/
structure Split (tn₀ : TaskNetwork I A C) (lP : List I) (tn : TaskNetwork I A C) : Prop where
  /-- The progressed tasks are pairwise distinct. -/
  nodup : lP.Nodup
  /-- `tn₀` consists of the progressed tasks and the remaining ones. -/
  mem : ∀ x, x ∈ tn₀.T ↔ (x ∈ lP ∨ x ∈ tn.T)
  /-- A progressed task is no longer in the remaining network. -/
  disj : ∀ x ∈ lP, x ∉ tn.T
  /-- The progressed tasks are listed in an order compatible with `≺`. -/
  pairwise : lP.Pairwise (fun a b => ¬ tn₀.ord b a)
  /-- No remaining task precedes a progressed one. -/
  front : ∀ x ∈ tn.T, ∀ y ∈ lP, ¬ tn₀.ord x y
  /-- The remaining tasks are ordered as in `tn`. -/
  ord_iff : ∀ x ∈ tn.T, ∀ y ∈ tn.T, (tn₀.ord x y ↔ tn.ord x y)
  /-- The remaining tasks carry the names they have in `tn`. -/
  alpha : ∀ x ∈ tn.T, tn₀.α x = tn.α x

namespace Split

variable {tn₀ tn : TaskNetwork I A C} {lP : List I}

/-- Every progressed task belongs to the whole network. -/
lemma mem_of_mem_prefix (h : Split tn₀ lP tn) {x : I} (hx : x ∈ lP) : x ∈ tn₀.T :=
  (h.mem x).2 (Or.inl hx)

/-- Every remaining task belongs to the whole network. -/
lemma mem_of_mem_rest (h : Split tn₀ lP tn) {x : I} (hx : x ∈ tn.T) : x ∈ tn₀.T :=
  (h.mem x).2 (Or.inr hx)

/-- A linearization of the remainder, appended to the progressed prefix, is a linearization of
the whole network. -/
lemma isLinearization (h : Split tn₀ lP tn) {l : List I} (hl : tn.IsLinearization l) :
    tn₀.IsLinearization (lP ++ l) := by
  refine ⟨?_, ?_, ?_⟩
  · refine List.Nodup.append h.nodup hl.1 ?_
    intro x hx hxl
    exact h.disj x hx ((hl.2.1 x).1 hxl)
  · intro x
    rw [List.mem_append, h.mem x, hl.2.1 x]
  · refine List.pairwise_append.2 ⟨h.pairwise, ?_, ?_⟩
    · refine List.Pairwise.imp_of_mem ?_ hl.2.2
      intro a b ha hb hab hcon
      exact hab ((h.ord_iff b ((hl.2.1 b).1 hb) a ((hl.2.1 a).1 ha)).1 hcon)
    · intro a ha b hb
      exact h.front b ((hl.2.1 b).1 hb) a ha

/-- The action sequences add up as well. -/
lemma isActionSeq (h : Split tn₀ lP tn) {l : List I} {π as : List A}
    (hπ : tn₀.IsActionSeq lP π) (hl : tn.IsLinearization l) (has : tn.IsActionSeq l as) :
    tn₀.IsActionSeq (lP ++ l) (π ++ as) := by
  have hmap : l.map tn₀.α = l.map tn.α := by
    refine List.map_congr_left ?_
    intro x hx
    exact h.alpha x ((hl.2.1 x).1 hx)
  simp only [IsActionSeq, List.map_append] at hπ has ⊢
  rw [hmap, hπ, has]

end Split

end TaskNetwork

end HTN
