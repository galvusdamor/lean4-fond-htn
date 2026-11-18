import ComplexityTheory.Petri.StepD
/-!
# Reversal of components and blocks

`Comp.rev` reverses every edge (negating its vector) and swaps entry and exit.  Runs reverse:
`runC_rev`.  `Block.rev b = ⟨0, b.out, b.comp.rev, b.inp⟩` has the reversed runs
(`blockRun_rev`), so the backward version of step (d) is the forward version applied to the
reversed block, reversed back (`dAltsB`, `dB_valid`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*}

/-- The reversed edge. -/
def revEdge (e : Edge ι) : Edge ι := (e.2.2, -e.2.1, e.1)

@[simp] theorem revEdge_revEdge (e : Edge ι) : revEdge (revEdge e) = e := by
  simp [revEdge]

theorem revEdge_injective : Function.Injective (revEdge (ι := ι)) := fun a b h => by
  rw [← revEdge_revEdge a, h, revEdge_revEdge]

/-- Reversal of a list of edges. -/
def revL (es : List (Edge ι)) : List (Edge ι) := (es.map revEdge).reverse

@[simp] theorem revL_nil : revL ([] : List (Edge ι)) = [] := rfl

theorem revL_cons (e : Edge ι) (es : List (Edge ι)) : revL (e :: es) = revL es ++ [revEdge e] := by
  simp [revL]

theorem revL_revL (es : List (Edge ι)) : revL (revL es) = es := by
  simp [revL, List.map_reverse, List.map_map, Function.comp_def]

theorem teff_revL (es : List (Edge ι)) : teff (revL es) = -teff es := by
  induction es with
  | nil => simp
  | cons e es ih => rw [revL_cons, teff_append, ih]; simp [revEdge]

theorem twalk_revL {E : List (Edge ι)} {u v : ℕ} {es : List (Edge ι)} (h : TWalk E u es v) :
    TWalk (E.map revEdge) v (revL es) u := by
  induction h with
  | nil => exact TWalk.nil _
  | @cons e es v he _ ih =>
    rw [revL_cons]
    exact twalk_append_iff.2 ⟨e.2.2, ih,
      TWalk.cons (List.mem_map.2 ⟨e, he, rfl⟩) (TWalk.nil _)⟩

theorem tfires_revL {S : ι → Prop} {X : ι → ℤ} {es : List (Edge ι)} (h : TFires S X es) :
    TFires S (X + teff es) (revL es) := by
  induction es generalizing X with
  | nil => simpa using h
  | cons e es ih =>
    rw [revL_cons, tfires_append]
    have h2 := ih h.2
    refine ⟨by rwa [teff_cons, ← add_assoc], ?_⟩
    rw [teff_revL, teff_cons]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h.2.start j hj
      simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
      linarith
    · have := h.1 j hj
      simp only [revEdge, Pi.add_apply, Pi.neg_apply] at this ⊢
      linarith

theorem tlab_revL {C C' : Comp ι} (hl : C.lab = C'.lab) {S : ι → Prop} {E : List (Edge ι)}
    {u v : ℕ} {X : ι → ℤ} {es : List (Edge ι)} (hw : TWalk E u es v) (h : TLab C S u X es) :
    TLab C' S v (X + teff es) (revL es) := by
  induction hw generalizing X with
  | nil u =>
    have := tlab_congr hl h
    simpa using this
  | @cons e es v he hw ih =>
    rw [revL_cons, tlab_append (twalk_revL hw)]
    have h2 := ih h.2
    refine ⟨by rwa [teff_cons, ← add_assoc], ?_⟩
    rw [teff_revL, teff_cons]
    refine ⟨fun j hj hj' => ?_, fun j hj hj' => ?_⟩
    · have := h.2.head j hj (by rwa [hl])
      rw [← hl]
      simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
      rw [← this]; ring
    · have := h.1 j hj (by rwa [hl])
      simp only [revEdge, Pi.add_apply, Pi.neg_apply]
      rw [← hl]
      rw [← this]; ring

/-! ### Reversed components and blocks -/

/-- The reversed component. -/
def Comp.rev (C : Comp ι) : Comp ι := ⟨C.nodes, C.lab, C.edges.map revEdge, C.exit, C.entry⟩

@[simp] theorem Comp.rev_rev (C : Comp ι) : C.rev.rev = C := by
  cases C
  simp [Comp.rev, List.map_map, Function.comp_def]

theorem runC_rev {C : Comp ι} {u v : ℕ} {X : ι → ℤ} {es : List (Edge ι)} (h : RunC C u v X es) :
    RunC C.rev v u (X + teff es) (revL es) :=
  ⟨twalk_revL h.1, tfires_revL h.2.1, tlab_revL (C := C) (C' := C.rev) rfl h.1 h.2.2⟩

theorem runC_rev_iff {C : Comp ι} {u v : ℕ} {X : ι → ℤ} {es : List (Edge ι)} :
    RunC C u v X es ↔ RunC C.rev v u (X + teff es) (revL es) := by
  refine ⟨runC_rev, fun h => ?_⟩
  have := runC_rev h
  rwa [Comp.rev_rev, revL_revL, teff_revL, add_neg_cancel_right] at this

/-- The reversed block. -/
def Block.rev (b : Block ι) : Block ι := ⟨0, b.out, b.comp.rev, b.inp⟩

/-- Reversing back, with a given link vector. -/
def Block.unrev (g : Block ι) (pre : ι → ℤ) : Block ι := ⟨pre, g.out, g.comp.rev, g.inp⟩

theorem blockRun_rev {b : Block ι} {M M' : ι → ℤ} :
    BlockRun b M M' ↔ BlockRun b.rev M' (M + b.pre) := by
  rw [blockRun_iff_runC, blockRun_iff_runC]
  simp only [Block.rev, add_zero]
  constructor
  · rintro ⟨h1, es, hr, he, h2⟩
    refine ⟨h2, revL es, ?_, ?_, h1⟩
    · rw [he]; exact runC_rev hr
    · rw [teff_revL, he]; abel
  · rintro ⟨h1, es, hr, he, h2⟩
    refine ⟨h2, revL es, ?_, ?_, h1⟩
    · rw [runC_rev_iff, revL_revL, he, teff_revL]
      simp only [Comp.rev] at hr ⊢
      convert hr using 2
      abel
    · rw [he, teff_revL]; abel

theorem blockRun_unrev {g : Block ι} (hg : g.pre = 0) (pre : ι → ℤ) {M M' : ι → ℤ} :
    BlockRun (g.unrev pre) M M' ↔ BlockRun g M' (M + pre) := by
  rw [blockRun_rev]
  have : (g.unrev pre).rev = g := by
    cases g
    simp only at hg
    simp [Block.unrev, Block.rev, hg]
  rw [this]
  rfl

/-- The alternatives of the backward version of step (d). -/
noncomputable def dAltsB (b : Block ι) (Ns : List (ℕ × (ι → ℕ∞))) : List (List (Block ι)) :=
  (dAlts b.rev Ns).map fun A => A.map fun g => g.unrev b.pre

theorem dAlts_shape {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))} {A : List (Block ι)}
    (h : A ∈ dAlts b Ns) : ∃ g, A = [g] ∧ g.pre = b.pre := by
  simp only [dAlts, List.mem_map] at h
  obtain ⟨p, -, rfl⟩ := h
  exact ⟨_, rfl, rfl⟩

/-- **Validity of the backward step (d)**, from the forward one for the reversed block. -/
theorem dB_valid {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))}
    (hf : ∀ M M', BlockRun b.rev M M' ↔ ∃ A ∈ dAlts b.rev Ns, ListRun A M M')
    (M M' : ι → ℤ) : BlockRun b M M' ↔ ∃ A ∈ dAltsB b Ns, ListRun A M M' := by
  rw [blockRun_rev, hf]
  constructor
  · rintro ⟨A, hA, hr⟩
    obtain ⟨g, rfl, hg⟩ := dAlts_shape hA
    refine ⟨[g.unrev b.pre], List.mem_map.2 ⟨[g], hA, rfl⟩, listRun_singleton.2 ?_⟩
    exact (blockRun_unrev hg _).2 (listRun_singleton.1 hr)
  · rintro ⟨A, hA, hr⟩
    obtain ⟨A', hA', rfl⟩ := List.mem_map.1 hA
    obtain ⟨g, rfl, hg⟩ := dAlts_shape hA'
    refine ⟨[g], hA', listRun_singleton.2 ?_⟩
    exact (blockRun_unrev hg _).1 (listRun_singleton.1 hr)

end KLM

end Petri

end HTN
