import ComplexityTheory.Petri.Split
/-!
# Walks on edge triples: splitting, staying in a set, sub-components

Tools for the decomposition steps: splitting triple walks, label agreement along
concatenations, the first exit of a walk from a set of nodes, walks staying in a closed set,
and sub-components (`Comp.sub`) together with the transfer of well-formedness.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*} {E : List (Edge ι)}

theorem TWalk.nil_inv {u v : ℕ} (h : TWalk E u [] v) : u = v := by
  cases h; rfl

theorem TWalk.cons_inv {u v : ℕ} {e : Edge ι} {es : List (Edge ι)} (h : TWalk E u (e :: es) v) :
    u = e.1 ∧ e ∈ E ∧ TWalk E e.2.2 es v := by
  cases h with
  | cons he h => exact ⟨rfl, he, h⟩

theorem twalk_append_iff {u w : ℕ} {es es' : List (Edge ι)} :
    TWalk E u (es ++ es') w ↔ ∃ v, TWalk E u es v ∧ TWalk E v es' w := by
  induction es generalizing u with
  | nil =>
    simp only [List.nil_append]
    exact ⟨fun h => ⟨u, TWalk.nil _, h⟩, fun ⟨v, h1, h2⟩ => h1.nil_inv ▸ h2⟩
  | cons e es ih =>
    simp only [List.cons_append]
    constructor
    · intro h
      obtain ⟨rfl, he, h⟩ := h.cons_inv
      obtain ⟨v, h1, h2⟩ := ih.1 h
      exact ⟨v, TWalk.cons he h1, h2⟩
    · rintro ⟨v, h1, h2⟩
      obtain ⟨rfl, he, h1⟩ := h1.cons_inv
      exact TWalk.cons he (ih.2 ⟨v, h1, h2⟩)

theorem TWalk.endpoint {u v : ℕ} {es : List (Edge ι)} {e : Edge ι} (h : TWalk E u es v)
    (hl : es.getLast? = some e) : v = e.2.2 := by
  induction h with
  | nil => simp at hl
  | @cons e' es v he h ih =>
    cases es with
    | nil => simp at hl; subst hl; exact h.nil_inv.symm
    | cons e'' es => exact ih (by simpa [List.getLast?_cons_cons] using hl)

/-- Label agreement at the start. -/
theorem TLab.head {C : Comp ι} {S : ι → Prop} {u : ℕ} {x : ι → ℤ} {es : List (Edge ι)}
    (h : TLab C S u x es) : ∀ j, S j → C.lab u j ≠ ⊤ → x j = (C.lab u j).toNat := by
  cases es with
  | nil => exact h
  | cons e es => exact h.1

theorem tlab_append {C : Comp ι} {S : ι → Prop} {u v : ℕ} {x : ι → ℤ} {es es' : List (Edge ι)}
    (hw : TWalk E u es v) :
    TLab C S u x (es ++ es') ↔ TLab C S u x es ∧ TLab C S v (x + teff es) es' := by
  induction hw generalizing x with
  | nil u =>
    simp only [List.nil_append, teff_nil, add_zero]
    exact ⟨fun h => ⟨h.head, h⟩, fun h => h.2⟩
  | @cons e es v he h ih =>
    simp only [List.cons_append, TLab, teff_cons]
    rw [ih, ← add_assoc]
    tauto

/-- Label agreement at the end. -/
theorem TLab.last {C : Comp ι} {S : ι → Prop} {u v : ℕ} {x : ι → ℤ} {es : List (Edge ι)}
    (hw : TWalk E u es v) (h : TLab C S u x es) :
    ∀ j, S j → C.lab v j ≠ ⊤ → (x + teff es) j = (C.lab v j).toNat := by
  have := ((tlab_append (es' := []) hw).1 (by simpa using h)).2
  exact this

/-- Label agreement depends only on the labels. -/
theorem tlab_congr {C C' : Comp ι} (hl : C.lab = C'.lab) {S : ι → Prop} {u : ℕ} {x : ι → ℤ}
    {es : List (Edge ι)} (h : TLab C S u x es) : TLab C' S u x es := by
  induction es generalizing u x with
  | nil => exact fun j hj => by rw [← hl]; exact h j hj
  | cons e es ih => exact ⟨fun j hj => by rw [← hl]; exact h.1 j hj, ih h.2⟩

/-- The first occurrence of an element. -/
theorem exists_first {α : Type*} {a : α} {l : List α} (h : a ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ a ∉ l₁ := by
  classical
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · exact ⟨[], l, by simp [hb], by simp⟩
    · obtain ⟨l₁, l₂, rfl, h₁⟩ := ih (by simpa [Ne.symm hb] using h)
      exact ⟨b :: l₁, l₂, rfl, by simp [Ne.symm hb, h₁]⟩

/-- A walk starting in a forward-closed set stays in it. -/
theorem TWalk.stay {u v : ℕ} {es : List (Edge ι)} (hw : TWalk E u es v) (P : ℕ → Prop)
    (hu : P u) (hcl : ∀ e ∈ E, P e.1 → P e.2.2) : P v ∧ ∀ e ∈ es, P e.1 ∧ P e.2.2 := by
  induction hw with
  | nil => exact ⟨hu, by simp⟩
  | @cons e es v he h ih =>
    have h2 := hcl e he hu
    obtain ⟨h3, h4⟩ := ih h2
    refine ⟨h3, fun e' he' => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨hu, h2⟩
    · exact h4 e' he'

/-- The first exit of a walk from a set of nodes. -/
theorem TWalk.split_exit {u v : ℕ} {es : List (Edge ι)} (hw : TWalk E u es v) (P : ℕ → Prop)
    (hu : P u) :
    (∀ e ∈ es, P e.1 ∧ P e.2.2) ∨
      ∃ es₁ e es₂, es = es₁ ++ e :: es₂ ∧ (∀ e' ∈ es₁, P e'.1 ∧ P e'.2.2) ∧ P e.1 ∧ ¬ P e.2.2 := by
  classical
  induction hw with
  | nil => left; simp
  | @cons e es v he h ih =>
    by_cases h2 : P e.2.2
    · rcases ih h2 with h3 | ⟨es₁, e', es₂, rfl, h4, h5, h6⟩
      · left
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · exact ⟨hu, h2⟩
        · exact h3 e' he'
      · right
        refine ⟨e :: es₁, e', es₂, rfl, fun e'' he'' => ?_, h5, h6⟩
        rcases List.mem_cons.1 he'' with rfl | he''
        · exact ⟨hu, h2⟩
        · exact h4 e'' he''
    · right
      exact ⟨[], e, es, rfl, by simp, hu, h2⟩

/-! ### Edge-wise formulations of well-formedness -/

theorem forall_edge_iff {C : Comp ι} {P : ℕ → (ι → ℤ) → ℕ → Prop} :
    (∀ k < C.edges.length, P (src C.gr k) (C.vec k) (tgt C.gr k)) ↔
      ∀ e ∈ C.edges, P e.1 e.2.1 e.2.2 := by
  constructor
  · intro h e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have := h k hk
    rwa [src_gr, tgt_gr, Comp.vec, List.getD_eq_getElem _ _ hk] at this
  · intro h k hk
    rw [src_gr, tgt_gr, Comp.vec, List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)

theorem labOK_iff {C : Comp ι} : LabOK C ↔ ∀ e ∈ C.edges, ∀ j, C.lab e.2.2 j ≠ ⊤ →
    C.lab e.1 j ≠ ⊤ ∧ ((C.lab e.2.2 j).toNat : ℤ) = (C.lab e.1 j).toNat + e.2.1 j :=
  forall_edge_iff (P := fun s a t => ∀ j, C.lab t j ≠ ⊤ →
    C.lab s j ≠ ⊤ ∧ ((C.lab t j).toNat : ℤ) = (C.lab s j).toNat + a j)

theorem labOKB_iff {C : Comp ι} : LabOKB C ↔ ∀ e ∈ C.edges, ∀ j, C.lab e.1 j ≠ ⊤ →
    C.lab e.2.2 j ≠ ⊤ ∧ ((C.lab e.2.2 j).toNat : ℤ) = (C.lab e.1 j).toNat + e.2.1 j :=
  forall_edge_iff (P := fun s a t => ∀ j, C.lab s j ≠ ⊤ →
    C.lab t j ≠ ⊤ ∧ ((C.lab t j).toNat : ℤ) = (C.lab s j).toNat + a j)

theorem wf_iff {C : Comp ι} : WF C ↔ (∀ e ∈ C.edges, e.1 ∈ C.nodes ∧ e.2.2 ∈ C.nodes) ∧
    C.entry ∈ C.nodes ∧ C.exit ∈ C.nodes := by
  unfold WF
  rw [forall_edge_iff (P := fun s _ t => s ∈ C.nodes ∧ t ∈ C.nodes)]

/-! ### Sub-components -/

/-- The sub-component with the nodes satisfying `p`, the edges satisfying `q`, and the given
entry and exit. -/
def Comp.sub (C : Comp ι) (p : ℕ → Prop) [DecidablePred p] (q : Edge ι → Prop)
    [DecidablePred q] (s t : ℕ) : Comp ι :=
  ⟨C.nodes.filter p, C.lab, C.edges.filter q, s, t⟩

theorem labMono_sub {C : Comp ι} (h : LabMono C) (p : ℕ → Prop) [DecidablePred p]
    (q : Edge ι → Prop) [DecidablePred q] (s t : ℕ) : LabMono (C.sub p q s t) := by
  rcases h with h | h
  · left
    rw [labOK_iff] at h ⊢
    intro e he
    exact h e (List.mem_of_mem_filter he)
  · right
    rw [labOKB_iff] at h ⊢
    intro e he
    exact h e (List.mem_of_mem_filter he)

theorem wf_sub {C : Comp ι} (h : WF C) (p : ℕ → Prop) [DecidablePred p]
    (q : Edge ι → Prop) [DecidablePred q] (s t : ℕ)
    (hq : ∀ e ∈ C.edges, q e → p e.1 ∧ p e.2.2) (hs : s ∈ C.nodes ∧ p s)
    (ht : t ∈ C.nodes ∧ p t) : WF (C.sub p q s t) := by
  rw [wf_iff] at h ⊢
  refine ⟨fun e he => ?_, ?_, ?_⟩
  · have he' := List.mem_filter.1 he
    have h1 := h.1 e he'.1
    have h2 := hq e he'.1 (by simpa using he'.2)
    exact ⟨List.mem_filter.2 ⟨h1.1, by simpa using h2.1⟩,
      List.mem_filter.2 ⟨h1.2, by simpa using h2.2⟩⟩
  · exact List.mem_filter.2 ⟨hs.1, by simpa using hs.2⟩
  · exact List.mem_filter.2 ⟨ht.1, by simpa using ht.2⟩

theorem twalk_sub {C : Comp ι} {p : ℕ → Prop} [DecidablePred p] {q : Edge ι → Prop}
    [DecidablePred q] {s t u v : ℕ} {es : List (Edge ι)} :
    TWalk (C.sub p q s t).edges u es v ↔ TWalk C.edges u es v ∧ ∀ e ∈ es, q e := by
  constructor
  · intro h
    refine ⟨h.mono fun e he => List.mem_of_mem_filter (h.mem e he), fun e he => ?_⟩
    simpa using (List.mem_filter.1 (h.mem e he)).2
  · rintro ⟨h, hq⟩
    exact h.mono fun e he => List.mem_filter.2 ⟨h.mem e he, by simpa using hq e he⟩

end KLM

end Petri

end HTN
