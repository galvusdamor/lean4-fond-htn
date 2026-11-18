import ComplexityTheory.Petri.KLM
/-!
# Generalised problems (KLM sequences) and their characteristic systems

* Walks on **edge triples**: `TWalk E u es v` (each edge of `es` belongs to `E`), effects `teff`,
  firing `TFires`.  Index walks of `KLM.lean` convert to triple walks (`Walk.toT`) and back
  (`TWalk.toIdx`).
* A **block** `(pre, inp, comp, out)`, a **GP** is a list of blocks.  `BlockRun b M M'`: the
  marking `M + pre` agrees with `inp`, a walk of the component from entry to exit fires on all
  coordinates and ends in `M'`, which agrees with `out`.  `Solvable bs`.
* The **characteristic system** (`CharSol`), its **homogeneous** version (`HomSol`), fullness
  (`Full`), the pumping conditions `PumpF`, `PumpB`, well-formedness `WFB`, and **perfectness**
  (`Perfect`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset

variable {ι : Type*}

/-- An edge `(source, vector, target)`. -/
abbrev Edge (ι : Type*) : Type _ := ℕ × (ι → ℤ) × ℕ

/-- Walks on edge triples. -/
inductive TWalk (E : List (Edge ι)) : ℕ → List (Edge ι) → ℕ → Prop
  | nil (u : ℕ) : TWalk E u [] u
  | cons {e : Edge ι} {es : List (Edge ι)} {v : ℕ} : e ∈ E → TWalk E e.2.2 es v →
      TWalk E e.1 (e :: es) v

/-- The effect of a list of edges. -/
def teff (es : List (Edge ι)) : ι → ℤ := (es.map fun e => e.2.1).sum

/-- Firing a list of edges on the coordinates in `S`. -/
def TFires (S : ι → Prop) : (ι → ℤ) → List (Edge ι) → Prop
  | x, [] => ∀ j, S j → 0 ≤ x j
  | x, e :: es => (∀ j, S j → 0 ≤ x j) ∧ TFires S (x + e.2.1) es

section Triples

variable {E E' : List (Edge ι)}

@[simp] theorem teff_nil : teff ([] : List (Edge ι)) = 0 := by simp [teff]

@[simp] theorem teff_cons (e : Edge ι) (es : List (Edge ι)) : teff (e :: es) = e.2.1 + teff es := by
  simp [teff]

theorem teff_append (es es' : List (Edge ι)) : teff (es ++ es') = teff es + teff es' := by
  simp [teff]

theorem TWalk.append {u v w : ℕ} {es es' : List (Edge ι)} (h : TWalk E u es v)
    (h' : TWalk E v es' w) : TWalk E u (es ++ es') w := by
  induction h with
  | nil => exact h'
  | cons he _ ih => exact TWalk.cons he (ih h')

theorem TWalk.mono {u v : ℕ} {es : List (Edge ι)} (h : TWalk E u es v) (hE : ∀ e ∈ es, e ∈ E') :
    TWalk E' u es v := by
  induction h with
  | nil => exact TWalk.nil _
  | cons he _ ih =>
    exact TWalk.cons (hE _ (by simp)) (ih fun e h => hE e (List.mem_cons_of_mem _ h))

theorem TWalk.mem {u v : ℕ} {es : List (Edge ι)} (h : TWalk E u es v) : ∀ e ∈ es, e ∈ E := by
  induction h with
  | nil => simp
  | cons he _ ih =>
    intro e h'
    rcases List.mem_cons.1 h' with rfl | h'
    · exact he
    · exact ih e h'

theorem TFires.start {S : ι → Prop} {x : ι → ℤ} {es : List (Edge ι)} (h : TFires S x es) :
    ∀ j, S j → 0 ≤ x j := by
  cases es with
  | nil => exact h
  | cons e es => exact h.1

theorem tfires_append {S : ι → Prop} (x : ι → ℤ) (es es' : List (Edge ι)) :
    TFires S x (es ++ es') ↔ TFires S x es ∧ TFires S (x + teff es) es' := by
  induction es generalizing x with
  | nil =>
    simp only [List.nil_append, TFires, teff_nil, add_zero]
    exact ⟨fun h => ⟨h.start, h⟩, fun h => h.2⟩
  | cons e es ih =>
    simp only [List.cons_append, TFires, teff_cons]
    rw [ih, ← add_assoc]
    tauto

theorem TFires.end_ok {S : ι → Prop} {x : ι → ℤ} {es : List (Edge ι)} (h : TFires S x es) :
    ∀ j, S j → 0 ≤ (x + teff es) j := by
  have := (tfires_append (S := S) x es []).1 (by simpa using h)
  exact this.2

theorem tfires_mono_set {S T : ι → Prop} {x : ι → ℤ} {es : List (Edge ι)} (h : TFires S x es)
    (hST : ∀ j, T j → S j) : TFires T x es := by
  induction es generalizing x with
  | nil => exact fun j hj => h j (hST j hj)
  | cons e es ih => exact ⟨fun j hj => h.1 j (hST j hj), ih h.2⟩

/-- Firing on `S` depends only on the coordinates in `S`. -/
theorem tfires_congr {S : ι → Prop} {x y : ι → ℤ} {es : List (Edge ι)} (h : TFires S x es)
    (hxy : ∀ j, S j → x j = y j) : TFires S y es := by
  induction es generalizing x y with
  | nil => exact fun j hj => (hxy j hj) ▸ h j hj
  | cons e es ih =>
    refine ⟨fun j hj => (hxy j hj) ▸ h.1 j hj, ih h.2 fun j hj => ?_⟩
    simp [hxy j hj]

end Triples

/-! ### From index walks to triple walks and back -/

namespace Comp

/-- The edge with a given index. -/
def edge (C : Comp ι) (k : ℕ) : Edge ι := C.edges.getD k (0, 0, 0)

end Comp

open Comp

variable {C : Comp ι}

theorem edge_mem {k : ℕ} (hk : k < C.edges.length) : C.edge k ∈ C.edges := by
  unfold Comp.edge
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem Walk.toT {u v : ℕ} {π : List ℕ} (h : Walk C u π v) :
    TWalk C.edges u (π.map C.edge) v := by
  induction h with
  | nil => exact TWalk.nil _
  | @cons k π v hk _ ih =>
    rw [gr_length] at hk
    rw [tgt_gr] at ih
    have := TWalk.cons (edge_mem (C := C) hk) ih
    rw [src_gr]
    exact this

theorem teff_map_edge (π : List ℕ) : teff (π.map C.edge) = C.eff π := by
  induction π with
  | nil => simp
  | cons k π ih => simp [ih, Comp.vec, Comp.edge]

theorem firesOn_iff_tfires {S : ι → Prop} {x : ι → ℤ} {π : List ℕ} :
    FiresOn C S x π ↔ TFires S x (π.map C.edge) := by
  induction π generalizing x with
  | nil => rfl
  | cons k π ih =>
    simp only [FiresOn, List.map_cons, TFires]
    rw [ih]
    rfl

/-- Label agreement along a list of edges, on the coordinates in `S`. -/
def TLab (C : Comp ι) (S : ι → Prop) : ℕ → (ι → ℤ) → List (Edge ι) → Prop
  | u, x, [] => ∀ j, S j → C.lab u j ≠ ⊤ → x j = (C.lab u j).toNat
  | u, x, e :: es => (∀ j, S j → C.lab u j ≠ ⊤ → x j = (C.lab u j).toNat) ∧
      TLab C S e.2.2 (x + e.2.1) es

theorem labOn_iff_tlab {S : ι → Prop} {u : ℕ} {x : ι → ℤ} {π : List ℕ} :
    LabOn C S u x π ↔ TLab C S u x (π.map C.edge) := by
  induction π generalizing u x with
  | nil => rfl
  | cons k π ih =>
    simp only [LabOn, List.map_cons, TLab]
    rw [ih, tgt_gr]
    rfl

theorem TWalk.toIdx {u v : ℕ} {es : List (Edge ι)} (h : TWalk C.edges u es v) :
    ∃ π, Walk C u π v ∧ π.map C.edge = es := by
  induction h with
  | nil u => exact ⟨[], Walk.nil _, rfl⟩
  | @cons e es v he _ ih =>
    obtain ⟨π, hπ, rfl⟩ := ih
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have hkE : C.edge k = C.edges[k] := by
      unfold Comp.edge; rw [List.getD_eq_getElem _ _ hk]
    refine ⟨k :: π, ?_, by simp [hkE]⟩
    have hk' : k < C.gr.length := by rwa [gr_length]
    have := Walk.cons (E := C.gr) hk' (by rwa [tgt_gr, ← Comp.edge, hkE])
    rwa [src_gr, ← Comp.edge, hkE] at this

/-! ### Blocks and generalised problems -/

/-- A block of a generalised problem. -/
structure Block (ι : Type*) where
  pre : ι → ℤ
  inp : ι → ℕ∞
  comp : Comp ι
  out : ι → ℕ∞

/-- A run through a block: from `M` (before adding `pre`) to `M'`. -/
def BlockRun (b : Block ι) (M M' : ι → ℤ) : Prop :=
  Agree (M + b.pre) b.inp ∧ ∃ es, TWalk b.comp.edges b.comp.entry es b.comp.exit ∧
    TFires (fun _ => True) (M + b.pre) es ∧ TLab b.comp (fun _ => True) b.comp.entry (M + b.pre) es ∧
    M' = M + b.pre + teff es ∧ Agree M' b.out

/-- A run through a list of blocks. -/
def ListRun : List (Block ι) → (ι → ℤ) → (ι → ℤ) → Prop
  | [], M, M' => M = M'
  | b :: bs, M, M' => ∃ M₁, BlockRun b M M₁ ∧ ListRun bs M₁ M'

/-- A generalised problem is solvable if it has a run. -/
def Solvable (bs : List (Block ι)) : Prop := ∃ M M', ListRun bs M M'

/-! ### The characteristic system -/

/-- A candidate solution of one block: input marking, edge multiplicities, output marking. -/
structure Tri (ι : Type*) where
  M₁ : ι → ℤ
  ψ : ℕ → ℕ
  M' : ι → ℤ

/-- The effect of a multiset of edges, given by multiplicities. -/
def psum (C : Comp ι) (ψ : ℕ → ℕ) : ι → ℤ := ∑ k ∈ range C.edges.length, (ψ k : ℤ) • C.vec k

/-- The characteristic constraints of one block. -/
def CharOK (b : Block ι) (t : Tri ι) : Prop :=
  (∀ j, 0 ≤ t.M₁ j) ∧ Agree t.M₁ b.inp ∧ Kirch b.comp.gr t.ψ b.comp.entry b.comp.exit ∧
    t.M' = t.M₁ + psum b.comp t.ψ ∧ (∀ j, 0 ≤ t.M' j) ∧ Agree t.M' b.out

/-- The linking constraints, with a function giving the input of the next block from the output
of the previous block and the `pre` vector. -/
def LinkedBy (f : (ι → ℤ) → (ι → ℤ) → (ι → ℤ)) : List (Block ι) → List (Tri ι) → Prop
  | _ :: b' :: bs, t :: t' :: ts => t'.M₁ = f t.M' b'.pre ∧ LinkedBy f (b' :: bs) (t' :: ts)
  | _, _ => True

/-- Solutions of the characteristic system. -/
def CharSol (bs : List (Block ι)) (ts : List (Tri ι)) : Prop :=
  List.Forall₂ CharOK bs ts ∧ LinkedBy (fun M a => M + a) bs ts

/-- The homogeneous constraints of one block. -/
def HomOK (b : Block ι) (t : Tri ι) : Prop :=
  (∀ j, 0 ≤ t.M₁ j) ∧ (∀ j, b.inp j ≠ ⊤ → t.M₁ j = 0) ∧
    Kirch b.comp.gr t.ψ b.comp.entry b.comp.entry ∧ t.M' = t.M₁ + psum b.comp t.ψ ∧
    (∀ j, 0 ≤ t.M' j) ∧ (∀ j, b.out j ≠ ⊤ → t.M' j = 0)

/-- Solutions of the homogeneous system. -/
def HomSol (bs : List (Block ι)) (hs : List (Tri ι)) : Prop :=
  List.Forall₂ HomOK bs hs ∧ LinkedBy (fun M _ => M) bs hs

/-- A homogeneous solution is **full** on a block: every edge and every ω-coordinate of the
boundary is positive. -/
def Full (b : Block ι) (h : Tri ι) : Prop :=
  (∀ k < b.comp.edges.length, 1 ≤ h.ψ k) ∧ (∀ j, b.inp j = ⊤ → 1 ≤ h.M₁ j) ∧
    (∀ j, b.out j = ⊤ → 1 ≤ h.M' j)

/-- The finite values of an ω-vector. -/
def fin0 (μ : ι → ℕ∞) : ι → ℤ := fun j => ((μ j).toNat : ℤ)

/-- **Forward pumping**: a cycle at the entry, firable from the input on its finite coordinates,
strictly increasing every coordinate that is finite in the input but `ω` in the entry label. -/
def PumpF (b : Block ι) : Prop :=
  ∃ es, TWalk b.comp.edges b.comp.entry es b.comp.entry ∧
    TFires (fun j => b.inp j ≠ ⊤) (fin0 b.inp) es ∧
    ∀ j, b.inp j ≠ ⊤ → b.comp.lab b.comp.entry j = ⊤ → 1 ≤ teff es j

/-- **Backward pumping**: a cycle at the exit, firable on the finite coordinates of the output and
ending in the output, strictly decreasing every coordinate that is finite in the output but `ω`
in the exit label. -/
def PumpB (b : Block ι) : Prop :=
  ∃ es, TWalk b.comp.edges b.comp.exit es b.comp.exit ∧
    TFires (fun j => b.out j ≠ ⊤) (fin0 b.out - teff es) es ∧
    ∀ j, b.out j ≠ ⊤ → b.comp.lab b.comp.exit j = ⊤ → teff es j ≤ -1

/-- Well-formed blocks: the component is well formed with monotone labels, and the boundary
vectors agree with the labels of the entry and the exit. -/
def WFB (b : Block ι) : Prop :=
  WF b.comp ∧ LabMono b.comp ∧
    (∀ j, b.comp.lab b.comp.entry j ≠ ⊤ → b.inp j = b.comp.lab b.comp.entry j) ∧
    (∀ j, b.comp.lab b.comp.exit j ≠ ⊤ → b.out j = b.comp.lab b.comp.exit j)

/-- **Perfect** generalised problems. -/
def Perfect (bs : List (Block ι)) : Prop :=
  (∀ b ∈ bs, WFB b ∧ SC b.comp ∧ PumpF b ∧ PumpB b) ∧
    ∃ ts hs, CharSol bs ts ∧ HomSol bs hs ∧ List.Forall₂ Full bs hs

end KLM

end Petri

end HTN
