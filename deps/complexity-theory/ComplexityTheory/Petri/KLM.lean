import ComplexityTheory.Petri.Euler
/-!
# Components of KLM sequences: graphs with ω-labelled nodes

This file fixes the vocabulary of the Kosaraju–Lambert–Mayr decomposition, over a finite type
`ι` of coordinates (places).

* `HTN.Petri.KLM.Comp ι` — a **component**: nodes, an ω-vector label `lab v : ι → ℕ∞` for each
  node, a list of edges `(u, a, v)` labelled by integer vectors `a : ι → ℤ`, an entry and an
  exit node.
* `Walk C u π v` — `π` is a list of edge indices forming a walk from `u` to `v`;
  `eff C π` is its total effect, `FiresOn C S x π` says that, starting from `x : ι → ℤ`, the
  coordinates in `S` stay non-negative along `π`.
* `LabOK C` — the labels are consistent along edges: a coordinate that is finite at the target
  of an edge is finite at its source, and the values differ by the vector of the edge.
* `SC C` — strong connectivity, `WF C` — edges and the entry/exit are among the nodes.

and proves the bookkeeping lemmas the iteration lemma of `ComplexityTheory/Petri/Lambert.lean`
needs: effects and Parikh vectors of concatenations and repetitions, Kirchhoff's law for the
Parikh vector of a walk, firing along concatenations and repetitions, label agreement along
walks.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset

/-- **A component**: a graph with ω-labelled nodes and vector-labelled edges, with an entry and
an exit node. -/
structure Comp (ι : Type*) where
  nodes : List ℕ
  lab : ℕ → ι → ℕ∞
  edges : List (ℕ × (ι → ℤ) × ℕ)
  entry : ℕ
  exit : ℕ

variable {ι : Type*}

namespace Comp

variable (C : Comp ι)

/-- The underlying graph. -/
def gr : List (ℕ × ℕ) := C.edges.map fun e => (e.1, e.2.2)

/-- The vector of an edge. -/
def vec (k : ℕ) : ι → ℤ := (C.edges.getD k (0, 0, 0)).2.1

/-- The effect of a list of edges. -/
def eff (π : List ℕ) : ι → ℤ := (π.map C.vec).sum

/-- `x` agrees with the ω-vector `μ`: equal on the finite coordinates of `μ`. -/
def Agree (x : ι → ℤ) (μ : ι → ℕ∞) : Prop := ∀ j, μ j ≠ ⊤ → x j = ((μ j).toNat : ℤ)

end Comp

open Comp

variable {C : Comp ι}

theorem gr_length (C : Comp ι) : C.gr.length = C.edges.length := by simp [gr]

theorem gr_getD (C : Comp ι) (k : ℕ) :
    C.gr.getD k (0, 0) = ((C.edges.getD k (0, 0, 0)).1, (C.edges.getD k (0, 0, 0)).2.2) := by
  simp only [gr, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases C.edges[k]? <;> rfl

theorem src_gr (C : Comp ι) (k : ℕ) : src C.gr k = (C.edges.getD k (0, 0, 0)).1 := by
  unfold src; rw [gr_getD]

theorem tgt_gr (C : Comp ι) (k : ℕ) : tgt C.gr k = (C.edges.getD k (0, 0, 0)).2.2 := by
  unfold tgt; rw [gr_getD]

/-- A walk of a component. -/
abbrev Walk (C : Comp ι) : ℕ → List ℕ → ℕ → Prop := Euler.Walk C.gr

/-! ### Effects -/

@[simp] theorem eff_nil : C.eff [] = 0 := by simp [eff]

@[simp] theorem eff_cons (k : ℕ) (π : List ℕ) : C.eff (k :: π) = C.vec k + C.eff π := by
  simp [eff]

theorem eff_append (π π' : List ℕ) : C.eff (π ++ π') = C.eff π + C.eff π' := by
  simp [eff]

theorem eff_rep (n : ℕ) (π : List ℕ) : C.eff (List.replicate n π).flatten = n • C.eff π := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, eff_append, ih, succ_nsmul']

theorem count_rep (n : ℕ) (π : List ℕ) (k : ℕ) :
    (List.replicate n π).flatten.count k = n * π.count k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.count_append, ih]; ring

/-- The effect of a list of edges of the component, through its Parikh vector. -/
theorem eff_eq_sum (π : List ℕ) (hπ : ∀ k ∈ π, k < C.edges.length) :
    C.eff π = ∑ k ∈ range C.edges.length, (π.count k : ℤ) • C.vec k := by
  induction π with
  | nil => simp
  | cons k π ih =>
    rw [eff_cons, ih fun k' h => hπ k' (List.mem_cons_of_mem _ h)]
    have hk : k ∈ range C.edges.length := Finset.mem_range.2 (hπ k (by simp))
    rw [← Finset.add_sum_erase (range _) (fun k' => (π.count k' : ℤ) • C.vec k') hk,
      ← Finset.add_sum_erase (range _) (fun k' => ((k :: π).count k' : ℤ) • C.vec k') hk]
    have hs : (∑ x ∈ (range C.edges.length).erase k, ((k :: π).count x : ℤ) • C.vec x) =
        ∑ x ∈ (range C.edges.length).erase k, (π.count x : ℤ) • C.vec x :=
      Finset.sum_congr rfl fun x hx => by
        rw [List.count_cons_of_ne (Ne.symm (Finset.ne_of_mem_erase hx))]
    rw [hs, List.count_cons_self]
    push_cast
    rw [add_smul, one_smul]
    abel

/-- The absolute bound on the coordinates of the edge vectors. -/
def Comp.amax (C : Comp ι) [Fintype ι] : ℤ := ∑ k ∈ range C.edges.length, ∑ j, |C.vec k j|

theorem amax_nonneg [Fintype ι] : 0 ≤ C.amax :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_vec_le [Fintype ι] {k : ℕ} (hk : k < C.edges.length) (j : ι) :
    |C.vec k j| ≤ C.amax := by
  have h1 : |C.vec k j| ≤ ∑ j, |C.vec k j| :=
    Finset.single_le_sum (f := fun j => |C.vec k j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j, |C.vec k j| ≤ C.amax :=
    Finset.single_le_sum (f := fun k => ∑ j, |C.vec k j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hk)
  linarith

theorem abs_eff_le [Fintype ι] (π : List ℕ) (hπ : ∀ k ∈ π, k < C.edges.length) (j : ι) :
    |C.eff π j| ≤ π.length * C.amax := by
  induction π with
  | nil => simp
  | cons k π ih =>
    rw [eff_cons, Pi.add_apply, List.length_cons]
    have h1 := abs_vec_le (C := C) (hπ k (by simp)) j
    have h2 := ih fun k' h => hπ k' (List.mem_cons_of_mem _ h)
    calc |C.vec k j + C.eff π j| ≤ |C.vec k j| + |C.eff π j| := abs_add_le _ _
      _ ≤ C.amax + π.length * C.amax := add_le_add h1 h2
      _ = ((π.length + 1 : ℕ) : ℤ) * C.amax := by push_cast; ring

/-! ### Firing -/

/-- Along `π` from `x`, every coordinate in `S` stays non-negative. -/
def FiresOn (C : Comp ι) (S : ι → Prop) : (ι → ℤ) → List ℕ → Prop
  | x, [] => ∀ j, S j → 0 ≤ x j
  | x, k :: π => (∀ j, S j → 0 ≤ x j) ∧ FiresOn C S (x + C.vec k) π

theorem FiresOn.start {S : ι → Prop} {x : ι → ℤ} {π : List ℕ} (h : FiresOn C S x π) :
    ∀ j, S j → 0 ≤ x j := by
  cases π with
  | nil => exact h
  | cons k π => exact h.1

theorem firesOn_append {S : ι → Prop} (x : ι → ℤ) (π π' : List ℕ) :
    FiresOn C S x (π ++ π') ↔ FiresOn C S x π ∧ FiresOn C S (x + C.eff π) π' := by
  induction π generalizing x with
  | nil =>
    simp only [List.nil_append, FiresOn, eff_nil, add_zero]
    exact ⟨fun h => ⟨h.start, h⟩, fun h => h.2⟩
  | cons k π ih =>
    simp only [List.cons_append, FiresOn, eff_cons]
    rw [ih, ← add_assoc]
    tauto

theorem FiresOn.end_ok {S : ι → Prop} {x : ι → ℤ} {π : List ℕ} (h : FiresOn C S x π) :
    FiresOn C S (x + C.eff π) [] := by
  induction π generalizing x with
  | nil => simpa using h
  | cons k π ih =>
    have := ih h.2
    simpa [add_assoc] using this

theorem firesOn_rep {S : ι → Prop} (x : ι → ℤ) (π : List ℕ) (n : ℕ) (hn : 1 ≤ n) :
    FiresOn C S x (List.replicate n π).flatten ↔
      ∀ i < n, FiresOn C S (x + i • C.eff π) π := by
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, firesOn_append]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp only [List.replicate_zero, List.flatten_nil, zero_add, Nat.lt_one_iff, forall_eq,
        zero_smul, add_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, h.end_ok⟩⟩
    · rw [ih _ hn']
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases i with _ | i
        · simpa using h1
        · have := h2 i (by omega)
          rwa [add_assoc, ← succ_nsmul'] at this
      · intro h
        refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
        have := h (i + 1) (by omega)
        rwa [add_assoc, ← succ_nsmul']

/-- A single coordinate stays non-negative if it starts high enough. -/
theorem firesOn_of_ge [Fintype ι] {j : ι} {x : ι → ℤ} {π : List ℕ}
    (hπ : ∀ k ∈ π, k < C.edges.length) (hx : π.length * C.amax ≤ x j) :
    FiresOn C (· = j) x π := by
  induction π generalizing x with
  | nil =>
    intro j' hj'
    rw [hj']
    simp at hx
    exact hx
  | cons k π ih =>
    refine ⟨?_, ih (fun k' h => hπ k' (List.mem_cons_of_mem _ h)) ?_⟩
    · intro j' hj'
      rw [hj']
      have := amax_nonneg (C := C)
      have : (0 : ℤ) ≤ (List.length (k :: π) : ℤ) * C.amax := by positivity
      linarith
    · have h1 := abs_vec_le (C := C) (hπ k (by simp)) j
      rw [Pi.add_apply]
      rw [List.length_cons] at hx
      push_cast at hx
      have := neg_abs_le (C.vec k j)
      linarith

/-- Firing a single coordinate is monotone in the start. -/
theorem firesOn_mono {j : ι} {x y : ι → ℤ} {π : List ℕ} (h : FiresOn C (· = j) y π)
    (hxy : y j ≤ x j) : FiresOn C (· = j) x π := by
  induction π generalizing x y with
  | nil => intro j' hj'; rw [hj']; exact le_trans (h j rfl) hxy
  | cons k π ih =>
    refine ⟨?_, ih h.2 ?_⟩
    · intro j' hj'; rw [hj']; exact le_trans (h.1 j rfl) hxy
    · simp only [Pi.add_apply]; linarith

theorem firesOn_of_forall {S : ι → Prop} {x : ι → ℤ} {π : List ℕ}
    (h : ∀ j, S j → FiresOn C (· = j) x π) : FiresOn C S x π := by
  induction π generalizing x with
  | nil => exact fun j hj => h j hj j rfl
  | cons k π ih =>
    exact ⟨fun j hj => (h j hj).1 j rfl, ih fun j hj => (h j hj).2⟩

theorem FiresOn.single {S : ι → Prop} {x : ι → ℤ} {π : List ℕ} (h : FiresOn C S x π)
    {j : ι} (hj : S j) : FiresOn C (· = j) x π := by
  induction π generalizing x with
  | nil => intro j' hj'; rw [hj']; exact h j hj
  | cons k π ih => exact ⟨fun j' hj' => hj' ▸ h.1 j hj, ih h.2⟩

/-! ### Well-formedness, labels, strong connectivity -/

/-- The labels are consistent along the edges. -/
def LabOK (C : Comp ι) : Prop :=
  ∀ k < C.edges.length, ∀ j, C.lab (tgt C.gr k) j ≠ ⊤ →
    C.lab (src C.gr k) j ≠ ⊤ ∧
      ((C.lab (tgt C.gr k) j).toNat : ℤ) = (C.lab (src C.gr k) j).toNat + C.vec k j

/-- The edges, the entry and the exit are among the nodes. -/
def WF (C : Comp ι) : Prop :=
  (∀ k < C.edges.length, src C.gr k ∈ C.nodes ∧ tgt C.gr k ∈ C.nodes) ∧
    C.entry ∈ C.nodes ∧ C.exit ∈ C.nodes

/-- Strong connectivity. -/
def SC (C : Comp ι) : Prop := ∀ u ∈ C.nodes, ∀ v ∈ C.nodes, ∃ π, Walk C u π v

/-- A coordinate finite at the end of a walk is finite at its start. -/
theorem lab_ne_top_of_walk (hL : LabOK C) {u v : ℕ} {π : List ℕ} (hw : Walk C u π v) {j : ι}
    (hv : C.lab v j ≠ ⊤) : C.lab u j ≠ ⊤ := by
  induction hw with
  | nil => exact hv
  | cons hk _ ih => exact (hL _ (by rwa [gr_length] at hk) j (ih hv)).1

/-- In a strongly connected component, the finite coordinates are the same at every node. -/
theorem lab_ne_top_iff (hL : LabOK C) (hS : SC C) {u v : ℕ} (hu : u ∈ C.nodes)
    (hv : v ∈ C.nodes) {j : ι} : C.lab u j ≠ ⊤ ↔ C.lab v j ≠ ⊤ := by
  obtain ⟨π, hπ⟩ := hS u hu v hv
  obtain ⟨π', hπ'⟩ := hS v hv u hu
  exact ⟨fun h => lab_ne_top_of_walk hL hπ' h, fun h => lab_ne_top_of_walk hL hπ h⟩

/-- **Along a walk, a coordinate finite at every edge target follows the labels**, hence stays
non-negative. -/
theorem firesOn_of_lab (hL : LabOK C) {j : ι}
    (hfin : ∀ k < C.edges.length, C.lab (tgt C.gr k) j ≠ ⊤) {u v : ℕ} {π : List ℕ}
    (hw : Walk C u π v) {x : ι → ℤ} (hx : x j = (C.lab u j).toNat) :
    FiresOn C (· = j) x π := by
  induction hw generalizing x with
  | nil u => intro j' hj'; rw [hj', hx]; exact Nat.cast_nonneg _
  | @cons k π v hk _ ih =>
    rw [gr_length] at hk
    refine ⟨?_, ih ?_⟩
    · intro j' hj'; rw [hj', hx]; exact Nat.cast_nonneg _
    · rw [Pi.add_apply, hx, (hL k hk j (hfin k hk)).2]

/-- The labels are consistent along the edges, backwards: a coordinate finite at the source of an
edge is finite at its target, and the values differ by the vector of the edge. -/
def LabOKB (C : Comp ι) : Prop :=
  ∀ k < C.edges.length, ∀ j, C.lab (src C.gr k) j ≠ ⊤ →
    C.lab (tgt C.gr k) j ≠ ⊤ ∧
      ((C.lab (tgt C.gr k) j).toNat : ℤ) = (C.lab (src C.gr k) j).toNat + C.vec k j

/-- Labels consistent forwards or backwards. -/
def LabMono (C : Comp ι) : Prop := LabOK C ∨ LabOKB C

/-- Exactness of the labels on the coordinates finite at both ends of an edge. -/
def Exact (C : Comp ι) : Prop :=
  ∀ k < C.edges.length, ∀ j, C.lab (src C.gr k) j ≠ ⊤ → C.lab (tgt C.gr k) j ≠ ⊤ →
    ((C.lab (tgt C.gr k) j).toNat : ℤ) = (C.lab (src C.gr k) j).toNat + C.vec k j

theorem LabMono.exact (h : LabMono C) : Exact C := by
  rcases h with h | h
  · exact fun k hk j _ ht => (h k hk j ht).2
  · exact fun k hk j hs _ => (h k hk j hs).2

theorem lab_ne_top_of_walkB (hL : LabOKB C) {u v : ℕ} {π : List ℕ} (hw : Walk C u π v) {j : ι}
    (hu : C.lab u j ≠ ⊤) : C.lab v j ≠ ⊤ := by
  induction hw with
  | nil => exact hu
  | cons hk _ ih => exact ih (hL _ (by rwa [gr_length] at hk) j hu).1

/-- In a strongly connected component with monotone labels, the finite coordinates are the same
at every node. -/
theorem lab_ne_top_iff' (hM : LabMono C) (hS : SC C) {u v : ℕ} (hu : u ∈ C.nodes)
    (hv : v ∈ C.nodes) {j : ι} : C.lab u j ≠ ⊤ ↔ C.lab v j ≠ ⊤ := by
  rcases hM with hL | hL
  · exact lab_ne_top_iff hL hS hu hv
  · obtain ⟨π, hπ⟩ := hS u hu v hv
    obtain ⟨π', hπ'⟩ := hS v hv u hu
    exact ⟨fun h => lab_ne_top_of_walkB hL hπ h, fun h => lab_ne_top_of_walkB hL hπ' h⟩

/-- Label agreement along a walk, on the coordinates in `S`. -/
def LabOn (C : Comp ι) (S : ι → Prop) : ℕ → (ι → ℤ) → List ℕ → Prop
  | u, x, [] => ∀ j, S j → C.lab u j ≠ ⊤ → x j = (C.lab u j).toNat
  | u, x, k :: π => (∀ j, S j → C.lab u j ≠ ⊤ → x j = (C.lab u j).toNat) ∧
      LabOn C S (tgt C.gr k) (x + C.vec k) π

theorem labOn_of_forall {S : ι → Prop} {u : ℕ} {x : ι → ℤ} {π : List ℕ}
    (h : ∀ j, S j → LabOn C (· = j) u x π) : LabOn C S u x π := by
  induction π generalizing u x with
  | nil => exact fun j hj => h j hj j rfl
  | cons k π ih =>
    exact ⟨fun j hj => (h j hj).1 j rfl, ih fun j hj => (h j hj).2⟩

/-- Along a walk, a coordinate finite at both ends of every edge follows the labels. -/
theorem labOn_of_exact (hE : Exact C) {j : ι}
    (hfin : ∀ k < C.edges.length, C.lab (src C.gr k) j ≠ ⊤ ∧ C.lab (tgt C.gr k) j ≠ ⊤)
    {u v : ℕ} {π : List ℕ} (hw : Walk C u π v) {x : ι → ℤ} (hx : x j = (C.lab u j).toNat) :
    LabOn C (· = j) u x π ∧ FiresOn C (· = j) x π := by
  induction hw generalizing x with
  | nil u =>
    exact ⟨fun j' hj' _ => hj' ▸ hx, fun j' hj' => by rw [hj', hx]; exact Nat.cast_nonneg _⟩
  | @cons k π v hk _ ih =>
    rw [gr_length] at hk
    have := ih (x := x + C.vec k) (by
      rw [Pi.add_apply, hx, hE k hk j (hfin k hk).1 (hfin k hk).2])
    exact ⟨⟨fun j' hj' _ => hj' ▸ hx, this.1⟩,
      ⟨fun j' hj' => by rw [hj', hx]; exact Nat.cast_nonneg _, this.2⟩⟩

/-- Along a walk, a coordinate that is `ω` everywhere imposes nothing. -/
theorem labOn_of_top {j : ι} (htop : ∀ k < C.edges.length, C.lab (tgt C.gr k) j = ⊤)
    {u v : ℕ} {π : List ℕ} (hw : Walk C u π v) (hu : C.lab u j = ⊤) (x : ι → ℤ) :
    LabOn C (· = j) u x π := by
  induction hw generalizing x with
  | nil u => exact fun j' hj' h => absurd (hj' ▸ hu) h
  | @cons k π v hk _ ih =>
    rw [gr_length] at hk
    exact ⟨fun j' hj' h => absurd (hj' ▸ hu) h, ih (htop k hk) _⟩

/-- Walks only use edges of the component. -/
theorem Walk.lt' {u v : ℕ} {π : List ℕ} (hw : Walk C u π v) : ∀ k ∈ π, k < C.edges.length := by
  intro k hk
  have := Euler.Walk.lt hw k hk
  rwa [gr_length] at this

/-! ### Kirchhoff's law -/

theorem outF_add (E : List (ℕ × ℕ)) (ψ φ : ℕ → ℕ) (w : ℕ) :
    outF E (ψ + φ) w = outF E ψ w + outF E φ w := by
  unfold outF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem inF_add (E : List (ℕ × ℕ)) (ψ φ : ℕ → ℕ) (w : ℕ) :
    inF E (ψ + φ) w = inF E ψ w + inF E φ w := by
  unfold inF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem outF_smul (E : List (ℕ × ℕ)) (c : ℕ) (ψ : ℕ → ℕ) (w : ℕ) :
    outF E (c • ψ) w = c * outF E ψ w := by
  unfold outF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem inF_smul (E : List (ℕ × ℕ)) (c : ℕ) (ψ : ℕ → ℕ) (w : ℕ) :
    inF E (c • ψ) w = c * inF E ψ w := by
  unfold inF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem kirch_add {E : List (ℕ × ℕ)} {ψ φ : ℕ → ℕ} {s t u : ℕ} (h : Kirch E ψ s t)
    (h' : Kirch E φ u u) : Kirch E (ψ + φ) s t := by
  intro w
  have h1 := h w
  have h2 := h' w
  rw [outF_add, inF_add]
  omega

theorem kirch_smul {E : List (ℕ × ℕ)} {ψ : ℕ → ℕ} {u : ℕ} (c : ℕ) (h : Kirch E ψ u u) :
    Kirch E (c • ψ) u u := by
  intro w
  have h1 := h w
  rw [outF_smul, inF_smul]
  split_ifs at h1 ⊢ <;> simp_all

/-- Balanced flows may be subtracted. -/
theorem kirch_of_add {E : List (ℕ × ℕ)} {ψ φ : ℕ → ℕ} {s t u : ℕ} (h : Kirch E (ψ + φ) s t)
    (h' : Kirch E φ u u) : Kirch E ψ s t := by
  intro w
  have h1 := h w
  have h2 := h' w
  rw [outF_add, inF_add] at h1
  omega

theorem kirch_balanced_iff {E : List (ℕ × ℕ)} {ψ : ℕ → ℕ} {u u' : ℕ} :
    Kirch E ψ u u ↔ Kirch E ψ u' u' := by
  constructor <;> intro h w <;> have := h w <;> split_ifs at this ⊢ <;> omega

theorem sum_ite_count_cons (n k : ℕ) (hk : k < n) (π : List ℕ) (g : ℕ → Prop)
    [DecidablePred g] :
    (∑ k' ∈ range n, if g k' then (k :: π).count k' else 0) =
      (∑ k' ∈ range n, if g k' then π.count k' else 0) + if g k then 1 else 0 := by
  have hk' := Finset.mem_range.2 hk
  rw [← Finset.add_sum_erase (range n) (fun k' => if g k' then (k :: π).count k' else 0) hk',
    ← Finset.add_sum_erase (range n) (fun k' => if g k' then π.count k' else 0) hk']
  have : (∑ x ∈ (range n).erase k, if g x then (k :: π).count x else 0) =
      ∑ x ∈ (range n).erase k, if g x then π.count x else 0 :=
    Finset.sum_congr rfl fun x hx => by
      rw [List.count_cons_of_ne (Ne.symm (Finset.ne_of_mem_erase hx))]
  rw [this, List.count_cons_self]
  split_ifs <;> omega

/-- **The Parikh vector of a walk satisfies Kirchhoff's law.** -/
theorem kirch_walk {E : List (ℕ × ℕ)} {s t : ℕ} {π : List ℕ} (hw : Euler.Walk E s π t) :
    Kirch E (fun k => π.count k) s t := by
  induction hw with
  | nil u =>
    intro w
    have : outF E (fun k => ([] : List ℕ).count k) w = 0 := by simp [outF]
    have h2 : inF E (fun k => ([] : List ℕ).count k) w = 0 := by simp [inF]
    rw [this, h2]
  | @cons k π v hk _ ih =>
    intro w
    have h := ih w
    have hout : outF E (fun k' => (k :: π).count k') w =
        outF E (fun k' => π.count k') w + (if src E k = w then 1 else 0) :=
      sum_ite_count_cons _ k hk π (fun k' => src E k' = w)
    have hin : inF E (fun k' => (k :: π).count k') w =
        inF E (fun k' => π.count k') w + (if tgt E k = w then 1 else 0) :=
      sum_ite_count_cons _ k hk π (fun k' => tgt E k' = w)
    rw [hout, hin]
    by_cases h1 : src E k = w <;> by_cases h2 : tgt E k = w <;>
      simp only [h1, h2, if_true, if_false, eq_comm (a := w)] at h ⊢ <;> omega

end KLM

end Petri

end HTN
