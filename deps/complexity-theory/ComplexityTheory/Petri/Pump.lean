import ComplexityTheory.Petri.Hom
import ComplexityTheory.Petri.Ideal
/-!
# Certificates for step (d) when forward pumping fails

For a well-formed strongly connected block `b` without a forward pumping cycle, the downward
closure of the configurations reachable from the input (on the coordinates finite in the input)
is, at each node, a finite union of ideals (`exists_finset_idl`).  The ideals give a finite node
list `Ns` satisfying the conditions (N1)–(N3) of step (d) (`exists_dcert`), all of whose
`ω`-vectors have fewer `ω`s than the labels of the block.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

variable {ι : Type*}

/-- The number of `ω`-coordinates of an `ω`-vector. -/
noncomputable def topCount [Fintype ι] (μ : ι → ℕ∞) : ℕ := (univ.filter fun j => μ j = ⊤).card

/-! ### Walks in well-formed components -/

theorem sc_twalk {C : Comp ι} (hS : SC C) {u v : ℕ} (hu : u ∈ C.nodes) (hv : v ∈ C.nodes) :
    ∃ es, TWalk C.edges u es v := by
  obtain ⟨π, h⟩ := hS u hu v hv
  exact ⟨_, h.toT⟩

theorem twalk_nodes {E : List (Edge ι)} {P : ℕ → Prop} (hN : ∀ e ∈ E, P e.1 → P e.2.2) {u v : ℕ}
    {es : List (Edge ι)} (h : TWalk E u es v) (hu : P u) : P v := by
  induction h with
  | nil => exact hu
  | cons he _ ih => exact ih (hN _ he hu)

theorem fin_iff {C : Comp ι} (hW : WF C) (hL : LabMono C) (hS : SC C) {u v : ℕ}
    (hu : u ∈ C.nodes) (hv : v ∈ C.nodes) {j : ι} : C.lab u j ≠ ⊤ ↔ C.lab v j ≠ ⊤ := by
  rcases hL with hL | hL
  · exact lab_ne_top_iff hL hS hu hv
  · rw [labOKB_iff] at hL
    have key : ∀ {a c : ℕ} {es : List (Edge ι)}, TWalk C.edges a es c → C.lab a j ≠ ⊤ →
        C.lab c j ≠ ⊤ := fun h ha =>
      twalk_nodes (P := fun w => C.lab w j ≠ ⊤) (fun e he h1 => (hL e he j h1).1) h ha
    obtain ⟨es, h⟩ := sc_twalk hS hu hv
    obtain ⟨es', h'⟩ := sc_twalk hS hv hu
    exact ⟨key h, key h'⟩

/-- **Coordinates finite at every node follow the labels.** -/
theorem track {C : Comp ι} (hW : WF C) (hL : LabMono C) {j : ι}
    (hfin : ∀ u ∈ C.nodes, C.lab u j ≠ ⊤) {u v : ℕ} {es : List (Edge ι)}
    (h : TWalk C.edges u es v) (hu : u ∈ C.nodes) {x : ι → ℤ} (hx : x j = (C.lab u j).toNat) :
    (x + teff es) j = (C.lab v j).toNat ∧ TFires (· = j) x es := by
  have hX : ∀ e ∈ C.edges, C.lab e.1 j ≠ ⊤ → C.lab e.2.2 j ≠ ⊤ →
      ((C.lab e.2.2 j).toNat : ℤ) = (C.lab e.1 j).toNat + e.2.1 j := fun e he h1 h2 =>
    (forall_edge_iff (P := fun s a t => ∀ j, C.lab s j ≠ ⊤ → C.lab t j ≠ ⊤ →
      ((C.lab t j).toNat : ℤ) = (C.lab s j).toNat + a j)).1 hL.exact e he j h1 h2
  have hN := (wf_iff.1 hW).1
  induction h generalizing x with
  | nil u =>
    refine ⟨by simpa using hx, fun j' hj' => ?_⟩
    subst hj'; rw [hx]; exact Nat.cast_nonneg _
  | @cons e es v he _ ih =>
    have h2 := (hN e he).2
    obtain ⟨a, b⟩ := ih h2 (x := x + e.2.1) (by
      rw [Pi.add_apply, hx, hX e he (hfin _ hu) (hfin _ h2)])
    refine ⟨by rw [teff_cons, ← add_assoc]; exact a, fun j' hj' => ?_, b⟩
    subst hj'; rw [hx]; exact Nat.cast_nonneg _

/-- The total absolute drift of a list of edges on a coordinate. -/
def drift (es : List (Edge ι)) (j : ι) : ℤ := (es.map fun e => |e.2.1 j|).sum

theorem drift_nonneg (es : List (Edge ι)) (j : ι) : 0 ≤ drift es j := by
  unfold drift
  exact List.sum_nonneg fun a ha => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 ha; exact abs_nonneg _

theorem neg_drift_le (es : List (Edge ι)) (j : ι) : -drift es j ≤ teff es j := by
  induction es with
  | nil => simp [drift]
  | cons e es ih =>
    simp only [drift, List.map_cons, List.sum_cons, teff_cons, Pi.add_apply] at ih ⊢
    have := neg_abs_le (e.2.1 j)
    linarith

theorem tfires_of_big {es : List (Edge ι)} {x : ι → ℤ} {j : ι} (h : drift es j ≤ x j) :
    TFires (· = j) x es := by
  induction es generalizing x with
  | nil => intro j' hj'; subst hj'; simpa [drift] using h
  | cons e es ih =>
    simp only [drift, List.map_cons, List.sum_cons] at h
    have h0 : 0 ≤ (es.map fun e => |e.2.1 j|).sum := drift_nonneg es j
    have := abs_nonneg (e.2.1 j)
    refine ⟨fun j' hj' => by subst hj'; linarith, ih ?_⟩
    simp only [Pi.add_apply]
    have := neg_abs_le (e.2.1 j)
    unfold drift; linarith

theorem tfires_of_forall {S : ι → Prop} {es : List (Edge ι)} {x : ι → ℤ}
    (h : ∀ j, S j → TFires (· = j) x es) : TFires S x es := by
  induction es generalizing x with
  | nil => intro j hj; exact h j hj j rfl
  | cons e es ih => exact ⟨fun j hj => (h j hj).1 j rfl, ih fun j hj => (h j hj).2⟩

/-! ### The reachable configurations -/

section Construction

variable [Fintype ι] (b : Block ι)

/-- The configurations covered by a run from the input to `u`, on the coordinates finite in the
input (the other coordinates are arbitrary). -/
def Reach (u : ℕ) : Set (ι → ℕ) :=
  {y | ∃ es, TWalk b.comp.edges b.comp.entry es u ∧ TFires (fun j => b.inp j ≠ ⊤) (fin0 b.inp) es ∧
    ∀ j, b.inp j ≠ ⊤ → (y j : ℤ) ≤ fin0 b.inp j + teff es j}

theorem reach_down (u : ℕ) : ∀ y ∈ Reach b u, ∀ y' ≤ y, y' ∈ Reach b u := by
  rintro y ⟨es, h1, h2, h3⟩ y' hy'
  refine ⟨es, h1, h2, fun j hj => le_trans ?_ (h3 j hj)⟩
  exact_mod_cast hy' j

variable {b}

theorem inp_lab (hW : WFB b) {j : ι} (hj : b.comp.lab b.comp.entry j ≠ ⊤) :
    b.inp j = b.comp.lab b.comp.entry j := hW.2.2.1 j hj

theorem reach_lab (hW : WFB b) (hS : SC b.comp) {u : ℕ} (hu : u ∈ b.comp.nodes) {y : ι → ℕ}
    (hy : y ∈ Reach b u) {j : ι} (hj : b.comp.lab b.comp.entry j ≠ ⊤) :
    (y j : ℤ) ≤ (b.comp.lab u j).toNat := by
  obtain ⟨es, h1, -, h3⟩ := hy
  have he := hW.1.2.1
  have hfin : ∀ v ∈ b.comp.nodes, b.comp.lab v j ≠ ⊤ := fun v hv =>
    (fin_iff hW.1 hW.2.1 hS he hv).1 hj
  have hinp := inp_lab hW hj
  have hinp' : b.inp j ≠ ⊤ := by rw [hinp]; exact hj
  obtain ⟨a, -⟩ := track hW.1 hW.2.1 hfin h1 he (x := fin0 b.inp) (by simp [fin0, hinp])
  have := h3 j hinp'
  rw [Pi.add_apply] at a
  linarith

theorem idl_fin (hW : WFB b) (hS : SC b.comp) {u : ℕ} (hu : u ∈ b.comp.nodes) {μ : ι → ℕ∞}
    (hμ : idl μ ⊆ Reach b u) {j : ι} (hj : b.comp.lab b.comp.entry j ≠ ⊤) : μ j ≠ ⊤ := by
  intro htop
  have h1 := reach_lab hW hS hu (hμ (capPt_mem μ ((b.comp.lab u j).toNat + 1))) hj
  have h2 := capPt_of_top (N := (b.comp.lab u j).toNat + 1) htop
  have : ((b.comp.lab u j).toNat + 1 : ℤ) ≤ (capPt μ ((b.comp.lab u j).toNat + 1) j : ℤ) := by
    exact_mod_cast h2
  linarith

theorem no_pump_idl (hW : WFB b) (hS : SC b.comp) (hP : ¬ PumpF b) {u : ℕ}
    (hu : u ∈ b.comp.nodes) {μ : ι → ℕ∞} (hμ : idl μ ⊆ Reach b u) :
    ∃ j, b.inp j ≠ ⊤ ∧ b.comp.lab b.comp.entry j = ⊤ ∧ μ j ≠ ⊤ := by
  by_contra hcon
  push_neg at hcon
  have he := hW.1.2.1
  obtain ⟨τ, hτ⟩ := sc_twalk hS hu he
  let x := fin0 b.inp
  let K : ℕ := ∑ j, ((x j).toNat + (drift τ j).toNat) + 1
  have hK : ∀ j, x j + drift τ j + 1 ≤ K := fun j => by
    have h1 : (x j).toNat + (drift τ j).toNat ≤ ∑ j, ((x j).toNat + (drift τ j).toNat) :=
      Finset.single_le_sum (f := fun j => (x j).toNat + (drift τ j).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : 0 ≤ x j := Nat.cast_nonneg _
    have h3 := drift_nonneg τ j
    have : ((∑ j, ((x j).toNat + (drift τ j).toNat) : ℕ) : ℤ) + 1 = (K : ℤ) := by
      simp only [K]; push_cast; ring
    have h4 : ((x j).toNat : ℤ) + (drift τ j).toNat ≤ (∑ j, ((x j).toNat + (drift τ j).toNat) : ℕ) := by
      exact_mod_cast h1
    rw [Int.toNat_of_nonneg h2, Int.toNat_of_nonneg h3] at h4
    linarith
  obtain ⟨es, h1, h2, h3⟩ := hμ (capPt_mem μ K)
  have hbig : ∀ j, b.inp j ≠ ⊤ → b.comp.lab b.comp.entry j = ⊤ → (K : ℤ) ≤ x j + teff es j :=
    fun j hj hl => by
      have := h3 j hj
      have h' : (K : ℤ) ≤ capPt μ K j := by exact_mod_cast capPt_of_top (hcon j hj hl)
      linarith
  apply hP
  refine ⟨es ++ τ, h1.append hτ, (tfires_append _ _ _).2 ⟨h2, tfires_of_forall fun j hj => ?_⟩,
    fun j hj hl => ?_⟩
  · by_cases hl : b.comp.lab b.comp.entry j = ⊤
    · refine tfires_of_big ?_
      show drift τ j ≤ x j + teff es j
      have := hbig j hj hl; have := hK j
      have : 0 ≤ x j := Nat.cast_nonneg _
      linarith
    · have hfin : ∀ v ∈ b.comp.nodes, b.comp.lab v j ≠ ⊤ := fun v hv =>
        (fin_iff hW.1 hW.2.1 hS he hv).1 hl
      have hx : x j = (b.comp.lab b.comp.entry j).toNat := by
        simp [x, fin0, inp_lab hW hl]
      obtain ⟨a, -⟩ := track hW.1 hW.2.1 hfin h1 he hx
      exact (track hW.1 hW.2.1 hfin hτ hu a).2
  · have := hbig j hj hl; have := hK j
    have := neg_drift_le τ j
    rw [teff_append, Pi.add_apply]
    linarith

/-- The ideals decomposing the covered configurations at each node. -/
noncomputable def Dset (u : ℕ) : Finset (ι → ℕ∞) :=
  Classical.choose (exists_finset_idl (Reach b u) (reach_down b u))

omit [Fintype ι] in
theorem dset_spec [Fintype ι] (u : ℕ) : Reach b u = ⋃ v ∈ Dset (b := b) u, idl v :=
  Classical.choose_spec (exists_finset_idl (Reach b u) (reach_down b u))

theorem dset_sub {u : ℕ} {μ : ι → ℕ∞} (h : μ ∈ Dset (b := b) u) : idl μ ⊆ Reach b u := by
  rw [dset_spec (b := b) u]
  exact Set.subset_biUnion_of_mem (u := fun v => idl v) h

variable (b)

/-- The node set of the ideal graph. -/
def NSet : Set (ℕ × (ι → ℕ∞)) :=
  {p | p.1 ∈ b.comp.nodes ∧ ∃ μ ∈ Dset (b := b) p.1, p.2 ≤ μ ∧ (∀ j, p.2 j = ⊤ ↔ μ j = ⊤) ∧
    ∀ j, b.comp.lab p.1 j ≠ ⊤ → p.2 j = b.comp.lab p.1 j}

/-- The `ω`-vectors below `μ` with the same `ω`-coordinates. -/
theorem finite_below (μ : ι → ℕ∞) :
    {m : ι → ℕ∞ | m ≤ μ ∧ ∀ j, m j = ⊤ ↔ μ j = ⊤}.Finite := by
  refine (Set.Finite.pi (t := fun j => insert ⊤ ((Set.Iic (μ j).toNat).image
    fun k : ℕ => (k : ℕ∞))) fun j => ((Set.finite_Iic _).image _).insert _).subset ?_
  rintro m ⟨hle, hω⟩ j -
  by_cases hm : m j = ⊤
  · exact Or.inl hm
  · right
    have hμ : μ j ≠ ⊤ := fun h => hm ((hω j).2 h)
    refine ⟨(m j).toNat, ?_, ENat.coe_toNat hm⟩
    have := hle j
    rw [← ENat.coe_toNat hm, ← ENat.coe_toNat hμ] at this
    exact Set.mem_Iic.2 (ENat.coe_le_coe.1 this)

theorem nset_finite : (NSet b).Finite := by
  refine (Set.Finite.biUnion (s := {u | u ∈ b.comp.nodes}) (b.comp.nodes.finite_toSet)
    (t := fun u => ⋃ μ ∈ Dset (b := b) u, ({u} : Set ℕ) ×ˢ
      {m : ι → ℕ∞ | m ≤ μ ∧ ∀ j, m j = ⊤ ↔ μ j = ⊤}) fun u _ =>
      Set.Finite.biUnion (Dset u).finite_toSet fun μ _ =>
        (Set.finite_singleton u).prod (finite_below μ)).subset ?_
  rintro ⟨u, m⟩ ⟨hu, μ, hμ, hle, hω, -⟩
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact ⟨u, hu, μ, hμ, rfl, hle, hω⟩

variable {b}

theorem idl_inp_sub (hW : WFB b) : idl b.inp ⊆ Reach b b.comp.entry := by
  intro y hy
  refine ⟨[], TWalk.nil _, fun j _ => Nat.cast_nonneg _, fun j hj => ?_⟩
  have := hy j
  rw [← ENat.coe_toNat hj] at this
  simpa [fin0] using (ENat.coe_le_coe.1 this)

/-- **Step (d) certificates exist when forward pumping fails.** -/
theorem exists_dcert (hW : WFB b) (hS : SC b.comp) (hP : ¬ PumpF b) :
    ∃ Ns, DCert b Ns ∧ ∀ p ∈ Ns, topCount p.2 < topCount (b.comp.lab b.comp.entry) := by
  have he := hW.1.2.1
  let Ns := (nset_finite b).toFinset.toList
  have hmem : ∀ p, p ∈ Ns ↔ p ∈ NSet b := by simp [Ns]
  have hEx : ∀ e ∈ b.comp.edges, ∀ j, b.comp.lab e.1 j ≠ ⊤ → b.comp.lab e.2.2 j ≠ ⊤ →
      ((b.comp.lab e.2.2 j).toNat : ℤ) = (b.comp.lab e.1 j).toNat + e.2.1 j :=
    (forall_edge_iff (P := fun s a t => ∀ j, b.comp.lab s j ≠ ⊤ → b.comp.lab t j ≠ ⊤ →
      ((b.comp.lab t j).toNat : ℤ) = (b.comp.lab s j).toNat + a j)).1 hW.2.1.exact
  refine ⟨Ns, ⟨fun p hp j hj => ?_, ?_, ?_⟩, fun p hp => ?_⟩
  · obtain ⟨-, μ, -, -, -, hlab⟩ := (hmem p).1 hp
    exact hlab j hj
  · -- (N2): the input is covered at the entry
    have hsub := idl_inp_sub hW
    rw [dset_spec (b := b)] at hsub
    obtain ⟨μ, hμD, hle⟩ := le_of_idl_subset_biUnion hsub
    let m : ι → ℕ∞ := fun j => if μ j = ⊤ then ⊤ else b.inp j
    refine ⟨(b.comp.entry, m), (hmem _).2 ⟨he, μ, hμD, fun j => ?_, fun j => ?_, fun j hj => ?_⟩,
      rfl, fun j hj => ?_, fun j hj => ?_⟩
    · by_cases h : μ j = ⊤ <;> simp [m, h, hle j]
    · by_cases h : μ j = ⊤
      · simp [m, h]
      · simp only [m, h, if_false]
        exact ⟨fun h' => absurd (top_le_iff.1 (h' ▸ hle j)) h, fun h' => h'.elim⟩
    · have hμ := idl_fin hW hS he (dset_sub hμD) hj
      simp [m, hμ, inp_lab hW hj]
    · have : μ j = ⊤ := top_le_iff.1 (hj ▸ hle j)
      simp [m, this]
    · by_cases h : μ j = ⊤
      · simp [m, h] at hj
      · simp [m, h]
  · -- (N3): closure under the edges
    rintro ⟨u, m⟩ hp e hE he1 hfire
    obtain ⟨hu, μ, hμD, hle, hω, hlab⟩ := (hmem _).1 hp
    simp only at he1 hfire hu hle hω hlab hμD
    have hv : e.2.2 ∈ b.comp.nodes := ((wf_iff.1 hW.1).1 e hE).2
    let n : ι → ℕ∞ := fun j => if m j = ⊤ then ⊤ else ((((m j).toNat : ℤ) + e.2.1 j).toNat : ℕ)
    have hsub : idl n ⊆ Reach b e.2.2 := by
      intro y hy
      let w : ι → ℕ := fun j => if m j = ⊤ then y j + (e.2.1 j).natAbs else (m j).toNat
      have hw : w ∈ idl m := fun j => by
        by_cases h : m j = ⊤
        · rw [h]; exact le_top
        · simp only [w, h, if_false]; exact (ENat.coe_toNat h).le
      obtain ⟨es, h1, h2, h3⟩ := dset_sub hμD (idl_mono hle hw)
      have key : ∀ j, b.inp j ≠ ⊤ → 0 ≤ (fin0 b.inp + teff es) j + e.2.1 j ∧
          (y j : ℤ) ≤ (fin0 b.inp + teff es) j + e.2.1 j := fun j hj => by
        have h3j := h3 j hj
        rw [Pi.add_apply]
        by_cases h : m j = ⊤
        · simp only [w, h, if_true] at h3j
          push_cast at h3j
          have := Int.natCast_natAbs (e.2.1 j)
          have := neg_abs_le (e.2.1 j)
          constructor <;> linarith
        · simp only [w, h, if_false] at h3j
          have hf := hfire j h
          have hyj := hy j
          simp only [n, h, if_false] at hyj
          have hyj' : (y j : ℤ) ≤ ((m j).toNat : ℤ) + e.2.1 j := by
            have := ENat.coe_le_coe.1 hyj
            omega
          constructor <;> linarith
      refine ⟨es ++ [e], h1.append ?_, (tfires_append _ _ _).2 ⟨h2, ?_⟩, fun j hj => ?_⟩
      · rw [← he1]; exact TWalk.cons hE (TWalk.nil _)
      · exact ⟨fun j hj => h2.end_ok j hj, fun j hj => (key j hj).1⟩
      · have := (key j hj).2
        rw [teff_append, teff_cons, teff_nil, add_zero]
        simp only [Pi.add_apply] at this ⊢
        linarith
    rw [dset_spec (b := b)] at hsub
    obtain ⟨μ', hμ'D, hle'⟩ := le_of_idl_subset_biUnion hsub
    let m' : ι → ℕ∞ := fun j => if μ' j = ⊤ then ⊤ else n j
    refine ⟨(e.2.2, m'), (hmem _).2 ⟨hv, μ', hμ'D, fun j => ?_, fun j => ?_, fun j hj => ?_⟩,
      rfl, fun j hj => ?_⟩
    · by_cases h : μ' j = ⊤ <;> simp [m', h, hle' j]
    · by_cases h : μ' j = ⊤
      · simp [m', h]
      · simp only [m', h, if_false]
        exact ⟨fun h' => absurd (top_le_iff.1 (h' ▸ hle' j)) h, fun h' => h'.elim⟩
    · simp only at hj ⊢
      have hle := (fin_iff hW.1 hW.2.1 hS hv he).1 hj
      have hμ' := idl_fin hW hS hv (dset_sub hμ'D) hle
      have hlu : b.comp.lab u j ≠ ⊤ := (fin_iff hW.1 hW.2.1 hS hu he).2 hle
      have hmu := hlab j hlu
      have hm : m j ≠ ⊤ := by rw [hmu]; exact hlu
      have hx := hEx e hE j (by rw [he1]; exact hlu) hj
      rw [he1] at hx
      simp only [m', hμ', n, hm, if_false]
      rw [hmu, ← hx, Int.toNat_natCast, ENat.coe_toNat hj]
    · simp only at hj ⊢
      have hμ' : μ' j ≠ ⊤ := fun h => hj (by simp [m', h])
      have hn : m j ≠ ⊤ := fun h => hj (by simp [m', hμ', n, h])
      refine ⟨hn, ?_⟩
      simp only [m', hμ', n, hn, if_false, ENat.toNat_coe]
      have := hfire j hn
      omega
  · obtain ⟨hu, μ, hμD, -, hω, -⟩ := (hmem p).1 hp
    obtain ⟨j₀, -, hj₀l, hj₀μ⟩ := no_pump_idl hW hS hP hu (dset_sub hμD)
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun j hj => ?_).2 ⟨j₀, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hl
      exact idl_fin hW hS hu (dset_sub hμD) hl ((hω j).1 hj)
    · simpa using hj₀l
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hj₀μ ((hω j₀).1 h)

end Construction

end KLM

end Petri

end HTN
