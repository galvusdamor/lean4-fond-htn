import ComplexityTheory.Petri.StepB
/-!
# Decomposition step (d): replacing a component by a finite exact graph

Given a block `b` and a finite list `Ns` of pairs `(v, m)` (a node of the component and an
`ω`-vector) satisfying

* (N1) `m` agrees with the label of `v`,
* (N2) some `(entry, m₀) ∈ Ns` describes the input,
* (N3) closure: for `(v, m) ∈ Ns` and an edge `v →a v'` firable from `m` (on the finite
  coordinates of `m`) there is `(v', m') ∈ Ns` with fewer finite coordinates on which
  `m' = m + a`,

the graph `gComp` with node set `Ns` (as indices), labels `m` and the exact edges has the same
runs as the component (`d_valid`).  The alternatives `dAlts` range over the possible pairs of
first and last nodes compatible with the input and the output.  The labels of the new graph are
consistent forwards (`labOK_gComp`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp Classical

noncomputable section

variable {ι : Type*}

/-- The `i`-th node of `Ns`. -/
def nd (Ns : List (ℕ × (ι → ℕ∞))) (i : ℕ) : ℕ × (ι → ℕ∞) := Ns.getD i (0, ⊤)

/-- An exact edge between two `ω`-vectors. -/
def GEdge (m : ι → ℕ∞) (a : ι → ℤ) (m' : ι → ℕ∞) : Prop :=
  (∀ j, m j ≠ ⊤ → 0 ≤ ((m j).toNat : ℤ) + a j) ∧
    ∀ j, m' j ≠ ⊤ → m j ≠ ⊤ ∧ ((m' j).toNat : ℤ) = (m j).toNat + a j

/-- The edges of the graph over `Ns`. -/
def gEdges (C : Comp ι) (Ns : List (ℕ × (ι → ℕ∞))) : List (Edge ι) :=
  ((List.range Ns.length).flatMap fun i => (List.range Ns.length).flatMap fun i' =>
    (C.edges.filter fun e => (nd Ns i).1 = e.1 ∧ (nd Ns i').1 = e.2.2 ∧
      GEdge (nd Ns i).2 e.2.1 (nd Ns i').2).map fun e => (i, e.2.1, i')).dedup

/-- The graph over `Ns` with given first and last node. -/
def gComp (C : Comp ι) (Ns : List (ℕ × (ι → ℕ∞))) (i₀ i₁ : ℕ) : Comp ι :=
  ⟨List.range Ns.length, fun i => (nd Ns i).2, gEdges C Ns, i₀, i₁⟩

/-- Imposing the finite values of `m` on `μ`. -/
def impose (μ m : ι → ℕ∞) : ι → ℕ∞ := fun j => if m j ≠ ⊤ then m j else μ j

/-- Compatibility of two `ω`-vectors. -/
def Compat (μ m : ι → ℕ∞) : Prop := ∀ j, μ j ≠ ⊤ → m j ≠ ⊤ → μ j = m j

/-- The alternatives of step (d). -/
def dAlts (b : Block ι) (Ns : List (ℕ × (ι → ℕ∞))) : List (List (Block ι)) :=
  ((((List.range Ns.length).flatMap fun i₀ => (List.range Ns.length).map fun i₁ => (i₀, i₁)).filter
    fun p => (nd Ns p.1).1 = b.comp.entry ∧ (nd Ns p.2).1 = b.comp.exit ∧
      Compat b.inp (nd Ns p.1).2 ∧ Compat b.out (nd Ns p.2).2)).map fun p =>
    [⟨b.pre, impose b.inp (nd Ns p.1).2, gComp b.comp Ns p.1 p.2, impose b.out (nd Ns p.2).2⟩]

theorem nd_mem {Ns : List (ℕ × (ι → ℕ∞))} {i : ℕ} (hi : i < Ns.length) : nd Ns i ∈ Ns := by
  unfold nd; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem agree_impose {x : ι → ℤ} {μ m : ι → ℕ∞} (hc : Compat μ m) :
    Agree x (impose μ m) ↔ Agree x μ ∧ Agree x m := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by unfold impose; split_ifs <;> assumption)
      unfold impose at this
      split_ifs at this with hm
      · rw [this, hc j hj hm]
      · exact this
    · have := h j (by unfold impose; rw [if_pos hj]; exact hj)
      unfold impose at this; rwa [if_pos hj] at this
  · rintro ⟨h1, h2⟩ j hj
    unfold impose at hj ⊢
    split_ifs at hj ⊢ with hm
    · exact h2 j hm
    · exact h1 j hj

theorem runC_congr {C C' : Comp ι} (he : C.edges = C'.edges) (hl : C.lab = C'.lab) {u v : ℕ}
    {X : ι → ℤ} {es : List (Edge ι)} : RunC C u v X es ↔ RunC C' u v X es := by
  unfold RunC
  rw [he]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, tlab_congr hl c⟩, fun ⟨a, b, c⟩ => ⟨a, b, tlab_congr hl.symm c⟩⟩

theorem gEdges_nodup (C : Comp ι) (Ns : List (ℕ × (ι → ℕ∞))) : (gEdges C Ns).Nodup :=
  List.nodup_dedup _

theorem mem_gEdges {C : Comp ι} {Ns : List (ℕ × (ι → ℕ∞))} {g : Edge ι} :
    g ∈ gEdges C Ns ↔ g.1 < Ns.length ∧ g.2.2 < Ns.length ∧ ∃ e ∈ C.edges,
      (nd Ns g.1).1 = e.1 ∧ (nd Ns g.2.2).1 = e.2.2 ∧ GEdge (nd Ns g.1).2 e.2.1 (nd Ns g.2.2).2 ∧
      g.2.1 = e.2.1 := by
  unfold gEdges
  simp only [List.mem_dedup, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, i', hi', e, ⟨he, h1, h2, h3⟩, rfl⟩
    exact ⟨hi, hi', e, he, h1, h2, h3, rfl⟩
  · rintro ⟨hi, hi', e, he, h1, h2, h3, h4⟩
    obtain ⟨i, a, i'⟩ := g
    simp only at h4 hi hi' h1 h2 h3
    subst h4
    exact ⟨i, hi, i', hi', e, ⟨he, h1, h2, h3⟩, rfl⟩

/-- **Labels of the graph are consistent forwards.** -/
theorem labOK_gComp (C : Comp ι) (Ns : List (ℕ × (ι → ℕ∞))) (i₀ i₁ : ℕ) :
    LabOK (gComp C Ns i₀ i₁) := by
  rw [labOK_iff]
  intro g hg j hj
  obtain ⟨-, -, e, -, -, -, ⟨-, h2⟩, h4⟩ := mem_gEdges.1 hg
  obtain ⟨h5, h6⟩ := h2 j hj
  exact ⟨h5, by simp only [gComp]; rw [h6, h4]⟩

theorem wf_gComp (C : Comp ι) (Ns : List (ℕ × (ι → ℕ∞))) {i₀ i₁ : ℕ} (h₀ : i₀ < Ns.length)
    (h₁ : i₁ < Ns.length) : WF (gComp C Ns i₀ i₁) := by
  rw [wf_iff]
  refine ⟨fun g hg => ?_, List.mem_range.2 h₀, List.mem_range.2 h₁⟩
  obtain ⟨h1, h2, -⟩ := mem_gEdges.1 hg
  exact ⟨List.mem_range.2 h1, List.mem_range.2 h2⟩

section Valid

variable {b : Block ι} {Ns : List (ℕ × (ι → ℕ∞))}

/-- Simulation of runs of the component by runs of the graph. -/
theorem sim_run
    (hN3 : ∀ p ∈ Ns, ∀ e ∈ b.comp.edges, e.1 = p.1 →
      (∀ j, p.2 j ≠ ⊤ → 0 ≤ ((p.2 j).toNat : ℤ) + e.2.1 j) → ∃ p' ∈ Ns, p'.1 = e.2.2 ∧
        ∀ j, p'.2 j ≠ ⊤ → p.2 j ≠ ⊤ ∧ ((p'.2 j).toNat : ℤ) = (p.2 j).toNat + e.2.1 j)
    (i₀ i₁ : ℕ) : ∀ (es : List (Edge ι)) (u v : ℕ) (X : ι → ℤ), RunC b.comp u v X es →
      ∀ i < Ns.length, (nd Ns i).1 = u → Agree X (nd Ns i).2 →
      ∃ es' i', i' < Ns.length ∧ RunC (gComp b.comp Ns i₀ i₁) i i' X es' ∧ (nd Ns i').1 = v ∧
        teff es' = teff es
  | [], u, v, X, hr, i, hi, hu, hX => by
    obtain ⟨rfl, hpos, -⟩ := runC_nil.1 hr
    exact ⟨[], i, hi, runC_nil.2 ⟨rfl, hpos, hX⟩, hu, rfl⟩
  | e :: es, u, v, X, hr, i, hi, hu, hX => by
    obtain ⟨rfl, he, hpos, hag, hr'⟩ := runC_cons.1 hr
    have hfire : ∀ j, (nd Ns i).2 j ≠ ⊤ → 0 ≤ (((nd Ns i).2 j).toNat : ℤ) + e.2.1 j := by
      intro j hj
      rw [← hX j hj]
      exact hr'.first.1 j
    obtain ⟨p', hp', hp'1, hp'2⟩ := hN3 _ (nd_mem hi) e he hu.symm hfire
    obtain ⟨i', hi', hi'e⟩ := List.getElem_of_mem hp'
    have hnd : nd Ns i' = p' := by unfold nd; rw [List.getD_eq_getElem _ _ hi', hi'e]
    have hX' : Agree (X + e.2.1) (nd Ns i').2 := by
      intro j hj
      rw [hnd] at hj ⊢
      obtain ⟨h1, h2⟩ := hp'2 j hj
      rw [Pi.add_apply, hX j h1, h2]
    obtain ⟨es', i'', hi'', hr'', hv, heff⟩ :=
      sim_run hN3 i₀ i₁ es e.2.2 v (X + e.2.1) hr' i' hi' (by rw [hnd, hp'1]) hX'
    refine ⟨(i, e.2.1, i') :: es', i'', hi'', runC_cons.2 ⟨rfl, ?_, hpos, hX, hr''⟩, hv, ?_⟩
    · refine mem_gEdges.2 ⟨hi, hi', e, he, hu, by rw [hnd, hp'1], ⟨hfire, ?_⟩, rfl⟩
      intro j hj
      rw [hnd] at hj ⊢
      exact hp'2 j hj
    · simp [heff]

/-- Projection of runs of the graph to runs of the component. -/
theorem proj_run (hN1 : ∀ p ∈ Ns, ∀ j, b.comp.lab p.1 j ≠ ⊤ → p.2 j = b.comp.lab p.1 j)
    (i₀ i₁ : ℕ) : ∀ (es' : List (Edge ι)) (i i' : ℕ) (X : ι → ℤ), i < Ns.length →
      RunC (gComp b.comp Ns i₀ i₁) i i' X es' →
      ∃ es, RunC b.comp (nd Ns i).1 (nd Ns i').1 X es ∧ teff es = teff es'
  | [], i, i', X, hi, hr => by
    obtain ⟨rfl, hpos, hag⟩ := runC_nil.1 hr
    refine ⟨[], runC_nil.2 ⟨rfl, hpos, fun j hj => ?_⟩, rfl⟩
    have h1 := hN1 _ (nd_mem hi) j hj
    have := hag j (by simp only [gComp]; rw [h1]; exact hj)
    simp only [gComp] at this
    rw [this, h1]
  | g :: es', i, i', X, hi, hr => by
    obtain ⟨rfl, hg, hpos, hag, hr'⟩ := runC_cons.1 hr
    obtain ⟨-, hi2, e, he, h1, h2, -, h4⟩ := mem_gEdges.1 hg
    obtain ⟨es, hes, heff⟩ := proj_run hN1 i₀ i₁ es' g.2.2 i' (X + g.2.1) hi2 hr'
    refine ⟨e :: es, runC_cons.2 ⟨h1, he, hpos, fun j hj => ?_, ?_⟩, ?_⟩
    · have h5 := hN1 _ (nd_mem hi) j hj
      have := hag j (by simp only [gComp]; rw [h5]; exact hj)
      simp only [gComp] at this
      rw [this, h5]
    · rw [← h2, ← h4]; exact hes
    · simp [heff, h4]

/-- **Validity of step (d).** -/
theorem d_valid (hin : ∀ j, b.comp.lab b.comp.entry j ≠ ⊤ → b.inp j = b.comp.lab b.comp.entry j)
    (hN1 : ∀ p ∈ Ns, ∀ j, b.comp.lab p.1 j ≠ ⊤ → p.2 j = b.comp.lab p.1 j)
    (hN2 : ∃ p ∈ Ns, p.1 = b.comp.entry ∧ (∀ j, b.inp j = ⊤ → p.2 j = ⊤) ∧
      ∀ j, p.2 j ≠ ⊤ → p.2 j = b.inp j)
    (hN3 : ∀ p ∈ Ns, ∀ e ∈ b.comp.edges, e.1 = p.1 →
      (∀ j, p.2 j ≠ ⊤ → 0 ≤ ((p.2 j).toNat : ℤ) + e.2.1 j) → ∃ p' ∈ Ns, p'.1 = e.2.2 ∧
        ∀ j, p'.2 j ≠ ⊤ → p.2 j ≠ ⊤ ∧ ((p'.2 j).toNat : ℤ) = (p.2 j).toNat + e.2.1 j)
    (M M' : ι → ℤ) : BlockRun b M M' ↔ ∃ A ∈ dAlts b Ns, ListRun A M M' := by
  constructor
  · intro h
    obtain ⟨hA, es, hr, he, hA'⟩ := blockRun_iff_runC.1 h
    obtain ⟨p₀, hp₀, hp₀1, hp₀2, hp₀3⟩ := hN2
    obtain ⟨i₀, hi₀, hi₀e⟩ := List.getElem_of_mem hp₀
    have hnd₀ : nd Ns i₀ = p₀ := by unfold nd; rw [List.getD_eq_getElem _ _ hi₀, hi₀e]
    have hX₀ : Agree (M + b.pre) (nd Ns i₀).2 := by
      intro j hj
      rw [hnd₀] at hj ⊢
      have h1 := hp₀3 j hj
      have h2 : b.inp j ≠ ⊤ := by rw [← h1]; exact hj
      rw [hA j h2, h1]
    obtain ⟨es', i₁, hi₁, hr', hv, heff⟩ :=
      sim_run hN3 i₀ 0 es _ _ _ hr i₀ hi₀ (by rw [hnd₀, hp₀1]) hX₀
    have hlast := hr'.last.2
    have hc₀ : Compat b.inp (nd Ns i₀).2 := by
      intro j _ hj; rw [hnd₀] at hj ⊢; exact (hp₀3 j hj).symm
    have hc₁ : Compat b.out (nd Ns i₁).2 := by
      intro j hj1 hj2
      have h1 := hA' j hj1
      have h2 := hlast j hj2
      simp only [gComp] at h2
      rw [heff, ← he] at h2
      rw [h1] at h2
      have := congrArg Int.toNat h2
      simp only [Int.toNat_natCast] at this
      rw [← ENat.coe_toNat hj1, ← ENat.coe_toNat hj2, this]
    refine ⟨_, List.mem_map.2 ⟨(i₀, i₁), List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨i₀,
      List.mem_range.2 hi₀, List.mem_map.2 ⟨i₁, List.mem_range.2 hi₁, rfl⟩⟩, ?_⟩, rfl⟩,
      listRun_singleton.2 (blockRun_iff_runC.2 ⟨(agree_impose hc₀).2 ⟨hA, hX₀⟩, es', ?_, ?_, ?_⟩)⟩
    · simp only [decide_eq_true_eq]
      exact ⟨by rw [hnd₀, hp₀1], hv, hc₀, hc₁⟩
    · show RunC (gComp b.comp Ns i₀ i₁) i₀ i₁ (M + b.pre) es'
      exact (runC_congr (C := gComp b.comp Ns i₀ 0) (C' := gComp b.comp Ns i₀ i₁) rfl rfl).1 hr'
    · rw [he, heff]
    · refine (agree_impose hc₁).2 ⟨hA', ?_⟩
      have := hlast
      simp only [gComp] at this
      rw [heff, ← he] at this
      exact this
  · rintro ⟨A, hA, hr⟩
    simp only [dAlts, List.mem_map, List.mem_filter, decide_eq_true_eq] at hA
    obtain ⟨⟨i₀, i₁⟩, ⟨hp, h₀, h₁, hc₀, hc₁⟩, rfl⟩ := hA
    simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq] at hp
    obtain ⟨i₀', hi₀, i₁', hi₁, rfl, rfl⟩ := hp
    obtain ⟨hA1, es', hr', he, hA2⟩ := blockRun_iff_runC.1 (listRun_singleton.1 hr)
    obtain ⟨es, hes, heff⟩ := proj_run hN1 i₀' i₁' es' i₀' i₁' _ hi₀ hr'
    simp only at h₀ h₁
    rw [h₀, h₁] at hes
    refine blockRun_iff_runC.2 ⟨((agree_impose hc₀).1 hA1).1, es, hes, ?_,
      ((agree_impose hc₁).1 hA2).1⟩
    rw [he, heff]

end Valid

end

end KLM

end Petri

end HTN
