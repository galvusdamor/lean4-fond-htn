import HtnComplexity.Space.ThrInit
/-!
# The thread table decides solvability, given a correct initial configuration

Layer (C) of the planner P-REG (`NOTES.md` §64–66), semantic half, completed:

* `HTN.Space.Thr.solvable_of_initOk` — if a configuration `S` passes the local conditions
  `ThrInitOk` and the thread table reaches the goal from `S`, the instance is solvable;
* `HTN.Space.Thr.canonS` — the canonical configuration (canonical node numbering, the graph of
  the listed pairs, its reachability as the closed superset, all unreachable slot pairs as `nc`);
* `HTN.Space.Thr.initOk_canonS` — it passes the local conditions;
* `HTN.Space.Thr.thr_solvable_iff` — **solvability ⇔ some configuration passing the local
  conditions from which the thread table reaches the goal**.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-! ### Soundness -/

theorem nIds_le_length (q : InstDesc) : nIds q ≤ (wnodes q.tnI).length := by
  rw [nIds]
  refine (List.toFinset_card_le _).trans ?_
  simp [wnodes]

/-- **Soundness**: a configuration passing the local conditions from which the thread table
reaches the goal certifies solvability. -/
theorem solvable_of_initOk {d : DomDesc} {q : InstDesc} {S : List ℕ} {N : ℕ}
    (hreg : d.MethodsReg) (h : ThrInitOk d q S) (hN : nIds q ≤ N)
    (hT : SolvableTbl ((thrTbl d N).map (encRow enc)) S ((goalF q.goalList).map enc)) :
    Solvable d q := by
  have hH := hyp_of_initOk hreg h hN
  have h1 := (solvableTbl_iff_solvF enc_injective (initG_eq h) _).1 hT
  exact (solvable_iff_tsolv (P := parOf d q S) hH.good (iso_of_initOk h)).2
    (tsolv_of_solvF hH h1)

/-! ### The canonical configuration -/

section Canon

variable (d : DomDesc) (q : InstDesc)

/-- The canonical number of a node. -/
noncomputable def cpos (a : ℕ) : ℕ := wpos (canonR q.tnI) a

/-- The graph of the listed pairs, on canonical node numbers. -/
def cE (x y : ℕ) : Prop := ∃ e ∈ q.tnI.ordList, x = cpos q e.1 ∧ y = cpos q e.2

open Classical in
/-- **The canonical configuration.** -/
noncomputable def canonS : List ℕ :=
  q.initList.map cfI ++ [cfG (.cur 0)] ++
  (canonR q.tnI).map (fun w => cfG (.wit w.1 w.2)) ++
  ((canonR q.tnI).filter (fun w => decide (w.2 ∈ q.tnI.ids))).map
    (fun w => cfG (.lab w.1 (q.tnI.label w.2))) ++
  ((canonR q.tnI).filter (fun w => decide (w.2 ∈ q.tnI.ids) &&
    unknownPrimB d (q.tnI.label w.2))).map (fun w => cfG (.nop w.1)) ++
  [cfG (.len (nIds q))] ++
  q.tnI.ordList.map (fun e => cfN (.edge (cpos q e.1) (cpos q e.2))) ++
  ((List.range (allL q.tnI).length ×ˢ List.range (allL q.tnI).length).filter
    (fun p => decide (Relation.TransGen (cE q) p.1 p.2))).map (fun p => cfN (.cl p.1 p.2)) ++
  ((List.range (nIds q) ×ˢ List.range (nIds q)).filter
    (fun p => decide (¬ Relation.TransGen (cE q) p.1 p.2))).map (fun p => cfN (.nc p.1 p.2))

end Canon

section CanonProps

variable {d : DomDesc} {q : InstDesc}

@[simp] theorem cfI_inj' {a b : ℕ} : cfI a = cfI b ↔ a = b := cfI_injective.eq_iff
@[simp] theorem cfG_inj' {a b : GF} : cfG a = cfG b ↔ a = b := cfG_injective.eq_iff
@[simp] theorem cfN_inj' {a b : NF} : cfN a = cfN b ↔ a = b := cfN_injective.eq_iff
@[simp] theorem cfN_ne_cfG' (e : NF) (g : GF) : cfN e ≠ cfG g := cfN_ne_cfG e g
@[simp] theorem cfG_ne_cfN' (e : NF) (g : GF) : cfG g ≠ cfN e := (cfN_ne_cfG e g).symm
@[simp] theorem cfN_ne_cfI' (e : NF) (v : ℕ) : cfN e ≠ cfI v := cfN_ne_cfI e v
@[simp] theorem cfI_ne_cfN' (e : NF) (v : ℕ) : cfI v ≠ cfN e := (cfN_ne_cfI e v).symm
@[simp] theorem cfI_ne_cfG' (v : ℕ) (g : GF) : cfI v ≠ cfG g := cfI_ne_cfG v g
@[simp] theorem cfG_ne_cfI' (v : ℕ) (g : GF) : cfG g ≠ cfI v := (cfI_ne_cfG v g).symm

theorem mem_canonS_inst {v : ℕ} : cfI v ∈ canonS d q ↔ v ∈ q.initList := by
  simp [canonS]
theorem mem_canonS_cur {p : ℕ} : cfG (.cur p) ∈ canonS d q ↔ p = 0 := by
  simp [canonS]
theorem fin_notMem_canonS : cfG .fin ∉ canonS d q := by
  simp [canonS]
theorem mem_canonS_wit {p a : ℕ} : cfG (.wit p a) ∈ canonS d q ↔ (p, a) ∈ canonR q.tnI := by
  simp [canonS]
theorem mem_canonS_lab {p : ℕ} {x} : cfG (.lab p x) ∈ canonS d q ↔
    ∃ a, (p, a) ∈ canonR q.tnI ∧ a ∈ q.tnI.ids ∧ q.tnI.label a = x := by
  simp [canonS, and_assoc]
theorem mem_canonS_nop {p : ℕ} : cfG (.nop p) ∈ canonS d q ↔
    ∃ a, (p, a) ∈ canonR q.tnI ∧ a ∈ q.tnI.ids ∧ unknownPrimB d (q.tnI.label a) = true := by
  simp [canonS]
theorem mem_canonS_len {p : ℕ} : cfG (.len p) ∈ canonS d q ↔ p = nIds q := by
  simp [canonS]
theorem mem_canonS_edge {x y : ℕ} : cfN (.edge x y) ∈ canonS d q ↔ cE q x y := by
  simp only [canonS, cE, List.mem_append, List.mem_map, List.mem_singleton, List.mem_filter]
  simp
  constructor <;> rintro ⟨a, b, h, h1, h2⟩ <;> exact ⟨a, b, h, h1.symm, h2.symm⟩
theorem mem_canonS_cl {x y : ℕ} : cfN (.cl x y) ∈ canonS d q ↔
    x < (allL q.tnI).length ∧ y < (allL q.tnI).length ∧ Relation.TransGen (cE q) x y := by
  simp [canonS, and_assoc]
theorem mem_canonS_nc {x y : ℕ} : cfN (.nc x y) ∈ canonS d q ↔
    x < nIds q ∧ y < nIds q ∧ ¬ Relation.TransGen (cE q) x y := by
  simp [canonS, and_assoc]
theorem shape_canonS : ∀ f ∈ canonS d q, (∃ v, f = cfI v) ∨ (∃ g, f = cfG g) ∨ (∃ e, f = cfN e) := by
  intro f hf
  simp only [canonS, List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with (((((((( ⟨v, -, rfl⟩ | rfl) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) | rfl) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) <;> simp

theorem lt_of_mem_canonR' {p a : ℕ} (h : (p, a) ∈ canonR q.tnI) : p < (allL q.tnI).length :=
  (List.getElem?_eq_some_iff.1 (mem_canonR.1 h)).1

theorem exists_mem_canonR {p : ℕ} (h : p < (allL q.tnI).length) : ∃ a, (p, a) ∈ canonR q.tnI :=
  ⟨_, mem_canonR.2 (List.getElem?_eq_getElem h)⟩

theorem nIds_le_allL : nIds q ≤ (allL q.tnI).length := by
  rw [nIds, card_ids_eq_length_dedup, allL, List.length_append]
  omega

theorem mem_canonR_iff_cpos {p a : ℕ} (ha : ∃ p, (p, a) ∈ canonR q.tnI) :
    (p, a) ∈ canonR q.tnI ↔ p = cpos q a := witR_canonR.mem_iff' ha

theorem cE_lt {x y : ℕ} (h : cE q x y) : x < (allL q.tnI).length ∧ y < (allL q.tnI).length := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  obtain ⟨h1, h2⟩ := witR_canonR.endp e he
  exact ⟨lt_of_mem_canonR' (mem_wpos h1), lt_of_mem_canonR' (mem_wpos h2)⟩

theorem initOk_canonS : ThrInitOk d q (canonS d q) where
  shape := shape_canonS
  inst v := mem_canonS_inst
  cur p := mem_canonS_cur
  fin := fin_notMem_canonS
  wit := witR_canonR.congr fun w => by
    obtain ⟨p, a⟩ := w
    rw [mem_witList, mem_canonS_wit]
  lab p x := by
    rw [mem_canonS_lab]
    simp only [mem_canonS_wit]
    constructor
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h2, h1, h3⟩
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h2, h1, h3⟩
  nop p := by
    rw [mem_canonS_nop]
    simp only [mem_canonS_wit]
    constructor
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h2, h1, h3⟩
    · rintro ⟨a, h1, h2, h3⟩; exact ⟨a, h2, h1, h3⟩
  len k := by
    rw [mem_canonS_len]
    simp only [mem_canonS_wit]
    have h1 : (∀ i ∈ q.tnI.ids, (k, i) ∉ canonR q.tnI) ↔ ¬ k < nIds q := by
      rw [nIds, ← witR_canonR.exists_id_iff]
      simp
    have h2 : (∃ i ∈ q.tnI.ids, (k - 1, i) ∈ canonR q.tnI) ↔ k - 1 < nIds q := by
      rw [nIds, ← witR_canonR.exists_id_iff]
    rw [h1, h2]
    omega
  edge x y := by
    rw [mem_canonS_edge]
    simp only [mem_canonS_wit]
    constructor
    · rintro ⟨e, he, rfl, rfl⟩
      obtain ⟨h1, h2⟩ := witR_canonR.endp e he
      exact ⟨e, he, mem_wpos h1, mem_wpos h2⟩
    · rintro ⟨e, he, h1, h2⟩
      exact ⟨e, he, (mem_canonR_iff_cpos ⟨_, h1⟩).1 h1, (mem_canonR_iff_cpos ⟨_, h2⟩).1 h2⟩
  cl1 x y h := by
    rw [mem_canonS_edge] at h
    rw [mem_canonS_cl]
    exact ⟨(cE_lt h).1, (cE_lt h).2, .single h⟩
  cl2 x y z h h' := by
    rw [mem_canonS_edge] at h'
    rw [mem_canonS_cl] at h ⊢
    exact ⟨h.1, (cE_lt h').2, h.2.2.tail h'⟩
  nc x y h h' := by
    rw [mem_canonS_nc] at h
    rw [mem_canonS_cl] at h'
    exact h.2.2 h'.2.2
  clpos x y h := by
    rw [mem_canonS_cl] at h
    simp only [mem_canonS_wit]
    exact ⟨exists_mem_canonR h.1, exists_mem_canonR h.2.1⟩
  ncpos x y h := by
    rw [mem_canonS_nc] at h
    simp only [mem_canonS_wit]
    exact ⟨exists_mem_canonR (lt_of_lt_of_le h.1 nIds_le_allL),
      exists_mem_canonR (lt_of_lt_of_le h.2.1 nIds_le_allL)⟩

theorem grOf_canonS_E : (grOf (canonS d q)).E = cE q := by
  funext x y
  exact propext mem_canonS_edge

theorem hypC_canonS (hreg : d.MethodsReg) {N : ℕ} (hN : (wnodes q.tnI).length < N) :
    HypC (parOf d q (canonS d q)) (grOf (canonS d q)) N where
  toHyp := hyp_of_initOk hreg initOk_canonS ((nIds_le_length q).trans hN.le)
  kN' := lt_of_le_of_lt (nIds_le_length q) hN
  edgeN x y h := by
    have h' : cE q x y := mem_canonS_edge.1 h
    have := length_allL_le (t := q.tnI)
    exact ⟨by have := (cE_lt h').1; omega, by have := (cE_lt h').2; omega⟩
  ncC i hi j hj h := by
    rw [grOf_canonS_E] at h
    exact mem_canonS_nc.2 ⟨hi, hj, h⟩

end CanonProps

/-- **The thread table decides solvability**: for regular methods and `N` above the number of
nodes of the initial task network, the instance is solvable iff some configuration passing the
local conditions `ThrInitOk` reaches the goal in the (numbered) thread table. -/
theorem thr_solvable_iff {d : DomDesc} {q : InstDesc} {N : ℕ} (hreg : d.MethodsReg)
    (hN : (wnodes q.tnI).length < N) :
    Solvable d q ↔ ∃ S, ThrInitOk d q S ∧
      SolvableTbl ((thrTbl d N).map (encRow enc)) S ((goalF q.goalList).map enc) := by
  constructor
  · intro hs
    have h := initOk_canonS (d := d) (q := q)
    have hC := hypC_canonS hreg hN
    refine ⟨canonS d q, h, (solvableTbl_iff_solvF enc_injective (initG_eq h) _).2 ?_⟩
    exact (tsolv_iff_solvF hC).1
      ((solvable_iff_tsolv (P := parOf d q (canonS d q)) hC.good (iso_of_initOk h)).1 hs)
  · rintro ⟨S, h, hT⟩
    exact solvable_of_initOk hreg h ((nIds_le_length q).trans hN.le) hT

end Thr

end Space

end HTN
