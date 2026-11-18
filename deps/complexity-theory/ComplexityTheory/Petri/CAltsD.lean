import ComplexityTheory.Petri.CAlts
/-!
# Concrete alternatives of step (d), and its certificate conditions

* `cdAlts`, `d_dec` — the alternatives of step (d) (the exact graph over a list of `ω`-labelled
  nodes), computed concretely;
* `cdAltsB`, `dB_dec` — the backward version, through reversal;
* `cDCert`, `cDCert_iff` — the certificate conditions (N1)–(N3), with list-bounded quantifiers;
* `cEntryOK_iff` — the side condition on the entry label.
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp Classical

noncomputable section

variable {d : ℕ}

/-! ### Coordinates -/

theorem decO_inj {a b : Option ℕ} : decO a = decO b ↔ a = b := by
  cases a <;> cases b <;> simp [decO]

theorem decO_eq_top {a : Option ℕ} : decO a = ⊤ ↔ a = none := by
  cases a <;> simp [decO]

theorem toNat_decO (a : Option ℕ) : (decO a).toNat = a.getD 0 := by
  cases a <;> simp [decO]

theorem decW_apply (w : CW) (j : Fin d) : decW d w j = decO (w.getD j none) := rfl

theorem forall_fin_iff {P : ℕ → Prop} : (∀ j : Fin d, P j) ↔ ∀ j ∈ List.range d, P j :=
  ⟨fun h j hj => h ⟨j, List.mem_range.1 hj⟩, fun h j => h j (List.mem_range.2 j.2)⟩

theorem decW_nil : decW d [] = ⊤ := by
  funext j; simp [decW, decO]

/-! ### Operations on `ω`-vectors -/

/-- Concrete compatibility. -/
def cCompat (d : ℕ) (μ m : CW) : Prop :=
  ∀ j ∈ List.range d, (μ.getD j none).isSome → (m.getD j none).isSome →
    μ.getD j none = m.getD j none

theorem cCompat_iff (μ m : CW) : cCompat d μ m ↔ Compat (decW d μ) (decW d m) := by
  unfold cCompat Compat
  rw [← forall_fin_iff]
  simp only [decW_apply, ne_eq, decO_eq_top, decO_inj, Option.ne_none_iff_isSome]

/-- Concrete imposition. -/
def cimpose (d : ℕ) (μ m : CW) : CW :=
  (List.range d).map fun j => if (m.getD j none).isSome then m.getD j none else μ.getD j none

theorem decW_cimpose (μ m : CW) : decW d (cimpose d μ m) = impose (decW d μ) (decW d m) := by
  funext j
  simp only [decW_apply, cimpose, impose]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  simp only [ne_eq, decO_eq_top, Option.ne_none_iff_isSome]
  split_ifs <;> rfl

/-- Concrete exact edges. -/
def cGEdge (d : ℕ) (m : CW) (a : CV) (m' : CW) : Prop :=
  (∀ j ∈ List.range d, (m.getD j none).isSome → 0 ≤ (((m.getD j none).getD 0 : ℕ) : ℤ) + a.getD j 0) ∧
  ∀ j ∈ List.range d, (m'.getD j none).isSome → (m.getD j none).isSome ∧
    (((m'.getD j none).getD 0 : ℕ) : ℤ) = (((m.getD j none).getD 0 : ℕ) : ℤ) + a.getD j 0

theorem cGEdge_iff (m : CW) (a : CV) (m' : CW) :
    cGEdge d m a m' ↔ GEdge (decW d m) (decV d a) (decW d m') := by
  unfold cGEdge GEdge
  rw [← forall_fin_iff, ← forall_fin_iff]
  simp only [decW_apply, ne_eq, decO_eq_top, Option.ne_none_iff_isSome, toNat_decO, decV]

/-- Normalising an integer vector to length `d`. -/
def normV (d : ℕ) (v : CV) : CV := (List.range d).map fun j => v.getD j 0

theorem decV_normV (v : CV) : decV d (normV d v) = decV d v := by
  funext j
  simp only [decV, normV]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem normV_eq_of_decV {v w : CV} (h : decV d v = decV d w) : normV d v = normV d w := by
  unfold normV
  refine List.map_congr_left fun j hj => ?_
  exact congrFun h ⟨j, List.mem_range.1 hj⟩

/-! ### The exact graph -/

/-- The `i`-th concrete node. -/
def cnd (Ns : List (ℕ × CW)) (i : ℕ) : ℕ × CW := Ns.getD i (0, [])

/-- Decoding a node list. -/
def decNs (d : ℕ) (Ns : List (ℕ × CW)) : List (ℕ × (Fin d → ℕ∞)) := Ns.map fun p => (p.1, decW d p.2)

theorem nd_decNs (Ns : List (ℕ × CW)) (i : ℕ) :
    nd (decNs d Ns) i = ((cnd Ns i).1, decW d (cnd Ns i).2) := by
  unfold nd decNs cnd
  have : ((0 : ℕ), (⊤ : Fin d → ℕ∞)) = (fun p : ℕ × CW => (p.1, decW d p.2)) (0, []) := by
    simp [decW_nil]
  rw [this, List.getD_map]

@[simp] theorem length_decNs (Ns : List (ℕ × CW)) : (decNs d Ns).length = Ns.length := by
  simp [decNs]

/-- The concrete edge predicate of the exact graph. -/
def cgP (d : ℕ) (Ns : List (ℕ × CW)) (i i' : ℕ) (e : CE) : Prop :=
  (cnd Ns i).1 = e.1 ∧ (cnd Ns i').1 = e.2.2 ∧ cGEdge d (cnd Ns i).2 e.2.1 (cnd Ns i').2

/-- The concrete edges of the exact graph, before removing duplicates. -/
def cgRaw (d : ℕ) (c : CC) (Ns : List (ℕ × CW)) : List CE :=
  (List.range Ns.length).flatMap fun i => (List.range Ns.length).flatMap fun i' =>
    ((cEdges c).filter fun e => decide (cgP d Ns i i' e)).map fun e => (i, normV d e.2.1, i')

/-- The concrete edges of the exact graph. -/
def cgEdges (d : ℕ) (c : CC) (Ns : List (ℕ × CW)) : List CE := (cgRaw d c Ns).dedup

theorem map_dedup_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ l : List α, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).dedup = l.dedup.map f
  | [], _ => rfl
  | a :: l, h => by
    have ih := map_dedup_of_injOn f l fun x hx y hy => h x (by simp [hx]) y (by simp [hy])
    by_cases ha : a ∈ l
    · rw [List.map_cons, List.dedup_cons_of_mem (List.mem_map_of_mem ha), List.dedup_cons_of_mem ha,
        ih]
    · have hfa : f a ∉ l.map f := by
        intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
        exact ha (h b (by simp [hb]) a (by simp) hfb ▸ hb)
      rw [List.map_cons, List.dedup_cons_of_notMem hfa, List.dedup_cons_of_notMem ha, ih,
        List.map_cons]

theorem mem_cgRaw {c : CC} {Ns : List (ℕ × CW)} {e : CE} (he : e ∈ cgRaw d c Ns) :
    ∃ i i' a, e = (i, normV d a, i') := by
  simp only [cgRaw, List.mem_flatMap, List.mem_map] at he
  obtain ⟨i, -, i', -, e', -, rfl⟩ := he
  exact ⟨i, i', e'.2.1, rfl⟩

theorem cgEdges_dec (c : CC) (Ns : List (ℕ × CW)) :
    (cgEdges d c Ns).map (decE d) = gEdges (decC d c) (decNs d Ns) := by
  unfold cgEdges gEdges
  have hraw : (cgRaw d c Ns).map (decE d) =
      (List.range (decNs d Ns).length).flatMap fun i => (List.range (decNs d Ns).length).flatMap
        fun i' => ((decC d c).edges.filter fun e => (nd (decNs d Ns) i).1 = e.1 ∧
          (nd (decNs d Ns) i').1 = e.2.2 ∧ GEdge (nd (decNs d Ns) i).2 e.2.1
            (nd (decNs d Ns) i').2).map fun e => (i, e.2.1, i') := by
    simp only [cgRaw, length_decNs, List.map_flatMap, decC_edges]
    refine List.flatMap_congr fun i _ => List.flatMap_congr fun i' _ => ?_
    rw [List.filter_map, List.map_map, List.map_map]
    congr 1
    · funext e; simp [decE, decV_normV]
    · exact List.filter_congr fun e _ => by
        simp only [Function.comp, nd_decNs, cgP, cGEdge_iff, decE]
  rw [← hraw]
  convert (map_dedup_of_injOn (decE d) (cgRaw d c Ns) ?_).symm
  intro a ha b hb hab
  obtain ⟨i, i', x, rfl⟩ := mem_cgRaw ha
  obtain ⟨k, k', y, rfl⟩ := mem_cgRaw hb
  simp only [decE, decV_normV, Prod.mk.injEq] at hab
  obtain ⟨rfl, hxy, rfl⟩ := hab
  rw [normV_eq_of_decV hxy]

/-- The concrete exact graph. -/
def cgComp (d : ℕ) (c : CC) (Ns : List (ℕ × CW)) (i₀ i₁ : ℕ) : CC :=
  (List.range Ns.length, Ns.map (·.2), cgEdges d c Ns, i₀, i₁)

theorem decC_cgComp (c : CC) (Ns : List (ℕ × CW)) (i₀ i₁ : ℕ) :
    decC d (cgComp d c Ns i₀ i₁) = gComp (decC d c) (decNs d Ns) i₀ i₁ := by
  simp only [decC, cgComp, gComp, cNodes, cLabs, cEdges, cEntry, cExit, length_decNs,
    Comp.mk.injEq, true_and, and_true]
  refine ⟨funext fun u => ?_, cgEdges_dec c Ns⟩
  rw [nd_decNs]
  simp only [cnd]
  have : ([] : CW) = (fun p : ℕ × CW => p.2) (0, []) := rfl
  rw [this, List.getD_map]

/-- **Concrete alternatives of step (d).** -/
def cdAlts (d : ℕ) (b : CB) (Ns : List (ℕ × CW)) : List (List CB) :=
  ((((List.range Ns.length).flatMap fun i₀ => (List.range Ns.length).map fun i₁ => (i₀, i₁)).filter
    fun p => decide ((cnd Ns p.1).1 = cEntry (cComp b) ∧ (cnd Ns p.2).1 = cExit (cComp b) ∧
      cCompat d (cInp b) (cnd Ns p.1).2 ∧ cCompat d (cOut b) (cnd Ns p.2).2))).map fun p =>
    [(cPre b, cimpose d (cInp b) (cnd Ns p.1).2, cgComp d (cComp b) Ns p.1 p.2,
      cimpose d (cOut b) (cnd Ns p.2).2)]

theorem d_dec (b : CB) (Ns : List (ℕ × CW)) :
    dAlts (decB d b) (decNs d Ns) = (cdAlts d b Ns).map (List.map (decB d)) := by
  unfold dAlts cdAlts
  rw [List.map_map, length_decNs]
  rw [List.filter_congr (q := fun p => decide ((cnd Ns p.1).1 = cEntry (cComp b) ∧
      (cnd Ns p.2).1 = cExit (cComp b) ∧ cCompat d (cInp b) (cnd Ns p.1).2 ∧
        cCompat d (cOut b) (cnd Ns p.2).2)) fun p _ => by
    simp only [nd_decNs, decB_comp, decC_entry, decC_exit, decB_inp, decB_out, cCompat_iff]]
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp, List.map_cons, List.map_nil]
  show [Block.mk _ _ _ _] = [Block.mk _ _ _ _]
  simp only [cPre_mk, cInp_mk, cComp_mk, cOut_mk, nd_decNs, decW_cimpose, decC_cgComp]
  rfl

/-! ### Reversal -/

/-- The concrete reversed component. -/
def crevC (c : CC) : CC :=
  (cNodes c, cLabs c, (cEdges c).map fun e => (e.2.2, e.2.1.map Neg.neg, e.1), cExit c, cEntry c)

theorem decV_neg (v : CV) : decV d (v.map Neg.neg) = -decV d v := by
  funext j
  simp only [decV, Pi.neg_apply]
  have : (0 : ℤ) = Neg.neg 0 := by simp
  rw [this, List.getD_map]
  simp

theorem decC_crevC (c : CC) : decC d (crevC c) = (decC d c).rev := by
  simp only [decC, crevC, Comp.rev, cNodes, cLabs, cEdges, cEntry, cExit, List.map_map,
    Comp.mk.injEq, true_and, and_true]
  refine List.map_congr_left fun e _ => ?_
  simp [decE, revEdge, decV_neg]

/-- The concrete reversed block. -/
def crevB (b : CB) : CB := ([], cOut b, crevC (cComp b), cInp b)

theorem decB_crevB (b : CB) : decB d (crevB b) = (decB d b).rev := by
  show Block.mk _ _ _ _ = Block.mk _ _ _ _
  simp only [crevB, cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_crevC, decB_comp, decB_out, decB_inp]
  have : decV d [] = 0 := by funext j; simp [decV]
  rw [this]

/-- Concrete reversal back, with a link vector. -/
def cunrev (g : CB) (pre : CV) : CB := (pre, cOut g, crevC (cComp g), cInp g)

theorem decB_cunrev (g : CB) (pre : CV) : decB d (cunrev g pre) = (decB d g).unrev (decV d pre) := by
  show Block.mk _ _ _ _ = Block.mk _ _ _ _
  simp only [cunrev, cPre_mk, cInp_mk, cComp_mk, cOut_mk, decC_crevC, decB_comp, decB_out, decB_inp]

/-- **Concrete alternatives of backward step (d).** -/
def cdAltsB (d : ℕ) (b : CB) (Ns : List (ℕ × CW)) : List (List CB) :=
  (cdAlts d (crevB b) Ns).map fun A => A.map fun g => cunrev g (cPre b)

theorem dB_dec (b : CB) (Ns : List (ℕ × CW)) :
    dAltsB (decB d b) (decNs d Ns) = (cdAltsB d b Ns).map (List.map (decB d)) := by
  unfold dAltsB cdAltsB
  rw [← decB_crevB, d_dec, List.map_map, List.map_map]
  refine List.map_congr_left fun A _ => ?_
  simp only [Function.comp, List.map_map]
  refine List.map_congr_left fun g _ => ?_
  simp only [Function.comp, decB_cunrev]
  rfl

/-! ### The certificate conditions -/

theorem exists_mem_map_iff {α β : Type*} {f : α → β} {l : List α} {P : β → Prop} :
    (∃ b, b ∈ l.map f ∧ P b) ↔ ∃ a ∈ l, P (f a) := by
  constructor
  · rintro ⟨b, hb, hP⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact ⟨a, ha, hP⟩
  · rintro ⟨a, ha, hP⟩
    exact ⟨f a, List.mem_map_of_mem ha, hP⟩

/-- The concrete label of node `u` at coordinate `j`. -/
def clab (c : CC) (u j : ℕ) : Option ℕ := ((cLabs c).getD u []).getD j none

theorem decC_lab_apply (c : CC) (u : ℕ) (j : Fin d) : (decC d c).lab u j = decO (clab c u j) := rfl

/-- The concrete certificate conditions (N1)–(N3). -/
def cDCert (d : ℕ) (b : CB) (Ns : List (ℕ × CW)) : Prop :=
  (∀ p ∈ Ns, ∀ j ∈ List.range d, (clab (cComp b) p.1 j).isSome →
      p.2.getD j none = clab (cComp b) p.1 j) ∧
  (∃ p ∈ Ns, p.1 = cEntry (cComp b) ∧
      (∀ j ∈ List.range d, (cInp b).getD j none = none → p.2.getD j none = none) ∧
      ∀ j ∈ List.range d, (p.2.getD j none).isSome → p.2.getD j none = (cInp b).getD j none) ∧
  (∀ p ∈ Ns, ∀ e ∈ cEdges (cComp b), e.1 = p.1 →
      (∀ j ∈ List.range d, (p.2.getD j none).isSome →
        0 ≤ (((p.2.getD j none).getD 0 : ℕ) : ℤ) + e.2.1.getD j 0) →
      ∃ p' ∈ Ns, p'.1 = e.2.2 ∧ ∀ j ∈ List.range d, (p'.2.getD j none).isSome →
        (p.2.getD j none).isSome ∧
          (((p'.2.getD j none).getD 0 : ℕ) : ℤ) = (((p.2.getD j none).getD 0 : ℕ) : ℤ) + e.2.1.getD j 0)

theorem cDCert_iff (b : CB) (Ns : List (ℕ × CW)) : cDCert d b Ns ↔ DCert (decB d b) (decNs d Ns) := by
  unfold cDCert DCert decNs
  simp only [List.forall_mem_map, exists_mem_map_iff, decB_comp, decB_inp, decC_edges,
    List.forall_mem_map, decC_entry]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall₂_congr fun p _ => ?_
    rw [← forall_fin_iff]
    simp only [decC_lab_apply, decW_apply, ne_eq, decO_eq_top, decO_inj, Option.ne_none_iff_isSome]
  · refine exists_congr fun p => and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [← forall_fin_iff, ← forall_fin_iff]
    simp only [decW_apply, ne_eq, decO_eq_top, decO_inj, Option.ne_none_iff_isSome]
  · refine forall₂_congr fun p _ => forall₂_congr fun e _ => ?_
    simp only [decE]
    refine imp_congr_right fun _ => imp_congr ?_ ?_
    · rw [← forall_fin_iff]
      simp only [decW_apply, ne_eq, decO_eq_top, Option.ne_none_iff_isSome, toNat_decO, decV]
    · refine exists_congr fun p' => and_congr_right fun _ => and_congr_right fun _ => ?_
      rw [← forall_fin_iff]
      simp only [decW_apply, ne_eq, decO_eq_top, Option.ne_none_iff_isSome, toNat_decO, decV]

/-- The concrete side condition on the entry label of step (d). -/
def cEntryOK (d : ℕ) (b : CB) : Prop :=
  ∀ j ∈ List.range d, (clab (cComp b) (cEntry (cComp b)) j).isSome →
    (cInp b).getD j none = clab (cComp b) (cEntry (cComp b)) j

theorem cEntryOK_iff (b : CB) : cEntryOK d b ↔
    ∀ j, (decB d b).comp.lab (decB d b).comp.entry j ≠ ⊤ →
      (decB d b).inp j = (decB d b).comp.lab (decB d b).comp.entry j := by
  unfold cEntryOK
  rw [← forall_fin_iff]
  simp only [decB_comp, decC_entry, decC_lab_apply, decB_inp, decW_apply, ne_eq, decO_eq_top,
    decO_inj, Option.ne_none_iff_isSome]

/-- The concrete side condition on the exit label of backward step (d). -/
def cExitOK (d : ℕ) (b : CB) : Prop :=
  ∀ j ∈ List.range d, (clab (cComp b) (cExit (cComp b)) j).isSome →
    (cOut b).getD j none = clab (cComp b) (cExit (cComp b)) j

theorem cExitOK_iff (b : CB) : cExitOK d b ↔
    ∀ j, (decB d b).comp.lab (decB d b).comp.exit j ≠ ⊤ →
      (decB d b).out j = (decB d b).comp.lab (decB d b).comp.exit j := by
  unfold cExitOK
  rw [← forall_fin_iff]
  simp only [decB_comp, decC_exit, decC_lab_apply, decB_out, decW_apply, ne_eq, decO_eq_top,
    decO_inj, Option.ne_none_iff_isSome]

end

end KLM

end Petri

end HTN
