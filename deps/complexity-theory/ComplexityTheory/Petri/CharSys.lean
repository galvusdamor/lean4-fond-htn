import ComplexityTheory.Petri.Conc
/-!
# The characteristic system as explicit linear equations

For a list of concrete blocks `bs`, `sysFrom d o bs` is a list of linear equations (`TEq`) in
unknowns `x : ℕ → ℕ`, block `i` occupying the unknowns `[oᵢ, oᵢ + 2d + |Eᵢ|)`: first the input
marking, then the output marking, then the edge multiplicities.  We prove

* `sat_charSol` — a solution `x` of the system gives the solution `trisFrom d o bs x` of the
  characteristic system of the decoded problem;
* `charSol_sat` — every solution of the characteristic system arises in this way, up to the
  irrelevant multiplicities of non-existent edges (`TMatch`).
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp

variable (d : ℕ)

/-! ### The equations of one block -/

/-- The number of edges of a concrete block. -/
def nE (b : CB) : ℕ := (cEdges (cComp b)).length

/-- The number of unknowns of a block. -/
def bw (b : CB) : ℕ := 2 * d + nE b

/-- The `k`-th edge of a concrete block. -/
def cedge (b : CB) (k : ℕ) : CE := (cEdges (cComp b)).getD k (0, [], 0)

/-- The input equations. -/
def inpEqs (o : ℕ) (b : CB) : List TEq :=
  (List.range d).filterMap fun j => ((cInp b).getD j none).map fun c => ([(o + j, 1)], (c : ℤ))

/-- The output equations. -/
def outEqs (o : ℕ) (b : CB) : List TEq :=
  (List.range d).filterMap fun j => ((cOut b).getD j none).map fun c => ([(o + d + j, 1)], (c : ℤ))

/-- The effect equations: output = input + effect of the edges. -/
def effEqs (o : ℕ) (b : CB) : List TEq :=
  (List.range d).map fun j => ((o + d + j, 1) :: (o + j, -1) ::
    (List.range (nE b)).map (fun k => (o + 2 * d + k, -((cedge b k).2.1.getD j 0))), 0)

/-- The nodes for which Kirchhoff's law is written. -/
def kirW (b : CB) : List ℕ :=
  (cEdges (cComp b)).map (·.1) ++ (cEdges (cComp b)).map (·.2.2) ++
    [cEntry (cComp b), cExit (cComp b)]

/-- The coefficient of edge `k` in Kirchhoff's law at `w`. -/
def kv (b : CB) (w k : ℕ) : ℤ :=
  (if (cedge b k).1 = w then 1 else 0) - (if (cedge b k).2.2 = w then 1 else 0)

/-- Kirchhoff's equations. -/
def kirEqs (o : ℕ) (b : CB) : List TEq :=
  (kirW b).map fun w => ((List.range (nE b)).map (fun k => (o + 2 * d + k, kv b w k)),
    (if w = cEntry (cComp b) then 1 else 0) - (if w = cExit (cComp b) then 1 else 0))

/-- The equations of one block. -/
def blkEqs (o : ℕ) (b : CB) : List TEq := inpEqs d o b ++ outEqs d o b ++ effEqs d o b ++ kirEqs d o b

/-- The linking equations between a block at `o` and the next block `b'` at `o'`. -/
def linkEqs (o o' : ℕ) (b' : CB) : List TEq :=
  (List.range d).map fun j => ([(o' + j, 1), (o + d + j, -1)], (cPre b').getD j 0)

/-- **The characteristic system** of a list of concrete blocks, the first at offset `o`. -/
def sysFrom : ℕ → List CB → List TEq
  | _, [] => []
  | o, [b] => blkEqs d o b
  | o, b :: b' :: bs => blkEqs d o b ++ linkEqs d o (o + bw d b) b' ++ sysFrom (o + bw d b) (b' :: bs)

/-- The candidate solution of a block read off `x` at offset `o`. -/
def triAt (o : ℕ) (x : ℕ → ℕ) : Tri (Fin d) :=
  ⟨fun j => (x (o + j) : ℤ), fun k => x (o + 2 * d + k), fun j => (x (o + d + j) : ℤ)⟩

/-- The candidate solutions of all blocks. -/
def trisFrom : ℕ → List CB → (ℕ → ℕ) → List (Tri (Fin d))
  | _, [], _ => []
  | o, b :: bs, x => triAt d o x :: trisFrom (o + bw d b) bs x

variable {d}

/-! ### Basic facts -/

theorem src_decC (b : CB) (k : ℕ) : src (decC d (cComp b)).gr k = (cedge b k).1 := by
  rw [src_gr, decC_edges, getD_map_decE]; rfl

theorem tgt_decC (b : CB) (k : ℕ) : tgt (decC d (cComp b)).gr k = (cedge b k).2.2 := by
  rw [tgt_gr, decC_edges, getD_map_decE]; rfl

theorem length_gr_decC (b : CB) : (decC d (cComp b)).gr.length = nE b := by
  rw [gr_length, decC_edges, List.length_map]; rfl

theorem psum_decC (b : CB) (ψ : ℕ → ℕ) (j : Fin d) :
    psum (decC d (cComp b)) ψ j = ∑ k ∈ range (nE b), (ψ k : ℤ) * (cedge b k).2.1.getD j 0 := by
  unfold psum
  rw [Finset.sum_apply]
  simp only [decC_edges, List.length_map, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vec_decC]; rfl

theorem outF_sub_inF (b : CB) (ψ : ℕ → ℕ) (w : ℕ) :
    (outF (decC d (cComp b)).gr ψ w : ℤ) - inF (decC d (cComp b)).gr ψ w =
      ∑ k ∈ range (nE b), kv b w k * (ψ k : ℤ) := by
  unfold outF inF
  rw [length_gr_decC]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [src_decC, tgt_decC]
  unfold kv
  split_ifs <;> simp

theorem not_mem_kirW_src {b : CB} {w : ℕ} (hw : w ∉ kirW b) (k : ℕ) (hk : k < nE b) :
    (cedge b k).1 ≠ w ∧ (cedge b k).2.2 ≠ w := by
  have hm : cedge b k ∈ cEdges (cComp b) := by
    unfold cedge; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  constructor
  · rintro rfl
    exact hw (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨_, hm, rfl⟩)))))
  · rintro rfl
    exact hw (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨_, hm, rfl⟩)))))

theorem outF_eq_zero_of {b : CB} {w : ℕ} (hw : w ∉ kirW b) (ψ : ℕ → ℕ) :
    outF (decC d (cComp b)).gr ψ w = 0 ∧ inF (decC d (cComp b)).gr ψ w = 0 := by
  unfold outF inF
  rw [length_gr_decC]
  constructor
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [src_decC, if_neg (not_mem_kirW_src hw k (Finset.mem_range.1 hk)).1]
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [tgt_decC, if_neg (not_mem_kirW_src hw k (Finset.mem_range.1 hk)).2]

theorem entry_mem_kirW (b : CB) : cEntry (cComp b) ∈ kirW b := by simp [kirW]
theorem exit_mem_kirW (b : CB) : cExit (cComp b) ∈ kirW b := by simp [kirW]

/-- Kirchhoff's law of a decoded block, through the integer equations. -/
theorem kirch_iff (b : CB) (ψ : ℕ → ℕ) :
    Kirch (decC d (cComp b)).gr ψ (cEntry (cComp b)) (cExit (cComp b)) ↔
      ∀ w ∈ kirW b, ∑ k ∈ range (nE b), kv b w k * (ψ k : ℤ) =
        (if w = cEntry (cComp b) then 1 else 0) - (if w = cExit (cComp b) then 1 else 0) := by
  constructor
  · intro h w _
    rw [← outF_sub_inF (d := d) b ψ w]
    have := h w
    generalize outF (decC d (cComp b)).gr ψ w = A at this ⊢
    generalize inF (decC d (cComp b)).gr ψ w = B at this ⊢
    split_ifs at this ⊢ <;> push_cast <;> omega
  · intro h w
    by_cases hw : w ∈ kirW b
    · have := h w hw
      rw [← outF_sub_inF (d := d) b ψ w] at this
      generalize outF (decC d (cComp b)).gr ψ w = A at this ⊢
      generalize inF (decC d (cComp b)).gr ψ w = B at this ⊢
      split_ifs at this ⊢ <;> push_cast at this <;> omega
    · obtain ⟨h1, h2⟩ := outF_eq_zero_of (d := d) hw ψ
      rw [h1, h2, if_neg (fun h : w = cExit (cComp b) => hw (h ▸ exit_mem_kirW b)),
        if_neg (fun h : w = cEntry (cComp b) => hw (h ▸ entry_mem_kirW b))]

/-! ### Agreement with the boundary equations -/

theorem mem_inpEqs {o : ℕ} {b : CB} {e : TEq} :
    e ∈ inpEqs d o b ↔ ∃ j < d, ∃ c, (cInp b).getD j none = some c ∧ e = ([(o + j, 1)], (c : ℤ)) := by
  unfold inpEqs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, he⟩
    cases hc : (cInp b).getD j none with
    | none => rw [hc] at he; simp at he
    | some c =>
      rw [hc] at he
      exact ⟨j, List.mem_range.1 hj, c, hc, (Option.some.inj he).symm⟩
  · rintro ⟨j, hj, c, hc, rfl⟩
    exact ⟨j, List.mem_range.2 hj, by rw [hc]; rfl⟩

theorem mem_outEqs {o : ℕ} {b : CB} {e : TEq} :
    e ∈ outEqs d o b ↔ ∃ j < d, ∃ c, (cOut b).getD j none = some c ∧ e = ([(o + d + j, 1)], (c : ℤ)) := by
  unfold outEqs
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, he⟩
    cases hc : (cOut b).getD j none with
    | none => rw [hc] at he; simp at he
    | some c =>
      rw [hc] at he
      exact ⟨j, List.mem_range.1 hj, c, hc, (Option.some.inj he).symm⟩
  · rintro ⟨j, hj, c, hc, rfl⟩
    exact ⟨j, List.mem_range.2 hj, by rw [hc]; rfl⟩

theorem agree_iff_w (w : CW) (y : Fin d → ℤ) :
    Agree y (decW d w) ↔ ∀ j : Fin d, ∀ c, w.getD j none = some c → y j = c := by
  unfold Agree decW
  constructor
  · intro h j c hc
    have := h j (by rw [hc]; simp [decO])
    rw [this, hc, decO_toNat]
  · intro h j hj
    cases hc : w.getD j none with
    | none => rw [hc] at hj; simp [decO] at hj
    | some c => rw [h j c hc, decO_toNat]

theorem tSatL_inpEqs {o : ℕ} {b : CB} {x : ℕ → ℕ} :
    TSatL (inpEqs d o b) x ↔ Agree (triAt d o x).M₁ (decW d (cInp b)) := by
  rw [agree_iff_w]
  constructor
  · intro h j c hc
    have := h _ (mem_inpEqs.2 ⟨j, j.2, c, hc, rfl⟩)
    simpa [TSat, triAt] using this
  · intro h e he
    obtain ⟨j, hj, c, hc, rfl⟩ := mem_inpEqs.1 he
    have := h ⟨j, hj⟩ c hc
    simpa [TSat, triAt] using this

theorem tSatL_outEqs {o : ℕ} {b : CB} {x : ℕ → ℕ} :
    TSatL (outEqs d o b) x ↔ Agree (triAt d o x).M' (decW d (cOut b)) := by
  rw [agree_iff_w]
  constructor
  · intro h j c hc
    have := h _ (mem_outEqs.2 ⟨j, j.2, c, hc, rfl⟩)
    simpa [TSat, triAt] using this
  · intro h e he
    obtain ⟨j, hj, c, hc, rfl⟩ := mem_outEqs.1 he
    have := h ⟨j, hj⟩ c hc
    simpa [TSat, triAt] using this

theorem tSatL_effEqs {o : ℕ} {b : CB} {x : ℕ → ℕ} :
    TSatL (effEqs d o b) x ↔
      (triAt d o x).M' = (triAt d o x).M₁ + psum (decC d (cComp b)) (triAt d o x).ψ := by
  constructor
  · intro h
    funext j
    have := h _ (List.mem_map.2 ⟨j, List.mem_range.2 j.2, rfl⟩)
    simp only [TSat, tval_cons, tval_map_range] at this
    simp only [triAt, Pi.add_apply, psum_decC]
    have e : ∑ k ∈ range (nE b), -(cedge b k).2.1.getD (j : ℕ) 0 * (x (o + 2 * d + k) : ℤ) =
        -∑ k ∈ range (nE b), (x (o + 2 * d + k) : ℤ) * (cedge b k).2.1.getD (j : ℕ) 0 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e] at this
    linarith
  · intro h e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    have := congrFun h ⟨j, List.mem_range.1 hj⟩
    simp only [triAt, Pi.add_apply, psum_decC] at this
    simp only [TSat, tval_cons, tval_map_range]
    have e : ∑ k ∈ range (nE b), -(cedge b k).2.1.getD j 0 * (x (o + 2 * d + k) : ℤ) =
        -∑ k ∈ range (nE b), (x (o + 2 * d + k) : ℤ) * (cedge b k).2.1.getD j 0 := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    linarith

theorem tSatL_kirEqs {o : ℕ} {b : CB} {x : ℕ → ℕ} :
    TSatL (kirEqs d o b) x ↔
      Kirch (decC d (cComp b)).gr (triAt d o x).ψ (cEntry (cComp b)) (cExit (cComp b)) := by
  rw [kirch_iff]
  simp only [TSatL, kirEqs, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    TSat, tval_map_range, triAt]

/-- **One block**: the equations of a block at `o` hold iff the candidate read off `x` satisfies
the characteristic constraints of the decoded block. -/
theorem tSatL_blkEqs {o : ℕ} {b : CB} {x : ℕ → ℕ} :
    TSatL (blkEqs d o b) x ↔ CharOK (decB d b) (triAt d o x) := by
  simp only [blkEqs, tSatL_append, tSatL_inpEqs, tSatL_outEqs, tSatL_effEqs, tSatL_kirEqs, CharOK,
    decB_inp, decB_out, decB_comp, decC_entry, decC_exit]
  have h1 : ∀ j, 0 ≤ (triAt d o x).M₁ j := fun j => by simp [triAt]
  have h2 : ∀ j, 0 ≤ (triAt d o x).M' j := fun j => by simp [triAt]
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, e⟩
    exact ⟨h1, a, e, c, h2, b⟩
  · rintro ⟨-, a, e, c, -, b⟩
    exact ⟨⟨⟨a, b⟩, c⟩, e⟩

theorem tSatL_linkEqs {o o' : ℕ} {b' : CB} {x : ℕ → ℕ} :
    TSatL (linkEqs d o o' b') x ↔ (triAt d o' x).M₁ = (triAt d o x).M' + decV d (cPre b') := by
  constructor
  · intro h
    funext j
    have := h _ (List.mem_map.2 ⟨j, List.mem_range.2 j.2, rfl⟩)
    simp only [TSat, tval_cons, tval_nil] at this
    simp only [triAt, Pi.add_apply, decV]
    linarith
  · intro h e he
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
    have := congrFun h ⟨j, List.mem_range.1 hj⟩
    simp only [triAt, Pi.add_apply, decV] at this
    simp only [TSat, tval_cons, tval_nil]
    linarith

/-! ### Variables -/

/-- All variables of a system satisfy `P`. -/
def VarsIn (es : List TEq) (P : ℕ → Prop) : Prop := ∀ e ∈ es, ∀ p ∈ e.1, P p.1

theorem tSatL_congr' {es : List TEq} {P : ℕ → Prop} (hv : VarsIn es P) {x y : ℕ → ℕ}
    (h : ∀ v, P v → x v = y v) : TSatL es x ↔ TSatL es y := by
  have : ∀ e ∈ es, tval e.1 x = tval e.1 y := fun e he =>
    tval_congr fun p hp => h _ (hv e he p hp)
  simp only [TSatL, TSat]
  exact ⟨fun H e he => (this e he) ▸ H e he, fun H e he => (this e he).symm ▸ H e he⟩

theorem VarsIn.append {es es' : List TEq} {P : ℕ → Prop} (h : VarsIn es P) (h' : VarsIn es' P) :
    VarsIn (es ++ es') P := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact h e he
  · exact h' e he

theorem VarsIn.mono {es : List TEq} {P Q : ℕ → Prop} (h : VarsIn es P) (hPQ : ∀ v, P v → Q v) :
    VarsIn es Q := fun e he p hp => hPQ _ (h e he p hp)

theorem varsIn_blkEqs (o : ℕ) (b : CB) : VarsIn (blkEqs d o b) fun v => o ≤ v ∧ v < o + bw d b := by
  unfold bw
  refine ((VarsIn.append ?_ ?_).append ?_).append ?_
  · intro e he p hp
    obtain ⟨j, hj, c, -, rfl⟩ := mem_inpEqs.1 he
    simp only [List.mem_singleton] at hp
    subst hp; simp only; omega
  · intro e he p hp
    obtain ⟨j, hj, c, -, rfl⟩ := mem_outEqs.1 he
    simp only [List.mem_singleton] at hp
    subst hp; simp only; omega
  · intro e he p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (show e ∈ effEqs d o b from he)
    have hj := List.mem_range.1 hj
    simp only [List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | rfl | ⟨k, hk, rfl⟩ <;> simp only <;> omega
  · intro e he p hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 (show e ∈ kirEqs d o b from he)
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only; omega

theorem varsIn_linkEqs (o o' : ℕ) (b' : CB) :
    VarsIn (linkEqs d o o' b') fun v => (o' ≤ v ∧ v < o' + d) ∨ (o + d ≤ v ∧ v < o + 2 * d) := by
  intro e he p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 he
  have hj := List.mem_range.1 hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp only <;> omega

theorem varsIn_sysFrom : ∀ (o : ℕ) (bs : List CB), VarsIn (sysFrom d o bs) fun v => o ≤ v
  | _, [] => fun e he => by simp [sysFrom] at he
  | o, [b] => (varsIn_blkEqs o b).mono fun v h => h.1
  | o, b :: b' :: bs => by
    simp only [sysFrom]
    refine (((varsIn_blkEqs o b).mono fun v h => h.1).append
      ((varsIn_linkEqs o _ b').mono fun v h => ?_)).append
        ((varsIn_sysFrom _ (b' :: bs)).mono fun v h => ?_)
    · unfold bw at h; omega
    · unfold bw at h; omega

/-- The total number of unknowns. -/
def totW : List CB → ℕ
  | [] => 0
  | b :: bs => bw d b + totW bs

theorem varsIn_sysFrom_lt : ∀ (o : ℕ) (bs : List CB), VarsIn (sysFrom d o bs) fun v => v < o + totW (d := d) bs
  | _, [] => fun e he => by simp [sysFrom] at he
  | o, [b] => (varsIn_blkEqs o b).mono fun v h => by simp [totW]; omega
  | o, b :: b' :: bs => by
    simp only [sysFrom]
    refine (((varsIn_blkEqs o b).mono fun v h => ?_).append
      ((varsIn_linkEqs o _ b').mono fun v h => ?_)).append
        ((varsIn_sysFrom_lt _ (b' :: bs)).mono fun v h => ?_)
    · simp only [totW]; omega
    · simp only [totW]; unfold bw at h ⊢; omega
    · simp only [totW] at h ⊢; omega

theorem trisFrom_congr : ∀ (o : ℕ) (bs : List CB) {x y : ℕ → ℕ}, (∀ v, o ≤ v → x v = y v) →
    trisFrom d o bs x = trisFrom d o bs y
  | _, [], _, _, _ => rfl
  | o, b :: bs, x, y, h => by
    simp only [trisFrom]
    congr 1
    · simp only [triAt, Tri.mk.injEq]
      refine ⟨funext fun j => ?_, funext fun k => ?_, funext fun j => ?_⟩ <;> rw [h _ (by omega)]
    · exact trisFrom_congr _ bs fun v hv => h v (by unfold bw at hv; omega)

/-! ### Solutions of the system are characteristic solutions -/

theorem linkedBy_cons_cons {f : (Fin d → ℤ) → (Fin d → ℤ) → (Fin d → ℤ)} {b b' : Block (Fin d)}
    {bs : List (Block (Fin d))} {t t' : Tri (Fin d)} {ts : List (Tri (Fin d))} :
    LinkedBy f (b :: b' :: bs) (t :: t' :: ts) ↔ t'.M₁ = f t.M' b'.pre ∧ LinkedBy f (b' :: bs) (t' :: ts) :=
  Iff.rfl

/-- **Solutions of the system give characteristic solutions.** -/
theorem sat_charSol : ∀ (o : ℕ) (bs : List CB) (x : ℕ → ℕ), TSatL (sysFrom d o bs) x →
    CharSol (bs.map (decB d)) (trisFrom d o bs x)
  | _, [], _, _ => ⟨List.Forall₂.nil, trivial⟩
  | o, [b], x, h => ⟨List.Forall₂.cons (tSatL_blkEqs.1 h) List.Forall₂.nil, trivial⟩
  | o, b :: b' :: bs, x, h => by
    simp only [sysFrom, tSatL_append] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := sat_charSol _ (b' :: bs) x h3
    simp only [List.map_cons, trisFrom] at ih1 ih2 ⊢
    exact ⟨List.Forall₂.cons (tSatL_blkEqs.1 h1) ih1, linkedBy_cons_cons.2 ⟨tSatL_linkEqs.1 h2, ih2⟩⟩

/-! ### Characteristic solutions come from solutions of the system -/

/-- The unknowns encoding one candidate solution at offset `o`. -/
noncomputable def xOf (o : ℕ) (t : Tri (Fin d)) (v : ℕ) : ℕ :=
  if h : o ≤ v ∧ v < o + d then (t.M₁ ⟨v - o, by omega⟩).toNat
  else if h' : o + d ≤ v ∧ v < o + 2 * d then (t.M' ⟨v - o - d, by omega⟩).toNat
  else t.ψ (v - o - 2 * d)

theorem triAt_xOf (o : ℕ) (t : Tri (Fin d)) (h1 : ∀ j, 0 ≤ t.M₁ j) (h2 : ∀ j, 0 ≤ t.M' j) :
    triAt d o (xOf o t) = t := by
  obtain ⟨M₁, ψ, M'⟩ := t
  simp only [triAt, Tri.mk.injEq]
  refine ⟨funext fun j => ?_, funext fun k => ?_, funext fun j => ?_⟩
  · rw [xOf, dif_pos ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel_left, Fin.eta]
    exact Int.toNat_of_nonneg (h1 j)
  · rw [xOf, dif_neg (by omega), dif_neg (by omega)]
    rw [show o + 2 * d + k - o - 2 * d = k by omega]
  · rw [xOf, dif_neg (by omega), dif_pos ⟨by omega, by omega⟩]
    have : o + d + (j : ℕ) - o - d = j := by omega
    simp only [this, Fin.eta]
    exact Int.toNat_of_nonneg (h2 j)

/-- Agreement of candidate solutions on the data the characteristic system reads. -/
def TMatch : List CB → List (Tri (Fin d)) → List (Tri (Fin d)) → Prop
  | b :: bs, t :: ts, t' :: ts' =>
      (t.M₁ = t'.M₁ ∧ t.M' = t'.M' ∧ ∀ k < nE b, t.ψ k = t'.ψ k) ∧ TMatch bs ts ts'
  | [], [], [] => True
  | _, _, _ => False

theorem tMatch_head {b : CB} {bs : List CB} {t : Tri (Fin d)} {ts : List (Tri (Fin d))}
    {ts' : List (Tri (Fin d))} (h : TMatch (b :: bs) (t :: ts) ts') :
    ∃ t' ts'', ts' = t' :: ts'' ∧ t.M₁ = t'.M₁ := by
  cases ts' with
  | nil => simp [TMatch] at h
  | cons t' ts'' => exact ⟨t', ts'', rfl, h.1.1⟩

/-- **Characteristic solutions come from solutions of the system.** -/
theorem charSol_sat : ∀ (o : ℕ) (bs : List CB) (ts : List (Tri (Fin d))),
    CharSol (bs.map (decB d)) ts → ∃ x, TSatL (sysFrom d o bs) x ∧ TMatch bs (trisFrom d o bs x) ts
  | _, [], ts, h => by
    cases h.1
    exact ⟨fun _ => 0, fun e he => by simp [sysFrom] at he, trivial⟩
  | o, [b], ts, h => by
    obtain ⟨h1, -⟩ := h
    cases h1 with
    | cons hc hr =>
      rename_i t ts'
      cases hr
      have hx := triAt_xOf o t hc.1 hc.2.2.2.2.1
      refine ⟨xOf o t, ?_, ?_⟩
      · show TSatL (blkEqs d o b) _
        rw [tSatL_blkEqs, hx]; exact hc
      · simp only [trisFrom, TMatch]
        rw [hx]
        exact ⟨⟨rfl, rfl, fun _ _ => rfl⟩, trivial⟩
  | o, b :: b' :: bs, ts, h => by
    obtain ⟨h1, h2⟩ := h
    cases h1 with
    | cons hc hr =>
      rename_i t ts'
      obtain ⟨x', hx', hm⟩ := charSol_sat (o + bw d b) (b' :: bs) ts'
        ⟨hr, by cases ts' with
          | nil => trivial
          | cons t' ts'' => exact h2.2⟩
      have hxt := triAt_xOf o t hc.1 hc.2.2.2.2.1
      let x : ℕ → ℕ := fun v => if v < o + bw d b then xOf o t v else x' v
      have hlo : ∀ v, v < o + bw d b → x v = xOf o t v := fun v hv => if_pos hv
      have hhi : ∀ v, o + bw d b ≤ v → x v = x' v := fun v hv => if_neg (by omega)
      have hT : trisFrom d (o + bw d b) (b' :: bs) x = trisFrom d (o + bw d b) (b' :: bs) x' :=
        trisFrom_congr _ _ hhi
      unfold bw at hlo hhi hT
      have hblk : TSatL (blkEqs d o b) x := by
        rw [tSatL_congr' (varsIn_blkEqs o b) (y := xOf o t) fun v hv => hlo v (by unfold bw at hv; omega),
          tSatL_blkEqs, hxt]
        exact hc
      have hM' : (triAt d o x).M' = t.M' := by
        rw [← hxt]; simp only [triAt]; funext j; rw [hlo _ (by omega)]
      have hM₁ : (triAt d o x).M₁ = t.M₁ := by
        rw [← hxt]; simp only [triAt]; funext j; rw [hlo _ (by omega)]
      have hψ : ∀ k < nE b, (triAt d o x).ψ k = t.ψ k := by
        intro k hk
        rw [← hxt]; simp only [triAt]; rw [hlo _ (by omega)]
      simp only [trisFrom] at hm
      cases ts' with
      | nil => simp [TMatch] at hm
      | cons t' ts'' =>
        obtain ⟨⟨hm1, hm2, hm3⟩, hmr⟩ := hm
        have hl : t'.M₁ = t.M' + (decB d b').pre := h2.1
        refine ⟨x, ?_, ?_⟩
        · simp only [sysFrom, tSatL_append]
          refine ⟨⟨hblk, ?_⟩, ?_⟩
          · rw [tSatL_linkEqs, hM']
            have : (triAt d (o + bw d b) x).M₁ = (triAt d (o + bw d b) x').M₁ := by
              simp only [triAt]; funext j; rw [hhi _ (by unfold bw; omega)]
            rw [this, hm1, hl]; rfl
          · rwa [tSatL_congr' (varsIn_sysFrom _ _) (y := x') fun v hv => hhi v (by unfold bw at hv; omega)]
        · simp only [trisFrom]
          rw [show trisFrom d (o + bw d b + bw d b') bs x = trisFrom d (o + bw d b + bw d b') bs x' from
            trisFrom_congr _ _ fun v hv => hhi v (by simp only [bw] at *; omega)]
          have hh : triAt d (o + bw d b) x = triAt d (o + bw d b) x' := by
            simp only [triAt, Tri.mk.injEq]
            refine ⟨funext fun j => ?_, funext fun k => ?_, funext fun j => ?_⟩ <;>
              rw [hhi _ (by unfold bw; omega)]
          rw [hh]
          exact ⟨⟨hM₁, hM', hψ⟩, ⟨hm1, hm2, hm3⟩, hmr⟩

end KLM

end Petri

end HTN
