import ComplexityTheory.Petri.CharSys
/-!
# Deciding the side conditions on the characteristic system

* `noChar_iff` — the characteristic system of a decoded problem is infeasible iff the explicit
  system `sysFrom d 0 bs` is;
* `bound_iff` — a linear quantity of block `i` is bounded by `B` in every characteristic solution
  iff the system with the extra equation `quantity - slack = B + 1` is infeasible;
  instances `inpBound_iff`, `outBound_iff`, `edgeBound_iff` for the three side conditions of
  refutations;
* `feasB` — feasibility of a system of term equations, by bounded search (`feasB_iff`).
-/

namespace HTN

namespace Petri

namespace KLM

open Finset Euler Comp

variable {d : ℕ}

/-! ### Indexing -/

theorem getElem?_trisFrom : ∀ (o : ℕ) (bs : List CB) (x : ℕ → ℕ) (i : ℕ), i < bs.length →
    (trisFrom d o bs x)[i]? = some (triAt d (o + totW (d := d) (bs.take i)) x)
  | _, [], _, _, h => by simp at h
  | o, b :: bs, x, 0, _ => by simp [trisFrom, totW]
  | o, b :: bs, x, i + 1, h => by
    simp only [trisFrom, List.getElem?_cons_succ, List.take_succ_cons, totW]
    rw [getElem?_trisFrom _ bs x i (by simpa using h)]
    congr 2
    omega

theorem tMatch_get : ∀ (bs : List CB) (ts ts' : List (Tri (Fin d))), TMatch bs ts ts' →
    ∀ i (hi : i < bs.length), ∃ t t', ts[i]? = some t ∧ ts'[i]? = some t' ∧ t.M₁ = t'.M₁ ∧
      t.M' = t'.M' ∧ ∀ k < nE bs[i], t.ψ k = t'.ψ k
  | [], _, _, _, _, hi => by simp at hi
  | b :: bs, t :: ts, t' :: ts', h, 0, _ => ⟨t, t', rfl, rfl, h.1⟩
  | b :: bs, t :: ts, t' :: ts', h, i + 1, hi =>
    tMatch_get bs ts ts' h.2 i (by simpa using hi)
  | _ :: _, [], _, h, _, _ => by simp [TMatch] at h
  | _ :: _, _ :: _, [], h, _, _ => by simp [TMatch] at h

/-! ### Infeasibility -/

/-- **No characteristic solution** iff the explicit system is infeasible. -/
theorem noChar_iff (bs : List CB) :
    (¬ ∃ ts, CharSol (bs.map (decB d)) ts) ↔ ¬ ∃ x, TSatL (sysFrom d 0 bs) x := by
  constructor
  · rintro h ⟨x, hx⟩
    exact h ⟨_, sat_charSol 0 bs x hx⟩
  · rintro h ⟨ts, hts⟩
    obtain ⟨x, hx, -⟩ := charSol_sat 0 bs ts hts
    exact h ⟨x, hx⟩

/-- **Bounds in all characteristic solutions**, as infeasibility. -/
theorem bound_iff (bs : List CB) (i : ℕ) (hi : i < bs.length) (f : Tri (Fin d) → ℤ)
    (lin : List (ℕ × ℤ))
    (hlin : ∀ x, f (triAt d (totW (d := d) (bs.take i)) x) = tval lin x)
    (hf : ∀ t t' : Tri (Fin d), t.M₁ = t'.M₁ → t.M' = t'.M' → (∀ k < nE bs[i], t.ψ k = t'.ψ k) →
      f t = f t')
    (hvars : ∀ p ∈ lin, p.1 < totW (d := d) bs) (B : ℤ) :
    (∀ ts, CharSol (bs.map (decB d)) ts → ∀ t ∈ ts[i]?, f t ≤ B) ↔
      ¬ ∃ x, TSatL (sysFrom d 0 bs ++ [(lin ++ [(totW (d := d) bs, -1)], B + 1)]) x := by
  constructor
  · rintro h ⟨x, hx⟩
    rw [tSatL_append] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have := h _ (sat_charSol 0 bs x hx1) _ (by rw [getElem?_trisFrom 0 bs x i hi]; rfl)
    rw [zero_add, hlin] at this
    have h2 := hx2 _ (List.mem_singleton_self _)
    simp only [TSat, tval_append, tval_cons, tval_nil] at h2
    have : (0 : ℤ) ≤ x (totW (d := d) bs) := Int.natCast_nonneg _
    linarith
  · intro h ts hts t ht
    by_contra hlt
    push_neg at hlt
    obtain ⟨x, hx, hm⟩ := charSol_sat 0 bs ts hts
    obtain ⟨t₁, t₂, h1, h2, hM₁, hM', hψ⟩ := tMatch_get bs _ ts hm i hi
    rw [getElem?_trisFrom 0 bs x i hi] at h1
    obtain rfl := Option.some.inj h1
    obtain rfl : t₂ = t := Option.some.inj (h2.symm.trans ht)
    have hft := hf _ _ hM₁ hM' hψ
    rw [zero_add, hlin] at hft
    let S := totW (d := d) bs
    let x' := Function.update x S (tval lin x - B - 1).toNat
    have hagree : ∀ v < S, x' v = x v := fun v hv => Function.update_of_ne (by omega) _ _
    apply h
    refine ⟨x', tSatL_append.2 ⟨?_, ?_⟩⟩
    · exact (tSatL_congr' (varsIn_sysFrom_lt 0 bs) fun v hv => hagree v (by simpa using hv)).2 hx
    · intro e he
      rw [List.mem_singleton] at he
      subst he
      simp only [TSat, tval_append, tval_cons, tval_nil]
      rw [tval_congr (y := x) fun p hp => hagree _ (hvars p hp)]
      have : x' S = (tval lin x - B - 1).toNat := Function.update_self _ _ _
      rw [this, Int.toNat_of_nonneg (by linarith)]
      ring

/-! ### The three kinds of bounds -/

/-- The offset of block `i`. -/
def offs (bs : List CB) (i : ℕ) : ℕ := totW (d := d) (bs.take i)

theorem totW_take_le (bs : List CB) (i : ℕ) (hi : i < bs.length) :
    totW (d := d) (bs.take i) + bw d bs[i] ≤ totW (d := d) bs := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [totW]
    | succ i =>
      simp only [List.take_succ_cons, totW, List.getElem_cons_succ]
      have := ih i (by simpa using hi)
      omega

theorem inpBound_iff (bs : List CB) (i : ℕ) (hi : i < bs.length) (j : Fin d) (B : ℤ) :
    (∀ ts, CharSol (bs.map (decB d)) ts → ∀ t ∈ ts[i]?, t.M₁ j ≤ B) ↔
      ¬ ∃ x, TSatL (sysFrom d 0 bs ++
        [([(offs (d := d) bs i + j, 1)] ++ [(totW (d := d) bs, -1)], B + 1)]) x := by
  refine bound_iff bs i hi (fun t => t.M₁ j) _ (fun x => by simp [triAt, offs])
    (fun t t' h _ _ => by simp only [h]) (fun p hp => ?_) B
  simp only [List.mem_singleton] at hp
  subst hp
  have := totW_take_le (d := d) bs i hi
  unfold bw at this; simp only [offs]; omega

theorem outBound_iff (bs : List CB) (i : ℕ) (hi : i < bs.length) (j : Fin d) (B : ℤ) :
    (∀ ts, CharSol (bs.map (decB d)) ts → ∀ t ∈ ts[i]?, t.M' j ≤ B) ↔
      ¬ ∃ x, TSatL (sysFrom d 0 bs ++
        [([(offs (d := d) bs i + d + j, 1)] ++ [(totW (d := d) bs, -1)], B + 1)]) x := by
  refine bound_iff bs i hi (fun t => t.M' j) _ (fun x => by simp [triAt, offs])
    (fun t t' _ h _ => by simp only [h]) (fun p hp => ?_) B
  simp only [List.mem_singleton] at hp
  subst hp
  have := totW_take_le (d := d) bs i hi
  unfold bw at this; simp only [offs]; omega

/-- Decoded equality of concrete edges, as a boolean. -/
def ceqB (d : ℕ) (e e' : CE) : Bool :=
  e.1 == e'.1 && e.2.2 == e'.2.2 && (List.range d).all fun j => e.2.1.getD j 0 == e'.2.1.getD j 0

theorem ceqB_iff (e e' : CE) : ceqB d e e' = true ↔ decE d e = decE d e' := by
  simp only [ceqB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decE,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, funext fun j => h3 j j.2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, fun j hj => congrFun h2 ⟨j, hj⟩⟩

/-- The terms counting the uses of the edge `ce` in block `i`. -/
def edgeLin (bs : List CB) (i : ℕ) (ce : CE) : List (ℕ × ℤ) :=
  (List.range (nE (bs.getD i default))).map fun k =>
    (offs (d := d) bs i + 2 * d + k, if ceqB d (cedge (bs.getD i default) k) ce then 1 else 0)

theorem fib_decC (b : CB) (ce : CE) (ψ : ℕ → ℕ) :
    (fib (decC d (cComp b)) (decE d ce) ψ : ℤ) =
      ∑ k ∈ range (nE b), (if ceqB d (cedge b k) ce then 1 else 0) * (ψ k : ℤ) := by
  unfold fib
  simp only [decC_edges, List.length_map]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (decC d (cComp b)).edge k = decE d (cedge b k) := by
    simp only [Comp.edge, decC_edges, getD_map_decE]; rfl
  rw [this]
  by_cases h : ceqB d (cedge b k) ce = true
  · rw [if_pos ((ceqB_iff _ _).1 h), if_pos h]; simp
  · rw [if_neg (fun h' => h ((ceqB_iff _ _).2 h')), if_neg h]; simp

theorem edgeBound_iff (bs : List CB) (i : ℕ) (hi : i < bs.length) (ce : CE) (B : ℕ) :
    (∀ ts, CharSol (bs.map (decB d)) ts → ∀ t ∈ ts[i]?,
        fib (decC d (cComp bs[i])) (decE d ce) t.ψ ≤ B) ↔
      ¬ ∃ x, TSatL (sysFrom d 0 bs ++
        [(edgeLin (d := d) bs i ce ++ [(totW (d := d) bs, -1)], (B : ℤ) + 1)]) x := by
  have hb : bs.getD i default = bs[i] := List.getD_eq_getElem _ _ hi
  rw [← bound_iff bs i hi (fun t => (fib (decC d (cComp bs[i])) (decE d ce) t.ψ : ℤ))
    (edgeLin (d := d) bs i ce) ?_ ?_ ?_ (B : ℤ)]
  · simp only [Nat.cast_le]
  · intro x
    show (fib (decC d (cComp bs[i])) (decE d ce) _ : ℤ) = _
    rw [fib_decC, edgeLin, hb, tval_map_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [triAt, offs]
  · intro t t' _ _ hψ
    show (fib (decC d (cComp bs[i])) (decE d ce) _ : ℤ) = (fib (decC d (cComp bs[i])) (decE d ce) _ : ℤ)
    rw [fib_decC, fib_decC]
    exact Finset.sum_congr rfl fun k hk => by rw [hψ k (Finset.mem_range.1 hk)]
  · intro p hp
    simp only [edgeLin, hb, List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    have := totW_take_le (d := d) bs i hi
    unfold bw at this; simp only [offs]; omega

/-! ### Bounded search -/

/-- All lists of length `n` with entries `≤ B`. -/
def boxes : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, B => (boxes n B).flatMap fun v => (List.range (B + 1)).map fun a => a :: v

theorem mem_boxes : ∀ (n B : ℕ) (v : List ℕ), v ∈ boxes n B ↔ v.length = n ∧ ∀ a ∈ v, a ≤ B
  | 0, B, v => by cases v <;> simp [boxes]
  | n + 1, B, v => by
    simp only [boxes, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨w, hw, a, ha, rfl⟩
      rw [mem_boxes] at hw
      refine ⟨by simp [hw.1], fun c hc => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · omega
      · exact hw.2 c hc
    · intro ⟨hl, hb⟩
      cases v with
      | nil => simp at hl
      | cons a w =>
        exact ⟨w, (mem_boxes n B w).2 ⟨by simpa using hl, fun c hc => hb c (by simp [hc])⟩,
          a, by have := hb a (by simp); omega, rfl⟩

/-- An equation holds at a list of values. -/
def eqHoldsB (v : List ℕ) (e : TEq) : Bool := decide (tval e.1 (fun i => v.getD i 0) = e.2)

/-- **Feasibility by bounded search.** -/
def feasB (es : List TEq) : Bool :=
  (boxes (ILP.nVar (es.map dense)) (ILP.solBnd (es.map dense))).any fun v => es.all (eqHoldsB v)

theorem feasB_iff (es : List TEq) : feasB es = true ↔ ∃ x, TSatL es x := by
  unfold feasB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨v, -, hv⟩
    refine ⟨fun i => v.getD i 0, fun e he => ?_⟩
    have := (List.all_eq_true.1 hv) e he
    simpa [eqHoldsB] using this
  · rintro ⟨x, hx⟩
    rw [← lsat_dense] at hx
    obtain ⟨y, hy, hyB, hy0⟩ := ILP.small_sol hx
    rw [lsat_dense] at hy
    let n := ILP.nVar (es.map dense)
    refine ⟨(List.range n).map y, (mem_boxes _ _ _).2 ⟨by simp [n], ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
      exact hyB v
    · have hfun : (fun i => ((List.range n).map y).getD i 0) = y := by
        funext i
        by_cases h : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
        · rw [List.getD_eq_default _ _ (by simpa using h), hy0 i (by omega)]
      refine List.all_eq_true.2 fun e he => ?_
      simp only [eqHoldsB, hfun, decide_eq_true_eq]
      exact hy e he

end KLM

end Petri

end HTN
