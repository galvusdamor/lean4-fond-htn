import Mathlib

/-!
# Euler's theorem for directed multigraphs

A directed multigraph is a list `E` of edges `(source, target)`; edges are referred to by their
index.  A flow `ψ` assigns a multiplicity to every edge.  `HTN.Petri.Euler.euler`:

> if `ψ` satisfies Kirchhoff's law with source `s` and sink `t` (every node is balanced, except
> that `s` has one more outgoing and `t` one more incoming unit, nothing if `s = t`), and every
> edge of positive multiplicity can be reached from `s` along edges of positive multiplicity,
> then there is a walk from `s` to `t` using every edge exactly as often as `ψ` says.

The proof is a strong induction on the total multiplicity: remove one unit of an edge `e`
leaving `s` towards `v`; the part of the remaining flow reachable from `v` is a flow from `v` to
`t`, and what is left is a balanced flow which (if non-zero) is reachable from `s` and is
spliced in front of `e`.
-/

namespace HTN

namespace Petri

namespace Euler

open Finset

variable (E : List (ℕ × ℕ))

/-- The source of an edge. -/
def src (k : ℕ) : ℕ := (E.getD k (0, 0)).1

/-- The target of an edge. -/
def tgt (k : ℕ) : ℕ := (E.getD k (0, 0)).2

/-- The outflow of a node. -/
def outF (ψ : ℕ → ℕ) (w : ℕ) : ℕ := ∑ k ∈ range E.length, if src E k = w then ψ k else 0

/-- The inflow of a node. -/
def inF (ψ : ℕ → ℕ) (w : ℕ) : ℕ := ∑ k ∈ range E.length, if tgt E k = w then ψ k else 0

/-- **Kirchhoff's law** with source `s` and sink `t`. -/
def Kirch (ψ : ℕ → ℕ) (s t : ℕ) : Prop :=
  ∀ w, outF E ψ w + (if w = t then 1 else 0) = inF E ψ w + (if w = s then 1 else 0)

/-- One step along an edge of positive multiplicity. -/
def PosStep (ψ : ℕ → ℕ) (u v : ℕ) : Prop :=
  ∃ k < E.length, 0 < ψ k ∧ src E k = u ∧ tgt E k = v

/-- Reachability along edges of positive multiplicity. -/
def PosReach (ψ : ℕ → ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen (PosStep E ψ)

/-- **Connectedness**: every edge of positive multiplicity starts at a node reachable from `s`. -/
def Conn (ψ : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ k < E.length, 0 < ψ k → PosReach E ψ s (src E k)

/-- Walks: lists of edge indices. -/
inductive Walk : ℕ → List ℕ → ℕ → Prop
  | nil (u : ℕ) : Walk u [] u
  | cons {k : ℕ} {π : List ℕ} {v : ℕ} : k < E.length → Walk (tgt E k) π v →
      Walk (src E k) (k :: π) v

variable {E}

theorem Walk.append {u v w : ℕ} {π π' : List ℕ} (h : Walk E u π v) (h' : Walk E v π' w) :
    Walk E u (π ++ π') w := by
  induction h with
  | nil => exact h'
  | cons hk _ ih => exact Walk.cons hk (ih h')

theorem Walk.lt {u v : ℕ} {π : List ℕ} (h : Walk E u π v) : ∀ k ∈ π, k < E.length := by
  induction h with
  | nil => simp
  | cons hk _ ih =>
    intro k hk'
    rcases List.mem_cons.1 hk' with rfl | h
    · exact hk
    · exact ih k h

/-! ### Sums over a set of nodes -/

theorem sum_outF (ψ : ℕ → ℕ) (W : Finset ℕ) :
    ∑ w ∈ W, outF E ψ w = ∑ k ∈ range E.length, if src E k ∈ W then ψ k else 0 := by
  unfold outF
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]

theorem sum_inF (ψ : ℕ → ℕ) (W : Finset ℕ) :
    ∑ w ∈ W, inF E ψ w = ∑ k ∈ range E.length, if tgt E k ∈ W then ψ k else 0 := by
  unfold inF
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq]

/-- All endpoints of edges. -/
def ends (E : List (ℕ × ℕ)) : Finset ℕ := (E.flatMap fun e => [e.1, e.2]).toFinset

theorem src_mem_ends {k : ℕ} (hk : k < E.length) : src E k ∈ ends E := by
  simp only [ends, List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]
  exact ⟨E[k], List.getElem_mem hk, Or.inl (by simp [src, List.getElem?_eq_getElem hk])⟩

theorem tgt_mem_ends {k : ℕ} (hk : k < E.length) : tgt E k ∈ ends E := by
  simp only [ends, List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false]
  exact ⟨E[k], List.getElem_mem hk, Or.inr (by simp [tgt, List.getElem?_eq_getElem hk])⟩

/-! ### The total multiplicity -/

/-- The total multiplicity of a flow. -/
def tot (ψ : ℕ → ℕ) : ℕ := ∑ k ∈ range E.length, ψ k

/-! ### The induction step -/

theorem exists_out_of_src {ψ : ℕ → ℕ} {s t : ℕ} (hK : Kirch E ψ s t) (hC : Conn E ψ s)
    (hpos : 0 < tot (E := E) ψ ∨ s ≠ t) : ∃ e < E.length, 0 < ψ e ∧ src E e = s := by
  by_cases hst : s = t
  · subst hst
    have hpos : 0 < tot (E := E) ψ := hpos.resolve_right (fun h => h rfl)
    obtain ⟨k, hk, hψ⟩ : ∃ k ∈ range E.length, 0 < ψ k := by
      by_contra h
      push_neg at h
      have : tot (E := E) ψ = 0 := Finset.sum_eq_zero fun k hk => by have := h k hk; omega
      omega
    rw [Finset.mem_range] at hk
    have hr := hC k hk hψ
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨e, he, hψe, hse, -⟩, -⟩
    · exact ⟨k, hk, hψ, h.symm⟩
    · exact ⟨e, he, hψe, hse⟩
  · have h := hK s
    rw [if_neg hst, if_pos rfl] at h
    have hout : 0 < outF E ψ s := by omega
    obtain ⟨e, he, hψe⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.1 hout)
    rw [Finset.mem_range] at he
    split_ifs at hψe with hse
    · exact ⟨e, he, Nat.pos_iff_ne_zero.2 hψe, hse⟩
    · exact absurd rfl hψe

section Step

variable {ψ : ℕ → ℕ} {s t : ℕ} {e : ℕ}

/-- The flow with one unit of `e` removed. -/
def dec (ψ : ℕ → ℕ) (e : ℕ) : ℕ → ℕ := Function.update ψ e (ψ e - 1)

theorem dec_le (k : ℕ) : dec ψ e k ≤ ψ k := by
  unfold dec
  by_cases h : k = e
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem dec_of_ne {k : ℕ} (h : k ≠ e) : dec ψ e k = ψ k := by
  simp [dec, Function.update_of_ne h]

theorem dec_self : dec ψ e e = ψ e - 1 := by simp [dec]

theorem tot_dec (he : e < E.length) (hψ : 0 < ψ e) : tot (E := E) (dec ψ e) + 1 = tot (E := E) ψ := by
  unfold tot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 he),
    ← Finset.add_sum_erase _ _ (Finset.mem_range.2 he), dec_self]
  rw [Finset.sum_congr rfl fun k hk => dec_of_ne (Finset.ne_of_mem_erase hk)]
  omega

theorem kirch_dec (hK : Kirch E ψ s t) (he : e < E.length) (hψ : 0 < ψ e) (hs : src E e = s) :
    Kirch E (dec ψ e) (tgt E e) t := by
  intro w
  have h := hK w
  have hout : outF E (dec ψ e) w + (if src E e = w then 1 else 0) = outF E ψ w := by
    unfold outF
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 he),
      ← Finset.add_sum_erase _ _ (Finset.mem_range.2 he), dec_self]
    rw [Finset.sum_congr rfl fun k hk => by rw [dec_of_ne (Finset.ne_of_mem_erase hk)]]
    split_ifs <;> omega
  have hin : inF E (dec ψ e) w + (if tgt E e = w then 1 else 0) = inF E ψ w := by
    unfold inF
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 he),
      ← Finset.add_sum_erase _ _ (Finset.mem_range.2 he), dec_self]
    rw [Finset.sum_congr rfl fun k hk => by rw [dec_of_ne (Finset.ne_of_mem_erase hk)]]
    split_ifs <;> omega
  subst hs
  by_cases h1 : src E e = w <;> by_cases h2 : tgt E e = w <;>
    simp only [h1, h2, if_true, if_false, eq_comm (a := w)] at hout hin h ⊢ <;> omega

end Step

/-- The restriction of a flow to the edges whose source satisfies `p`. -/
def restr (ψ : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] : ℕ → ℕ :=
  fun k => if p (src E k) then ψ k else 0

theorem restr_le (ψ : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    restr (E := E) ψ p k ≤ ψ k := by
  by_cases h : p (src E k) <;> simp [restr, h]

theorem restr_add (ψ : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    restr (E := E) ψ p k + restr (E := E) ψ (fun x => ¬ p x) k = ψ k := by
  by_cases h : p (src E k) <;> simp [restr, h]

theorem tot_mono {φ ψ : ℕ → ℕ} (h : ∀ k, φ k ≤ ψ k) : tot (E := E) φ ≤ tot (E := E) ψ :=
  Finset.sum_le_sum fun k _ => h k

/-- **The reachable part.**  With `V` the nodes reachable from `v` along `φ`, where `φ` is a
flow from `v` to `t`: the sink `t` is in `V`, and no edge of positive multiplicity enters `V`
from outside. -/
theorem reach_part {φ : ℕ → ℕ} {v t : ℕ} (hK : Kirch E φ v t) :
    PosReach E φ v t ∧ ∀ k < E.length, 0 < φ k → PosReach E φ v (tgt E k) →
      PosReach E φ v (src E k) := by
  classical
  set V : ℕ → Prop := fun w => PosReach E φ v w with hV
  have hclos : ∀ k < E.length, 0 < φ k → V (src E k) → V (tgt E k) :=
    fun k hk hφ h => h.tail ⟨k, hk, hφ, rfl, rfl⟩
  set W : Finset ℕ := (ends E ∪ {v, t}).filter V with hW
  have hsum := Finset.sum_congr rfl fun w (_ : w ∈ W) => hK w
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_outF, sum_inF] at hsum
  have hvW : v ∈ W := by simp [hW, V, PosReach, Relation.ReflTransGen.refl]
  rw [Finset.sum_ite_eq' W v (fun _ => 1), if_pos hvW] at hsum
  rw [Finset.sum_ite_eq' W t (fun _ => 1)] at hsum
  -- `[src ∈ W]` and `[tgt ∈ W]` against `V`
  have hsrc : ∀ k ∈ range E.length, (if src E k ∈ W then φ k else 0) =
      if V (src E k) then φ k else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp [hW, src_mem_ends hk]
  have htgt : ∀ k ∈ range E.length, (if tgt E k ∈ W then φ k else 0) =
      if V (tgt E k) then φ k else 0 := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp [hW, tgt_mem_ends hk]
  rw [Finset.sum_congr rfl hsrc, Finset.sum_congr rfl htgt] at hsum
  -- split the inflow into edges from inside and from outside
  have hsplit : ∀ k ∈ range E.length, (if V (tgt E k) then φ k else 0) =
      (if V (src E k) then φ k else 0) +
        (if ¬ V (src E k) ∧ V (tgt E k) then φ k else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases h1 : V (src E k)
    · by_cases hφ : φ k = 0
      · simp [hφ]
      · have := hclos k hk (Nat.pos_of_ne_zero hφ) h1
        simp [h1, this]
    · simp [h1]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib] at hsum
  have ht : t ∈ W ∧ ∑ k ∈ range E.length, (if ¬ V (src E k) ∧ V (tgt E k) then φ k else 0) = 0 := by
    by_cases ht : t ∈ W
    · rw [if_pos ht] at hsum; exact ⟨ht, by omega⟩
    · rw [if_neg ht] at hsum; omega
  refine ⟨(Finset.mem_filter.1 ht.1).2, fun k hk hφ hr => ?_⟩
  by_contra hs
  have := (Finset.sum_eq_zero_iff.1 ht.2) k (Finset.mem_range.2 hk)
  rw [if_pos ⟨hs, hr⟩] at this
  omega

/-- **Euler's theorem.** -/
theorem euler : ∀ (n : ℕ) (ψ : ℕ → ℕ) (s t : ℕ), tot (E := E) ψ = n → Kirch E ψ s t →
    Conn E ψ s → ∃ π, Walk E s π t ∧ ∀ k < E.length, π.count k = ψ k := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ψ s t hn hK hC
  by_cases hbase : n = 0 ∧ s = t
  · obtain ⟨rfl, rfl⟩ := hbase
    refine ⟨[], Walk.nil s, fun k hk => ?_⟩
    have := (Finset.sum_eq_zero_iff.1 hn) k (Finset.mem_range.2 hk)
    simp [this]
  have hpos : 0 < tot (E := E) ψ ∨ s ≠ t := by
    by_cases hst : s = t
    · left; rw [hn]; exact Nat.pos_of_ne_zero fun h => hbase ⟨h, hst⟩
    · right; exact hst
  obtain ⟨e, he, hψe, hse⟩ := exists_out_of_src hK hC hpos
  set v := tgt E e with hv
  set φ := dec ψ e with hφ
  have hKφ : Kirch E φ v t := kirch_dec hK he hψe hse
  have htotφ : tot (E := E) φ + 1 = n := hn ▸ tot_dec he hψe
  obtain ⟨hvt, hin⟩ := reach_part hKφ
  set V : ℕ → Prop := fun w => PosReach E φ v w with hV
  set φR := restr (E := E) φ V with hφR
  set φO := restr (E := E) φ (fun x => ¬ V x) with hφO
  have hRO : ∀ k, φR k + φO k = φ k := restr_add φ V
  -- the reachable part is a flow from `v` to `t`
  have hstay : ∀ k < E.length, 0 < φ k → V (src E k) → V (tgt E k) :=
    fun k hk hφk h => Relation.ReflTransGen.tail h ⟨k, hk, hφk, rfl, rfl⟩
  have hR_out : ∀ w, outF E φR w = if V w then outF E φ w else 0 := by
    intro w
    unfold outF
    split_ifs with hw
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : src E k = w
      · simp [h, hφR, restr, hw]
      · simp [h]
    · refine Finset.sum_eq_zero fun k _ => ?_
      by_cases h : src E k = w
      · simp [h, hφR, restr, hw]
      · simp [h]
  have hR_in : ∀ w, inF E φR w = if V w then inF E φ w else 0 := by
    intro w
    unfold inF
    split_ifs with hw
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      by_cases h : tgt E k = w
      · simp only [h, if_true, hφR, restr]
        split_ifs with hs
        · rfl
        · by_contra hne
          exact hs (hin k hk (Nat.pos_of_ne_zero (Ne.symm hne)) (h ▸ hw))
      · simp [h]
    · refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      by_cases h : tgt E k = w
      · simp only [h, if_true, hφR, restr]
        split_ifs with hs
        · by_contra hne
          exact hw (h ▸ hstay k hk (Nat.pos_of_ne_zero hne) hs)
        · rfl
      · simp [h]
  have hvV : V v := Relation.ReflTransGen.refl
  have hKR : Kirch E φR v t := by
    intro w
    rw [hR_out, hR_in]
    by_cases hw : V w
    · rw [if_pos hw, if_pos hw]; exact hKφ w
    · rw [if_neg hw, if_neg hw]
      have h1 : w ≠ t := fun h => hw (h ▸ hvt)
      have h2 : w ≠ v := fun h => hw (h ▸ hvV)
      simp [h1, h2]
  have hCR : Conn E φR v := by
    intro k hk hpos'
    have hs : V (src E k) := by
      by_contra hs
      simp [hφR, restr, hs] at hpos'
    -- a path inside `V` uses only edges of the restriction
    have key : ∀ w, PosReach E φ v w → PosReach E φR v w := by
      intro w hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b hab hstep ih =>
        obtain ⟨k', hk', hφk', hsa, htb⟩ := hstep
        refine ih.tail ⟨k', hk', ?_, hsa, htb⟩
        simp only [hφR, restr]
        rw [if_pos (hsa ▸ hab)]
        exact hφk'
    exact key _ hs
  have htotR : tot (E := E) φR < n := by
    have : tot (E := E) φR ≤ tot (E := E) φ := tot_mono (E := E) (restr_le (E := E) φ V)
    omega
  obtain ⟨πR, hwR, hcR⟩ := ih _ htotR φR v t rfl hKR hCR
  by_cases hsV : V s
  · -- nothing is left over
    have hO0 : ∀ k < E.length, φO k = 0 := by
      intro k hk
      by_contra hne
      have hpos' : 0 < φ k := lt_of_lt_of_le (Nat.pos_of_ne_zero hne) (restr_le _ _ k)
      have hsk : ¬ V (src E k) := by
        intro h; simp [hφO, restr, h] at hne
      have hreach := hC k hk (lt_of_lt_of_le hpos' (dec_le k))
      -- every node reachable from `s` along `ψ` is in `V`
      have key : ∀ w, PosReach E ψ s w → V w := by
        intro w hw
        induction hw with
        | refl => exact hsV
        | @tail a b _ hstep ih =>
          obtain ⟨k', hk', hψk', hsa, htb⟩ := hstep
          by_cases hke : k' = e
          · rw [hke] at htb; rw [← htb]; exact hvV
          · have : 0 < φ k' := by rw [hφ, dec_of_ne hke]; exact hψk'
            exact htb ▸ hstay k' hk' this (hsa ▸ ih)
      exact hsk (key _ hreach)
    refine ⟨e :: πR, hse ▸ Walk.cons he hwR, fun k hk => ?_⟩
    have h1 := hRO k
    rw [hO0 k hk] at h1
    by_cases hke : k = e
    · have h3 : φ k = ψ k - 1 := by rw [hφ, hke, dec_self]
      have h4 : 0 < ψ k := hke ▸ hψe
      rw [hke, List.count_cons_self, ← hke, hcR k hk]
      omega
    · have h3 : φ k = ψ k := by rw [hφ, dec_of_ne hke]
      rw [List.count_cons_of_ne (Ne.symm hke), hcR k hk]
      omega
  · -- the left-over part is a balanced flow at `s`
    have hO_out : ∀ w, outF E φO w = if V w then 0 else outF E φ w := by
      intro w
      have h1 := hR_out w
      have h2 : outF E φR w + outF E φO w = outF E φ w := by
        unfold outF
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp [hRO]
      split_ifs at h1 ⊢ <;> omega
    have hO_in : ∀ w, inF E φO w = if V w then 0 else inF E φ w := by
      intro w
      have h1 := hR_in w
      have h2 : inF E φR w + inF E φO w = inF E φ w := by
        unfold inF
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp [hRO]
      split_ifs at h1 ⊢ <;> omega
    have hKO : Kirch E φO s s := by
      intro w
      rw [hO_out, hO_in]
      by_cases hw : V w
      · rw [if_pos hw, if_pos hw]
      · rw [if_neg hw, if_neg hw]
        have h1 := hKφ w
        have h2 : w ≠ t := fun h => hw (h ▸ hvt)
        have h3 : w ≠ v := fun h => hw (h ▸ hvV)
        simp only [h2, h3, if_false] at h1
        omega
    have hCO : Conn E φO s := by
      intro k hk hpos'
      have hsk : ¬ V (src E k) := by
        intro h; simp [hφO, restr, h] at hpos'
      have hpos'' : 0 < ψ k :=
        lt_of_lt_of_le (lt_of_lt_of_le hpos' (restr_le _ _ k)) (dec_le k)
      have key : ∀ w, PosReach E ψ s w → ¬ V w → PosReach E φO s w := by
        intro w hw
        induction hw with
        | refl => exact fun _ => Relation.ReflTransGen.refl
        | @tail a b _ hstep ih =>
          intro hb
          obtain ⟨k', hk', hψk', hsa, htb⟩ := hstep
          have hke : k' ≠ e := by
            rintro rfl
            exact hb (htb ▸ hvV)
          have hφk' : 0 < φ k' := by rw [hφ, dec_of_ne hke]; exact hψk'
          have ha : ¬ V a := fun h => hb (htb ▸ hstay k' hk' hφk' (hsa ▸ h))
          refine (ih ha).tail ⟨k', hk', ?_, hsa, htb⟩
          simp only [hφO, restr]
          rw [if_pos (by rw [hsa]; exact ha)]
          exact hφk'
      exact key _ (hC k hk hpos'') hsk
    have htotO : tot (E := E) φO < n := by
      have : tot (E := E) φO ≤ tot (E := E) φ :=
        tot_mono (E := E) (restr_le (E := E) φ (fun x => ¬ V x))
      omega
    obtain ⟨πO, hwO, hcO⟩ := ih _ htotO φO s s rfl hKO hCO
    refine ⟨πO ++ e :: πR, hwO.append (hse ▸ Walk.cons he hwR), fun k hk => ?_⟩
    rw [List.count_append]
    have h1 := hRO k
    by_cases hke : k = e
    · have h3 : φ k = ψ k - 1 := by rw [hφ, hke, dec_self]
      have h4 : 0 < ψ k := hke ▸ hψe
      rw [hke, List.count_cons_self, ← hke, hcR k hk, hcO k hk]
      omega
    · have h3 : φ k = ψ k := by rw [hφ, dec_of_ne hke]
      rw [List.count_cons_of_ne (Ne.symm hke), hcR k hk, hcO k hk]
      omega

end Euler

end Petri

end HTN
