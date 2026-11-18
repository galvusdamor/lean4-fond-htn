import HtnComplexity.Computable.PoSearch
import HtnPlanning.Computable.Classes
/-!
# The measure that makes the search of an acyclic domain terminate

The search space of `HtnComplexity/Computable/PoSearch.lean` is infinite for a cyclic
hierarchy.  For an **acyclic** domain description it is not: this file supplies the measure
that decreases along every step.

* `HTN.Syn.compEdges d` — the dependency graph of the domain description: an edge `(c, c')` for
  every listed method for `c` with a subtask labelled `c'`;
* `HTN.Syn.rkD d c` — the *rank* of a compound name: the number of names reachable from it in
  that graph.  It is computable, and for an acyclic description it strictly decreases along an
  edge (`HTN.Syn.rkD_lt_of_mem_compEdges`) — the rank function `HTN.Syn.DomDesc.IsAcyclic` only
  asserts to exist;
* `HTN.Syn.phi d p` — the weight of a search network: every task still to be processed
  contributes `1` if it is primitive and `(M + 1) ^ (rank + 1)` if it is compound, where `M`
  bounds the number of subtasks of a listed method.

The two theorems are `HTN.Syn.phi_finish_lt` and `HTN.Syn.phi_expand_lt`: **every step of the
search strictly decreases the measure**.  A decomposition replaces a compound task of rank `r`
by at most `M` tasks of weight at most `(M + 1) ^ r`, and `M * (M + 1) ^ r < (M + 1) ^ (r + 1)`.
-/

namespace HTN

namespace Syn

/-! ### The dependency graph of a domain description -/

/-- The edges of the dependency graph: `(c, c')` if a listed method for `c` has a subtask
labelled with the compound name `c'`. -/
def compEdges (d : DomDesc) : List (ℕ × ℕ) :=
  d.methods.flatMap fun e =>
    e.2.ids.dedup.filterMap fun x =>
      match e.2.label x with
      | Sum.inr c' => some (e.1, c')
      | Sum.inl _ => none

/-- The compound names the dependency graph mentions. -/
def compNames (d : DomDesc) : List ℕ := (compEdges d).flatMap fun p => [p.1, p.2]

theorem mem_compEdges {d : DomDesc} {a b : ℕ} :
    (a, b) ∈ compEdges d ↔
      ∃ e ∈ d.methods, e.1 = a ∧ ∃ x ∈ e.2.ids, e.2.label x = Sum.inr b := by
  simp only [compEdges, List.mem_flatMap, List.mem_filterMap, List.mem_dedup]
  constructor
  · rintro ⟨e, he, x, hx, hval⟩
    rcases hlab : e.2.label x with c' | c'
    · rw [hlab] at hval
      simp at hval
    · rw [hlab] at hval
      simp only [Option.some.injEq, Prod.ext_iff] at hval
      exact ⟨e, he, hval.1, x, hx, by rw [hlab, hval.2]⟩
  · rintro ⟨e, he, rfl, x, hx, hlab⟩
    exact ⟨e, he, x, hx, by rw [hlab]⟩

theorem mem_compNames_right {d : DomDesc} {a b : ℕ} (h : (a, b) ∈ compEdges d) :
    b ∈ compNames d := by
  simp only [compNames, List.mem_flatMap]
  exact ⟨(a, b), h, by simp⟩

/-- Along an edge of the dependency graph an acyclicity rank strictly decreases. -/
theorem rk_lt_of_mem_compEdges {d : DomDesc} {rk : ℕ → ℕ} (hrk : d.AcyclicBy rk) {a b : ℕ}
    (h : (a, b) ∈ compEdges d) : rk b < rk a := by
  obtain ⟨e, he, rfl, x, hx, hlab⟩ := mem_compEdges.1 h
  exact hrk e he x (by simpa using hx) b hlab

/-- An acyclic description has no cycle in its dependency graph. -/
theorem not_transGen_compEdges {d : DomDesc} (hd : d.IsAcyclic) (c : ℕ) :
    ¬ Relation.TransGen (fun a b => (a, b) ∈ compEdges d) c c := by
  obtain ⟨rk, hrk⟩ := hd
  intro h
  have key : ∀ {a b : ℕ}, Relation.TransGen (fun a b => (a, b) ∈ compEdges d) a b → rk b < rk a := by
    intro a b hab
    induction hab with
    | single hst => exact rk_lt_of_mem_compEdges hrk hst
    | tail _ hst ih => exact lt_trans (rk_lt_of_mem_compEdges hrk hst) ih
  exact absurd (key h) (lt_irrefl _)

/-- **The rank of a compound name**: the number of names reachable from it in the dependency
graph.  Unlike the rank function whose existence `DomDesc.IsAcyclic` asserts, this one is
computable. -/
def rkD (d : DomDesc) (c : ℕ) : ℕ :=
  ((compNames d).dedup.filter fun c' => reachB (compEdges d) c c').length

/-- **The computed rank decreases along an edge** of the dependency graph of an acyclic
description. -/
theorem rkD_lt_of_mem_compEdges {d : DomDesc} (hd : d.IsAcyclic) {a b : ℕ}
    (h : (a, b) ∈ compEdges d) : rkD d b < rkD d a := by
  refine length_filter_lt (x := b) ?_ ?_ ?_ ?_
  · intro x _ hx
    refine (reachB_iff (E := compEdges d)).2 ?_
    exact Relation.TransGen.head h ((reachB_iff (E := compEdges d)).1 hx)
  · exact List.mem_dedup.2 (mem_compNames_right h)
  · exact (reachB_iff (E := compEdges d)).2 (Relation.TransGen.single h)
  · rcases hr : reachB (compEdges d) b b with _ | _
    · rfl
    · exact absurd ((reachB_iff (E := compEdges d)).1 hr) (not_transGen_compEdges hd b)

/-! ### The measure -/

/-- A bound on the number of subtasks of a listed method. -/
def maxBody (d : DomDesc) : ℕ := (d.methods.map fun e => e.2.ids.dedup.length).foldr Nat.max 0

theorem le_foldr_max {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr Nat.max 0 := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    have hstep : (y :: ys).foldr Nat.max 0 = Nat.max y (ys.foldr Nat.max 0) := rfl
    rcases List.mem_cons.1 h with rfl | hys
    · rw [hstep]
      exact Nat.le_max_left _ _
    · rw [hstep]
      exact le_trans (ih hys) (Nat.le_max_right _ _)

theorem length_le_maxBody {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    e.2.ids.dedup.length ≤ maxBody d :=
  le_foldr_max (List.mem_map_of_mem he)

/-- The weight of a task: `1` for a primitive one, and `(M + 1) ^ (rank + 1)` for a compound
one. -/
def wOf (d : DomDesc) (lbl : Bool × ℕ) : ℕ :=
  if lbl.1 then (maxBody d + 1) ^ (rkD d lbl.2 + 1) else 1

theorem one_le_wOf (d : DomDesc) (lbl : Bool × ℕ) : 1 ≤ wOf d lbl := by
  rw [wOf]
  split
  · exact Nat.one_le_pow _ _ (Nat.succ_pos _)
  · exact le_rfl

/-- **The measure of a search network**: the total weight of the tasks still to be
processed. -/
def phi (d : DomDesc) (p : PNet) : ℕ := (p.map fun x => if x.2.2.1 then wOf d x.2.1 else 0).sum

@[simp] theorem phi_append (d : DomDesc) (p q : PNet) : phi d (p ++ q) = phi d p + phi d q := by
  simp [phi]

@[simp] theorem phi_cons (d : DomDesc) (x : PItem) (xs : PNet) :
    phi d (x :: xs) = (if x.2.2.1 then wOf d x.2.1 else 0) + phi d xs := by
  simp [phi]

/-- Clearing one processed task removes exactly its weight. -/
theorem phi_clear (d : DomDesc) (i : ℕ) (g : PItem → List ℕ) :
    ∀ p : PNet, p.allIds.Nodup → ∀ x ∈ p, x.1 = i → x.2.2.1 = true →
      phi d (p.map fun z => if z.1 = i then (z.1, z.2.1, false, ([] : List ℕ))
        else (z.1, z.2.1, z.2.2.1, g z)) + wOf d x.2.1 = phi d p := by
  intro p
  induction p with
  | nil => intro _ x hx; simp at hx
  | cons y ys ih =>
    intro hnd x hx hx1 hpres
    have hnd0 : (y.1 :: PNet.allIds ys).Nodup := hnd
    have hy : y.1 ∉ PNet.allIds ys := (List.nodup_cons.1 hnd0).1
    have hnd' : (PNet.allIds ys).Nodup := (List.nodup_cons.1 hnd0).2
    rcases List.mem_cons.1 hx with rfl | hxs
    · -- the cleared task is the head
      subst hx1
      have hrest : ∀ z ∈ ys, z.1 ≠ x.1 := by
        intro z hz hzx
        exact hy (hzx ▸ List.mem_map_of_mem hz)
      have hmap : (ys.map fun z => if z.1 = x.1 then ((z.1, z.2.1, false, ([] : List ℕ)) : PItem)
          else (z.1, z.2.1, z.2.2.1, g z)) = ys.map fun z => (z.1, z.2.1, z.2.2.1, g z) :=
        List.map_congr_left fun z hz => by rw [if_neg (hrest z hz)]
      have hphi : phi d (ys.map fun z => ((z.1, z.2.1, z.2.2.1, g z) : PItem)) = phi d ys := by
        simp [phi, List.map_map, Function.comp_def]
      rw [List.map_cons, if_pos rfl, hmap, phi_cons, phi_cons, hphi, hpres]
      simp
      omega
    · -- the cleared task is in the tail
      have hyx : y.1 ≠ i := by
        intro hyi
        exact hy (by rw [hyi, ← hx1]; exact List.mem_map_of_mem hxs)
      have ihs := ih hnd' x hxs hx1 hpres
      rw [List.map_cons, if_neg hyx, phi_cons, phi_cons]
      simp only
      omega

theorem phi_finish_lt {d : DomDesc} {p : PNet} (hnd : p.allIds.Nodup) {i : ℕ} {x : PItem}
    (hx : x ∈ p) (hx1 : x.1 = i) (hpres : x.2.2.1 = true) :
    phi d (p.finish i) < phi d p := by
  have h := phi_clear d i (fun z => z.2.2.2.filter fun y => y ≠ i) p hnd x hx hx1 hpres
  have hw := one_le_wOf d x.2.1
  rw [PNet.finish]
  simp only at h ⊢
  omega

/-- The weight the new items of a decomposition contribute. -/
theorem phi_newItems (d : DomDesc) (p : PNet) (i : ℕ) (e : MethodDesc) :
    phi d (p.newItems i e) = (e.2.ids.dedup.map fun x => wOf d (e.2.lblPair x)).sum := by
  simp [phi, PNet.newItems, List.map_map, Function.comp_def]

theorem wOf_le_of_mem_body {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) (hd : d.IsAcyclic)
    {cc : ℕ} (hec : e.1 = cc) {x : ℕ} (hx : x ∈ e.2.ids.dedup) :
    wOf d (e.2.lblPair x) ≤ (maxBody d + 1) ^ rkD d cc := by
  rcases hlab : e.2.label x with a | c'
  · have hpair : e.2.lblPair x = (false, a) :=
      TnDesc.ofPair_eq_inl_iff.1 (by rw [TnDesc.ofPair_lblPair, hlab])
    rw [hpair, wOf]
    simp only [Bool.false_eq_true, if_false]
    exact Nat.one_le_pow _ _ (Nat.succ_pos _)
  · have hpair : e.2.lblPair x = (true, c') :=
      TnDesc.ofPair_eq_inr_iff.1 (by rw [TnDesc.ofPair_lblPair, hlab])
    have hedge : (cc, c') ∈ compEdges d :=
      mem_compEdges.2 ⟨e, he, hec, x, List.mem_dedup.1 hx, hlab⟩
    have hrk : rkD d c' < rkD d cc := rkD_lt_of_mem_compEdges hd hedge
    rw [hpair, wOf]
    simp only [if_pos]
    exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)

theorem phi_newItems_lt {d : DomDesc} (hd : d.IsAcyclic) (p : PNet) (i : ℕ) {e : MethodDesc}
    (he : e ∈ d.methods) {cc : ℕ} (hec : e.1 = cc) :
    phi d (p.newItems i e) < wOf d (true, cc) := by
  rw [phi_newItems]
  have hbound : (e.2.ids.dedup.map fun x => wOf d (e.2.lblPair x)).sum ≤
      (e.2.ids.dedup.map fun x => wOf d (e.2.lblPair x)).length * (maxBody d + 1) ^ rkD d cc := by
    refine List.sum_le_card_nsmul _ _ ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact wOf_le_of_mem_body he hd hec hx
  have hlen : (e.2.ids.dedup.map fun x => wOf d (e.2.lblPair x)).length ≤ maxBody d := by
    rw [List.length_map]
    exact length_le_maxBody he
  have hpow : 0 < (maxBody d + 1) ^ rkD d cc := pow_pos (Nat.succ_pos _) _
  have hw : wOf d (true, cc) = (maxBody d + 1) * (maxBody d + 1) ^ rkD d cc := by
    rw [wOf]
    simp only [if_pos]
    ring
  have : (e.2.ids.dedup.map fun x => wOf d (e.2.lblPair x)).length *
      (maxBody d + 1) ^ rkD d cc < (maxBody d + 1) * (maxBody d + 1) ^ rkD d cc :=
    Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hpow
  omega

theorem phi_expand_lt {d : DomDesc} (hd : d.IsAcyclic) {p : PNet} (hnd : p.allIds.Nodup)
    {i cc : ℕ} {x : PItem} (hx : x ∈ p) (hx1 : x.1 = i) (hpres : x.2.2.1 = true)
    (hlbl : x.2.1 = (true, cc)) {e : MethodDesc} (he : e ∈ d.methods) (hec : e.1 = cc) :
    phi d (p.expand i e) < phi d p := by
  have h := phi_clear d i (fun z => PNet.substDep i (p.newIds e) z.2.2.2) p hnd x hx hx1 hpres
  have hnew := phi_newItems_lt hd p i he hec
  rw [PNet.expand, phi_append, PNet.oldItems]
  rw [hlbl] at h
  simp only at h ⊢
  omega

/-- **Every step of the search of an acyclic domain strictly decreases the measure.** -/
theorem phi_lt_of_pStep {d : DomDesc} (hd : d.IsAcyclic) {c c' : PConfig} (hOk : PNet.Ok c.2)
    (h : PStep d c c') : phi d c'.2 < phi d c.2 := by
  obtain ⟨x, hx, hcase⟩ := mem_succsOf_iff.1 h
  obtain ⟨hxm, hpres, -⟩ := mem_readyItems.1 hx
  rcases hcase with ⟨e, he, hk, hename, rfl⟩ | ⟨-, -, rfl⟩
  · refine phi_expand_lt hd hOk.nodup hxm rfl hpres ?_ he hename
    rcases hb : x.2.1 with ⟨b, m⟩
    rw [hb] at hk
    simp only at hk
    rw [hk]
  · exact phi_finish_lt hOk.nodup hxm rfl hpres

theorem rkD_le (d : DomDesc) (c : ℕ) : rkD d c ≤ (compNames d).dedup.length :=
  List.length_filter_le _ _

end Syn

end HTN
