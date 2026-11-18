import HtnPlanning.Computable.Reach
import HtnComplexity.Complexity.TOPlan.Pos
/-!
# The order of a serialised initial task network, inside Cobham's class

`HTN.Syn.TnDesc.preOrd t a b` — the transitive closure of the listed ordering pairs — decided on
the serialisation `HTN.Syn.instSer q` by a function of Cobham's class.

* `HTN.Syn.TOPlan.rStep K x V` — one round of marking: an ordering pair (named by the position of
  its entry in `x`) is marked if its source is the node `K`, or the target of a pair marked in
  `V`;
* `HTN.Syn.TOPlan.reachV K x` — `|x|` rounds, starting from nothing marked;
* `HTN.Syn.TOPlan.preOrdB K K' x` — some marked pair has target `K'`;
* `HTN.Syn.TOPlan.preOrdB_iff` — **correctness**: on `x = instSer q`, for the doubled numerals
  `key a`, `key b`, this is `q.tnI.preOrd a b`;
* `HTN.Syn.TOPlan.cobhamB_preOrdB` — it is a predicate of Cobham's class.
-/

namespace HTN

namespace Syn

namespace TOPlan

open PTime Compress

/-! ### The functions -/

/-- **One round of marking** the ordering pairs reachable from the node `K`. -/
def rStep (K x V : List Bool) : List Bool :=
  x.tails.map fun e => edgePos x e &&
    (decide (srcD e = K) || x.tails.any fun e' => bitAt V x e' && decide (tgtD e' = srcD e))

/-- The ordering pairs reachable from the node `K` (by their entry positions). -/
def reachV (K x : List Bool) : List Bool :=
  (rStep K x)^[x.length] (x.tails.map fun _ => false)

/-- **The listed pairs lead from `K` to `K'`.** -/
def preOrdB (K K' x : List Bool) : Bool :=
  x.tails.any fun e => bitAt (reachV K x) x e && decide (tgtD e = K')

/-! ### Correctness -/

theorem mem_reachIter_iff {E : List (ℕ × ℕ)} {a b : ℕ} : ∀ m : ℕ,
    b ∈ reachIter E a m ↔ (a, b) ∈ E ∨ ∃ m', m = m' + 1 ∧ ∃ c ∈ reachIter E a m', (c, b) ∈ E
  | 0 => by simp
  | m + 1 => by
    rw [reachIter_succ, List.mem_append, mem_succsOfList, mem_reachIter_iff m]
    constructor
    · rintro ((h | ⟨m', rfl, c, hc, hcb⟩) | ⟨c, hc, hcb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨m' + 1, rfl, c, reachIter_subset_succ m' hc, hcb⟩
      · exact Or.inr ⟨m, rfl, c, hc, hcb⟩
    · rintro (h | ⟨m', hm, c, hc, hcb⟩)
      · exact Or.inl (Or.inl h)
      · obtain rfl : m' = m := by omega
        exact Or.inr ⟨c, hc, hcb⟩

/-- The sources marked after `n` rounds. -/
def Hm (E : List (ℕ × ℕ)) (a : ℕ) : ℕ → ℕ → Prop
  | 0, _ => False
  | n + 1, u => u = a ∨ ∃ m, n = m + 1 ∧ u ∈ reachIter E a m

theorem Hm_succ_iff {E : List (ℕ × ℕ)} {a : ℕ} (n u : ℕ) :
    Hm E a (n + 1) u ↔ u = a ∨ ∃ p ∈ E, Hm E a n p.1 ∧ p.2 = u := by
  cases n with
  | zero => simp [Hm]
  | succ m =>
    simp only [Hm, add_left_inj, exists_eq_left']
    rw [mem_reachIter_iff m]
    constructor
    · rintro (h | h | ⟨m', rfl, c, hc, hcb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(a, u), h, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨(c, u), hcb, Or.inr ⟨m', rfl, hc⟩, rfl⟩
    · rintro (h | ⟨p, hp, (h1 | ⟨m', rfl, h1⟩), rfl⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl (by rw [← h1]; exact hp))
      · exact Or.inr (Or.inr ⟨m', rfl, p.1, h1, hp⟩)

theorem bitAt_rStep {K x V e : List Bool} (he : e <:+ x) :
    bitAt (rStep K x V) x e = (edgePos x e &&
      (decide (srcD e = K) || x.tails.any fun e' => bitAt V x e' && decide (tgtD e' = srcD e))) :=
  bitAt_map_tails _ he

/-- **The invariant of the marking rounds.** -/
theorem bitAt_iterate_rStep (q : InstDesc) (a : ℕ) : ∀ (n : ℕ) {e : List Bool}, e <:+ instSer q →
    (bitAt ((rStep (key a) (instSer q))^[n] ((instSer q).tails.map fun _ => false))
      (instSer q) e = true ↔
      edgePos (instSer q) e = true ∧ ∃ u, srcD e = key u ∧ Hm q.tnI.ordList a n u)
  | 0, e, he => by
    simp only [Function.iterate_zero, id, bitAt_map_tails _ he, Hm]
    simp
  | n + 1, e, he => by
    rw [Function.iterate_succ_apply', bitAt_rStep he]
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_tails]
    refine and_congr_right fun hep => ?_
    obtain ⟨p0, hp0, hs0, -⟩ := edgePos_val hep
    have hex : (∃ e', e' <:+ instSer q ∧
        (bitAt ((rStep (key a) (instSer q))^[n] ((instSer q).tails.map fun _ => false))
          (instSer q) e' = true ∧ tgtD e' = srcD e)) ↔
        ∃ p ∈ q.tnI.ordList, Hm q.tnI.ordList a n p.1 ∧ p.2 = p0.1 := by
      have h1 : (∃ e', e' <:+ instSer q ∧
          (bitAt ((rStep (key a) (instSer q))^[n] ((instSer q).tails.map fun _ => false))
            (instSer q) e' = true ∧ tgtD e' = srcD e)) ↔
          ∃ e', e' <:+ instSer q ∧ edgePos (instSer q) e' = true ∧
            ((∃ u, srcD e' = key u ∧ Hm q.tnI.ordList a n u) ∧ tgtD e' = srcD e) := by
        refine exists_congr fun e' => ⟨fun ⟨hs, hb, ht⟩ => ?_, fun ⟨hs, hp, hu, ht⟩ => ?_⟩
        · obtain ⟨h1, h2⟩ := (bitAt_iterate_rStep q a n hs).1 hb
          exact ⟨hs, h1, h2, ht⟩
        · exact ⟨hs, (bitAt_iterate_rStep q a n hs).2 ⟨hp, hu⟩, ht⟩
      rw [h1, exists_edgePos_iff q (fun s t => (∃ u, s = key u ∧ Hm q.tnI.ordList a n u) ∧
        t = srcD e), hs0]
      refine exists_congr fun p => and_congr_right fun _ => ?_
      constructor
      · rintro ⟨⟨u, hu, hH⟩, ht⟩
        rw [key_injective hu]
        exact ⟨hH, key_injective ht⟩
      · rintro ⟨hH, ht⟩
        exact ⟨⟨p.1, rfl, hH⟩, by rw [ht]⟩
    rw [hex, hs0]
    constructor
    · rintro (h | h)
      · exact ⟨p0.1, rfl, (Hm_succ_iff n p0.1).2 (Or.inl (key_injective h))⟩
      · exact ⟨p0.1, rfl, (Hm_succ_iff n p0.1).2 (Or.inr h)⟩
    · rintro ⟨u, hu, hH⟩
      rw [← key_injective hu] at hH
      rcases (Hm_succ_iff n p0.1).1 hH with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr h

theorem length_instSer_ge (q : InstDesc) : q.tnI.ordList.length + 2 ≤ (instSer q).length := by
  have h1 : (zD q).length ≤ (instSer q).length := (zD_suffix q).length_le
  have h2 : (zD q).length = (blist (q.tnI.ordList.map serPair)).length + (zE q).length := by
    simp [zD]
  have h3 := length_blist (q.tnI.ordList.map serPair)
  have h4 : q.tnI.ordList.length ≤ ((q.tnI.ordList.map serPair).map
      fun x => 2 * x.length + 2).sum := by
    have : ∀ l : List (ℕ × ℕ), l.length ≤ ((l.map serPair).map fun x => 2 * x.length + 2).sum := by
      intro l
      induction l with
      | nil => simp
      | cons p l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
    exact this _
  have h5 : 1 ≤ (zE q).length := by
    simp only [zE]; rw [length_blist]; omega
  omega

/-- **Correctness of the order test.** -/
theorem preOrdB_iff (q : InstDesc) (a b : ℕ) :
    preOrdB (key a) (key b) (instSer q) = true ↔ q.tnI.preOrd a b := by
  obtain ⟨M, hM⟩ : ∃ M, (instSer q).length = M + 2 :=
    ⟨(instSer q).length - 2, by have := length_instSer_ge q; omega⟩
  have hME : q.tnI.ordList.length ≤ M := by have := length_instSer_ge q; omega
  simp only [preOrdB, reachV, List.any_eq_true, List.mem_tails, Bool.and_eq_true,
    decide_eq_true_eq]
  have h1 : (∃ e, e <:+ instSer q ∧
      (bitAt ((rStep (key a) (instSer q))^[(instSer q).length]
        ((instSer q).tails.map fun _ => false)) (instSer q) e = true ∧ tgtD e = key b)) ↔
      ∃ e, e <:+ instSer q ∧ edgePos (instSer q) e = true ∧
        ((∃ u, srcD e = key u ∧ Hm q.tnI.ordList a (instSer q).length u) ∧ tgtD e = key b) := by
    refine exists_congr fun e => ⟨fun ⟨hs, hb, ht⟩ => ?_, fun ⟨hs, hp, hu, ht⟩ => ?_⟩
    · obtain ⟨h1, h2⟩ := (bitAt_iterate_rStep q a _ hs).1 hb
      exact ⟨hs, h1, h2, ht⟩
    · exact ⟨hs, (bitAt_iterate_rStep q a _ hs).2 ⟨hp, hu⟩, ht⟩
  rw [h1, exists_edgePos_iff q (fun s t => (∃ u, s = key u ∧
    Hm q.tnI.ordList a (instSer q).length u) ∧ t = key b), hM]
  have h2 : (∃ p ∈ q.tnI.ordList, (∃ u, key p.1 = key u ∧ Hm q.tnI.ordList a (M + 2) u) ∧
      key p.2 = key b) ↔ b ∈ reachIter q.tnI.ordList a (M + 1) := by
    rw [mem_reachIter_iff (M + 1)]
    constructor
    · rintro ⟨p, hp, ⟨u, hu, hH⟩, hb⟩
      rw [← key_injective hu] at hH
      rw [← key_injective hb]
      rcases hH with h | ⟨m, hm, h⟩
      · left; rw [← h]; exact hp
      · rw [show m = M by omega] at h
        exact Or.inr ⟨M, rfl, p.1, h, hp⟩
    · rintro (h | ⟨m, hm, c, hc, hcb⟩)
      · exact ⟨(a, b), h, ⟨a, rfl, Or.inl rfl⟩, rfl⟩
      · rw [show m = M by omega] at hc
        exact ⟨(c, b), hcb, ⟨c, rfl, Or.inr ⟨M, rfl, hc⟩⟩, rfl⟩
  rw [h2]
  constructor
  · exact transGen_of_mem_reachIter _
  · intro h
    have := reachB_iff.2 h
    rw [reachB, memB_iff, reachList] at this
    exact reachIter_mono (by omega) this

/-! ### Cobham's class -/

theorem cobham_rStep {K x V : Fn} (hK : Cobham K) (hx : Cobham x) (hV : Cobham V) :
    Cobham fun args => rStep (K args) (x args) (V args) := by
  unfold rStep
  refine cobham_mapTailsF (P := fun args e => edgePos (x args) e && (decide (srcD e = K args) ||
    (x args).tails.any fun e' => bitAt (V args) (x args) e' && decide (tgtD e' = srcD e))) ?_ hx
  refine (cobhamB_edgePos (cobham_tailArgs hx) cobham_var0).and
    ((cobhamB_eqStr (cobham_srcD cobham_var0) (cobham_tailArgs hK)).or ?_)
  refine cobhamB_anyTailsF (P := fun a e' => bitAt (V a.tail) (x a.tail) e' &&
    decide (tgtD e' = srcD (a.getD 0 []))) ?_ (cobham_tailArgs hx)
  exact (cobhamB_bitAt (cobham_tailArgs (cobham_tailArgs hV))
    (cobham_tailArgs (cobham_tailArgs hx)) cobham_var0).and
    (cobhamB_eqStr (cobham_tgtD cobham_var0) (cobham_srcD (cobham_tailArgs cobham_var0)))

theorem length_rStep (K x V : List Bool) : (rStep K x V).length = x.length + 1 := by
  simp [rStep]

theorem cobham_reachV {K x : Fn} (hK : Cobham K) (hx : Cobham x) :
    Cobham fun args => reachV (K args) (x args) := by
  have hinit : Cobham fun args => (x args).tails.map fun _ => false :=
    cobham_mapTailsF (P := fun _ _ => false) (cobhamB_const false) hx
  have hbd : Cobham fun args => (x args).tails.map fun _ => true :=
    cobham_mapTailsF (P := fun _ _ => true) (cobhamB_const true) hx
  have hstep : Cobham fun a => rStep (K a.tail) (x a.tail) (a.getD 0 []) :=
    cobham_rStep (cobham_tailArgs hK) (cobham_tailArgs hx) cobham_var0
  refine (cobham_iterateC hinit hstep hx hbd (fun args => by simp)
    (fun c args => by simp [length_rStep])).of_eq' fun args => ?_
  simp [reachV]

theorem cobhamB_preOrdB {K K' x : Fn} (hK : Cobham K) (hK' : Cobham K') (hx : Cobham x) :
    CobhamB fun args => preOrdB (K args) (K' args) (x args) := by
  unfold preOrdB
  refine cobhamB_anyTailsF (P := fun args e => bitAt (reachV (K args) (x args)) (x args) e &&
    decide (tgtD e = K' args)) ?_ hx
  exact (cobhamB_bitAt (cobham_reachV (cobham_tailArgs hK) (cobham_tailArgs hx))
    (cobham_tailArgs hx) cobham_var0).and
    (cobhamB_eqStr (cobham_tgtD cobham_var0) (cobham_tailArgs hK'))

end TOPlan

end Syn

end HTN
