import HtnComplexity.AcVerify.CertSize
import ComplexityTheory.TrVerify.Arith
/-!
# The length of the certificate of a path witness, without acyclicity

`HtnComplexity/AcVerify/CertSize.lean` bounds the certificate `certOf d q W` of a path witness
of an *acyclic* problem, where acyclicity bounds both the length of the paths and the number of
entries.  Here both are parameters: if every path has at most `m` steps and the witness has at
most `N` entries, the certificate has length at most `certBoundG q.size d.size B m N`
(`HTN.Syn.TrVer.length_certOf_le_of_bounds`).
-/

namespace HTN

namespace Syn

namespace TrVer

open PTime TOPlan PolyInst Compress Space Classical AcVer

variable {d : DomDesc} {q : InstDesc}

/-- **The content of an entry with a short path is short.** -/
theorem length_enc_ceOf_le_of_len {B m : ℕ} (hB : NamesLt d q B) {u : Entry}
    (hu : EntryOK d q u) (hm : u.1.length ≤ m)
    (h0 : u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) {L' : List ℕ}
    (hL : ∀ x ∈ L', x ∈ factPool d q) (hLl : L'.length ≤ q.size + d.size) :
    (ceOf d q u L').enc.length ≤ entBoundG q.size d.size B m := by
  rw [CE.enc_eq]
  simp only [List.length_append, List.length_singleton]
  have hrecs : (blist (ceOf d q u L').recs).length ≤ 1 + m * (2 * (8 * B + 4) + 2) := by
    refine (length_blist_le' (M := 8 * B + 4) fun s hs => ?_).trans ?_
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
      exact length_recOf_le hB (mem_allSteps hu h0 z hz)
    · simp only [ceOf, List.length_map]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hm) _
  have hst : (blist (ceOf d q u L').st).length ≤ 1 + (q.size + d.size) * (2 * B + 2) := by
    refine (length_blist_le' (M := B) fun s hs => ?_).trans ?_
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
      exact length_bitsOfNat_le_of_lt B x (factPool_lt hB x (hL x hx))
    · simp only [ceOf, List.length_map]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hLl) _
  have hrow : ∀ l : List ℕ, (l = (actLists d (leafAct d q u.1)).1 ∨
      l = (actLists d (leafAct d q u.1)).2.1 ∨ l = (actLists d (leafAct d q u.1)).2.2) →
      ∀ m : List (List Bool), m = (if u.2 then [] else l.map bitsOfNat) →
        (blist m).length ≤ 1 + d.size * (2 * B + 2) := by
    intro l hl m hm
    subst hm
    split_ifs
    · simp [blist]
    · exact length_actS_le hB hl
  have hpr := hrow _ (Or.inl rfl) (ceOf d q u L').pr rfl
  have had := hrow _ (Or.inr (Or.inl rfl)) (ceOf d q u L').ad rfl
  have hde := hrow _ (Or.inr (Or.inr rfl)) (ceOf d q u L').de rfl
  unfold entBoundG
  omega

theorem length_certL_le_of_len {B m : ℕ} (hB : NamesLt d q B) {W : List Entry}
    (hW : ∀ u ∈ W, EntryOK d q u) (hm : ∀ u ∈ W, u.1.length ≤ m)
    (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    ∀ (L : List ℕ) (W' : List Entry), (∀ u ∈ W', u ∈ W) → (∀ x ∈ L, x ∈ factPool d q) →
      L.length ≤ q.size + d.size →
      ∀ e ∈ certL d q L W', e.enc.length ≤ entBoundG q.size d.size B m
  | _, [], _, _, _ => by simp [certL]
  | L, u :: r, hsub, hL, hLl => by
    have hu := hsub u (by simp)
    have hnext : (∀ x ∈ nextL d q L u, x ∈ factPool d q) ∧
        (nextL d q L u).length ≤ q.size + d.size := by
      unfold nextL
      split_ifs
      · exact ⟨hL, hLl⟩
      · have := stepL_pool (a := leafAct d q u.1) hL
        exact ⟨this.1, this.2.trans (length_factPool_le d q)⟩
    intro e he
    simp only [certL, List.mem_cons] at he
    rcases he with rfl | he
    · exact length_enc_ceOf_le_of_len hB (hW u hu) (hm u hu) (h0 u hu) hnext.1 hnext.2
    · exact length_certL_le_of_len hB hW hm h0 _ r (fun v hv => hsub v (by simp [hv])) hnext.1
        hnext.2 e he

/-- **The certificate of a path witness with short paths and few entries is short.** -/
theorem length_certOf_le_of_bounds {B m N : ℕ} (hB : NamesLt d q B) {W : List Entry}
    (hW : PathOK d q W) (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)])
    (hm : ∀ u ∈ W, u.1.length ≤ m) (hN : W.length ≤ N) :
    (certOf d q W).length ≤ certBoundG q.size d.size B m N := by
  unfold certOf certBoundG
  refine (length_blist_le' (M := entBoundG q.size d.size B m) fun s hs => ?_).trans ?_
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
    refine length_certL_le_of_len hB hW.entries hm h0 q.initList W (fun _ h => h) ?_ ?_ e he
    · intro x hx; simp [factPool, hx]
    · have : q.initList.length ≤ q.size := by simp only [InstDesc.size]; omega
      omega
  · rw [List.length_map, length_certL]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hN) _

end TrVer

end Syn

end HTN
