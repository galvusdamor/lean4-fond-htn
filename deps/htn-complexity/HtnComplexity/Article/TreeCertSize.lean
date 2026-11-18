import HtnComplexity.Article.TreeCertComplete
import HtnComplexity.PT.Decode
import HtnComplexity.PT.NExp
/-!
# The size of tree certificates

`HTN.Article.sz_cert_le`: a certificate of `N` nodes for a plan of length `Y` produced by
`HTN.Article.exists_certB` has a code of length at most `64 M³`, `M = N + Y + |p| + 1`, where
`|p|` is the length of the code of the description.  The numbers taken from the description are
not longer than its code, and node indices are below `N`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst

theorem sum_map_sz_le {α : Type} [BEnc α] (l : List α) : (l.map sz).sum ≤ sz l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, sz_cons]; omega

theorem sz_list_le {α : Type} [BEnc α] {l : List α} {K : ℕ} (h : ∀ a ∈ l, sz a ≤ K) :
    sz l ≤ l.length * (2 * K + 2) + 1 := by
  induction l with
  | nil => simp [sz_nil]
  | cons a l ih =>
    rw [sz_cons, List.length_cons]
    have h1 := ih fun b hb => h b (by simp [hb])
    have h2 := h a (by simp)
    nlinarith

theorem lt_two_pow' (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem sz_nat_le_of_lt {n k : ℕ} (h : n < 2 ^ k) : sz n ≤ 2 * k + 1 := by
  rw [sz_nat]
  have := (length_bitsOfNat_le_iff k n).2 h
  omega

theorem sz_nat_le_of_lt' {n N : ℕ} (h : n < N) : sz n ≤ 2 * N + 1 :=
  sz_nat_le_of_lt (lt_trans h (lt_two_pow' N))

theorem sz_tnDesc (t : TnDesc) : sz t = sz t.ids + (sz t.ordList + sz t.lbl) := by
  show sz (t.1, t.2.1, t.2.2) = _
  rw [sz_prod, sz_prod]; rfl

theorem sz_le_of_mem_tnNums {t : TnDesc} {a : ℕ} (h : a ∈ tnNums t) : sz a ≤ sz t := by
  rw [sz_tnDesc]
  rcases List.mem_append.1 h with h | h
  · have := sz_le_of_mem h; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have h1 := sz_le_of_mem hq
    have h2 : sz q.2.2 ≤ sz q := by
      show sz q.2.2 ≤ sz (q.1, q.2.1, q.2.2)
      rw [sz_prod, sz_prod]; omega
    omega

theorem length_tnNums_le (t : TnDesc) : (tnNums t).length ≤ sz t := by
  rw [sz_tnDesc]
  unfold tnNums
  rw [List.length_append, List.length_map]
  have := length_le_sz t.ids
  have := length_le_sz t.lbl
  omega

theorem sz_probDesc (p : ProbDesc) :
    sz p = sz p.actions + sz p.methods + (sz p.init + (sz p.tnI + (sz p.goalPos + sz p.goalNeg))) := by
  show sz ((p.1.1, p.1.2), p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2) = _
  simp only [sz_prod]; rfl

theorem sz_methodDesc (m : MethodDesc) : sz m = sz m.1 + sz m.2 := by
  show sz (m.1, m.2) = _
  rw [sz_prod]

theorem sz_le_of_mem_numsOf {p : ProbDesc} {a : ℕ} (h : a ∈ numsOf p) : sz a ≤ sz p := by
  rw [sz_probDesc]
  rcases List.mem_append.1 h with h | h
  · have := sz_le_of_mem_tnNums h; omega
  · obtain ⟨m, hm, ha⟩ := List.mem_flatMap.1 h
    have h1 := sz_le_of_mem hm
    have h2 : sz a ≤ sz m := by
      rw [sz_methodDesc]
      rcases List.mem_cons.1 ha with rfl | ha
      · omega
      · have := sz_le_of_mem_tnNums ha; omega
    omega

theorem length_numsOf_le (p : ProbDesc) : (numsOf p).length ≤ sz p := by
  rw [sz_probDesc]
  unfold numsOf
  rw [List.length_append, List.length_flatMap]
  have h1 := length_tnNums_le p.tnI
  have h2 : (p.methods.map fun m => (m.1 :: tnNums m.2).length).sum ≤ (p.methods.map sz).sum := by
    apply List.sum_le_sum
    intro m _
    rw [List.length_cons, sz_methodDesc, sz_nat]
    have := length_tnNums_le m.2
    omega
  have h3 := sum_map_sz_le p.methods
  omega

theorem length_methods_le (p : ProbDesc) : p.methods.length ≤ sz p := by
  rw [sz_probDesc]
  have := length_le_sz p.methods
  omega

/-- The size of a node. -/
theorem sz_node_le {p : ProbDesc} {N Y : ℕ} {v : NodeC} (h : NodeNums p N Y v) :
    sz v ≤ 22 * (N + Y + sz p + 1) ^ 2 := by
  obtain ⟨⟨b, n⟩, mi, kids, ys, w⟩ := v
  obtain ⟨hn, hmi, hk, hkl, hys, hw, hysl, hwl⟩ := h
  simp only [NodeC.lbl, NodeC.mi, NodeC.kids, NodeC.ys, NodeC.w] at hn hmi hk hkl hys hw hysl hwl
  set S := sz p
  set M := N + Y + S + 1
  simp only [sz_prod, sz_bool]
  have e1 := sz_le_of_mem_numsOf hn
  have e2 : sz mi ≤ 2 * (S + 1) + 1 :=
    sz_nat_le_of_lt' (lt_of_lt_of_le hmi (by have := length_methods_le p; omega))
  have e3 : sz kids ≤ kids.length * (2 * (S + (2 * N + 1)) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hk q hq).1
    have := sz_nat_le_of_lt' (hk q hq).2
    omega
  have e4 : sz ys ≤ ys.length * (2 * S + 2) + 1 := sz_list_le fun a ha => sz_le_of_mem_numsOf (hys a ha)
  have e5 : sz w ≤ w.length * (2 * (S + S) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hw q hq).1
    have := sz_le_of_mem_numsOf (hw q hq).2
    omega
  have hkl' : kids.length ≤ S := le_trans hkl (length_numsOf_le p)
  have hMd : M = N + Y + S + 1 := rfl
  have f3 : kids.length * (2 * (S + (2 * N + 1)) + 2) ≤ 6 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (6 * M)).trans_eq (by ring)
  have f4 : ys.length * (2 * S + 2) ≤ 2 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (2 * M)).trans_eq (by ring)
  have f5 : w.length * (2 * (S + S) + 2) ≤ 4 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (4 * M)).trans_eq (by ring)
  have hM : 1 ≤ M := by omega
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hSM : S + 1 ≤ M := by omega
  linarith

/-- **The size of a tree certificate.** -/
theorem sz_cert_le {p : ProbDesc} {c : TCert} {Y : ℕ}
    (hnodes : ∀ v ∈ c.1, NodeNums p c.1.length Y v)
    (hroots : ∀ q ∈ c.2.1, q.1 ∈ numsOf p ∧ q.2 < c.1.length)
    (hrl : c.2.1.length ≤ (numsOf p).length) (hw : ∀ q ∈ c.2.2.2, q.1 ∈ numsOf p ∧ q.2 ∈ numsOf p)
    (hwl : c.2.2.2.length = Y) (hπl : c.2.2.1.length = Y) (hπ : ∀ a ∈ c.2.2.1, a ∈ numsOf p) :
    sz c ≤ 64 * (c.1.length + Y + sz p + 1) ^ 3 := by
  obtain ⟨nodes, roots, π, w⟩ := c
  simp only at hnodes hroots hrl hw hwl hπl hπ ⊢
  set S := sz p
  set N := nodes.length
  set M := N + Y + S + 1
  simp only [sz_prod]
  have e1 : sz nodes ≤ N * (2 * (22 * M ^ 2) + 2) + 1 := sz_list_le fun v hv => sz_node_le (hnodes v hv)
  have e2 : sz roots ≤ roots.length * (2 * (S + (2 * N + 1)) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hroots q hq).1
    have := sz_nat_le_of_lt' (hroots q hq).2
    omega
  have e3 : sz π ≤ π.length * (2 * S + 2) + 1 := sz_list_le fun a ha => sz_le_of_mem_numsOf (hπ a ha)
  have e4 : sz w ≤ w.length * (2 * (S + S) + 2) + 1 := sz_list_le fun q hq => by
    rw [sz_prod]
    have := sz_le_of_mem_numsOf (hw q hq).1
    have := sz_le_of_mem_numsOf (hw q hq).2
    omega
  have hrl' : roots.length ≤ S := le_trans hrl (length_numsOf_le p)
  have hMd : M = N + Y + S + 1 := rfl
  have hM : 1 ≤ M := by omega
  have hM2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM
  have f1 : N * (2 * (22 * M ^ 2) + 2) ≤ 46 * M ^ 3 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (46 * M ^ 2)).trans_eq (by ring)
  have f2 : roots.length * (2 * (S + (2 * N + 1)) + 2) ≤ 6 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (6 * M)).trans_eq (by ring)
  have f3 : π.length * (2 * S + 2) ≤ 2 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (2 * M)).trans_eq (by ring)
  have f4 : w.length * (2 * (S + S) + 2) ≤ 4 * M ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega) : _ ≤ M * (4 * M)).trans_eq (by ring)
  have hM3 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM (by norm_num)
  have hM3' : 1 ≤ M ^ 3 := Nat.one_le_pow _ _ hM
  linarith

end Article

end HTN
