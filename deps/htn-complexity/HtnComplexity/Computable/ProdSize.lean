import HtnComplexity.Computable.ProdDom
/-!
# The size of the product construction

For each fixed bound `k` on the length of the initial chain the product domain of
`HtnComplexity/Computable/ProdDom.lean` is only polynomially larger than the source domain:
it has one method per pair of a source method and a remaining chain of at most `k - 1` compound
names, and there are at most `k · (|d| + 1)^(k-1)` such chains.

* `HTN.Syn.size_prodBody_le` — a copied body is at most twice the source body;
* `HTN.Syn.size_prodDom_le` — the compiled domain is of size `O(|d|^{k+2})`;
* `HTN.Syn.size_prodInst_le` — the compiled instance is of size `|q| + 2`.
-/

namespace HTN

namespace Syn

theorem size_prodBody_le (t : TnDesc) (w : List ℕ) : (prodBody t w).size ≤ 2 * t.size + 2 := by
  have hids : t.ids.length ≤ t.size := by simp [TnDesc.size]; omega
  rcases hnext : TnDesc.hasNextB t with _ | _
  · rcases w with _ | ⟨u, w⟩
    · rw [prodBody_of_nil hnext]
      omega
    · rw [prodBody_of_cons hnext]
      have h : (t.appendTask (chainName (u :: w))).size = t.size + t.ids.length + 2 := by
        simp only [TnDesc.size, TnDesc.appendTask_ids, TnDesc.appendTask_ordList,
          TnDesc.appendTask_lbl, List.length_append, List.length_map, List.length_cons,
          List.length_nil]
        omega
      omega
  · rw [prodBody_of_hasNext hnext]
    have h : (t.setTail (chainName (TnDesc.nextName t :: w))).size = t.size := by
      simp only [TnDesc.size, TnDesc.setTail_ids, TnDesc.setTail_ordList,
        TnDesc.setTail_lbl, List.length_map]
    omega

theorem size_prodInst_le (q : InstDesc) : (prodInst q).size ≤ q.size + 2 := by
  have h : (prodInst q).size = q.initList.length + q.goalList.length + 2 := rfl
  rw [h, InstDesc.size]
  omega

/-- Every method of the product domain is at most twice as large as the source domain. -/
theorem size_mem_prodMethods_le {k : ℕ} {d : DomDesc} {x : ℕ}
    (hx : x ∈ (prodMethods k d).map MethodDesc.size) : x ≤ 2 * d.size + 3 := by
  rw [List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  rcases mem_prodMethods_iff.1 hp with rfl | ⟨e₀, he₀, w, -, rfl⟩
  · show 1 + TnDesc.size TnDesc.nil ≤ 2 * d.size + 3
    simp only [TnDesc.size, TnDesc.nil, TnDesc.ids, TnDesc.ordList, TnDesc.lbl,
      List.length_nil]
    omega
  · have hle : e₀.2.size ≤ d.size := by
      have h1 : MethodDesc.size e₀ ≤ (d.methods.map MethodDesc.size).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem he₀)
      have h2 : (d.methods.map MethodDesc.size).sum ≤ d.size := by
        rw [DomDesc.size]; omega
      have : MethodDesc.size e₀ = 1 + e₀.2.size := rfl
      omega
    have h := size_prodBody_le e₀.2 w
    show 1 + (prodBody e₀.2 w).size ≤ 2 * d.size + 3
    omega

/-- The number of methods of the product domain. -/
theorem length_prodMethods_le (k : ℕ) (d : DomDesc) :
    (prodMethods k d).length ≤ 1 + d.size * ((k + 1) * (d.size + 1) ^ k) := by
  have hN : (tuplesLe (k - 1) d.heads).length ≤ (k + 1) * (d.size + 1) ^ k := by
    have h1 := length_tuplesLe (k - 1) d.heads
    have h2 : d.heads.length ≤ d.size := by
      rw [DomDesc.heads, List.length_map]
      exact methods_length_le_size d
    have h3 : (d.heads.length + 1) ^ (k - 1) ≤ (d.size + 1) ^ k :=
      le_trans (Nat.pow_le_pow_left (by omega) (k - 1))
        (Nat.pow_le_pow_right (by omega) (by omega))
    calc (tuplesLe (k - 1) d.heads).length ≤ (k - 1 + 1) * (d.heads.length + 1) ^ (k - 1) := h1
      _ ≤ (k + 1) * (d.size + 1) ^ k :=
          Nat.mul_le_mul (by omega) h3
  have hflat : (d.methods.flatMap fun e => (tuplesLe (k - 1) d.heads).map fun w =>
      ((chainName (e.1 :: w), prodBody e.2 w) : MethodDesc)).length ≤
        d.methods.length * ((k + 1) * (d.size + 1) ^ k) :=
    length_flatMap_le _ _ _ fun _ _ => by rw [List.length_map]; exact hN
  have hm : d.methods.length ≤ d.size := methods_length_le_size d
  have : (prodMethods k d).length = 1 + (d.methods.flatMap fun e =>
      (tuplesLe (k - 1) d.heads).map fun w =>
        ((chainName (e.1 :: w), prodBody e.2 w) : MethodDesc)).length := by
    rw [prodMethods, List.length_cons]
    omega
  rw [this]
  have := Nat.mul_le_mul_right ((k + 1) * (d.size + 1) ^ k) hm
  omega

theorem size_prodDom_le (k : ℕ) (d : DomDesc) :
    (prodDom k d).size ≤
      d.size + (1 + d.size * ((k + 1) * (d.size + 1) ^ k)) * (2 * d.size + 3) := by
  have hsize : (prodDom k d).size =
      (d.actions.map ActionDesc.size).sum + ((prodMethods k d).map MethodDesc.size).sum := rfl
  have hact : (d.actions.map ActionDesc.size).sum ≤ d.size := by
    rw [DomDesc.size]; omega
  have hsum : ((prodMethods k d).map MethodDesc.size).sum ≤
      ((prodMethods k d).map MethodDesc.size).length • (2 * d.size + 3) :=
    List.sum_le_card_nsmul _ (2 * d.size + 3) fun _ hx => size_mem_prodMethods_le hx
  have hcard : ((prodMethods k d).map MethodDesc.size).length ≤
      1 + d.size * ((k + 1) * (d.size + 1) ^ k) := by
    rw [List.length_map]
    exact length_prodMethods_le k d
  have hmul : ((prodMethods k d).map MethodDesc.size).length * (2 * d.size + 3) ≤
      (1 + d.size * ((k + 1) * (d.size + 1) ^ k)) * (2 * d.size + 3) :=
    Nat.mul_le_mul_right _ hcard
  have hsmul : ((prodMethods k d).map MethodDesc.size).length • (2 * d.size + 3) =
      ((prodMethods k d).map MethodDesc.size).length * (2 * d.size + 3) := by
    simp [smul_eq_mul]
  rw [hsize]
  omega

/-- **The compiled domain is polynomially larger than the source domain.** -/
theorem size_prodDom_le_pow (k : ℕ) (d : DomDesc) :
    (prodDom k d).size ≤ (3 * k + 4) * (d.size + 1) ^ (k + 2) := by
  set S := d.size with hS
  have hpow1 : S + 1 ≤ (S + 1) ^ (k + 2) := by
    calc S + 1 = (S + 1) ^ 1 := (pow_one _).symm
      _ ≤ (S + 1) ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : 1 + S * ((k + 1) * (S + 1) ^ k) ≤ (k + 1) * (S + 1) ^ (k + 1) := by
    have h1 : (k + 1) * (S + 1) ^ (k + 1) = (k + 1) * (S + 1) ^ k * S + (k + 1) * (S + 1) ^ k := by
      rw [pow_succ]
      ring
    have h2 : 1 ≤ (k + 1) * (S + 1) ^ k :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    have h3 : S * ((k + 1) * (S + 1) ^ k) = (k + 1) * (S + 1) ^ k * S := by ring
    omega
  have hlast : (2 * S + 3) ≤ 3 * (S + 1) := by omega
  have hmul : (1 + S * ((k + 1) * (S + 1) ^ k)) * (2 * S + 3) ≤
      3 * (k + 1) * (S + 1) ^ (k + 2) := by
    calc (1 + S * ((k + 1) * (S + 1) ^ k)) * (2 * S + 3)
        ≤ ((k + 1) * (S + 1) ^ (k + 1)) * (3 * (S + 1)) := Nat.mul_le_mul hstep hlast
      _ = 3 * (k + 1) * ((S + 1) ^ (k + 1) * (S + 1)) := by ring
      _ = 3 * (k + 1) * (S + 1) ^ (k + 2) := by rw [← pow_succ]
  have h := size_prodDom_le k d
  have hSle : S ≤ (S + 1) ^ (k + 2) := by omega
  calc (prodDom k d).size ≤ S + (1 + S * ((k + 1) * (S + 1) ^ k)) * (2 * S + 3) := h
    _ ≤ (S + 1) ^ (k + 2) + 3 * (k + 1) * (S + 1) ^ (k + 2) := by omega
    _ = (3 * k + 4) * (S + 1) ^ (k + 2) := by ring

end Syn

end HTN
