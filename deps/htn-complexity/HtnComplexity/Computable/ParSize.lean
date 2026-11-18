import HtnComplexity.Computable.ParDom
/-!
# The size of the parallel product construction

For each fixed bound `k` on the number of tasks of the initial task network the compiled domain
of `HtnComplexity/Computable/ParDom.lean` is only polynomially larger than the source
domain: it has one method per step of one process of a configuration, the configurations are the
tuples of at most `k` entries over a pool of at most `(|d| + 1)²` entries, and every body is of
constant size.

* `HTN.Syn.length_suffixesOf` — a list of length `n` has `n + 1` suffixes;
* `HTN.Syn.length_parEntries_le` — the pool of entries has at most `(|d| + 1)²` entries;
* `HTN.Syn.size_parDom_le_pow` — the compiled domain is of size `O(|d|^{2k+2})`;
* `HTN.Syn.size_parInst_le` — the compiled instance is of size `|q| + 2`.
-/

namespace HTN

namespace Syn

/-! ### The pool of entries -/

theorem length_suffixesOf {α : Type} (l : List α) : (suffixesOf l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [suffixesOf_cons, List.length_cons, ih, List.length_cons]

/-- Every method of a domain description is at most as large as the description. -/
theorem methodDesc_size_le {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    MethodDesc.size e ≤ d.size := by
  have h1 : MethodDesc.size e ≤ (d.methods.map MethodDesc.size).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem he)
  have h2 : (d.methods.map MethodDesc.size).sum ≤ d.size := by
    rw [DomDesc.size]; omega
  omega

/-- **The pool of entries is quadratic in the size of the source domain.** -/
theorem length_parEntries_le (d : DomDesc) : (parEntries d).length ≤ (d.size + 1) ^ 2 := by
  have hbody : ∀ e ∈ d.methods, (suffixesOf (TnDesc.seqBody e.2)).length ≤ d.size + 1 := by
    intro e he
    have hsize : MethodDesc.size e ≤ d.size := methodDesc_size_le he
    have hms : MethodDesc.size e = 1 + e.2.size := rfl
    have hids : e.2.ids.length ≤ e.2.size := by rw [TnDesc.size]; omega
    have hseq : (TnDesc.seqBody e.2).length ≤ e.2.ids.length + 1 :=
      TnDesc.length_seqBody_le e.2
    rw [length_suffixesOf]
    omega
  have hflat : (d.methods.flatMap fun e => suffixesOf (TnDesc.seqBody e.2)).length ≤
      d.methods.length * (d.size + 1) :=
    length_flatMap_le _ _ _ hbody
  have hheads : d.heads.length = d.methods.length := by rw [DomDesc.heads, List.length_map]
  have hm : d.methods.length ≤ d.size := methods_length_le_size d
  have hlen : (parEntries d).length =
      1 + d.heads.length + (d.methods.flatMap fun e => suffixesOf (TnDesc.seqBody e.2)).length := by
    rw [parEntries]
    simp [List.length_append]
    omega
  have hsq : (d.size + 1) ^ 2 = d.size * d.size + 2 * d.size + 1 := by ring
  have hmul : d.methods.length * (d.size + 1) ≤ d.size * (d.size + 1) :=
    Nat.mul_le_mul_right _ hm
  rw [hlen, hheads]
  have : d.size * (d.size + 1) = d.size * d.size + d.size := by ring
  omega

theorem length_parCfgs_le (k : ℕ) (d : DomDesc) :
    (parCfgs k d).length ≤ (k + 1) * ((d.size + 1) ^ 2 + 1) ^ k := by
  have h := length_parTuplesLe k (parEntries d)
  have hmono : ((parEntries d).length + 1) ^ k ≤ ((d.size + 1) ^ 2 + 1) ^ k :=
    Nat.pow_le_pow_left (by have := length_parEntries_le d; omega) k
  calc (parCfgs k d).length ≤ (k + 1) * ((parEntries d).length + 1) ^ k := h
    _ ≤ (k + 1) * ((d.size + 1) ^ 2 + 1) ^ k := Nat.mul_le_mul_left _ hmono

/-! ### The number and the size of the methods -/

theorem length_parStepMethods_le (d : DomDesc) (L : ParCfg) (i : ℕ) :
    (parStepMethods d L i).length ≤ d.methods.length + 1 := by
  rw [parStepMethods]
  rcases L.getI i with _ | ⟨x, xs⟩
  · simp
  · rcases x with a | c
    · simp
    · have h := List.length_filter_le (fun e : MethodDesc => e.1 = c) d.methods
      simp only [List.length_map]
      omega

theorem length_parMethodsOf_le (d : DomDesc) (L : ParCfg) :
    (parMethodsOf d L).length ≤ 1 + L.length * (d.methods.length + 1) := by
  have hflat : ((List.range L.length).flatMap (parStepMethods d L)).length ≤
      L.length * (d.methods.length + 1) := by
    have h := length_flatMap_le (List.range L.length) (parStepMethods d L)
      (d.methods.length + 1) fun i _ => length_parStepMethods_le d L i
    simpa using h
  rw [parMethodsOf, List.length_append]
  have hif : (if L.all (fun xs => xs.isEmpty) then [(parName L, TnDesc.nil)] else
      ([] : List MethodDesc)).length ≤ 1 := by
    by_cases h : L.all (fun xs => xs.isEmpty) = true <;> simp [h]
  omega

theorem length_parMethods_le (k : ℕ) (d : DomDesc) :
    (parMethods k d).length ≤ (parCfgs k d).length * (1 + k * (d.size + 1)) := by
  refine length_flatMap_le _ _ _ fun L hL => ?_
  have hlen : L.length ≤ k := (mem_parTuplesLe.1 hL).1
  have hm : d.methods.length ≤ d.size := methods_length_le_size d
  have h := length_parMethodsOf_le d L
  have hmul : L.length * (d.methods.length + 1) ≤ k * (d.size + 1) :=
    Nat.mul_le_mul hlen (by omega)
  omega

/-- Every method of the compiled domain is of constant size. -/
theorem size_mem_parMethods_le {k : ℕ} {d : DomDesc} {x : ℕ}
    (hx : x ∈ (parMethods k d).map MethodDesc.size) : x ≤ 6 := by
  rw [List.mem_map] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  obtain ⟨L, -, hmem⟩ := mem_parMethods_iff.1 hm
  rcases parMethodsOf_cases hmem with ⟨rfl, -⟩ | ⟨i, -, a, xs, -, rfl⟩ |
      ⟨i, -, c, xs, -, e, -, -, rfl⟩
  · show 1 + TnDesc.size TnDesc.nil ≤ 6
    simp [TnDesc.size, TnDesc.nil, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  · show 1 + TnDesc.size (parStepTn a (parName (L.set i xs))) ≤ 6
    simp [TnDesc.size, parStepTn, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  · show 1 + TnDesc.size (singleTn (parName (L.set i (TnDesc.seqBody e.2 ++ xs)))) ≤ 6
    simp [TnDesc.size, singleTn, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

/-! ### The two size bounds -/

theorem size_parInst_le (q : InstDesc) : (parInst q).size ≤ q.size + 2 := by
  have h : (parInst q).size = q.initList.length + q.goalList.length + 2 := rfl
  rw [h, InstDesc.size]
  omega

theorem size_parDom_le (k : ℕ) (d : DomDesc) :
    (parDom k d).size ≤ d.size + (parMethods k d).length * 6 := by
  have hsize : (parDom k d).size =
      (d.actions.map ActionDesc.size).sum + ((parMethods k d).map MethodDesc.size).sum := rfl
  have hact : (d.actions.map ActionDesc.size).sum ≤ d.size := by
    rw [DomDesc.size]; omega
  have hsum : ((parMethods k d).map MethodDesc.size).sum ≤
      ((parMethods k d).map MethodDesc.size).length • 6 :=
    List.sum_le_card_nsmul _ 6 fun _ hx => size_mem_parMethods_le hx
  have hsmul : ((parMethods k d).map MethodDesc.size).length • 6 =
      (parMethods k d).length * 6 := by simp [smul_eq_mul]
  rw [hsize]
  omega

/-- **The compiled domain is polynomially larger than the source domain.** -/
theorem size_parDom_le_pow (k : ℕ) (d : DomDesc) :
    (parDom k d).size ≤ (6 * (k + 1) ^ 2 * 2 ^ k + 1) * (d.size + 1) ^ (2 * k + 2) := by
  set S := d.size with hS
  -- the number of configurations
  have hcfg : (parCfgs k d).length ≤ (k + 1) * (2 ^ k * (S + 1) ^ (2 * k)) := by
    have h := length_parCfgs_le k d
    have hstep : ((S + 1) ^ 2 + 1) ^ k ≤ 2 ^ k * (S + 1) ^ (2 * k) := by
      have h1 : ((S + 1) ^ 2 + 1) ^ k ≤ (2 * (S + 1) ^ 2) ^ k := by
        refine Nat.pow_le_pow_left ?_ k
        have : 1 ≤ (S + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have h2 : (2 * (S + 1) ^ 2) ^ k = 2 ^ k * (S + 1) ^ (2 * k) := by
        rw [Nat.mul_pow, ← pow_mul, Nat.mul_comm 2 k]
      omega
    calc (parCfgs k d).length ≤ (k + 1) * ((S + 1) ^ 2 + 1) ^ k := h
      _ ≤ (k + 1) * (2 ^ k * (S + 1) ^ (2 * k)) := Nat.mul_le_mul_left _ hstep
  -- the number of methods
  have hmeth : (parMethods k d).length ≤ (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1) := by
    have h := length_parMethods_le k d
    have hfac : 1 + k * (S + 1) ≤ (k + 1) * (S + 1) := by
      have : 1 ≤ S + 1 := by omega
      nlinarith
    have hmul : (parCfgs k d).length * (1 + k * (S + 1)) ≤
        ((k + 1) * (2 ^ k * (S + 1) ^ (2 * k))) * ((k + 1) * (S + 1)) :=
      Nat.mul_le_mul hcfg hfac
    have heq : ((k + 1) * (2 ^ k * (S + 1) ^ (2 * k))) * ((k + 1) * (S + 1)) =
        (k + 1) ^ 2 * 2 ^ k * ((S + 1) ^ (2 * k) * (S + 1)) := by ring
    have hpow : (S + 1) ^ (2 * k) * (S + 1) = (S + 1) ^ (2 * k + 1) := (pow_succ _ _).symm
    calc (parMethods k d).length ≤ (parCfgs k d).length * (1 + k * (S + 1)) := h
      _ ≤ ((k + 1) * (2 ^ k * (S + 1) ^ (2 * k))) * ((k + 1) * (S + 1)) := hmul
      _ = (k + 1) ^ 2 * 2 ^ k * ((S + 1) ^ (2 * k) * (S + 1)) := heq
      _ = (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1) := by rw [hpow]
  -- assembling
  have hS1 : S ≤ (S + 1) ^ (2 * k + 2) := by
    have : S + 1 ≤ (S + 1) ^ (2 * k + 2) := Nat.le_self_pow (by omega) _
    omega
  have hup : (S + 1) ^ (2 * k + 1) ≤ (S + 1) ^ (2 * k + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hmeth' : (parMethods k d).length * 6 ≤
      6 * (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 2) := by
    have h1 : (parMethods k d).length * 6 ≤ ((k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1)) * 6 :=
      Nat.mul_le_mul_right _ hmeth
    have h2 : ((k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1)) * 6 =
        6 * (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1) := by ring
    have h3 : 6 * (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 1) ≤
        6 * (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 2) := Nat.mul_le_mul_left _ hup
    omega
  have h := size_parDom_le k d
  have hfinal : (6 * (k + 1) ^ 2 * 2 ^ k + 1) * (S + 1) ^ (2 * k + 2) =
      6 * (k + 1) ^ 2 * 2 ^ k * (S + 1) ^ (2 * k + 2) + (S + 1) ^ (2 * k + 2) := by ring
  omega

end Syn

end HTN
