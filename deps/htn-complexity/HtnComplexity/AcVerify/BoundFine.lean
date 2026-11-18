import HtnComplexity.AcVerify.CertSize
/-!
# Certificates of acyclic problems are linear in the number of initial tasks

`HTN.Syn.AcVer.length_witness_le` bounds the number of entries of a path witness by
`(|q| + |d| + 1) ^ (2 |d| + 2)`, a polynomial in `|q|` whose degree grows with the domain.  The
first step of a path is a task `(0, i)` of the initial network, and all later steps are method
steps (`Link` asks for a method index `≥ 1`).  Hence:

* `HTN.Syn.AcVer.length_witness_le_fine` — at most `|ids(tn_I)| · (|d| + 1) ^ (2 |d| + 1)`
  entries;
* `HTN.Syn.AcVer.length_certOf_le_fine` — the certificate has length at most
  `certBoundF |q| |d| B |ids(tn_I)|`;
* `HTN.Syn.AcVer.certBoundF_le` — that is at most
  `256 · (n_I + 1) · (|q| + 1) · (B + 1) · (|d| + 1) ^ (2 |d| + 2)`:
  for a fixed domain, quadratic in the instance (`B` bounds the bit length of the names).

This is the fixed-exponent form needed by fine-grained arguments (`PROOFIDEAS.md`, 8d).
-/

namespace HTN

namespace Syn

namespace AcVer

open Classical

variable {d : DomDesc} {q : InstDesc}

/-- The method steps: the steps `(k, j)` of the listed methods, `j = 0` included. -/
def mSteps (d : DomDesc) : List PStep :=
  (mIdx d).flatMap fun k => (0 :: (methodAt d k).2.ids).map fun j => (k, j)

theorem allSteps_eq : allSteps d q = q.tnI.ids.map (fun i => (0, i)) ++ mSteps d := rfl

theorem length_mSteps_le (d : DomDesc) : (mSteps d).length ≤ d.size := by
  simp only [mSteps, List.length_flatMap, List.length_map, List.length_cons]
  have h1 : ((mIdx d).map fun k => (methodAt d k).2.ids.length + 1) =
      d.methods.map fun e => e.2.ids.length + 1 := by
    rw [← map_methodAt_mIdx d, List.map_map]; rfl
  have h2 : (d.methods.map fun e => e.2.ids.length + 1).sum ≤
      (d.methods.map MethodDesc.size).sum :=
    List.sum_le_sum fun e _ => by simp only [MethodDesc.size, TnDesc.size]; omega
  rw [h1]
  simp only [DomDesc.size]
  omega

theorem exists_pred_of_isChain {R : PStep → PStep → Prop} :
    ∀ {a : PStep} {l : List PStep}, (a :: l).IsChain R → ∀ z ∈ l, ∃ x, R x z
  | _, [], _, z, hz => by simp at hz
  | a, b :: l, h, z, hz => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨a, h.1⟩
    · exact exists_pred_of_isChain h.2 z hz

/-- **The later steps of an entry are method steps.** -/
theorem tail_mem_mSteps {u : Entry} (hu : EntryOK d q u)
    (h0 : u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) {i : ℕ} {s : List PStep}
    (hs : u.1 = (0, i) :: s) : ∀ z ∈ s, z ∈ mSteps d := by
  intro z hz
  have hc := isChain_of_entryOK hu
  rw [hs] at hc
  obtain ⟨x, hx⟩ := exists_pred_of_isChain hc z hz
  have hmem := mem_allSteps hu h0 z (by rw [hs]; exact List.mem_cons_of_mem _ hz)
  rw [allSteps_eq, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hmem
    exact absurd hx.1 (by simp)
  · exact hmem

/-- **A path witness of an acyclic problem has `O(|ids(tn_I)|)` entries for a fixed domain.** -/
theorem length_witness_le_fine (hd : d.IsAcyclic) {W : List Entry} (hW : PathOK d q W)
    (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    W.length ≤ q.tnI.ids.length * (d.size + 1) ^ (2 * d.size + 1) := by
  set S := (W.map (·.1)).toFinset
  set T := q.tnI.ids.toFinset ×ˢ listsUpTo (mSteps d).toFinset (2 * d.size + 1)
  let f : List PStep → ℕ × List PStep := fun l => ((l.headD (0, 0)).2, l.tail)
  have hshape : ∀ l ∈ S, ∃ u ∈ W, u.1 = l := by
    intro l hl
    exact List.mem_map.1 (List.mem_toFinset.1 hl)
  have hmaps : ∀ l ∈ S, f l ∈ T := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := hshape l hl
    have he := hW.entries u hu
    obtain ⟨i, s, hs⟩ := first_of_entryOK he
    have hlen := length_path_le hd he
    have hi : i ∈ q.tnI.ids := by
      have := mem_allSteps he (h0 u hu) (0, i) (by rw [hs]; exact List.mem_cons_self ..)
      rw [allSteps_eq, List.mem_append] at this
      rcases this with h | h
      · obtain ⟨j, hj, hji⟩ := List.mem_map.1 h
        simp only [Prod.mk.injEq, true_and] at hji
        exact hji ▸ hj
      · exfalso
        obtain ⟨k, hk, hk'⟩ := List.mem_flatMap.1 h
        obtain ⟨j, -, hj⟩ := List.mem_map.1 hk'
        simp only [Prod.mk.injEq] at hj
        exact mIdx_ne_zero hk hj.1
    simp only [f, hs, List.headD_cons, List.tail_cons, T, Finset.mem_product,
      List.mem_toFinset]
    refine ⟨hi, mem_listsUpTo ?_ fun z hz => List.mem_toFinset.2
      (tail_mem_mSteps he (h0 u hu) hs z hz)⟩
    rw [hs] at hlen
    simp only [List.length_cons] at hlen
    omega
  have hinj : Set.InjOn f S := by
    intro l₁ h₁ l₂ h₂ he
    obtain ⟨u₁, hu₁, rfl⟩ := hshape l₁ h₁
    obtain ⟨u₂, hu₂, rfl⟩ := hshape l₂ h₂
    obtain ⟨i₁, s₁, hs₁⟩ := first_of_entryOK (hW.entries u₁ hu₁)
    obtain ⟨i₂, s₂, hs₂⟩ := first_of_entryOK (hW.entries u₂ hu₂)
    simp only [f, hs₁, hs₂, List.headD_cons, List.tail_cons, Prod.mk.injEq] at he
    rw [hs₁, hs₂, he.1, he.2]
  have h1 := Finset.card_le_card_of_injOn f (fun l hl => hmaps l hl) hinj
  rw [List.toFinset_card_of_nodup hW.nodup_paths, List.length_map] at h1
  rw [Finset.card_product] at h1
  have h2 := card_listsUpTo_le (mSteps d).toFinset (2 * d.size + 1)
  have h3 : (mSteps d).toFinset.card ≤ d.size :=
    (List.toFinset_card_le _).trans (length_mSteps_le d)
  have h4 : q.tnI.ids.toFinset.card ≤ q.tnI.ids.length := List.toFinset_card_le _
  refine h1.trans (Nat.mul_le_mul h4 (h2.trans (Nat.pow_le_pow_left (by omega) _)))

/-- The refined bound on the certificate. -/
def certBoundF (sq sd B nI : ℕ) : ℕ :=
  1 + nI * (sd + 1) ^ (2 * sd + 1) * (2 * entBound sq sd B + 2)

/-- **The certificate of a path witness of an acyclic problem, refined.** -/
theorem length_certOf_le_fine (hd : d.IsAcyclic) {B : ℕ} (hB : NamesLt d q B) {W : List Entry}
    (hW : PathOK d q W) (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    (certOf d q W).length ≤ certBoundF q.size d.size B q.tnI.ids.length := by
  unfold certOf certBoundF
  refine (length_blist_le' (M := entBound q.size d.size B) fun s hs => ?_).trans ?_
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
    refine length_certL_le hd hB hW.entries h0 q.initList W (fun _ h => h) ?_ ?_ e he
    · intro x hx; simp [factPool, hx]
    · have : q.initList.length ≤ q.size := by simp only [InstDesc.size]; omega
      omega
  · rw [List.length_map, length_certL]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (length_witness_le_fine hd hW h0)) _

theorem entBound_le (sq sd B : ℕ) : entBound sq sd B ≤ 64 * (sq + 1) * (sd + 1) * (B + 1) := by
  unfold entBound
  nlinarith [Nat.zero_le (sq * sd * B), Nat.zero_le (sq * sd), Nat.zero_le (sq * B),
    Nat.zero_le (sd * B)]

/-- **The refined bound in product form**: for a fixed domain it is quadratic in the instance. -/
theorem certBoundF_le (sq sd B nI : ℕ) :
    certBoundF sq sd B nI ≤
      256 * (nI + 1) * (sq + 1) * (B + 1) * (sd + 1) ^ (2 * sd + 2) := by
  unfold certBoundF
  have he := entBound_le sq sd B
  have hp : (sd + 1) ^ (2 * sd + 2) = (sd + 1) ^ (2 * sd + 1) * (sd + 1) := pow_succ _ _
  rw [hp]
  set P := (sd + 1) ^ (2 * sd + 1)
  have hP : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 * entBound sq sd B + 2 ≤ 256 * (sq + 1) * (sd + 1) * (B + 1) := by
    nlinarith [Nat.zero_le (sq * sd * B), Nat.zero_le (sq * sd), Nat.zero_le (sq * B),
      Nat.zero_le (sd * B)]
  have h3 : nI * P * (2 * entBound sq sd B + 2) ≤
      nI * P * (256 * (sq + 1) * (sd + 1) * (B + 1)) := Nat.mul_le_mul_left _ h2
  have h4 : 1 ≤ 256 * (sq + 1) * (B + 1) * (P * (sd + 1)) := by
    have : 1 ≤ (sq + 1) * (B + 1) * (P * (sd + 1)) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  calc 1 + nI * P * (2 * entBound sq sd B + 2)
      ≤ 256 * (sq + 1) * (B + 1) * (P * (sd + 1)) +
          nI * (256 * (sq + 1) * (B + 1) * (P * (sd + 1))) := by
        have : nI * P * (256 * (sq + 1) * (sd + 1) * (B + 1)) =
            nI * (256 * (sq + 1) * (B + 1) * (P * (sd + 1))) := by ring
        omega
    _ = 256 * (nI + 1) * (sq + 1) * (B + 1) * (P * (sd + 1)) := by ring

end AcVer

end Syn

end HTN
