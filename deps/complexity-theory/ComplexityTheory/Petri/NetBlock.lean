import ComplexityTheory.Petri.Exists
import ComplexityTheory.HDDecide.Petri
/-!
# Petri net reachability as a generalised problem with one block

For a Petri net `N` over places `< d` and markings `m₀, m₁`, the block `netBlock d N m₀ m₁` over
the coordinates `Fin d` has a central node `0` and, for the `i`-th transition `t`, a node `i + 1`
with the edges `0 →(−pre t) i+1 →(+post t) 0`; all labels are `ω`, the input is `m₀` and the
output is `m₁`.  Then (`HTN.Petri.KLM.reach_iff_solvable`)

    Petri.Reach N m₀ m₁ ↔ Solvable [netBlock d N m₀ m₁],

and the block satisfies the invariant `Inv` of the existence theorem for refutations
(`HTN.Petri.KLM.inv_netBlock`).
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

/-- The vector of a marking. -/
def mv (d : ℕ) (m : Multiset ℕ) : Fin d → ℤ := fun j => (m.count (j : ℕ) : ℤ)

/-- The edges of the net block. -/
def netEdges (d : ℕ) (N : List (Trans ℕ)) : List (Edge (Fin d)) :=
  N.zipIdx.flatMap fun p => [(0, -mv d p.1.1, p.2 + 1), (p.2 + 1, mv d p.1.2, 0)]

/-- **The block of a Petri net reachability question.** -/
def netBlock (d : ℕ) (N : List (Trans ℕ)) (m₀ m₁ : Multiset ℕ) : Block (Fin d) :=
  ⟨0, fun j => (m₀.count (j : ℕ) : ℕ∞),
    ⟨List.range (N.length + 1), fun _ _ => ⊤, netEdges d N, 0, 0⟩,
    fun j => (m₁.count (j : ℕ) : ℕ∞)⟩

/-- All places of a marking are `< d`. -/
def PB (d : ℕ) (m : Multiset ℕ) : Prop := ∀ p ∈ m, p < d

/-- All places of a net are `< d`. -/
def NB (d : ℕ) (N : List (Trans ℕ)) : Prop :=
  ∀ t ∈ N, PB d (t.1 : Multiset ℕ) ∧ PB d (t.2 : Multiset ℕ)

variable {d : ℕ} {N : List (Trans ℕ)}

theorem mv_inj {m m' : Multiset ℕ} (h : PB d m) (h' : PB d m') (he : mv d m = mv d m') :
    m = m' := by
  ext p
  by_cases hp : p < d
  · have := congrFun he ⟨p, hp⟩
    simp only [mv] at this
    exact_mod_cast this
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hp (h p hm),
      Multiset.count_eq_zero_of_notMem fun hm => hp (h' p hm)]

theorem mv_add (m m' : Multiset ℕ) : mv d (m + m') = mv d m + mv d m' := by
  funext j; simp [mv]

theorem mv_sub {m m' : Multiset ℕ} (h : m' ≤ m) : mv d (m - m') = mv d m - mv d m' := by
  funext j
  simp only [mv, Multiset.count_sub, Pi.sub_apply]
  have := Multiset.count_le_of_le (j : ℕ) h
  omega

theorem mv_nonneg (m : Multiset ℕ) (j : Fin d) : 0 ≤ mv d m j := by simp [mv]

theorem PB.add {m m' : Multiset ℕ} (h : PB d m) (h' : PB d m') : PB d (m + m') := by
  intro p hp
  rcases Multiset.mem_add.1 hp with hp | hp
  · exact h p hp
  · exact h' p hp

theorem PB.sub {m : Multiset ℕ} (h : PB d m) (m' : Multiset ℕ) : PB d (m - m') :=
  fun p hp => h p (Multiset.mem_of_le (Multiset.sub_le_self _ _) hp)

/-- The multiset of a non-negative vector. -/
def vm (x : Fin d → ℤ) : Multiset ℕ := ∑ j : Fin d, Multiset.replicate (x j).toNat (j : ℕ)

theorem count_vm (x : Fin d → ℤ) (j : Fin d) : (vm x).count (j : ℕ) = (x j).toNat := by
  unfold vm
  rw [Multiset.count_sum', Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Multiset.count_replicate, if_neg]
    intro h
    exact hij (Fin.ext h)
  · simp

theorem PB_vm (x : Fin d → ℤ) : PB d (vm x) := by
  intro p hp
  unfold vm at hp
  obtain ⟨j, -, hj⟩ := Multiset.mem_sum.1 hp
  rw [Multiset.eq_of_mem_replicate hj]
  exact j.2

theorem mv_vm {x : Fin d → ℤ} (hx : ∀ j, 0 ≤ x j) : mv d (vm x) = x := by
  funext j
  simp only [mv, count_vm]
  exact Int.toNat_of_nonneg (hx j)

theorem le_of_mv {m t : Multiset ℕ} (ht : PB d t) (h : ∀ j, 0 ≤ (mv d m - mv d t) j) : t ≤ m := by
  rw [Multiset.le_iff_count]
  intro p
  by_cases hp : p < d
  · have := h ⟨p, hp⟩
    simp only [mv, Pi.sub_apply] at this
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hp (ht p hm)]
    exact Nat.zero_le _

/-! ### The edges -/

theorem mem_netEdges {e : Edge (Fin d)} :
    e ∈ netEdges d N ↔ ∃ i, ∃ h : i < N.length,
      e = (0, -mv d (N[i].1 : Multiset ℕ), i + 1) ∨ e = (i + 1, mv d (N[i].2 : Multiset ℕ), 0) := by
  unfold netEdges
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    rw [List.length_zipIdx] at hi
    refine ⟨i, hi, ?_⟩
    simpa [List.getElem_zipIdx] using he
  · rintro ⟨i, hi, he⟩
    refine ⟨(N[i], i), ?_, by simpa using he⟩
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp [List.getElem_zipIdx]⟩

/-! ### Reachability gives a run -/

theorem walk_of_reach {m m' : Multiset ℕ} (h : Petri.Reach N m m') :
    ∃ es, TWalk (netEdges d N) 0 es 0 ∧ TFires (fun _ => True) (mv d m) es ∧
      mv d m' = mv d m + teff es := by
  induction h with
  | refl => exact ⟨[], TWalk.nil _, fun j _ => mv_nonneg _ j, by simp⟩
  | @tail m₂ m₃ _ hf ih =>
    obtain ⟨es, hw, hfi, he⟩ := ih
    obtain ⟨t, ht, hle, rfl⟩ := hf
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ht
    let e₁ : Edge (Fin d) := (0, -mv d (N[i].1 : Multiset ℕ), i + 1)
    let e₂ : Edge (Fin d) := (i + 1, mv d (N[i].2 : Multiset ℕ), 0)
    have h₁ : e₁ ∈ netEdges d N := mem_netEdges.2 ⟨i, hi, Or.inl rfl⟩
    have h₂ : e₂ ∈ netEdges d N := mem_netEdges.2 ⟨i, hi, Or.inr rfl⟩
    refine ⟨es ++ [e₁, e₂], hw.append (TWalk.cons h₁ (TWalk.cons h₂ (TWalk.nil _))), ?_, ?_⟩
    · rw [tfires_append, ← he]
      refine ⟨hfi, fun j _ => mv_nonneg _ j, ?_, fun j _ => ?_⟩
      · refine fun j _ => ?_
        rw [← sub_eq_add_neg, ← mv_sub hle]
        exact mv_nonneg _ j
      · show 0 ≤ (mv d m₂ + -mv d (N[i].1 : Multiset ℕ) + mv d (N[i].2 : Multiset ℕ)) j
        rw [← sub_eq_add_neg, ← mv_sub hle, ← mv_add]
        exact mv_nonneg _ j
    · rw [teff_append, ← add_assoc, ← he, mv_add, mv_sub hle]
      simp [e₁, e₂, teff]
      abel

/-! ### A run gives reachability -/

theorem out_of_zero {e : Edge (Fin d)} (he : e ∈ netEdges d N) (h0 : e.1 = 0) :
    ∃ i, ∃ hi : i < N.length, e = (0, -mv d (N[i].1 : Multiset ℕ), i + 1) := by
  obtain ⟨i, hi, he | he⟩ := mem_netEdges.1 he
  · exact ⟨i, hi, he⟩
  · rw [he] at h0; simp at h0

theorem out_of_succ {e : Edge (Fin d)} (he : e ∈ netEdges d N) {i : ℕ} (h0 : e.1 = i + 1)
    (hi : i < N.length) : e = (i + 1, mv d (N[i].2 : Multiset ℕ), 0) := by
  obtain ⟨i', hi', he' | he'⟩ := mem_netEdges.1 he
  · rw [he'] at h0; simp at h0
  · rw [he'] at h0 ⊢
    simp only at h0
    have : i' = i := by omega
    subst this
    rfl

theorem reach_of_walk (hN : NB d N) : ∀ (n : ℕ) (es : List (Edge (Fin d))), es.length = n →
    ∀ m, PB d m → TWalk (netEdges d N) 0 es 0 → TFires (fun _ => True) (mv d m) es →
      ∃ m', PB d m' ∧ Petri.Reach N m m' ∧ mv d m' = mv d m + teff es := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro es hn m hm hw hf
    match es, hw, hf with
    | [], _, _ => exact ⟨m, hm, Relation.ReflTransGen.refl, by simp⟩
    | [e₁], hw, _ =>
      obtain ⟨h01, he₁, hw'⟩ := hw.cons_inv
      obtain ⟨i, hi, rfl⟩ := out_of_zero he₁ h01.symm
      have := hw'.nil_inv
      simp at this
    | e₁ :: e₂ :: es'', hw, hf =>
      obtain ⟨h01, he₁, hw'⟩ := hw.cons_inv
      obtain ⟨i, hi, rfl⟩ := out_of_zero he₁ h01.symm
      obtain ⟨h02, he₂, hw''⟩ := hw'.cons_inv
      have := out_of_succ he₂ h02.symm hi
      subst this
      obtain ⟨-, hf1, hf2⟩ := hf
      have hle : (N[i].1 : Multiset ℕ) ≤ m :=
        le_of_mv (hN _ (List.getElem_mem hi)).1 fun j => by
          have := hf1 j trivial
          simpa [sub_eq_add_neg] using this
      let m₂ := m - (N[i].1 : Multiset ℕ) + (N[i].2 : Multiset ℕ)
      have hm₂ : PB d m₂ := (hm.sub _).add (hN _ (List.getElem_mem hi)).2
      have hv : mv d m₂ = mv d m + -mv d (N[i].1 : Multiset ℕ) + mv d (N[i].2 : Multiset ℕ) := by
        simp only [m₂, mv_add, mv_sub hle]; abel
      have hf2' : TFires (fun _ => True) (mv d m₂) es'' := by rw [hv]; exact hf2
      obtain ⟨m', hm', hr, he'⟩ := ih es''.length (by simp at hn; omega) es'' rfl m₂ hm₂ hw'' hf2'
      refine ⟨m', hm', Relation.ReflTransGen.head ⟨N[i], List.getElem_mem hi, hle, rfl⟩ hr, ?_⟩
      rw [he', hv]
      simp only [teff_cons]
      abel

/-! ### The equivalence -/

theorem agree_count {m : Multiset ℕ} {x : Fin d → ℤ} :
    Agree x (fun j => (m.count (j : ℕ) : ℕ∞)) ↔ x = mv d m := by
  constructor
  · intro h
    funext j
    have := h j (by simp)
    simpa [mv] using this
  · rintro rfl j _
    simp [mv]

theorem tlab_top (C : Comp (Fin d)) (hC : C.lab = fun _ _ => ⊤) (S : Fin d → Prop) (u : ℕ)
    (x : Fin d → ℤ) (es : List (Edge (Fin d))) : TLab C S u x es := by
  induction es generalizing u x with
  | nil => intro j _ h; simp [hC] at h
  | cons e es ih => exact ⟨fun j _ h => by simp [hC] at h, ih _ _⟩

/-- **Reachability is solvability of the net block.** -/
theorem reach_iff_solvable (hN : NB d N) {m₀ m₁ : Multiset ℕ} (h₀ : PB d m₀) (h₁ : PB d m₁) :
    Petri.Reach N m₀ m₁ ↔ Solvable [netBlock d N m₀ m₁] := by
  constructor
  · intro h
    obtain ⟨es, hw, hf, he⟩ := walk_of_reach h
    refine ⟨mv d m₀, mv d m₁, mv d m₁, ⟨?_, es, hw, ?_, ?_, ?_, ?_⟩, rfl⟩
    · simp only [netBlock, add_zero]; exact agree_count.2 rfl
    · simpa [netBlock] using hf
    · exact tlab_top _ rfl _ _ _ _
    · simpa [netBlock] using he
    · exact agree_count.2 rfl
  · rintro ⟨M, M', M₂, ⟨hA, es, hw, hf, -, he, hA'⟩, rfl⟩
    simp only [netBlock, add_zero] at hA hw hf he hA'
    rw [agree_count] at hA hA'
    subst hA
    obtain ⟨m', hm', hr, he'⟩ := reach_of_walk hN _ es rfl m₀ h₀ hw hf
    have : m' = m₁ := mv_inj hm' h₁ (by rw [he', ← he, hA'])
    rwa [this] at hr

theorem nodup_flat : ∀ (N : List (Trans ℕ)) (k : ℕ),
    ((N.zipIdx k).flatMap fun p => [((0 : ℕ), -mv d p.1.1, p.2 + 1), (p.2 + 1, mv d p.1.2, 0)]).Nodup ∧
    ∀ e ∈ (N.zipIdx k).flatMap (fun p => [((0 : ℕ), -mv d p.1.1, p.2 + 1), (p.2 + 1, mv d p.1.2, 0)]),
      k + 1 ≤ e.1 + e.2.2
  | [], _ => by simp
  | t :: N, k => by
    obtain ⟨ih1, ih2⟩ := nodup_flat N (k + 1)
    rw [List.zipIdx_cons, List.flatMap_cons]
    refine ⟨List.nodup_append.2 ⟨?_, ih1, ?_⟩, ?_⟩
    · simp
    · intro a ha b hb hab
      subst hab
      have := ih2 a hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> simp at this
    · intro e he
      rcases List.mem_append.1 he with he | he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp
      · have := ih2 e he; omega

/-- The net block satisfies the invariant of the existence theorem. -/
theorem inv_netBlock (N : List (Trans ℕ)) (m₀ m₁ : Multiset ℕ) : Inv (netBlock d N m₀ m₁) := by
  refine ⟨⟨wf_iff.2 ⟨fun e he => ?_, ?_, ?_⟩, Or.inl (labOK_iff.2 fun e _ j h => ?_),
    fun j h => ?_, fun j h => ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl | rfl⟩ := mem_netEdges.1 he <;>
      simp [netBlock, List.mem_range] <;> omega
  · simp [netBlock]
  · simp [netBlock]
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact (nodup_flat N 0).1

/-- **Non-reachability is refutability of the net block.** -/
theorem not_reach_iff_refutable (hN : NB d N) {m₀ m₁ : Multiset ℕ} (h₀ : PB d m₀)
    (h₁ : PB d m₁) : ¬ Petri.Reach N m₀ m₁ ↔ Refutable [netBlock d N m₀ m₁] := by
  rw [reach_iff_solvable hN h₀ h₁]
  exact not_solvable_iff_refutable _ (by simp [inv_netBlock])

end KLM

end Petri

end HTN
