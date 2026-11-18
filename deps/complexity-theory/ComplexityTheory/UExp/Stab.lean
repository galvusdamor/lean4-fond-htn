import ComplexityTheory.Complexity.PrimDiag.Diag
/-!
# Alternating acceptance stabilises

For an alternating machine `M` (`HTN.Space.AltSpace`) and fixed `x`, `a`:

* `AccN M x a d c` — acceptance by a game tree of depth at most `d`;
* **`HTN.UExp.acc_iff_accN`** — a bounded configuration (every component at most
  `M.bound (|x| + |a|)` long) accepts iff it accepts within depth `2 ^ (k (B + 1))`: the sets of
  bounded configurations accepted within depth `d` grow with `d`, stop growing as soon as they
  stop growing once, and there are at most `2 ^ (k (B + 1))` bounded configurations.
-/

namespace HTN

namespace UExp

open Space PrimDiag PTime

variable (M : AltSpace) (x a : List Bool)

open scoped Classical

/-- **Acceptance within depth `d`.** -/
def AccN : ℕ → Args → Prop
  | 0, c => c.length = M.k ∧ M.accB (x :: a :: c) = true
  | d + 1, c => c.length = M.k ∧ (M.accB (x :: a :: c) = true ∨
      (M.univB (x :: a :: c) = true ∧
        ∀ c', c'.length = M.k → M.stepB (x :: a :: (c' ++ c)) = true → AccN d c') ∨
      (M.univB (x :: a :: c) = false ∧
        ∃ c', c'.length = M.k ∧ M.stepB (x :: a :: (c' ++ c)) = true ∧ AccN d c'))

theorem accN_succ_of {d : ℕ} : ∀ {c : Args}, AccN M x a d c → AccN M x a (d + 1) c := by
  induction d with
  | zero => rintro c ⟨hl, hacc⟩; exact ⟨hl, Or.inl hacc⟩
  | succ d ih =>
    rintro c ⟨hl, h | ⟨hu, h⟩ | ⟨hu, c', h1, h2, h3⟩⟩
    · exact ⟨hl, Or.inl h⟩
    · exact ⟨hl, Or.inr (Or.inl ⟨hu, fun c' h1 h2 => ih (h c' h1 h2)⟩)⟩
    · exact ⟨hl, Or.inr (Or.inr ⟨hu, c', h1, h2, ih h3⟩)⟩

theorem accN_mono {d e : ℕ} (h : d ≤ e) {c : Args} (hc : AccN M x a d c) : AccN M x a e c := by
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le h
  induction f with
  | zero => exact hc
  | succ f ih => exact accN_succ_of M x a (ih (by omega))

theorem acc_of_accN : ∀ {d : ℕ} {c : Args}, AccN M x a d c → M.Acc x a c
  | 0, _, ⟨hl, hacc⟩ => AltSpace.Acc.acc hl hacc
  | _ + 1, _, ⟨hl, Or.inl h⟩ => AltSpace.Acc.acc hl h
  | _ + 1, _, ⟨hl, Or.inr (Or.inl ⟨hu, h⟩)⟩ =>
    AltSpace.Acc.univ hl hu fun c' h1 h2 => acc_of_accN (h c' h1 h2)
  | _ + 1, _, ⟨hl, Or.inr (Or.inr ⟨hu, _, h1, h2, h3⟩)⟩ =>
    AltSpace.Acc.ex hl hu h1 h2 (acc_of_accN h3)

/-! ### Bounded configurations -/

/-- The bound on the components. -/
def bnd : ℕ := M.bound.eval (x.length + a.length)

/-- All lists of length `k` with entries from `S`. -/
def listsOf {α : Type} (S : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => S.flatMap fun s => (listsOf S k).map (s :: ·)

theorem mem_listsOf {α : Type} {S : List α} : ∀ {k : ℕ} {l : List α},
    l ∈ listsOf S k ↔ l.length = k ∧ ∀ w ∈ l, w ∈ S
  | 0, l => by cases l <;> simp [listsOf]
  | k + 1, [] => by simp [listsOf]
  | k + 1, b :: l => by
    simp only [listsOf, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons,
      List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
    constructor
    · rintro ⟨s, hs, l', hl', rfl, rfl⟩
      exact ⟨(mem_listsOf.1 hl').1, hs, (mem_listsOf.1 hl').2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨b, h2, l, mem_listsOf.2 ⟨h1, h3⟩, rfl, rfl⟩

theorem length_listsOf {α : Type} (S : List α) : ∀ k, (listsOf S k).length = S.length ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [listsOf, List.length_flatMap, List.length_map, length_listsOf S k]
    rw [List.map_const', List.sum_replicate, smul_eq_mul, pow_succ]; ring

/-- A bounded configuration. -/
def Bd (c : Args) : Prop := c.length = M.k ∧ ∀ w ∈ c, w.length ≤ bnd M x a

/-- The finite set of bounded configurations. -/
noncomputable def bndSet : Finset Args := (listsOf (upTo (bnd M x a)) M.k).toFinset

theorem mem_bndSet {c : Args} : c ∈ bndSet M x a ↔ Bd M x a c := by
  simp [bndSet, mem_listsOf, Bd, mem_upTo]

theorem card_bndSet_le : (bndSet M x a).card ≤ 2 ^ (M.k * (bnd M x a + 1)) := by
  classical
  refine (List.toFinset_card_le _).trans ?_
  rw [length_listsOf]
  have h := length_upTo (bnd M x a)
  calc (upTo (bnd M x a)).length ^ M.k ≤ (2 ^ (bnd M x a + 1)) ^ M.k :=
        Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (M.k * (bnd M x a + 1)) := by rw [← pow_mul, mul_comm]

/-- Successors of configurations are bounded. -/
theorem bd_of_step {c c' : Args} (hc : c.length = M.k) (hc' : c'.length = M.k)
    (h : M.stepB (x :: a :: (c' ++ c)) = true) : Bd M x a c' :=
  ⟨hc', M.stepB_length x a c' c hc' hc h⟩

/-! ### Stabilisation -/

/-- The bounded configurations accepted within depth `d`. -/
noncomputable def accSet (d : ℕ) : Finset Args := (bndSet M x a).filter fun c => AccN M x a d c

theorem accSet_mono (d : ℕ) : accSet M x a d ⊆ accSet M x a (d + 1) := by
  intro c hc
  simp only [accSet, Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, accN_succ_of M x a hc.2⟩

theorem accSet_stable {d : ℕ} (h : accSet M x a d = accSet M x a (d + 1)) :
    accSet M x a (d + 1) = accSet M x a (d + 2) := by
  have key : ∀ c, Bd M x a c → (AccN M x a (d + 1) c ↔ AccN M x a d c) := fun c hc => by
    have := congrArg (fun S => c ∈ S) h
    simp only [accSet, Finset.mem_filter, (mem_bndSet M x a).2 hc, true_and] at this
    exact Iff.of_eq this.symm
  ext c
  simp only [accSet, Finset.mem_filter]
  refine and_congr_right fun hc => ?_
  have hb := (mem_bndSet M x a).1 hc
  constructor
  · exact accN_succ_of M x a
  · rintro ⟨hl, h | ⟨hu, h⟩ | ⟨hu, c', h1, h2, h3⟩⟩
    · exact ⟨hl, Or.inl h⟩
    · exact ⟨hl, Or.inr (Or.inl ⟨hu, fun c' h1 h2 =>
        (key c' (bd_of_step M x a hl h1 h2)).1 (h c' h1 h2)⟩)⟩
    · exact ⟨hl, Or.inr (Or.inr ⟨hu, c', h1, h2, (key c' (bd_of_step M x a hl h1 h2)).1 h3⟩)⟩

theorem accSet_card_le (d : ℕ) : (accSet M x a d).card ≤ (bndSet M x a).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem exists_stable : ∃ e ≤ (bndSet M x a).card, accSet M x a e = accSet M x a (e + 1) := by
  by_contra hne
  push_neg at hne
  have : ∀ d ≤ (bndSet M x a).card + 1, d ≤ (accSet M x a d).card := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := ih (by omega)
      have h2 := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨accSet_mono M x a d, hne d (by omega)⟩)
      omega
  have := this _ le_rfl
  have := accSet_card_le M x a ((bndSet M x a).card + 1)
  omega

theorem accSet_step_of_ge {e : ℕ} (h : accSet M x a e = accSet M x a (e + 1)) :
    ∀ f, accSet M x a (e + f) = accSet M x a (e + f + 1)
  | 0 => h
  | f + 1 => accSet_stable M x a (accSet_step_of_ge h f)

theorem accSet_eq_of_ge {e : ℕ} (h : accSet M x a e = accSet M x a (e + 1)) :
    ∀ f, accSet M x a (e + f) = accSet M x a e
  | 0 => rfl
  | f + 1 => by rw [← add_assoc, ← accSet_step_of_ge M x a h f, accSet_eq_of_ge h f]

/-- The depth after which nothing new is accepted. -/
noncomputable def depth : ℕ := (bndSet M x a).card

theorem accN_depth_succ {c : Args} (hc : Bd M x a c) (h : AccN M x a (depth M x a + 1) c) :
    AccN M x a (depth M x a) c := by
  obtain ⟨e, he, hst⟩ := exists_stable M x a
  obtain ⟨f, hf⟩ := Nat.exists_eq_add_of_le he
  have h1 := accSet_eq_of_ge M x a hst f
  have h2 := accSet_eq_of_ge M x a hst (f + 1)
  have hm : c ∈ accSet M x a (depth M x a + 1) := by
    simp only [accSet, Finset.mem_filter]; exact ⟨(mem_bndSet M x a).2 hc, h⟩
  have he' : depth M x a + 1 = e + (f + 1) := by rw [depth]; omega
  rw [he', h2, ← h1, ← hf] at hm
  simp only [accSet, Finset.mem_filter] at hm
  exact hm.2

/-- **Acceptance of a bounded configuration is acceptance within `depth`.** -/
theorem accN_of_acc {c : Args} (h : M.Acc x a c) : Bd M x a c → AccN M x a (depth M x a) c := by
  induction h with
  | acc hl hacc => exact fun _ => accN_mono M x a (Nat.zero_le _) ⟨hl, hacc⟩
  | univ hl hu _ ih =>
    exact fun hb => accN_depth_succ M x a hb
      ⟨hl, Or.inr (Or.inl ⟨hu, fun c' h1 h2 => ih c' h1 h2 (bd_of_step M x a hl h1 h2)⟩)⟩
  | ex hl hu h1 h2 _ ih =>
    exact fun hb => accN_depth_succ M x a hb
      ⟨hl, Or.inr (Or.inr ⟨hu, _, h1, h2, ih (bd_of_step M x a hl h1 h2)⟩)⟩

theorem acc_iff_accN {c : Args} (hc : Bd M x a c) : M.Acc x a c ↔ AccN M x a (depth M x a) c :=
  ⟨fun h => accN_of_acc M x a h hc, acc_of_accN M x a⟩

theorem depth_le : depth M x a ≤ 2 ^ (M.k * (bnd M x a + 1)) := card_bndSet_le M x a

end UExp

end HTN
