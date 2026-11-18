import HtnComplexity.AcVerify.Bound
import HtnPlanning.Computable.Names
/-!
# The length of the certificate

If every name of the domain and of the instance description is below `2 ^ B` (and so is the
number of methods plus one; `HTN.Syn.AcVer.NamesLt`), the certificate `certOf d q W` of a path
witness of an acyclic problem has length at most `certBound q.size d.size B`
(`HTN.Syn.AcVer.length_certOf_le`), a bound exponential in a polynomial of the three parameters
(`HTN.Syn.AcVer.certBound_le`).
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-! ### Bits -/

theorem length_bitsOfNat_le_of_lt : ∀ (B n : ℕ), n < 2 ^ B → (bitsOfNat n).length ≤ B
  | _, 0, _ => by simp
  | 0, n + 1, h => by simp at h
  | B + 1, n + 1, h => by
    rw [bitsOfNat_succ, List.length_cons]
    have := length_bitsOfNat_le_of_lt B ((n + 1) / 2) (by rw [pow_succ] at h; omega)
    omega

theorem length_serNat_le_of_lt {B n : ℕ} (h : n < 2 ^ B) : (serNat n).length ≤ 2 * B + 1 := by
  rw [serNat, length_bstr]
  have := length_bitsOfNat_le_of_lt B n h
  omega

theorem length_blist_le' {l : List (List Bool)} {M : ℕ} (h : ∀ s ∈ l, s.length ≤ M) :
    (blist l).length ≤ 1 + l.length * (2 * M + 2) := by
  rw [length_blist]
  have : (l.map fun x => 2 * x.length + 2).sum ≤ (l.map fun _ => 2 * M + 2).sum :=
    List.sum_le_sum fun s hs => by have := h s hs; omega
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

/-! ### Small names -/

/-- **All names are below `2 ^ B`**, and so is the number of methods plus one. -/
structure NamesLt (d : DomDesc) (q : InstDesc) (B : ℕ) : Prop where
  dom : ∀ x ∈ d.names, x < 2 ^ B
  inst : ∀ x ∈ q.names, x < 2 ^ B
  meth : d.methods.length + 1 < 2 ^ B

theorem label_val {t : TnDesc} {i v : ℕ} (h : t.label i = Sum.inl v ∨ t.label i = Sum.inr v) :
    v = 0 ∨ v ∈ t.names := by
  rcases hl : t.lbl.lookup i with _ | ⟨b, m⟩
  · rw [TnDesc.label, hl] at h
    rcases h with h | h
    · simp only [Sum.inl.injEq] at h; exact Or.inl h.symm
    · simp at h
  · have hin : (i, b, m) ∈ t.lbl := mem_of_lookup_eq_some hl
    have hm : v = m := by
      cases b <;> rw [TnDesc.label, hl] at h <;> simp at h <;> exact h.symm
    subst hm
    exact Or.inr (t.lbl_subset_names _ hin).2

theorem lt_of_names_or_zero {B v : ℕ} {l : List ℕ}
    (hl : ∀ x ∈ l, x < 2 ^ B) (h : v = 0 ∨ v ∈ l) : v < 2 ^ B := by
  rcases h with rfl | h
  · exact Nat.pos_of_ne_zero (by positivity)
  · exact hl v h

theorem methodAt_names_lt {B : ℕ} (hB : NamesLt d q B) {k : ℕ} (hk : k ∈ mIdx d) :
    ∀ x ∈ (methodAt d k).2.names, x < 2 ^ B := by
  intro x hx
  have h1 := (mem_mIdx.1 hk)
  refine hB.dom x (DomDesc.method_names_subset (methodAt_mem (k := k) h1.2) x ?_)
  simp [MethodDesc.names, hx]

theorem length_lblSer_le {B : ℕ} (hB : NamesLt d q B) {t : TnDesc}
    (ht : ∀ x ∈ t.names, x < 2 ^ B) (i : ℕ) : (lblSer (t.label i)).length ≤ 4 * B + 2 := by
  have h2 : (1 : ℕ) < 2 ^ B := by have := hB.meth; omega
  rcases hl : t.label i with v | v <;> simp only [lblSer, List.length_append]
  · have := length_serNat_le_of_lt (B := B) (n := 0) (by omega)
    have := length_serNat_le_of_lt (lt_of_names_or_zero ht (label_val (Or.inl hl)))
    omega
  · have := length_serNat_le_of_lt (B := B) (n := 1) h2
    have := length_serNat_le_of_lt (lt_of_names_or_zero ht (label_val (Or.inr hl)))
    omega

/-- **The record of a step is short.** -/
theorem length_recOf_le {B : ℕ} (hB : NamesLt d q B) {z : PStep} (hz : z ∈ allSteps d q) :
    (recOf d q z).length ≤ 8 * B + 4 := by
  have hq : ∀ x ∈ q.tnI.names, x < 2 ^ B := fun x hx => hB.inst x (by simp [InstDesc.names, hx])
  simp only [allSteps, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons] at hz
  rcases hz with ⟨i, hi, rfl⟩ | ⟨k, hk, j, hj, rfl⟩
  · simp only [recOf, List.length_append, stepLabel, netOf, if_true]
    have := length_serNat_le_of_lt (B := B) (n := 0) (Nat.pos_of_ne_zero (by positivity))
    have := length_serNat_le_of_lt (hq i (q.tnI.ids_subset_names i hi))
    have := length_lblSer_le hB hq i
    omega
  · have hm := methodAt_names_lt hB hk
    have hk0 := mIdx_ne_zero hk
    have hkl : k < 2 ^ B := by have := (mem_mIdx.1 hk); have := hB.meth; omega
    simp only [recOf, List.length_append, stepLabel, netOf, if_neg hk0]
    have := length_serNat_le_of_lt hkl
    have := length_serNat_le_of_lt (lt_of_names_or_zero hm
      (hj.imp id fun h => (methodAt d k).2.ids_subset_names j h))
    have := length_lblSer_le hB hm j
    omega

/-! ### The states -/

/-- The facts a state list can contain. -/
def factPool (d : DomDesc) (q : InstDesc) : List ℕ :=
  q.initList ++ d.actions.flatMap fun a => a.2.2.1

theorem mem_actLists_add_pool {a f : ℕ} (h : f ∈ (actLists d a).2.1) : f ∈ factPool d q := by
  unfold actLists at h
  rcases hl : d.actions.lookup a with _ | x
  · rw [hl] at h; simp at h
  · rw [hl] at h
    have hx : (a, x) ∈ d.actions := mem_of_lookup_eq_some hl
    simp only [Option.elim] at h
    simp only [factPool, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨(a, x), hx, h⟩

theorem stepL_pool {a : ℕ} {L : List ℕ} (hL : ∀ x ∈ L, x ∈ factPool d q) :
    (∀ x ∈ stepL d a L, x ∈ factPool d q) ∧ (stepL d a L).length ≤ (factPool d q).length := by
  have hsub : ∀ x ∈ stepL d a L, x ∈ factPool d q := by
    intro x hx
    simp only [stepL, List.mem_dedup, List.mem_append, List.mem_filter] at hx
    rcases hx with ⟨h, -⟩ | h
    · exact hL x h
    · exact mem_actLists_add_pool h
  refine ⟨hsub, ?_⟩
  have hnd : (stepL d a L).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hnd]
  refine (Finset.card_le_card fun x hx => ?_).trans (List.toFinset_card_le _)
  exact List.mem_toFinset.2 (hsub x (List.mem_toFinset.1 hx))

theorem length_factPool_le (d : DomDesc) (q : InstDesc) :
    (factPool d q).length ≤ q.size + d.size := by
  simp only [factPool, List.length_append, List.length_flatMap]
  have h1 : (d.actions.map fun a => a.2.2.1.length).sum ≤ (d.actions.map ActionDesc.size).sum :=
    List.sum_le_sum fun a _ => by simp only [ActionDesc.size]; omega
  have h2 : q.initList.length ≤ q.size := by simp only [InstDesc.size]; omega
  simp only [DomDesc.size]
  omega

theorem factPool_lt {B : ℕ} (hB : NamesLt d q B) : ∀ x ∈ factPool d q, x < 2 ^ B := by
  intro x hx
  simp only [factPool, List.mem_append, List.mem_flatMap] at hx
  rcases hx with h | ⟨a, ha, h⟩
  · exact hB.inst x (by simp [InstDesc.names, h])
  · refine hB.dom x (DomDesc.action_names_subset ha x ?_)
    simp [ActionDesc.names, h]

/-! ### The entries -/

/-- The bound on the content of one entry. -/
def entBound (sq sd B : ℕ) : ℕ :=
  1 + (1 + (2 * sd + 2) * (2 * (8 * B + 4) + 2)) + (1 + (sq + sd) * (2 * B + 2)) +
    3 * (1 + sd * (2 * B + 2))

theorem length_actList_le {l : List ℕ} {a : ℕ}
    (h : l = (actLists d a).1 ∨ l = (actLists d a).2.1 ∨ l = (actLists d a).2.2) :
    l.length ≤ d.size ∧ ∀ x ∈ l, x ∈ d.names := by
  unfold actLists at h
  rcases hl : d.actions.lookup a with _ | x
  · rw [hl] at h; simp only [Option.elim] at h
    rcases h with rfl | rfl | rfl <;> simp
  · rw [hl] at h
    have hx : (a, x) ∈ d.actions := mem_of_lookup_eq_some hl
    simp only [Option.elim] at h
    have hs : ActionDesc.size (a, x) ≤ d.size := by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := ActionDesc.size) hx)
      simp only [DomDesc.size]; omega
    have hn := DomDesc.action_names_subset hx
    simp only [ActionDesc.size, ActionDesc.names] at hs hn
    rcases h with rfl | rfl | rfl
    · exact ⟨by omega, fun y hy => hn y (by simp [hy])⟩
    · exact ⟨by omega, fun y hy => hn y (by simp [hy])⟩
    · exact ⟨by omega, fun y hy => hn y (by simp [hy])⟩

theorem length_actS_le {B : ℕ} (hB : NamesLt d q B) {l : List ℕ} {a : ℕ}
    (h : l = (actLists d a).1 ∨ l = (actLists d a).2.1 ∨ l = (actLists d a).2.2) :
    (blist (l.map bitsOfNat)).length ≤ 1 + d.size * (2 * B + 2) := by
  obtain ⟨h1, h2⟩ := length_actList_le h
  refine (length_blist_le' (M := B) fun s hs => ?_).trans ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    exact length_bitsOfNat_le_of_lt B x (hB.dom x (h2 x hx))
  · rw [List.length_map]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h1) _

/-- **The content of an entry is short.** -/
theorem length_enc_ceOf_le (hd : d.IsAcyclic) {B : ℕ} (hB : NamesLt d q B) {u : Entry}
    (hu : EntryOK d q u) (h0 : u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) {L' : List ℕ}
    (hL : ∀ x ∈ L', x ∈ factPool d q) (hLl : L'.length ≤ q.size + d.size) :
    (ceOf d q u L').enc.length ≤ entBound q.size d.size B := by
  rw [CE.enc_eq]
  simp only [List.length_append, List.length_singleton]
  have hrecs : (blist (ceOf d q u L').recs).length ≤
      1 + (2 * d.size + 2) * (2 * (8 * B + 4) + 2) := by
    refine (length_blist_le' (M := 8 * B + 4) fun s hs => ?_).trans ?_
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
      exact length_recOf_le hB (mem_allSteps hu h0 z hz)
    · simp only [ceOf, List.length_map]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (length_path_le hd hu)) _
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
  unfold entBound
  omega

/-! ### The certificate -/

theorem length_certL_le (hd : d.IsAcyclic) {B : ℕ} (hB : NamesLt d q B) {W : List Entry}
    (hW : ∀ u ∈ W, EntryOK d q u) (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    ∀ (L : List ℕ) (W' : List Entry), (∀ u ∈ W', u ∈ W) → (∀ x ∈ L, x ∈ factPool d q) →
      L.length ≤ q.size + d.size →
      ∀ e ∈ certL d q L W', e.enc.length ≤ entBound q.size d.size B
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
    · exact length_enc_ceOf_le hd hB (hW u hu) (h0 u hu) hnext.1 hnext.2
    · exact length_certL_le hd hB hW h0 _ r (fun v hv => hsub v (by simp [hv])) hnext.1
        hnext.2 e he

theorem length_certL (L : List ℕ) : ∀ W : List Entry, (certL d q L W).length = W.length := by
  intro W
  induction W generalizing L with
  | nil => rfl
  | cons u r ih => simp [certL, ih]

/-- The bound on the certificate. -/
def certBound (sq sd B : ℕ) : ℕ :=
  1 + (sq + sd + 1) ^ (2 * sd + 2) * (2 * entBound sq sd B + 2)

/-- **The certificate of a path witness of an acyclic problem is short.** -/
theorem length_certOf_le (hd : d.IsAcyclic) {B : ℕ} (hB : NamesLt d q B) {W : List Entry}
    (hW : PathOK d q W) (h0 : ∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) :
    (certOf d q W).length ≤ certBound q.size d.size B := by
  unfold certOf certBound
  refine (length_blist_le' (M := entBound q.size d.size B) fun s hs => ?_).trans ?_
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
    refine length_certL_le hd hB hW.entries h0 q.initList W (fun _ h => h) ?_ ?_ e he
    · intro x hx; simp [factPool, hx]
    · have : q.initList.length ≤ q.size := by simp only [InstDesc.size]; omega
      omega
  · rw [List.length_map, length_certL]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (length_witness_le hd hW h0)) _

/-! ### An exponential bound -/

theorem certBound_mono {a a' b b' c c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    certBound a b c ≤ certBound a' b' c' := by
  unfold certBound entBound
  have h1 : (a + b + 1) ^ (2 * b + 2) ≤ (a' + b' + 1) ^ (2 * b' + 2) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  gcongr

theorem certBound_le (X : ℕ) : certBound X X X ≤ 2 ^ (4 * X * X + 8 * X + 16) := by
  have h1 : 2 * X + 1 ≤ 2 ^ (X + 1) := by
    have := Nat.lt_two_pow_self (n := X)
    rw [pow_succ]; omega
  have hE : 2 * entBound X X X + 2 ≤ 64 * (2 * X + 1) ^ 2 := by
    unfold entBound; nlinarith
  have h2 : (2 * X + 1) ^ (2 * X + 4) ≤ 2 ^ ((X + 1) * (2 * X + 4)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 _
  have h3 : (X + 1) * (2 * X + 4) + 6 ≤ 4 * X * X + 8 * X + 15 := by nlinarith
  calc certBound X X X = 1 + (2 * X + 1) ^ (2 * X + 2) * (2 * entBound X X X + 2) := by
        unfold certBound; ring_nf
    _ ≤ 1 + (2 * X + 1) ^ (2 * X + 2) * (64 * (2 * X + 1) ^ 2) := by gcongr
    _ = 1 + 2 ^ 6 * (2 * X + 1) ^ (2 * X + 4) := by ring
    _ ≤ 1 + 2 ^ 6 * 2 ^ ((X + 1) * (2 * X + 4)) := by gcongr
    _ = 1 + 2 ^ ((X + 1) * (2 * X + 4) + 6) := by rw [← pow_add, add_comm 6]
    _ ≤ 2 ^ ((X + 1) * (2 * X + 4) + 6) + 2 ^ ((X + 1) * (2 * X + 4) + 6) := by
        have := Nat.one_le_two_pow (n := (X + 1) * (2 * X + 4) + 6); omega
    _ = 2 ^ ((X + 1) * (2 * X + 4) + 7) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (4 * X * X + 8 * X + 16) := Nat.pow_le_pow_right (by omega) (by omega)

end AcVer

end Syn

end HTN
