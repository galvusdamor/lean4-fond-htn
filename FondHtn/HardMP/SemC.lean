import FondHtn.HardMP.DescC
import FondHtn.HardMP.Final
/-!
# Semantics of the counter construction

* binary counters (`FOND.HardMP.bitsum`) and the increment `FOND.HardMP.incI`;
* the round programs leave the counter unchanged (frame), the invariants `Good`/`GoodK` do not
  read it;
* the list-game round lemmas for `FOND.HardMP.descC` (rounds preceded by the increment).
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## Binary counters -/

/-- The value of the bits `b 0, …, b (N - 1)`. -/
def bitsum (b : ℕ → Bool) (N : ℕ) : ℕ := ∑ j ∈ Finset.range N, if b j then 2 ^ j else 0

theorem bitsum_lt (b : ℕ → Bool) : ∀ N, bitsum b N < 2 ^ N
  | 0 => by simp [bitsum]
  | N + 1 => by
    have := bitsum_lt b N
    simp only [bitsum, Finset.sum_range_succ] at this ⊢
    split_ifs <;> rw [pow_succ] <;> omega

theorem bitsum_congr {b b' : ℕ → Bool} {N : ℕ} (h : ∀ j < N, b j = b' j) :
    bitsum b N = bitsum b' N :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]

theorem bitsum_all_true {b : ℕ → Bool} : ∀ {N : ℕ}, (∀ j < N, b j = true) →
    bitsum b N = 2 ^ N - 1
  | 0, _ => by simp [bitsum]
  | N + 1, h => by
    have ih := bitsum_all_true (N := N) fun j hj => h j (by omega)
    simp only [bitsum, Finset.sum_range_succ] at ih ⊢
    rw [ih, if_pos (h N (by omega)), pow_succ]
    have := Nat.one_le_two_pow (n := N)
    omega

/-- Increment: bits below `i` set and cleared, bit `i` clear and set. -/
theorem bitsum_inc {b b' : ℕ → Bool} {i : ℕ} (hlo : ∀ j < i, b j = true) (hi : b i = false)
    (hlo' : ∀ j < i, b' j = false) (hi' : b' i = true) (hhi : ∀ j, i < j → b' j = b j) :
    ∀ N, i < N → bitsum b' N = bitsum b N + 1 := by
  have hlow : ∀ N, N ≤ i → bitsum b N = 2 ^ N - 1 ∧ bitsum b' N = 0 := by
    intro N hN
    refine ⟨bitsum_all_true fun j hj => hlo j (by omega), ?_⟩
    exact Finset.sum_eq_zero fun j hj => by
      rw [hlo' j (by have := Finset.mem_range.1 hj; omega)]; rfl
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [bitsum, Finset.sum_range_succ] at ih ⊢
    rcases Nat.lt_or_ge i N with h | h
    · rw [ih h, hhi N h]; ring
    · obtain rfl : i = N := by omega
      obtain ⟨h1, h2⟩ := hlow i le_rfl
      simp only [bitsum] at h1 h2
      rw [h1, h2, hi, hi']
      have := Nat.one_le_two_pow (n := i)
      simp only [Bool.false_eq_true, if_false, if_true]
      omega

/-- A counter below its maximum has a lowest clear bit. -/
theorem exists_inc {b : ℕ → Bool} {N : ℕ} (h : bitsum b N + 1 < 2 ^ N) :
    ∃ i < N, (∀ j < i, b j = true) ∧ b i = false := by
  have hex : ∃ i, i < N ∧ b i = false := by
    by_contra hc
    push_neg at hc
    rw [bitsum_all_true fun j hj => by simpa using hc j hj] at h
    omega
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, fun j hj => ?_, (Nat.find_spec hex).2⟩
  have := Nat.find_min hex hj
  simp only [not_and, Bool.not_eq_false] at this
  exact this (by have := (Nat.find_spec hex).1; omega)

/-! ## The counter of a configuration -/

/-- The counter of a configuration. -/
def ctrC (p : ProbDesc) (c : Cfg) : ℕ := bitsum (fun j => c.val (fSlot (cslot p) j)) (Nc p)

/-- The specification of alternative `i` of the increment. -/
def incSpec (p : ProbDesc) (i : ℕ) : ASpec :=
  ((List.range i).map (fSlot (cslot p)), [fSlot (cslot p) i],
    [([fSlot (cslot p) i], (List.range i).map (fSlot (cslot p)))], [], [])

theorem incI_eqS (p : ProbDesc) : incI p = (List.range (Nc p)).map (incSpec p) := rfl

/-- The configuration after alternative `i` of the increment. -/
def incCfg (p : ProbDesc) (c : Cfg) (i : ℕ) : Cfg :=
  (incSpec p i).eff ([fSlot (cslot p) i], (List.range i).map (fSlot (cslot p))) c

theorem incCfg_val_ne {p : ProbDesc} {c : Cfg} {i f : ℕ} (hf : ∀ j, f ≠ fSlot (cslot p) j) :
    (incCfg p c i).val f = c.val f := by
  have h1 : f ∉ (List.range i).map (fSlot (cslot p)) := fun h => by
    obtain ⟨x, -, e⟩ := List.mem_map.1 h; exact hf x e.symm
  have h2 : f ∉ [fSlot (cslot p) i] := by simpa using hf i
  simp only [incCfg, ASpec.eff]
  rw [decide_eq_false h1, decide_eq_false h2]
  simp

@[simp] theorem incCfg_cur {p : ProbDesc} {c : Cfg} {i : ℕ} : (incCfg p c i).cur = c.cur := by
  simp [incCfg, ASpec.eff, ASpec.cnew, incSpec]

theorem mem_wpI_inc {p : ProbDesc} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (incI p) Ψ ↔ ∃ i < Nc p, (∀ j < i, c.val (fSlot (cslot p) j) = true) ∧
      c.val (fSlot (cslot p) i) = false ∧ incCfg p c i ∈ Ψ := by
  rw [mem_wpI_iff, incI_eqS]
  simp only [List.mem_map, List.mem_range, exists_exists_and_eq_and]
  refine exists_congr fun i => and_congr Iff.rfl ?_
  simp [incSpec, ASpec.App, ASpec.pre, ASpec.neg, ASpec.cpre, ASpec.effs, incCfg, and_assoc]

theorem ctrC_inc {p : ProbDesc} {c : Cfg} {i : ℕ} (hi : i < Nc p)
    (hlo : ∀ j < i, c.val (fSlot (cslot p) j) = true) (hb : c.val (fSlot (cslot p) i) = false) :
    ctrC p (incCfg p c i) = ctrC p c + 1 := by
  unfold ctrC
  refine bitsum_inc hlo hb (fun j hj => ?_) ?_ (fun j hj => ?_) _ hi
  · have h1 : fSlot (cslot p) j ∈ (List.range i).map (fSlot (cslot p)) :=
      List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
    have h2 : fSlot (cslot p) j ∉ [fSlot (cslot p) i] := by simp; omega
    simp only [incCfg, ASpec.eff]
    rw [decide_eq_true h1, decide_eq_false h2]; simp
  · simp [incCfg, ASpec.eff]
  · have h1 : fSlot (cslot p) j ∉ (List.range i).map (fSlot (cslot p)) := by simp; omega
    have h2 : fSlot (cslot p) j ∉ [fSlot (cslot p) i] := by simp; omega
    simp only [incCfg, ASpec.eff]
    rw [decide_eq_false h1, decide_eq_false h2]; simp

/-! ## Frames -/

/-- Programs that do not write the fields `G` keep them. -/
theorem wpP_frame {G : ℕ → Prop} :
    ∀ {prog : List (List ASpec)}, (∀ ins ∈ prog, ∀ a ∈ ins, ∀ e ∈ a.effs, ∀ f, G f →
      f ∉ e.1 ∧ f ∉ e.2) → ∀ {Ψ : Set Cfg} {c : Cfg}, c ∈ wpP prog Ψ →
      c ∈ wpP prog {c' | c' ∈ Ψ ∧ ∀ f, G f → c'.val f = c.val f}
  | [], _, Ψ, c, h => show c ∈ {c' | c' ∈ Ψ ∧ _} from ⟨h, fun _ _ => rfl⟩
  | ins :: prog, hG, Ψ, c, h => by
    obtain ⟨a, ha, happ, hall⟩ := h
    refine ⟨a, ha, happ, fun c' hc' => ?_⟩
    have h' := wpP_frame (fun ins' hins' => hG ins' (List.mem_cons_of_mem _ hins')) (hall c' hc')
    obtain ⟨e, he, rfl⟩ := hc'
    refine wpP_mono _ (fun c'' hc'' => ?_) h'
    obtain ⟨h1, h2⟩ := hc''
    refine ⟨h1, fun f hf => ?_⟩
    rw [h2 f hf]
    obtain ⟨h3, h4⟩ := hG ins (List.mem_cons_self ..) a ha e he f hf
    simp [ASpec.eff, h3, h4]

/-! ## The invariants ignore the counter -/

theorem good_congr {p : ProbDesc} {allV : List (List Bool)} {c d : Cfg}
    (h0 : ∀ j, c.val (fSlot 0 j) = d.val (fSlot 0 j)) (h1 : ∀ j, c.val (fSlot 1 j) = d.val (fSlot 1 j))
    (hd : c.val fDone = d.val fDone) (hc : c.cur = d.cur) :
    Good p allV c ↔ Good p allV d := by
  have e0 : vecC (pfacts p).length c 0 = vecC (pfacts p).length d 0 := vecC_congr fun j _ => h0 j
  have e1 : vecC (pfacts p).length c 1 = vecC (pfacts p).length d 1 := vecC_congr fun j _ => h1 j
  simp only [Good, e0, e1, hd, hc]

theorem goodK_congr {p : ProbDesc} {allV : List (List Bool)} {m : ℕ} {c d : Cfg}
    (h0 : ∀ j, c.val (fSlot 0 j) = d.val (fSlot 0 j)) (h1 : ∀ j, c.val (fSlot 1 j) = d.val (fSlot 1 j))
    (hd : c.val fDone = d.val fDone) (hc : c.cur = d.cur) :
    GoodK p allV m c ↔ GoodK p allV m d := by
  have e0 : vecC (pfacts p).length c 0 = vecC (pfacts p).length d 0 := vecC_congr fun j _ => h0 j
  have e1 : vecC (pfacts p).length c 1 = vecC (pfacts p).length d 1 := vecC_congr fun j _ => h1 j
  simp only [GoodK, e0, e1, hd, hc]

theorem cslot_ge (p : ProbDesc) : 2 ≤ cslot p := by unfold cslot; omega

theorem incCfg_good {p : ProbDesc} {allV : List (List Bool)} {c : Cfg} {i : ℕ} :
    Good p allV (incCfg p c i) ↔ Good p allV c :=
  good_congr (fun j => incCfg_val_ne fun j' h => by
      have := cslot_ge p; simp only [fSlot_inj] at h; omega)
    (fun j => incCfg_val_ne fun j' h => by have := cslot_ge p; simp only [fSlot_inj] at h; omega)
    (incCfg_val_ne fun j' h => fDone_ne_fSlot _ _ h) incCfg_cur

theorem incCfg_goodK {p : ProbDesc} {allV : List (List Bool)} {m : ℕ} {c : Cfg} {i : ℕ} :
    GoodK p allV m (incCfg p c i) ↔ GoodK p allV m c :=
  goodK_congr (fun j => incCfg_val_ne fun j' h => by
      have := cslot_ge p; simp only [fSlot_inj] at h; omega)
    (fun j => incCfg_val_ne fun j' h => by have := cslot_ge p; simp only [fSlot_inj] at h; omega)
    (incCfg_val_ne fun j' h => fDone_ne_fSlot _ _ h) incCfg_cur

/-! ## Rounds in the list game -/

/-- A bound on the length of the round programs. -/
def LrC (p : ProbDesc) : ℕ := ((rulesC p).map List.length).sum

section Round

variable {p : ProbDesc} {D : FProbDesc} {O : List MethodDesc}
  (hv : D.Valid) (hA : D.actions = acts (prgsC p))
  (hM : D.methods = chainMeths (prgsC p) [(true, roundN)] ++ O)
  (hO : ∀ e ∈ O, ∀ r pc, e.1 ≠ cN r pc) (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls)
  (hspec : ∀ r < (prgsC p).length, ∀ pc < ((prgsC p).getI r).length,
    ∀ alt < (((prgsC p).getI r).getI pc).length, ((((prgsC p).getI r).getI pc).getI alt).WF)
  (hR : ∀ ls, meth roundN ls ∈ D.methods ↔
    (∃ r < (rulesC p).length, ls = [(true, cN (r + 1) 0)]) ∨ ls ∈ [[(false, finN)]])
include hv hA hM hO hmeth hspec hR

theorem round_sound_LC {n : ℕ} {c : Cfg} {Φ : Set (Set ℕ)}
    (h : D.toProblem.LRunH (n + 1) [Sum.inr roundN] c.enc Φ) :
    (∃ r ∈ rulesC p, c ∈ wpP r {c' | D.toProblem.LRunH n [Sum.inr roundN] c'.enc Φ}) ∨
      D.toProblem.LRunH n [Sum.inl finN] c.enc Φ := by
  obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h
  obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
  rcases (hR ls).1 hls with ⟨r, hr, rfl⟩ | hx
  · left
    have hr' : r + 1 < (prgsC p).length := by simp [prgsC]; omega
    have := chain_sound hv hA hM hO hmeth hspec hr' _ 0 (Nat.zero_add _).symm
      (by simpa [toLab] using h)
    simp only [List.drop_zero, prgsC, List.getI_cons_succ] at this
    exact ⟨_, getI_memS hr, by simpa [toLab] using this⟩
  · simp only [List.mem_singleton] at hx
    subst hx
    exact Or.inr (by simpa [toLab] using h)

theorem round_complete_LC {m : ℕ} {c : Cfg} {Φ : Set (Set ℕ)}
    {r : List (List ASpec)} (hr : r ∈ rulesC p)
    (h : c ∈ wpP r {c' | D.toProblem.LRunH m [Sum.inr roundN] c'.enc Φ}) :
    D.toProblem.LRunH (m + 2 * LrC p + 2) [Sum.inr roundN] c.enc Φ := by
  obtain ⟨i, hi, rfl⟩ := exists_getI_of_mem hr
  have hi' : i + 1 < (prgsC p).length := by simp [prgsC]; omega
  have hc := chain_complete hv hA hM hO hmeth hspec hi' _ 0 (Nat.zero_add _).symm
    (xs := []) (m := m) (c := c) (Φ := Φ) (by simpa [prgsC, toLab] using h)
  refine Problem.LRunH.mono (.comp ((seqBodyF_iff hmeth).2 ⟨_, (hR _).2 (Or.inl ⟨i, hi, rfl⟩),
    rfl⟩) (by simpa [toLab] using hc)) ?_ le_rfl
  have : ((rulesC p).getI i).length ≤ LrC p :=
    List.le_sum_of_mem (List.mem_map.2 ⟨_, getI_memS hi, rfl⟩)
  simp only [prgsC, List.getI_cons_succ]
  omega

end Round

end HardMP

end FOND
