import HtnComplexity.PT.Iter
import ComplexityTheory.Complexity.Counter
/-!
# Derived combinators of the polynomial-time calculus

`flatMap`, `map`, `filter`, `append`, `length`, `List.range`, `dedup`, membership, `getI`,
lookups, comparisons and affine maps of numbers — all from the emission over the entries
(`HTN.Syn.PolyDom.PT.flatMapSplits`), the bounded iteration and a few transducers of the
project.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

variable {α β γ δ σ : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc σ]

/-! ### `flatMap`, `map`, `filter` -/

theorem flatMap_splits_entry' {β γ : Type} (l : List β) (G : β → List γ) :
    ((splits l).flatMap fun p => G p.2.1) = l.flatMap G := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [splits, List.flatMap_map, ih]

theorem flatMap_single_eq_map {β γ : Type} (l : List β) (G : β → γ) :
    (l.flatMap fun b => [G b]) = l.map G := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem PT.flatMap {f : α → List β} {g : α → β → List γ} (hf : PT f) (hg : PT₂ g) :
    PT fun a => (f a).flatMap (g a) := by
  have h := PT.flatMapSplits (g := fun a _ b _ => g a b) hf
    (hg.comp (PT.pair PT.fst (PT.fst.comp (PT.snd.comp PT.snd))))
  exact h.of_eq fun a => flatMap_splits_entry' (f a) (g a)

theorem PT.single {f : α → β} (hf : PT f) : PT fun a => [f a] := PT.cons hf PT.nil

theorem PT.map {f : α → List β} {g : α → β → γ} (hf : PT f) (hg : PT₂ g) :
    PT fun a => (f a).map (g a) := by
  have h := PT.flatMap (g := fun a b => [g a b]) hf (PT.single hg)
  exact h.of_eq fun a => flatMap_single_eq_map _ _

theorem PT.filter {f : α → List β} {p : α → β → Bool} (hf : PT f) (hp : PT₂ p) :
    PT fun a => (f a).filter (p a) := by
  have h := PT.flatMap (g := fun a b => bif p a b then [b] else []) hf
    (PT.cond hp (PT.single PT.snd) PT.nil)
  refine h.of_eq fun a => ?_
  induction f a with
  | nil => rfl
  | cons b l ih =>
    simp only [List.flatMap_cons, List.filter_cons] at ih ⊢
    rw [ih]; cases p a b <;> rfl

/-! ### Appending -/

theorem dropLast_enc_append (l l' : List β) :
    enc (l ++ l') = (enc l).dropLast ++ enc l' := by
  rw [enc_list, enc_list, enc_list, List.map_append, blist_append_eq,
    blist_eq_entriesEnc (l.map enc), List.dropLast_concat]

theorem uc_dropLast : UC fun x : List Bool => x.dropLast :=
  (cobham_rev (cobham_tail' (cobham_rev cobham_var0))).of_eq' fun args => by
    simp [List.tail_reverse]

theorem PT.append {f g : α → List β} (hf : PT f) (hg : PT g) : PT fun a => f a ++ g a := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨fun x => (F x).dropLast ++ G x, PH.cobham_app (uc_dropLast.app hF) hG,
    fun a => by beta_reduce; rw [hFf, hGg, dropLast_enc_append]⟩

/-! ### Length and indices -/

theorem length_splits (l : List β) : (splits l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [splits, ih]

theorem PT.length {f : α → List β} (hf : PT f) : PT fun a => (f a).length := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => bstr (lenFn (emitEnt (fun _ => [true]) x (F x))),
    cobham_bstr ((cobham_c1 cobham_lenFnArgs (uc_emitEnt (uc_const [true]) hF)).of_eq' fun args => by
      simp [compFn, lenFn]), fun a => ?_⟩
  beta_reduce
  rw [hFf, emitEnt_enc, lenFn_eq, enc_nat, serNat]
  congr 2
  simp [length_splits]

theorem map_splits_length (l : List β) :
    (splits l).map (fun p => p.1.length) = List.range l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [splits, List.map_cons, List.map_map, List.length_cons, List.range_succ_eq_map]
    rw [← ih]
    simp [Function.comp_def]

/-- The indices of a list. -/
theorem PT.rangeLength {f : α → List β} (hf : PT f) : PT fun a => List.range (f a).length := by
  have h := PT.flatMapSplits (g := fun _ l₁ _ _ => [l₁.length]) hf
    (PT.single (PT.length (PT.fst.comp PT.snd)))
  refine h.of_eq fun a => ?_
  rw [← map_splits_length, ← flatMap_single_eq_map]

/-! ### Comparisons and affine maps of numbers -/

theorem PT.lt {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => decide (f a < g a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => [ltBits (undbl (F x)) (undbl (G x))],
    cobhamB_ltBits (cobham_undbl hF) (cobham_undbl hG), fun a => ?_⟩
  beta_reduce
  rw [hFf, hGg, enc_nat, enc_nat, undbl_serNat, undbl_serNat, ltBits_bitsOfNat]
  rfl

theorem PT.le {f g : α → ℕ} (hf : PT f) (hg : PT g) : PT fun a => decide (f a ≤ g a) :=
  (PT.not (PT.lt hg hf)).of_eq fun a => by by_cases h : f a ≤ g a <;> simp [h] <;> omega

theorem PT.affine (c d : ℕ) {f : α → ℕ} (hf : PT f) : PT fun a => c * f a + d := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact (PT.const d).of_eq fun a => by simp
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨fun x => affNum c d (F x), cobham_affNum c d hF,
    fun a => by beta_reduce; rw [hFf, enc_nat, affNum_serNat hc]; rfl⟩

theorem PT.succ {f : α → ℕ} (hf : PT f) : PT fun a => f a + 1 :=
  (PT.affine 1 1 hf).of_eq fun a => by ring

/-! ### Membership, `dedup`, `getI` -/

theorem PT.elem [DecidableEq β] {f : α → List β} {g : α → β} (hf : PT f) (hg : PT g) :
    PT fun a => decide (g a ∈ f a) := by
  have h := PT.not (PT.isEmpty (PT.filter (p := fun a b => decide (b = g a)) hf
    (PT.eq PT.snd (hg.comp PT.fst))))
  refine h.of_eq fun a => ?_
  by_cases hm : g a ∈ f a
  · have hne : (f a).filter (fun b => decide (b = g a)) ≠ [] := by
      intro he; rw [List.filter_eq_nil_iff] at he; exact he _ hm (by simp)
    simp only [hm, decide_true]
    cases hc : (f a).filter (fun b => decide (b = g a)) with
    | nil => exact absurd hc hne
    | cons x xs => rfl
  · have he : (f a).filter (fun b => decide (b = g a)) = [] := by
      rw [List.filter_eq_nil_iff]; intro x hx hxe; simp at hxe; exact hm (hxe ▸ hx)
    simp [hm, he]

theorem dedup_eq_flatMap_splits [DecidableEq β] (l : List β) :
    l.dedup = (splits l).flatMap fun p => if p.2.1 ∈ p.2.2 then [] else [p.2.1] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [splits, List.flatMap_cons, List.flatMap_map]
    rw [← ih]
    by_cases h : a ∈ l
    · simp [List.dedup_cons_of_mem h, h]
    · simp [List.dedup_cons_of_notMem h, h]

theorem PT.dedup [DecidableEq β] {f : α → List β} (hf : PT f) : PT fun a => (f a).dedup := by
  have h := PT.flatMapSplits (g := fun _ _ b l₂ => if b ∈ l₂ then [] else [b]) hf
    (PT.ite (PT.elem (PT.snd.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.snd.comp PT.snd)))
      PT.nil (PT.single (PT.fst.comp (PT.snd.comp PT.snd))))
  exact h.of_eq fun a => (dedup_eq_flatMap_splits (f a)).symm

theorem getI_eq_flatMap_splits [Inhabited β] (l : List β) (n : ℕ) :
    l.getI n = ((splits l).flatMap fun p => if p.1.length = n then [p.2.1] else []).headI := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [splits, List.flatMap_cons, List.flatMap_map, List.length_nil, List.length_cons]
    cases n with
    | zero =>
      simp
    | succ n =>
      simp only [Nat.add_right_cancel_iff, show (0 = n + 1) = False from by simp, if_false,
        List.nil_append, List.getI_cons_succ]
      exact ih n

theorem PT.getI [Inhabited β] {f : α → List β} {n : α → ℕ} (hf : PT f) (hn : PT n) :
    PT fun a => (f a).getI (n a) := by
  have h := PT.headI (PT.flatMapSplits (g := fun a l₁ b _ => if l₁.length = n a then [b] else [])
    hf (PT.ite (PT.eq (PT.length (PT.fst.comp PT.snd)) (hn.comp PT.fst))
      (PT.single (PT.fst.comp (PT.snd.comp PT.snd))) PT.nil))
  exact h.of_eq fun a => (getI_eq_flatMap_splits (f a) (n a)).symm

end PolyDom

end Syn

end HTN
