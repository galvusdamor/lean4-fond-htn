import HtnComplexity.PT.Arith
/-!
# The predecessor in the polynomial-time calculus

* `HTN.Syn.PolyDom.decBits` — binary decrement on little-endian digits;
* `HTN.Syn.PolyDom.PT.pred` — `n ↦ n - 1` is a polynomial-time function of the calculus.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime PolyInst

variable {α β γ δ σ : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc σ]

/-! ### The predecessor -/

/-- Binary decrement on little-endian digits: flip the digits up to and including the first `1`. -/
def decBits (c : Bool) (w : List Bool) : List Bool :=
  (splits w).flatMap fun p => [bif c && p.1.all (fun x => !x) then !p.2.1 else p.2.1]

theorem flatMap_splits_cons {g : List β → β → List β → List γ} (a : β) (l : List β) :
    (splits (a :: l)).flatMap (fun p => g p.1 p.2.1 p.2.2) =
      g [] a l ++ (splits l).flatMap (fun p => g (a :: p.1) p.2.1 p.2.2) := by
  simp [splits, List.flatMap_map]

theorem decBits_nil (c : Bool) : decBits c [] = [] := rfl

theorem decBits_cons (c b : Bool) (w : List Bool) :
    decBits c (b :: w) = (bif c then !b else b) :: decBits (c && !b) w := by
  unfold decBits
  rw [flatMap_splits_cons (g := fun pre e _ => [bif c && pre.all (fun x => !x) then !e else e])]
  simp only [List.all_nil, Bool.and_true, List.singleton_append, List.all_cons, Bool.and_assoc]

theorem decBits_false : ∀ w : List Bool, decBits false w = w
  | [] => rfl
  | b :: w => by rw [decBits_cons, Bool.false_and, decBits_false w]; rfl

theorem natOfBits_decBits : ∀ w : List Bool, (natOfBits w = 0 → w = []) →
    natOfBits (decBits true w) = natOfBits w - 1
  | [] => fun _ => rfl
  | true :: w => fun _ => by
    rw [decBits_cons, Bool.not_true, Bool.and_false, decBits_false, natOfBits_cons,
      natOfBits_cons]
    simp
  | false :: w => fun h => by
    have hw : natOfBits w ≠ 0 := by
      intro h0
      have := h (by rw [natOfBits_cons]; simp [h0])
      exact absurd this (by simp)
    rw [decBits_cons]
    simp only [natOfBits_cons, Bool.not_false, Bool.and_true, cond_true]
    rw [natOfBits_decBits w (fun h0 => absurd h0 hw)]
    simp
    omega

theorem PT.pred {f : α → ℕ} (hf : PT f) : PT fun a => f a - 1 := by
  have hb : PT fun a => bitsOfNat (f a) := PT.bits.comp hf
  have h : PT fun a => (splits (bitsOfNat (f a))).flatMap fun p =>
      [bif true && p.1.all (fun x => !x) then !p.2.1 else p.2.1] :=
    PT.flatMapSplits (g := fun _ pre b _ => [bif true && pre.all (fun x => !x) then !b else b])
      hb (PT.single (PT.cond (PT.and (PT.const true)
      (PT.all (p := fun _ (x : Bool) => !x) (PT.fst.comp PT.snd) (PT.not PT.snd)))
      (PT.not (PT.fst.comp (PT.snd.comp PT.snd))) (PT.fst.comp (PT.snd.comp PT.snd))))
  refine (PT.ofBits h).of_eq fun a => ?_
  show natOfBits (decBits true (bitsOfNat (f a))) = f a - 1
  rw [natOfBits_decBits _ (fun h0 => by rw [natOfBits_bitsOfNat] at h0; rw [h0, bitsOfNat_zero]),
    natOfBits_bitsOfNat]

theorem PT.decBool {c : α → Bool} {b : Bool} (hc : PT c) : PT fun a => decide (c a = b) :=
  PT.eq hc (PT.const b)


end PolyDom

end Syn

end HTN
