import HtnComplexity.PT.Decode
import HtnComplexity.PolyInst.Kit
import ComplexityTheory.Lang.Basic
/-!
# Languages of codes

A language of the form `{enc a | Q a}` — the codes of the values of a type that satisfy a
property — is what a decision problem on structured inputs is.  This file connects the typed
calculus of `HtnComplexity/PT/` with languages of raw bit strings:

* `HTN.Syn.PolyDom.lift` / `unlift` — a raw string as a value of the calculus (`enc x`) and
  back; both are finite-state transductions, hence of Cobham's class;
* `HTN.Syn.PolyDom.codeLang α Q` — the language `{enc a | Q a}`;
* **`HTN.Syn.PolyDom.inP_codeLang`** — if `Q` is decided by a polynomial-time Boolean function of
  the calculus, the language is in `P`;
* **`HTN.Syn.PolyDom.redP_codeLang`** — a polynomial-time map `f` of the calculus with
  `Q a ↔ R (f a)`, and one value `b₀` with `¬ R b₀`, give a polynomial-time many-one reduction
  of `codeLang α Q` to `codeLang β R` (non-codes are sent to the code of `b₀`).
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-! ### Raw strings as values -/

/-- The transducer writing each bit `b` as the code `true true b false` of the singleton `[b]`. -/
def liftM : Mealy Unit where
  step _ _ := ()
  out _ b := [true, true, b, false]

/-- **A raw bit string as a value of the calculus.** -/
def lift (x : List Bool) : List Bool := enc x

theorem liftM_outs (x : List Bool) : liftM.outs () x ++ [false] = lift x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [Mealy.outs_cons, lift, enc_cons, List.append_assoc] at ih ⊢
    rw [ih]; rfl

theorem uc_lift : UC lift := by
  have h := Mealy.cobham_mealy liftM [()] () (fun _ => [false]) (by simp) (by simp) cobham_var0
  exact UC.of_eq (show UC fun x => liftM.outs () x ++ [false] from h) fun x => liftM_outs x

/-- The transducer reading the bits back. -/
def unliftM : Mealy ℕ where
  step s _ := (s + 1) % 4
  out s b := if s = 2 then [b] else []

theorem unliftM_outs (x : List Bool) : unliftM.outs 0 (lift x) = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [lift, enc_cons, enc_bool, bstr, List.foldr_cons, List.foldr_nil] at ih ⊢
    simp only [Mealy.outs_cons, List.cons_append]
    simp [unliftM]
    exact ih

/-- **A value of the calculus of type `List Bool` back as a raw string.** -/
def unlift (z : List Bool) : List Bool := unliftM.outs 0 z

theorem unlift_lift (x : List Bool) : unlift (lift x) = x := unliftM_outs x

theorem uc_unlift : UC unlift := by
  have h := Mealy.cobham_mealy unliftM [0, 1, 2, 3] 0 (fun _ => []) (by simp)
    (fun s b hs => by simp [unliftM] at hs ⊢; omega) cobham_var0
  exact UC.of_eq (show UC fun x => unliftM.outs 0 x ++ [] from h) fun x => by simp [unlift]

/-- A Boolean function of the calculus on raw strings: `x ↦ [h x]`. -/
theorem uc_of_pt_bool {h : List Bool → Bool} (hh : PT h) : UC fun x => [h x] := by
  obtain ⟨H, hH, hHh⟩ := hh
  exact UC.of_eq (hH.comp uc_lift) fun x => hHh x

/-- A function of the calculus from raw strings to raw strings. -/
theorem uc_of_pt_list {h : List Bool → List Bool} (hh : PT h) : UC fun x => h x := by
  obtain ⟨H, hH, hHh⟩ := hh
  exact UC.of_eq (uc_unlift.comp (hH.comp uc_lift)) fun x => by
    show unlift (H (enc x)) = h x
    rw [hHh]; exact unlift_lift (h x)

theorem polyTimeFun_of_uc {F : List Bool → List Bool} (hF : UC F) : PolyTimeFun F :=
  PolyTimeFun.of_cobham hF fun _ => rfl

/-! ### Languages of codes -/

/-- **The language of the codes of the values satisfying `Q`.** -/
def codeLang (α : Type) [BEnc α] (Q : α → Prop) : Cx.Language := fun x => ∃ a : α, enc a = x ∧ Q a

theorem codeLang_enc {α : Type} [BEnc α] {Q : α → Prop} (a : α) : codeLang α Q (enc a) ↔ Q a := by
  constructor
  · rintro ⟨a', h, hq⟩; rwa [BEnc.inj h] at hq
  · exact fun h => ⟨a, rfl, h⟩

/-- **A language of codes with a polynomial-time property is in `P`.** -/
theorem inP_codeLang {α : Type} [BEnc α] [BDec α] {Q : α → Prop} {q : α → Bool} (hq : PT q)
    (hQ : ∀ a, q a = true ↔ Q a) : Cx.P (codeLang α Q) := by
  have hh : PT fun y : List Bool => isCode α y && q (decR y : α × List Bool).1 :=
    PT.and (pt_isCode α) (hq.comp (PT.fst.comp BDec.pt_decR))
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_bool hh), fun x => ?_⟩
  simp only [List.getD_cons_zero, Bool.and_eq_true]
  constructor
  · rintro ⟨a, rfl, ha⟩
    refine ⟨(isCode_iff _).2 ⟨a, rfl⟩, ?_⟩
    rw [show enc a = enc a ++ [] by simp, BDec.decR_enc]
    exact (hQ a).2 ha
  · rintro ⟨hc, hq'⟩
    obtain ⟨a, rfl⟩ := (isCode_iff _).1 hc
    rw [show enc a = enc a ++ [] by simp, BDec.decR_enc] at hq'
    exact ⟨a, rfl, (hQ a).1 hq'⟩

/-- **A polynomial-time map of the calculus is a polynomial-time reduction of languages of
codes.** -/
theorem redP_codeLang {α β : Type} [BEnc α] [BDec α] [BEnc β] [BDec β] {Q : α → Prop}
    {R : β → Prop} {f : α → β} (hf : PT f) (hQR : ∀ a, Q a ↔ R (f a)) (b₀ : β) (hb₀ : ¬ R b₀) :
    Cx.RedP (codeLang α Q) (codeLang β R) := by
  let h : List Bool → List Bool := fun y =>
    bif isCode α y then (enc (f (decR y : α × List Bool).1) : List Bool) else enc b₀
  have hh : PT h := PT.cond (pt_isCode α)
    (BDec.pt_encL.comp (hf.comp (PT.fst.comp BDec.pt_decR))) (PT.const _)
  refine ⟨h, polyTimeFun_of_uc (uc_of_pt_list hh), fun x => ?_⟩
  by_cases hc : isCode α x = true
  · obtain ⟨a, rfl⟩ := (isCode_iff _).1 hc
    have : h (enc a) = enc (f a) := by
      simp only [h, hc, cond_true]
      rw [show enc a = enc a ++ [] by simp, BDec.decR_enc]
    rw [this, codeLang_enc, codeLang_enc, hQR]
  · have : h x = enc b₀ := by simp [h, hc]
    rw [this, codeLang_enc]
    constructor
    · rintro ⟨a, rfl, -⟩; exact absurd ((isCode_iff _).2 ⟨a, rfl⟩) hc
    · exact fun h => absurd h hb₀

end PolyDom

end Syn

end HTN
