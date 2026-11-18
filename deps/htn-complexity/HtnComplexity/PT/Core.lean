import HtnComplexity.Compress.ProfileCobham
import HtnComplexity.Complexity.TOPlan.Pos
import HtnComplexity.Complexity.TOPlan.Kit
import HtnComplexity.PolyInst.Kit
import HtnComplexity.PolyInst.Labels
import HtnComplexity.PolyInst.Compare
import HtnComplexity.Complexity.Serial
import ComplexityTheory.Complexity.CobhamString
import ComplexityTheory.Complexity.CobhamExamples
/-!
# A typed calculus of polynomial-time functions

To prove that a translation of descriptions runs in polynomial time one would like to argue as
for primitive recursion (`Primrec`): build the function from pairs, projections, list maps,
filters, folds, arithmetic, … and conclude.  This file sets up such a calculus on top of
Cobham's class (`HTN.PTime.Cobham`, which is polynomial time by
`HTN.PTime.PolyTimeFun.of_cobham`):

* `HTN.Syn.PolyDom.BEnc α` — a **self-delimiting bit encoding** of a type: an injective map
  `enc : α → List Bool` together with a function of Cobham's class `skip` that removes one
  encoded value from the front of a string (`skip (enc a ++ r) = r`).  Instances: `ℕ` (the
  self-delimiting binary numeral `serNat`), `Bool`, `Unit`, products (concatenation), lists
  (the self-delimiting list `blist` of the entries), `Option` and `Sum` (a tag bit);
* `HTN.Syn.PolyDom.PT f` — `f` acts on the encodings as a unary function of Cobham's class;
* the basic closure properties: identity, constants, composition, pairing, projections,
  conditionals, equality tests, the list constructors and destructors.

The list combinators and the bounded fold are in `HtnComplexity/PT/List.lean`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime Compress TOPlan PolyInst

/-- A unary function of the class, composed with a function of the class. -/
theorem cobham_un {G : List Bool → List Bool} (hG : Cobham fun args => G (args.getD 0 []))
    {a : Fn} (ha : Cobham a) : Cobham fun args => G (a args) :=
  (cobham_c1 hG ha).of_eq' fun args => by simp [compFn]

/-! ### Unary functions of the class -/

/-- A unary function on bit strings of Cobham's class. -/
def UC (F : List Bool → List Bool) : Prop := Cobham fun args => F (args.getD 0 [])

theorem UC.app {F : List Bool → List Bool} (hF : UC F) {a : Fn} (ha : Cobham a) :
    Cobham fun args => F (a args) := cobham_un hF ha

theorem UC.comp {F G : List Bool → List Bool} (hF : UC F) (hG : UC G) : UC fun x => F (G x) :=
  hF.app hG

theorem uc_id : UC fun x => x := cobham_var0

theorem uc_const (y : List Bool) : UC fun _ => y := cobham_const y

theorem UC.of_eq {F G : List Bool → List Bool} (hF : UC F) (h : ∀ x, F x = G x) : UC G :=
  Cobham.of_eq' hF fun args => h _

theorem cobham_tail' {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).tail :=
  (cobham_drop (cobham_const [false]) ha).of_eq' fun args => by simp

/-! ### Self-delimiting encodings -/

/-- **A self-delimiting bit encoding of a type**: an injective encoding together with a function
of Cobham's class that removes one encoded value from the front of a string. -/
class BEnc (α : Type) where
  /-- The encoding. -/
  enc : α → List Bool
  /-- Removing one encoded value from the front of a string. -/
  skip : List Bool → List Bool
  skip_enc : ∀ a r, skip (enc a ++ r) = r
  uc_skip : UC skip
  inj : Function.Injective enc

export BEnc (enc)

variable {α β γ δ ε : Type} [BEnc α] [BEnc β] [BEnc γ] [BEnc δ] [BEnc ε]

/-- The encoded value at the front of a string. -/
def front (α : Type) [BEnc α] (x : List Bool) : List Bool := cutS x (BEnc.skip α x)

theorem front_enc (a : α) (r : List Bool) : front α (enc a ++ r) = enc a := by
  rw [front, BEnc.skip_enc, cutS_append]

theorem front_enc' (a : α) : front α (enc a) = enc a := by
  simpa using front_enc a []

theorem skip_enc' (a : α) : BEnc.skip α (enc a) = [] := by
  simpa using BEnc.skip_enc a []

theorem uc_front : UC (front α) := cobham_cut cobham_var0 BEnc.uc_skip

/-! ### Instances -/

/-- Natural numbers: the self-delimiting binary numeral. -/
instance : BEnc ℕ where
  enc := serNat
  skip x := x.drop (bpre x).length
  skip_enc n r := by
    simp only [serNat]
    rw [bpre_bstr]
    simp
  uc_skip := cobham_drop (cobham_bpre cobham_var0) cobham_var0
  inj m n h := (serNat_parse (r := []) (s := []) (by simpa using h)).1

theorem enc_nat (n : ℕ) : enc n = serNat n := rfl

/-- Booleans: one bit. -/
instance : BEnc Bool where
  enc b := [b]
  skip x := x.tail
  skip_enc _ _ := rfl
  uc_skip := cobham_tail' cobham_var0
  inj a b h := by simpa using h

theorem enc_bool (b : Bool) : enc b = [b] := rfl

/-- The unit type: the empty string. -/
instance : BEnc Unit where
  enc _ := []
  skip x := x
  skip_enc _ _ := rfl
  uc_skip := cobham_var0
  inj a b _ := rfl

/-- Products: concatenation. -/
instance : BEnc (α × β) where
  enc p := enc p.1 ++ enc p.2
  skip x := BEnc.skip β (BEnc.skip α x)
  skip_enc p r := by
    rw [List.append_assoc, BEnc.skip_enc, BEnc.skip_enc]
  uc_skip := BEnc.uc_skip.comp BEnc.uc_skip
  inj p q h := by
    replace h : enc p.1 ++ enc p.2 = enc q.1 ++ enc q.2 := h
    have h1 := congrArg (BEnc.skip α) h
    rw [BEnc.skip_enc, BEnc.skip_enc] at h1
    have h0 : enc p.1 = enc q.1 := by
      have := h; rw [h1] at this; exact List.append_cancel_right this
    exact Prod.ext (BEnc.inj h0) (BEnc.inj h1)

theorem enc_prod (a : α) (b : β) : enc (a, b) = enc a ++ enc b := rfl

/-- Lists: the self-delimiting list of the encodings of the entries. -/
instance : BEnc (List α) where
  enc l := blist (l.map enc)
  skip x := dropBL x
  skip_enc l r := dropBL_blist _ r
  uc_skip := cobham_dropBL cobham_var0
  inj l l' h := List.map_injective_iff.2 BEnc.inj
    (blist_parse (r := []) (s := []) (by simpa using h)).1

theorem enc_list (l : List α) : enc l = blist (l.map enc) := rfl

theorem enc_nil : enc ([] : List α) = [false] := rfl

theorem enc_cons (a : α) (l : List α) : enc (a :: l) = true :: (bstr (enc a) ++ enc l) := rfl

/-- The tagged skip: on a leading `false` skip with `F`, on a leading `true` with `G`. -/
def tagSkip (F G : List Bool → List Bool) (x : List Bool) : List Bool :=
  if x.headD false = true then G x.tail else F x.tail

theorem uc_tagSkip {F G : List Bool → List Bool} (hF : UC F) (hG : UC G) : UC (tagSkip F G) :=
  (cobham_iteB (cobhamB_head cobham_var0) (hG.app (cobham_tail' cobham_var0))
    (hF.app (cobham_tail' cobham_var0))).of_eq' fun args => by simp [tagSkip]

/-- Options: a tag bit, then the value. -/
instance : BEnc (Option α) where
  enc o := match o with
    | none => [false]
    | some a => true :: enc a
  skip := tagSkip id (BEnc.skip α)
  skip_enc o r := by cases o <;> simp [tagSkip, BEnc.skip_enc]
  uc_skip := uc_tagSkip uc_id BEnc.uc_skip
  inj o o' h := by
    cases o <;> cases o' <;> simp at h ⊢
    exact BEnc.inj h

theorem enc_none : enc (none : Option α) = [false] := rfl

theorem enc_some (a : α) : enc (some a) = true :: enc a := rfl

/-- Sums: a tag bit, then the value. -/
instance : BEnc (α ⊕ β) where
  enc s := match s with
    | Sum.inl a => false :: enc a
    | Sum.inr b => true :: enc b
  skip := tagSkip (BEnc.skip α) (BEnc.skip β)
  skip_enc s r := by cases s <;> simp [tagSkip, BEnc.skip_enc]
  uc_skip := uc_tagSkip BEnc.uc_skip BEnc.uc_skip
  inj s s' h := by
    cases s <;> cases s' <;> simp at h ⊢
    · exact BEnc.inj h
    · exact BEnc.inj h

theorem enc_inl (a : α) : enc (Sum.inl a : α ⊕ β) = false :: enc a := rfl

theorem enc_inr (b : β) : enc (Sum.inr b : α ⊕ β) = true :: enc b := rfl

/-! ### Polynomial-time functions -/

/-- **A polynomial-time function between encoded types**: it acts on the encodings as a unary
function of Cobham's class. -/
def PT (f : α → β) : Prop := ∃ F : List Bool → List Bool, UC F ∧ ∀ a, F (enc a) = enc (f a)

/-- A polynomial-time function of two arguments. -/
def PT₂ (f : α → β → γ) : Prop := PT fun p : α × β => f p.1 p.2

theorem PT.of_eq {f g : α → β} (hf : PT f) (h : ∀ a, f a = g a) : PT g := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨F, hF, fun a => by beta_reduce; rw [hFf, h]⟩

theorem PT.id : PT fun a : α => a := ⟨fun x => x, uc_id, fun _ => rfl⟩

theorem PT.const (b : β) : PT fun _ : α => b := ⟨fun _ => enc b, uc_const _, fun _ => rfl⟩

theorem PT.comp {f : α → β} {g : β → γ} (hg : PT g) (hf : PT f) : PT fun a => g (f a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨fun x => G (F x), hG.comp hF, fun a => by beta_reduce; rw [hFf, hGg]⟩

theorem PT.pair {f : α → β} {g : α → γ} (hf : PT f) (hg : PT g) :
    PT fun a => (f a, g a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨fun x => F x ++ G x, PH.cobham_app hF hG, fun a => by beta_reduce; rw [hFf, hGg]; rfl⟩

theorem PT.fst : PT fun p : α × β => p.1 :=
  ⟨front α, uc_front, fun p => by rw [enc_prod, front_enc]⟩

theorem PT.snd : PT fun p : α × β => p.2 :=
  ⟨BEnc.skip α, BEnc.uc_skip, fun p => by rw [enc_prod, BEnc.skip_enc]⟩

theorem PT.comp₂ {f : α → β} {g : α → γ} {h : β → γ → δ} (hh : PT₂ h) (hf : PT f) (hg : PT g) :
    PT fun a => h (f a) (g a) :=
  (hh.comp (hf.pair hg)).of_eq fun _ => rfl

theorem PT.fst' {f : α → β × γ} (hf : PT f) : PT fun a => (f a).1 := PT.fst.comp hf

theorem PT.snd' {f : α → β × γ} (hf : PT f) : PT fun a => (f a).2 := PT.snd.comp hf

/-! ### Conditionals and equality -/

theorem PT.cond {c : α → Bool} {f g : α → β} (hc : PT c) (hf : PT f) (hg : PT g) :
    PT fun a => bif c a then f a else g a := by
  obtain ⟨C, hC, hCc⟩ := hc
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => if (C x).headD false = true then F x else G x,
    cobham_iteB (cobhamB_head hC) hF hG, fun a => ?_⟩
  simp only [hCc, enc_bool, List.headD_cons, hFf, hGg]
  cases c a <;> rfl

theorem PT.ite {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : PT fun a => decide (p a)) (hf : PT f) (hg : PT g) :
    PT fun a => if p a then f a else g a :=
  (PT.cond hp hf hg).of_eq fun a => by by_cases h : p a <;> simp [h]

theorem PT.not {c : α → Bool} (hc : PT c) : PT fun a => !c a :=
  (PT.cond hc (PT.const false) (PT.const true)).of_eq fun a => by cases c a <;> rfl

theorem PT.and {c d : α → Bool} (hc : PT c) (hd : PT d) : PT fun a => c a && d a :=
  (PT.cond hc hd (PT.const false)).of_eq fun a => by cases c a <;> rfl

theorem PT.or {c d : α → Bool} (hc : PT c) (hd : PT d) : PT fun a => c a || d a :=
  (PT.cond hc (PT.const true) hd).of_eq fun a => by cases c a <;> rfl

/-- **Equality is decidable in polynomial time**: the two codes are compared. -/
theorem PT.eq [DecidableEq β] {f g : α → β} (hf : PT f) (hg : PT g) :
    PT fun a => decide (f a = g a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => [decide (F x = G x)], cobhamB_eqStr hF hG, fun a => ?_⟩
  beta_reduce
  rw [hFf, hGg, enc_bool]
  congr 1
  exact decide_eq_decide.2 ⟨fun h => BEnc.inj h, fun h => by rw [h]⟩

theorem PT.beq [DecidableEq β] {f g : α → β} (hf : PT f) (hg : PT g) :
    PT fun a => (f a == g a) :=
  (PT.eq hf hg).of_eq fun a => (beq_eq_decide _ _).symm

/-! ### Constructors and destructors of lists -/

theorem PT.cons {f : α → β} {g : α → List β} (hf : PT f) (hg : PT g) :
    PT fun a => f a :: g a := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  exact ⟨fun x => true :: (bstr (F x) ++ G x), cobham_consTrue (PH.cobham_app (cobham_bstr hF) hG),
    fun a => by beta_reduce; rw [hFf, hGg, enc_cons]⟩

theorem PT.nil : PT fun _ : α => ([] : List β) := PT.const []

/-- The test for the empty list. -/
theorem PT.isEmpty {f : α → List β} (hf : PT f) : PT fun a => (f a).isEmpty := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => [!(F x).headD false], (cobhamB_head hF).not, fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases f a <;> rfl

/-- The content of the first entry of a serialised list. -/
def headCode (x : List Bool) : List Bool := undbl (bpre x.tail)

/-- The rest of a serialised list after its first entry. -/
def tailCode (x : List Bool) : List Bool := x.tail.drop (bpre x.tail).length

theorem headCode_cons (a : α) (l : List α) : headCode (enc (a :: l)) = enc a := by
  rw [enc_cons, headCode, List.tail_cons, bpre_bstr, undbl_bstr]

theorem tailCode_cons (a : α) (l : List α) : tailCode (enc (a :: l)) = enc l := by
  rw [enc_cons, tailCode, List.tail_cons, bpre_bstr]
  simp

theorem uc_headCode : UC headCode :=
  (cobham_undbl (cobham_bpre (cobham_tail' cobham_var0))).of_eq' fun args => by simp [headCode]

theorem uc_tailCode : UC tailCode :=
  (cobham_drop (cobham_bpre (cobham_tail' cobham_var0)) (cobham_tail' cobham_var0)).of_eq'
    fun args => by simp [tailCode]

theorem PT.headI [Inhabited β] {f : α → List β} (hf : PT f) : PT fun a => (f a).headI := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => if (F x).headD false = true then headCode (F x) else enc (default : β),
    cobham_iteB (cobhamB_head hF) (uc_headCode.app hF) (cobham_const _), fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases h : f a with
  | nil => rfl
  | cons b l => simpa using headCode_cons b l

theorem PT.tail {f : α → List β} (hf : PT f) : PT fun a => (f a).tail := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => if (F x).headD false = true then tailCode (F x) else F x,
    cobham_iteB (cobhamB_head hF) (uc_tailCode.app hF) hF, fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases h : f a with
  | nil => rfl
  | cons b l => simpa using tailCode_cons b l

/-! ### Options and sums -/

theorem PT.some {f : α → β} (hf : PT f) : PT fun a => some (f a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨fun x => true :: F x, cobham_consTrue hF, fun a => by beta_reduce; rw [hFf]; rfl⟩

theorem PT.inl {f : α → β} (hf : PT f) : PT fun a => (Sum.inl (f a) : β ⊕ γ) := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => false :: F x, ?_, fun a => by beta_reduce; rw [hFf]; rfl⟩
  exact (cobham_c1 (Cobham.cons false) hF).of_eq' fun args => by simp [compFn, consFn]

theorem PT.inr {f : α → γ} (hf : PT f) : PT fun a => (Sum.inr (f a) : β ⊕ γ) := by
  obtain ⟨F, hF, hFf⟩ := hf
  exact ⟨fun x => true :: F x, cobham_consTrue hF, fun a => by beta_reduce; rw [hFf]; rfl⟩

theorem PT.isSome {f : α → Option β} (hf : PT f) : PT fun a => (f a).isSome := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => [(F x).headD false], cobhamB_head hF, fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases f a <;> rfl

theorem PT.getD {f : α → Option β} {g : α → β} (hf : PT f) (hg : PT g) :
    PT fun a => (f a).getD (g a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  refine ⟨fun x => if (F x).headD false = true then (F x).tail else G x,
    cobham_iteB (cobhamB_head hF) (cobham_tail' hF) hG, fun a => ?_⟩
  beta_reduce
  rw [hFf, hGg]
  cases f a <;> rfl

theorem PT.isLeft {f : α → β ⊕ γ} (hf : PT f) : PT fun a => (f a).isLeft := by
  obtain ⟨F, hF, hFf⟩ := hf
  refine ⟨fun x => [!(F x).headD false], (cobhamB_head hF).not, fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases f a <;> rfl

theorem PT.sumElim {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} (hf : PT f) (hg : PT₂ g)
    (hh : PT₂ h) : PT fun a => Sum.elim (g a) (h a) (f a) := by
  obtain ⟨F, hF, hFf⟩ := hf
  obtain ⟨G, hG, hGg⟩ := hg
  obtain ⟨H, hH, hHh⟩ := hh
  have ht : Cobham fun args : Args => (F (args.getD 0 [])).tail := cobham_tail' hF
  refine ⟨fun x => if (F x).headD false = true then H (x ++ (F x).tail) else G (x ++ (F x).tail),
    cobham_iteB (cobhamB_head hF) (hH.app (PH.cobham_app cobham_var0 ht))
      (hG.app (PH.cobham_app cobham_var0 ht)), fun a => ?_⟩
  beta_reduce
  rw [hFf]
  cases hfa : f a with
  | inl b => simpa [enc_inl] using hGg (a, b)
  | inr c => simpa [enc_inr] using hHh (a, c)

end PolyDom

end Syn

end HTN
