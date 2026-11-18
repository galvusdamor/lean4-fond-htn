import HtnComplexity.Complexity.TOPlan.ReachB
import HtnComplexity.Complexity.TOPlan.Pos
import HtnComplexity.PolyInst.Enum
import HtnComplexity.Space.TestsCobham
/-!
# String toolkit for the verifier of path witnesses

Closure properties of Cobham's class used by the verifier of
`HtnComplexity/AcVerify/Verifier.lean`:

* `HTN.Syn.AcVer.entAny` — quantification over the entries of a serialised list, the body seeing
  the code of the entries *before* the entry, the entry itself and the rest of the string after
  it (`entAny_iff`, `cobhamB_entAny`);
* `HTN.Syn.AcVer.kat` — the `n`-th doubled numeral of an encoded record;
* `HTN.Syn.AcVer.cont` — the content `c` of an encoded entry `true :: bstr c`;
* `HTN.Syn.AcVer.nextEnt` — the encoded entry at the front of a serialised list.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress

/-! ### Quantification over the entries, with prefix and rest -/

/-- **Does some entry of the serialised list that starts `y` satisfy `P`?**  The body reads the
code of the entries before the entry, the encoded entry, and the rest of the string. -/
def entAny (y : List Bool) (P : List Bool → List Bool → List Bool → Bool) : Bool :=
  y.tails.any fun s₂ => entriesB (cutAt y s₂) &&
    s₂.tails.any fun s₃ => entryB (cutAt s₂ s₃) && P (cutAt y s₂) (cutAt s₂ s₃) s₃

/-- The universal form of `entAny`. -/
def entAll (y : List Bool) (P : List Bool → List Bool → List Bool → Bool) : Bool :=
  !entAny y fun a b c => !P a b c

theorem entAny_iff (P : List Bool → List Bool → List Bool → Bool) (l : List (List Bool))
    (z : List Bool) :
    entAny (blist l ++ z) P = true ↔
      ∃ l₁ w l₂, l = l₁ ++ w :: l₂ ∧
        P (entriesEnc l₁) (true :: bstr w) (blist l₂ ++ z) = true := by
  unfold entAny
  simp only [List.any_eq_true, List.mem_tails, Bool.and_eq_true]
  constructor
  · rintro ⟨s₂, hs₂, he, s₃, hs₃, hent, hp⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 he
    have hcut₂ : entriesEnc a ++ s₂ = blist l ++ z := by
      rw [← ha, cutAt]
      exact suffix_take_append hs₂
    obtain ⟨l₂, hleq, hs₂eq⟩ := entriesEnc_align a s₂ l z hcut₂
    obtain ⟨w, hw⟩ := entryB_iff.1 hent
    have hcut₃ : (true :: bstr w) ++ s₃ = blist l₂ ++ z := by
      rw [← hw, ← hs₂eq, cutAt]
      exact suffix_take_append hs₃
    obtain ⟨l₂', hl₂, hs₃eq⟩ := entry_split hcut₃
    refine ⟨a, w, l₂', by rw [hleq, hl₂], ?_⟩
    rw [← ha, ← hw, ← hs₃eq]
    exact hp
  · rintro ⟨l₁, w, l₂, rfl, hp⟩
    have hlist : blist (l₁ ++ w :: l₂) ++ z = entriesEnc l₁ ++ (blist (w :: l₂) ++ z) := by
      rw [blist_append_eq, List.append_assoc]
    have hentry : blist (w :: l₂) ++ z = (true :: bstr w) ++ (blist l₂ ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist (w :: l₂) ++ z, ⟨entriesEnc l₁, hlist.symm⟩, ?_,
      blist l₂ ++ z, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_⟩
    · rw [hlist, cutAt_append]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · rw [hentry, cutAt_append]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hlist, cutAt_append, hentry, cutAt_append]
      exact hp

theorem entAll_iff (P : List Bool → List Bool → List Bool → Bool) (l : List (List Bool))
    (z : List Bool) :
    entAll (blist l ++ z) P = true ↔
      ∀ l₁ w l₂, l = l₁ ++ w :: l₂ →
        P (entriesEnc l₁) (true :: bstr w) (blist l₂ ++ z) = true := by
  rw [entAll, Bool.not_eq_true', ← Bool.not_eq_true, entAny_iff]
  push_neg
  simp

theorem cobham_cutAt {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => cutAt (a args) (b args) :=
  (cobham_cut ha hb).of_eq' fun _ => rfl

theorem cobham_getD_consL {a : Fn} {G : Args → Args} (ha : Cobham a)
    (hG : ∀ i, Cobham fun args => (G args).getD i []) :
    ∀ i, Cobham fun args => (a args :: G args).getD i []
  | 0 => ha.of_eq' fun _ => rfl
  | i + 1 => (hG i).of_eq' fun _ => rfl

theorem cobham_getD_drop (k : ℕ) : ∀ i, Cobham fun args : Args => (args.drop k).getD i [] :=
  fun i => (Cobham.proj (k + i)).of_eq' fun args => by
    simp [proj, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- Substituting three computed strings for the bound variables of a three-variable body. -/
theorem cobhamB_subst3 {P : Args → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB fun a => P (a.drop 3) (a.getD 0 []) (a.getD 1 []) (a.getD 2 []))
    {G : Args → Args} (hG : ∀ i, Cobham fun args => (G args).getD i [])
    {e₁ e₂ e₃ : Fn} (h₁ : Cobham e₁) (h₂ : Cobham e₂) (h₃ : Cobham e₃) :
    CobhamB fun args => P (G args) (e₁ args) (e₂ args) (e₃ args) :=
  (hP.subst (T := fun args => e₁ args :: e₂ args :: e₃ args :: G args)
    (cobham_getD_consL h₁ (cobham_getD_consL h₂ (cobham_getD_consL h₃ hG)))).of_eq
      fun _ => rfl

/-- **The entry quantifier is a closure property of Cobham's class.**  The body sees the prefix,
the entry and the rest as its first three arguments, followed by the ambient arguments. -/
theorem cobhamB_entAny {P : Args → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB fun a => P (a.drop 3) (a.getD 0 []) (a.getD 1 []) (a.getD 2 []))
    {Y : Fn} (hY : Cobham Y) :
    CobhamB fun args => entAny (Y args) (P args) := by
  unfold entAny
  -- inner body: arguments `s₃ :: s₂ :: args`
  have hin : CobhamB fun a : Args =>
      entryB (cutAt (a.getD 1 []) (a.getD 0 [])) &&
        P (a.drop 2) (cutAt (Y (a.drop 2)) (a.getD 1 [])) (cutAt (a.getD 1 []) (a.getD 0 []))
          (a.getD 0 []) := by
    refine (cobhamB_entryB (cobham_cutAt (Cobham.proj 1) (Cobham.proj 0))).and ?_
    exact cobhamB_subst3 hP (cobham_getD_drop 2)
      (cobham_cutAt (cobham_dropArgs hY 2) (Cobham.proj 1))
      (cobham_cutAt (Cobham.proj 1) (Cobham.proj 0)) (Cobham.proj 0)
  -- outer body: arguments `s₂ :: args`
  have hout : CobhamB fun a : Args =>
      entriesB (cutAt (Y a.tail) (a.getD 0 [])) &&
        (a.getD 0 []).tails.any fun s₃ => entryB (cutAt (a.getD 0 []) s₃) &&
          P a.tail (cutAt (Y a.tail) (a.getD 0 [])) (cutAt (a.getD 0 []) s₃) s₃ := by
    refine (cobhamB_entriesB (cobham_cutAt (cobham_tailArgs hY) (Cobham.proj 0))).and ?_
    refine cobhamB_anyTailsF (P := fun a s₃ => entryB (cutAt (a.getD 0 []) s₃) &&
      P a.tail (cutAt (Y a.tail) (a.getD 0 [])) (cutAt (a.getD 0 []) s₃) s₃)
      (hin.of_eq fun a => ?_) (Cobham.proj 0)
    rcases a with _ | ⟨x, _ | ⟨y, a⟩⟩ <;> rfl
  exact (cobhamB_anyTailsF (P := fun args s₂ => entriesB (cutAt (Y args) s₂) &&
    s₂.tails.any fun s₃ => entryB (cutAt s₂ s₃) && P args (cutAt (Y args) s₂) (cutAt s₂ s₃) s₃)
    hout hY).of_eq fun _ => rfl

theorem cobhamB_entAll {P : Args → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB fun a => P (a.drop 3) (a.getD 0 []) (a.getD 1 []) (a.getD 2 []))
    {Y : Fn} (hY : Cobham Y) :
    CobhamB fun args => entAll (Y args) (P args) :=
  (cobhamB_entAny (P := fun args a b c => !P args a b c) hP.not hY).not.of_eq fun _ => rfl

/-! ### Fields of an encoded record -/

/-- Drop the doubled self-delimiting numeral at the front of a string. -/
def kdrop (z : List Bool) : List Bool := z.drop (dpre z).length

/-- **The `n`-th doubled numeral of an encoded record** `true :: key a₀ ++ key a₁ ++ …`. -/
def kat (n : ℕ) (E : List Bool) : List Bool := dpre (kdrop^[n] E.tail)

theorem key_eq (a : ℕ) : key a = dbl (bstr (bitsOfNat a)) := rfl

theorem dpre_key (a : ℕ) (r : List Bool) : dpre (key a ++ r) = key a := by
  rw [key_eq, dpre_dbl_bstr]

theorem kdrop_key (a : ℕ) (r : List Bool) : kdrop (key a ++ r) = r := by
  rw [kdrop, dpre_key, List.drop_left]

@[simp] theorem kat_zero (a : ℕ) (r : List Bool) : kat 0 (true :: (key a ++ r)) = key a := by
  simp [kat, dpre_key]

@[simp] theorem kat_succ (n a : ℕ) (r : List Bool) :
    kat (n + 1) (true :: (key a ++ r)) = kat n (true :: r) := by
  simp [kat, Function.iterate_succ, kdrop_key]

theorem bstr_serNat_append (a : ℕ) (r : List Bool) : bstr (serNat a ++ r) = key a ++ bstr r := by
  rw [bstr_eq_dbl, bstr_eq_dbl, dbl_append, List.append_assoc]; rfl

theorem cobham_kdrop {a : Fn} (ha : Cobham a) : Cobham fun args => kdrop (a args) :=
  (cobham_drop (cobham_dpre ha) ha).of_eq' fun _ => rfl

theorem cobham_iter_kdrop (n : ℕ) {a : Fn} (ha : Cobham a) :
    Cobham fun args => kdrop^[n] (a args) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    exact (cobham_kdrop ih).of_eq' fun args => by rw [Function.iterate_succ_apply']

theorem cobham_kat (n : ℕ) {a : Fn} (ha : Cobham a) : Cobham fun args => kat n (a args) :=
  cobham_dpre (cobham_iter_kdrop n (Space.cobham_tl ha))

/-! ### Entries -/

/-- **The content `c` of an encoded entry `true :: bstr c`.** -/
def cont (E : List Bool) : List Bool := undbl (E.tail.take (E.tail.length - 1))

@[simp] theorem cont_entry (c : List Bool) : cont (true :: bstr c) = c := by
  simp [cont, bstr_eq_dbl, undbl_dbl]

theorem cobham_cont {a : Fn} (ha : Cobham a) : Cobham fun args => cont (a args) :=
  cobham_undbl (Space.cobham_init (Space.cobham_tl ha))

/-- **The encoded entry at the front of a serialised list.** -/
def nextEnt (s : List Bool) : List Bool := true :: bpre s.tail

@[simp] theorem nextEnt_blist (w : List Bool) (l : List (List Bool)) (z : List Bool) :
    nextEnt (blist (w :: l) ++ z) = true :: bstr w := by
  simp [nextEnt, blist_cons, bpre_bstr]

theorem cobham_nextEnt {a : Fn} (ha : Cobham a) : Cobham fun args => nextEnt (a args) :=
  Space.cobham_consT (cobham_bpre (Space.cobham_tl ha))

/-! ### Parsing a leading serialised list -/

theorem findTail_suffix (P : List Bool → Bool) (x : List Bool) : findTail P x <:+ x := by
  unfold findTail
  rcases h : x.tails.find? P with _ | t
  · exact List.nil_suffix
  · exact (List.mem_tails _ _).1 (List.mem_of_find?_eq_some h)

/-- **The string starts with a serialised list** (recognised as the shortest one). -/
def blOK (z : List Bool) : Bool := blistB (cutS z (dropBL z))

theorem blOK_blist (l : List (List Bool)) (r : List Bool) : blOK (blist l ++ r) = true := by
  rw [blOK, dropBL_blist, cutS_append]
  exact blistB_iff.2 ⟨l, rfl⟩

theorem eq_of_blOK {z : List Bool} (h : blOK z = true) : ∃ l, z = blist l ++ dropBL z := by
  obtain ⟨l, hl⟩ := blistB_iff.1 h
  exact ⟨l, by rw [← hl]; exact (cutS_suffix_append (findTail_suffix _ _)).symm⟩

theorem cobhamB_blOK {a : Fn} (ha : Cobham a) : CobhamB fun args => blOK (a args) :=
  cobhamB_blistB (cobham_cut ha (cobham_dropBL ha))

end AcVer

end Syn

end HTN
