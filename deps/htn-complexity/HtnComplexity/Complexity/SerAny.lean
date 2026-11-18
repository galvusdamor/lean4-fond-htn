import HtnComplexity.Complexity.SerPos
/-!
# Quantifying over the entries of a serialised list, in polynomial time

`HtnComplexity/Complexity/SerSub.lean` decides one particular question about the entries of
a serialised list — "is some entry of this list missing from that one?" — by the pattern
"quantify over the positions of the code, cut out an entry there, and test it".  The machine of
`ComplexityTheory/Space/Model.lean` needs several such questions, so this file isolates the
pattern itself as a **closure property of Cobham's class**:

    HTN.Syn.anyEntB p y v₁ v₂ v₃  —  does some entry of the serialised list that starts `y`
                                     satisfy `p`?

* `HTN.Syn.anyEntB_iff` — on a serialised list it is what it should be:
  `anyEntB p (blist l ++ z) v₁ v₂ v₃ = true ↔ ∃ w ∈ l, p [true :: bstr w, v₁, v₂, v₃] = true`.
  The entry is handed to `p` in its *encoded* form `true :: bstr w`, which is the form the
  membership test `HTN.Syn.occB` expects, so the tests compose without any re-encoding;
* `HTN.Syn.cobhamB_anyEntB` — if the body is a predicate of Cobham's class, so is the
  quantification, for computed arguments.

The three spectator arguments `v₁, v₂, v₃` are what the body may look at besides the entry; three
is what the transition relation of a planner needs ("the fact is added, or it was there and is
not deleted").
-/

namespace HTN

namespace PTime

/-! ### One more composition helper -/

theorem cobham_c5 {g f₁ f₂ f₃ f₄ f₅ : Fn} (hg : Cobham g) (h₁ : Cobham f₁) (h₂ : Cobham f₂)
    (h₃ : Cobham f₃) (h₄ : Cobham f₄) (h₅ : Cobham f₅) :
    Cobham (compFn g [f₁, f₂, f₃, f₄, f₅]) := by
  refine Cobham.comp hg ?_
  intro h hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅

theorem CobhamB.comp5 {p : Args → Bool} (hp : CobhamB p) {a b c d e : Fn} (ha : Cobham a)
    (hb : Cobham b) (hc : Cobham c) (hd : Cobham d) (he : Cobham e) :
    CobhamB fun args => p [a args, b args, c args, d args, e args] :=
  (cobham_c5 hp ha hb hc hd he).of_eq' fun args => by simp [compFn]

end PTime

namespace Syn

open PTime

/-- The piece of `a` that lies before its suffix `b`. -/
def cutAt (a b : List Bool) : List Bool := a.take (a.length - b.length)

@[simp] theorem cutAt_append (p s : List Bool) : cutAt (p ++ s) s = p := take_compl p s

/-! ### The algorithm -/

/-- The inner test: the piece cut out between the positions `s₃ ⊑ s₂` is a single entry, and it
satisfies the body.  Arguments: `s₃`, `s₂`, `v₁`, `v₂`, `v₃`. -/
def entTest2 (p : Args → Bool) (args : Args) : Bool :=
  entryB (cutAt (args.getD 1 []) (args.getD 0 [])) &&
    p [cutAt (args.getD 1 []) (args.getD 0 []), args.getD 2 [], args.getD 3 [], args.getD 4 []]

/-- The outer test: the piece before `s₂` is a sequence of complete entries, and some position of
`s₂` cuts out an entry satisfying the body.  Arguments: `s₂`, `y`, `v₁`, `v₂`, `v₃`. -/
def entTest1 (p : Args → Bool) (args : Args) : Bool :=
  entriesB (cutAt (args.getD 1 []) (args.getD 0 [])) &&
    anyTailsB (entTest2 p) [args.getD 0 [], args.getD 2 [], args.getD 3 [], args.getD 4 []]
      (args.getD 0 [])

/-- **Does some entry of the serialised list that starts `y` satisfy `p`?** -/
def anyEntB (p : Args → Bool) (y v₁ v₂ v₃ : List Bool) : Bool :=
  anyTailsB (entTest1 p) [y, v₁, v₂, v₃] y

/-! ### Correctness -/

theorem anyEntB_eq_true {p : Args → Bool} {y v₁ v₂ v₃ : List Bool} :
    anyEntB p y v₁ v₂ v₃ = true ↔ ∃ s₂, s₂ <:+ y ∧ entriesB (cutAt y s₂) = true ∧
      ∃ s₃, s₃ <:+ s₂ ∧ entryB (cutAt s₂ s₃) = true ∧
        p [cutAt s₂ s₃, v₁, v₂, v₃] = true := by
  rw [anyEntB, anyTailsB_eq_true]
  constructor
  · rintro ⟨s₂, hs₂, h⟩
    rw [entTest1] at h
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h
    obtain ⟨he, h3⟩ := h
    rw [anyTailsB_eq_true] at h3
    obtain ⟨s₃, hs₃, h3⟩ := h3
    rw [entTest2] at h3
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true] at h3
    exact ⟨s₂, hs₂, he, s₃, hs₃, h3.1, h3.2⟩
  · rintro ⟨s₂, hs₂, he, s₃, hs₃, h1, h2⟩
    refine ⟨s₂, hs₂, ?_⟩
    rw [entTest1]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    refine ⟨he, ?_⟩
    rw [anyTailsB_eq_true]
    refine ⟨s₃, hs₃, ?_⟩
    rw [entTest2]
    simp only [List.getD_cons_zero, List.getD_cons_succ, Bool.and_eq_true]
    exact ⟨h1, h2⟩

/-- **The quantification is over the entries of the serialised list.** -/
theorem anyEntB_iff (p : Args → Bool) (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    anyEntB p (blist l ++ z) v₁ v₂ v₃ = true ↔
      ∃ w ∈ l, p [true :: bstr w, v₁, v₂, v₃] = true := by
  rw [anyEntB_eq_true]
  constructor
  · rintro ⟨s₂, hs₂, he, s₃, hs₃, hent, hp⟩
    obtain ⟨a, ha⟩ := entriesB_iff.1 he
    have hcut₂ : entriesEnc a ++ s₂ = blist l ++ z := by
      rw [← ha, cutAt]
      exact suffix_take_append hs₂
    obtain ⟨l₂, hleq, hs₂eq⟩ := entriesEnc_align a s₂ l z hcut₂
    obtain ⟨w, hw⟩ := entryB_iff.1 hent
    rw [hw] at hp
    have hcut₃ : (true :: bstr w) ++ s₃ = blist l₂ ++ z := by
      rw [← hw, ← hs₂eq, cutAt]
      exact suffix_take_append hs₃
    obtain ⟨l₂', hl₂, -⟩ := entry_split hcut₃
    have hwl : w ∈ l := by
      rw [hleq, hl₂]
      exact List.mem_append_right a List.mem_cons_self
    exact ⟨w, hwl, hp⟩
  · rintro ⟨w, hwl, hp⟩
    obtain ⟨l₁, l₂, hlsplit⟩ := List.append_of_mem hwl
    have hlist : blist l ++ z = entriesEnc l₁ ++ (blist (w :: l₂) ++ z) := by
      rw [hlsplit, blist_append_eq, List.append_assoc]
    have hentry : blist (w :: l₂) ++ z = (true :: bstr w) ++ (blist l₂ ++ z) := by
      rw [blist_cons]
      simp
    refine ⟨blist (w :: l₂) ++ z, ⟨entriesEnc l₁, hlist.symm⟩, ?_,
      blist l₂ ++ z, ⟨true :: bstr w, hentry.symm⟩, ?_, ?_⟩
    · rw [hlist, cutAt_append]
      exact entriesB_iff.2 ⟨l₁, rfl⟩
    · rw [hentry, cutAt_append]
      exact entryB_iff.2 ⟨w, rfl⟩
    · rw [hentry, cutAt_append]
      exact hp

/-! ### The quantification is a closure property of Cobham's class -/

theorem cobham_cutAt10 : Cobham fun args : Args => cutAt (args.getD 1 []) (args.getD 0 []) :=
  (cobham_trunc (Cobham.proj 0) (Cobham.proj 1)).of_eq' fun args => by simp [proj, cutAt]

theorem cobhamB_entTest2 {p : Args → Bool} (hp : CobhamB p) : CobhamB (entTest2 p) :=
  ((cobhamB_entryB cobham_cutAt10).and
    (hp.comp4 cobham_cutAt10 (Cobham.proj 2) (Cobham.proj 3) (Cobham.proj 4))).of_eq
      fun args => by simp [entTest2, proj]

theorem argDep_entTest2 (p : Args → Bool) : ArgDep 5 (entTest2 p) := by
  intro args
  simp only [entTest2, getD_padArgs (by norm_num : (0 : ℕ) < 5),
    getD_padArgs (by norm_num : (1 : ℕ) < 5), getD_padArgs (by norm_num : (2 : ℕ) < 5),
    getD_padArgs (by norm_num : (3 : ℕ) < 5), getD_padArgs (by norm_num : (4 : ℕ) < 5)]

theorem cobhamB_entTest1 {p : Args → Bool} (hp : CobhamB p) : CobhamB (entTest1 p) := by
  have hany := (cobhamB_anyTails (cobhamB_entTest2 hp) (argDep_entTest2 p)).comp5
    (Cobham.proj 0) (Cobham.proj 0) (Cobham.proj 2) (Cobham.proj 3) (Cobham.proj 4)
  exact ((cobhamB_entriesB cobham_cutAt10).and hany).of_eq fun args => by simp [entTest1, proj]

theorem argDep_entTest1 (p : Args → Bool) : ArgDep 5 (entTest1 p) := by
  intro args
  simp only [entTest1, getD_padArgs (by norm_num : (0 : ℕ) < 5),
    getD_padArgs (by norm_num : (1 : ℕ) < 5), getD_padArgs (by norm_num : (2 : ℕ) < 5),
    getD_padArgs (by norm_num : (3 : ℕ) < 5), getD_padArgs (by norm_num : (4 : ℕ) < 5)]

/-- **Quantifying over the entries of a serialised list is a closure property of Cobham's
class**, for computed arguments. -/
theorem cobhamB_anyEntB {p : Args → Bool} (hp : CobhamB p) {a b₁ b₂ b₃ : Fn} (ha : Cobham a)
    (hb₁ : Cobham b₁) (hb₂ : Cobham b₂) (hb₃ : Cobham b₃) :
    CobhamB fun args => anyEntB p (a args) (b₁ args) (b₂ args) (b₃ args) :=
  ((cobhamB_anyTails (cobhamB_entTest1 hp) (argDep_entTest1 p)).comp5 ha ha hb₁ hb₂ hb₃).of_eq
    fun args => by simp [anyEntB]

/-! ### The universal quantification -/

/-- **Does every entry of the serialised list that starts `y` satisfy `p`?** -/
def allEntB (p : Args → Bool) (y v₁ v₂ v₃ : List Bool) : Bool :=
  !anyEntB (fun args => !p args) y v₁ v₂ v₃

theorem allEntB_iff (p : Args → Bool) (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    allEntB p (blist l ++ z) v₁ v₂ v₃ = true ↔
      ∀ w ∈ l, p [true :: bstr w, v₁, v₂, v₃] = true := by
  rw [allEntB, Bool.not_eq_true', ← Bool.not_eq_true, anyEntB_iff]
  push_neg
  simp

/-- **The universal quantification over the entries of a serialised list is a closure property
of Cobham's class**, for computed arguments. -/
theorem cobhamB_allEntB {p : Args → Bool} (hp : CobhamB p) {a b₁ b₂ b₃ : Fn} (ha : Cobham a)
    (hb₁ : Cobham b₁) (hb₂ : Cobham b₂) (hb₃ : Cobham b₃) :
    CobhamB fun args => allEntB p (a args) (b₁ args) (b₂ args) (b₃ args) :=
  (cobhamB_anyEntB hp.not ha hb₁ hb₂ hb₃).not.of_eq fun args => by simp [allEntB]

end Syn

end HTN
