import ComplexityTheory.Complexity.Bits
import HtnPlanning.Computable.Syntax
import HtnPlanning.Basic
/-!
# A self-delimiting serialisation of descriptions as bit strings

`HtnComplexity/Complexity/InstPolyTime.lean` measures the running time of a translation of
descriptions in the length of `HTN.Syn.instBits q`, the binary code of the *Gödel number*
`Encodable.encode q`.  That coding is injective and computable, which is all the Karp–Lipton
argument needs of it, but it is a poor measure of the *size* of a description: the encoding of
a list iterates `Nat.pair`, so the code of a list of `n` numbers is of length exponential in
`n`.  Worse, for the same reason it is hopeless to *write down* a concrete translation as a
function of Cobham's class with respect to that coding: doing so would require binary
multiplication and the pairing function inside the class.

This file provides the coding one actually uses when talking about polynomial time on
descriptions: a **direct, self-delimiting serialisation into bits**, whose length is linear in
the number of symbols of the description and the lengths of the binary numerals occurring in
it.

The scheme has two layers:

* `HTN.Syn.bstr x` — a bit string `x` written self-delimitingly: every bit `b` of `x` becomes
  the pair `true, b`, and the string is terminated by `false`.  Length `2 * |x| + 1`;
* `HTN.Syn.blist l` — a list of bit strings: every entry is preceded by `true` and written with
  `bstr`, and the list is terminated by `false`.

Everything else is concatenation: a number is `bstr` of its binary digits, a list of numbers is
`blist` of their digit strings, a pair is the concatenation of its components, and a description
is the concatenation of its five lists.  Concatenation is unambiguous because each layer is
self-delimiting; this is the content of the *parse* lemmas (`HTN.Syn.bstr_parse`,
`HTN.Syn.blist_parse`, …), which say that a serialised object followed by arbitrary junk
determines both the object and the junk.  Injectivity of the serialisation
(`HTN.Syn.instSer_injective`) is the special case of empty junk.

Both the serialisation (`HTN.Syn.computable_instSer`) and, as a consequence of injectivity, its
inverse (`HtnComplexity/Complexity/Coding.lean`) are computable, so this coding can play
the role `instBits` plays for polynomial time, with the advantage that concrete translations can
be exhibited: see `HtnComplexity/Complexity/GuardFamily.lean`.
-/

namespace HTN

namespace Syn

open PTime

/-! ### The two layers -/

@[simp] theorem bstr_nil : bstr [] = [false] := rfl

@[simp] theorem bstr_cons (b : Bool) (x : List Bool) : bstr (b :: x) = true :: b :: bstr x := rfl

@[simp] theorem blist_nil : blist [] = [false] := rfl

@[simp] theorem blist_cons (x : List Bool) (l : List (List Bool)) :
    blist (x :: l) = true :: (bstr x ++ blist l) := rfl

/-! ### The parse lemmas -/

/-- A self-delimiting bit string followed by junk determines both. -/
theorem bstr_parse : ∀ {x y r s : List Bool}, bstr x ++ r = bstr y ++ s → x = y ∧ r = s := by
  intro x
  induction x with
  | nil =>
    intro y r s h
    cases y with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons c y => simp at h
  | cons b x ih =>
    intro y r s h
    cases y with
    | nil => simp at h
    | cons c y =>
      simp only [bstr_cons, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hbc, hrest⟩ := h
      obtain ⟨hxy, hrs⟩ := ih hrest
      exact ⟨by rw [hbc, hxy], hrs⟩

/-- A self-delimiting list of bit strings followed by junk determines both. -/
theorem blist_parse : ∀ {l l' : List (List Bool)} {r s : List Bool},
    blist l ++ r = blist l' ++ s → l = l' ∧ r = s := by
  intro l
  induction l with
  | nil =>
    intro l' r s h
    cases l' with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons y l' => simp at h
  | cons x l ih =>
    intro l' r s h
    cases l' with
    | nil => simp at h
    | cons y l' =>
      simp only [blist_cons, List.cons_append, List.cons.injEq, List.append_assoc,
        true_and] at h
      obtain ⟨hxy, hrest⟩ := bstr_parse h
      obtain ⟨hll, hrs⟩ := ih hrest
      exact ⟨by rw [hxy, hll], hrs⟩

/-! ### Numbers, lists, pairs -/

theorem serNat_parse {n m : ℕ} {r s : List Bool} (h : serNat n ++ r = serNat m ++ s) :
    n = m ∧ r = s := by
  obtain ⟨hb, hrs⟩ := bstr_parse h
  exact ⟨bitsOfNat_injective hb, hrs⟩

theorem serNatList_parse {l l' : List ℕ} {r s : List Bool}
    (h : serNatList l ++ r = serNatList l' ++ s) : l = l' ∧ r = s := by
  obtain ⟨hm, hrs⟩ := blist_parse h
  exact ⟨List.map_injective_iff.2 bitsOfNat_injective hm, hrs⟩

theorem serPair_injective : Function.Injective serPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [serPair] at h
  obtain ⟨hac, h2⟩ := serNat_parse (r := serNat b) (s := serNat d) h
  obtain ⟨hbd, -⟩ :=
    serNat_parse (r := ([] : List Bool)) (s := ([] : List Bool)) (by simpa using h2)
  simp [hac, hbd]

theorem serPairList_parse {l l' : List (ℕ × ℕ)} {r s : List Bool}
    (h : serPairList l ++ r = serPairList l' ++ s) : l = l' ∧ r = s := by
  obtain ⟨hm, hrs⟩ := blist_parse h
  exact ⟨List.map_injective_iff.2 serPair_injective hm, hrs⟩

theorem serLbl_injective : Function.Injective serLbl := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [serLbl] at h
  obtain ⟨haa, h2⟩ := serNat_parse (r := b :: serNat c) (s := b' :: serNat c') h
  simp only [List.cons.injEq] at h2
  obtain ⟨hbb, hcc⟩ := h2
  obtain ⟨hcc', -⟩ := serNat_parse (r := ([] : List Bool)) (s := ([] : List Bool)) (by simpa using hcc)
  simp [haa, hbb, hcc']

theorem serLblList_parse {l l' : List (ℕ × Bool × ℕ)} {r s : List Bool}
    (h : serLblList l ++ r = serLblList l' ++ s) : l = l' ∧ r = s := by
  obtain ⟨hm, hrs⟩ := blist_parse h
  exact ⟨List.map_injective_iff.2 serLbl_injective hm, hrs⟩

/-! ### Task networks and instance descriptions -/

theorem tnSer_parse {t t' : TnDesc} {r s : List Bool} (h : tnSer t ++ r = tnSer t' ++ s) :
    t = t' ∧ r = s := by
  obtain ⟨t1, t2, t3⟩ := t
  obtain ⟨t1', t2', t3'⟩ := t'
  simp only [tnSer, TnDesc.ids, TnDesc.ordList, TnDesc.lbl, List.append_assoc] at h
  obtain ⟨h1, h⟩ := serNatList_parse h
  obtain ⟨h2, h⟩ := serPairList_parse h
  obtain ⟨h3, h⟩ := serLblList_parse h
  exact ⟨by simp [h1, h2, h3], h⟩

theorem instSer_parse {q q' : InstDesc} {r s : List Bool} (h : instSer q ++ r = instSer q' ++ s) :
    q = q' ∧ r = s := by
  obtain ⟨i, g, t⟩ := q
  obtain ⟨i', g', t'⟩ := q'
  simp only [instSer, InstDesc.initList, InstDesc.goalList, InstDesc.tnI,
    List.append_assoc] at h
  obtain ⟨h1, h⟩ := serNatList_parse h
  obtain ⟨h2, h⟩ := serNatList_parse h
  obtain ⟨h3, h⟩ := tnSer_parse h
  exact ⟨by simp [h1, h2, h3], h⟩

/-- **The serialisation is injective.** -/
theorem instSer_injective : Function.Injective instSer := by
  intro q q' h
  exact (instSer_parse (r := []) (s := []) (by simpa using h)).1

/-! ### The serialisation is computable -/

theorem primrec_bstr : Primrec bstr :=
  Primrec.list_foldr (f := fun x : List Bool => x) (g := fun _ => [false])
    (h := fun _ p => true :: p.1 :: p.2) Primrec.id (Primrec.const [false])
    (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_blist : Primrec blist :=
  Primrec.list_foldr (f := fun l : List (List Bool) => l) (g := fun _ => [false])
    (h := fun _ p => true :: (bstr p.1 ++ p.2)) Primrec.id (Primrec.const [false])
    (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_append.comp (primrec_bstr.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_serNat : Primrec serNat := primrec_bstr.comp primrec_bitsOfNat

theorem primrec_serNatList : Primrec serNatList :=
  primrec_blist.comp (Primrec.list_map Primrec.id (primrec_bitsOfNat.comp Primrec.snd).to₂)

theorem primrec_serPair : Primrec serPair :=
  Primrec.list_append.comp (primrec_serNat.comp Primrec.fst) (primrec_serNat.comp Primrec.snd)

theorem primrec_serPairList : Primrec serPairList :=
  primrec_blist.comp (Primrec.list_map Primrec.id (primrec_serPair.comp Primrec.snd).to₂)

theorem primrec_serLbl : Primrec serLbl :=
  Primrec.list_append.comp (primrec_serNat.comp Primrec.fst)
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (primrec_serNat.comp (Primrec.snd.comp Primrec.snd)))

theorem primrec_serLblList : Primrec serLblList :=
  primrec_blist.comp (Primrec.list_map Primrec.id (primrec_serLbl.comp Primrec.snd).to₂)

theorem primrec_tnSer : Primrec tnSer := by
  have h : Primrec fun t : TnDesc => serNatList t.1 ++ (serPairList t.2.1 ++ serLblList t.2.2) :=
    Primrec.list_append.comp (primrec_serNatList.comp Primrec.fst)
      (Primrec.list_append.comp (primrec_serPairList.comp (Primrec.fst.comp Primrec.snd))
        (primrec_serLblList.comp (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun t => by
    simp [tnSer, TnDesc.ids, TnDesc.ordList, TnDesc.lbl, List.append_assoc]

/-- **The serialisation is primitive recursive.** -/
theorem primrec_instSer : Primrec instSer := by
  have h : Primrec fun q : InstDesc => serNatList q.1 ++ (serNatList q.2.1 ++ tnSer q.2.2) :=
    Primrec.list_append.comp (primrec_serNatList.comp Primrec.fst)
      (Primrec.list_append.comp (primrec_serNatList.comp (Primrec.fst.comp Primrec.snd))
        (primrec_tnSer.comp (Primrec.snd.comp Primrec.snd)))
  exact h.of_eq fun q => by
    simp [instSer, InstDesc.initList, InstDesc.goalList, InstDesc.tnI, List.append_assoc]

/-- **The serialisation is computable.** -/
theorem computable_instSer : Computable instSer := primrec_instSer.to_comp

/-! ### The length of the serialisation

The serialisation is short: a list of `k` numbers with at most `d` binary digits each takes
`2 + k * (2 * d + 2)` bits, so the length of `instSer q` is linear in the number of symbols of
`q` (`HTN.Syn.InstDesc.size`) once the numerals occurring in `q` are bounded — in contrast with
`HTN.Syn.instBits`, whose length is *exponential* in the number of symbols.  The two lemmas
below are the base cases of that count; they are what the concrete family of
`HtnComplexity/Complexity/GuardFamily.lean` needs. -/

@[simp] theorem length_bstr (x : List Bool) : (bstr x).length = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [bstr_cons, ih]; omega

theorem length_blist (l : List (List Bool)) :
    (blist l).length = 1 + (l.map fun x => 2 * x.length + 2).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [blist_cons, ih, length_bstr]; omega

end Syn

end HTN
