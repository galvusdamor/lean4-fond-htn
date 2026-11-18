import HtnComplexity.Space.SeqWitness
import HtnComplexity.Space.InstTests
/-!
# The concrete encodings of the sequencing gadget

`HtnComplexity/Space/SeqGadget.lean` leaves the encodings of the gadget's facts, actions and
compound task as parameters (`HTN.Syn.SeqG.Code`).  The machine of step A3 of `TABLE4-PLAN.md`
reads the compiled initial state of the gadget instance off the code of the original instance,
so the numerals of the gadget's facts must be **bit strings a test can take apart**.  This file
fixes them.

* A fact `v` of the instance becomes `ρ v = 2 v + 1`, whose numeral is `true :: bits v`; after the
  compiled renaming `4 · + 2` it is `[false, true, true] ++ bits v`.
* A gadget fact `g` becomes `gf g`, whose numeral is `false :: gbits g`; compiled, it is
  `[false, true, false] ++ gbits g`.  The string `gbits g` is a three-bit kind tag followed by the
  data, positions being written in **unary** (`false ^ p ++ [true]`), identifiers and names in
  the self-delimiting form `bstr (bits ·)` in which the code of an instance writes them.
* The gadget's actions get names above every primitive name the domain mentions, and the fresh
  compound task is the **least** name the domain does not mention, so that it is small.

The main results are `HTN.Space.SeqM.code_fresh` (the encodings are fresh for the domain) and the
bit-level lemmas `HTN.Space.SeqM.bits_cfact_inst`, `HTN.Space.SeqM.bits_cfact_gad`.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### Bit strings -/

/-- A position, in unary. -/
def unary (p : ℕ) : List Bool := List.replicate p false ++ [true]

/-- A task, as the part of a label that follows the identifier. -/
def lblBits : ℕ ⊕ ℕ → List Bool
  | Sum.inl a => false :: serNat a
  | Sum.inr c => true :: serNat c

/-- **The bit string of a gadget fact**: a kind tag, then the data. -/
def gbits : GF → List Bool
  | .cur p => [false, false, false] ++ unary p
  | .len p => [true, false, false] ++ unary p
  | .nop p => [false, true, false] ++ unary p
  | .fin => [true, true, false, true]
  | .lab p x => [false, false, true] ++ unary p ++ lblBits x ++ [true]
  | .wit p a => [true, false, true] ++ unary p ++ serNat a ++ [true]

theorem unary_parse {p p' : ℕ} {r s : List Bool} (h : unary p ++ r = unary p' ++ s) :
    p = p' ∧ r = s := by
  induction p generalizing p' with
  | zero =>
    cases p' with
    | zero => simpa [unary] using h
    | succ p' => simp [unary, List.replicate_succ] at h
  | succ p ih =>
    cases p' with
    | zero => simp [unary, List.replicate_succ] at h
    | succ p' =>
      simp only [unary, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih (by simpa [unary] using h)
      exact ⟨by rw [h1], h2⟩

theorem lblBits_parse {x x' : ℕ ⊕ ℕ} {r s : List Bool} (h : lblBits x ++ r = lblBits x' ++ s) :
    x = x' ∧ r = s := by
  cases x <;> cases x' <;> simp only [lblBits, List.cons_append, List.cons.injEq,
    Bool.false_eq_true, Bool.true_eq_false, false_and, true_and] at h ⊢ <;>
    exact (fun h' => ⟨by rw [h'.1], h'.2⟩) (serNat_parse h)

theorem gbits_ne_nil (g : GF) : gbits g ≠ [] := by
  cases g <;> simp [gbits]

theorem gbits_eq_concat (g : GF) : ∃ l, gbits g = l ++ [true] := by
  cases g with
  | cur p => exact ⟨[false, false, false] ++ List.replicate p false, by simp [gbits, unary]⟩
  | len p => exact ⟨[true, false, false] ++ List.replicate p false, by simp [gbits, unary]⟩
  | nop p => exact ⟨[false, true, false] ++ List.replicate p false, by simp [gbits, unary]⟩
  | fin => exact ⟨[true, true, false], rfl⟩
  | lab p x => exact ⟨[false, false, true] ++ unary p ++ lblBits x, by simp [gbits]⟩
  | wit p a => exact ⟨[true, false, true] ++ unary p ++ serNat a, by simp [gbits]⟩

theorem getLast_gbits (g : GF) : (gbits g).getLast? = some true := by
  obtain ⟨l, hl⟩ := gbits_eq_concat g
  rw [hl, List.getLast?_concat]

theorem gbits_injective : Function.Injective gbits := by
  intro g g' h
  cases g <;> cases g' <;> simp only [gbits, List.cons_append, List.nil_append,
    List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and, true_and,
    and_false, GF.cur.injEq, GF.len.injEq, GF.nop.injEq, GF.lab.injEq,
    GF.wit.injEq] at h ⊢
  · exact (unary_parse (r := []) (s := []) (by simpa using h)).1
  · exact (unary_parse (r := []) (s := []) (by simpa using h)).1
  · obtain ⟨hp, h⟩ := unary_parse (r := lblBits _ ++ [true]) (s := lblBits _ ++ [true])
      (by simpa [List.append_assoc] using h)
    exact ⟨hp, (lblBits_parse (r := [true]) (s := [true]) h).1⟩
  · exact (unary_parse (r := []) (s := []) (by simpa using h)).1
  · obtain ⟨hp, h⟩ := unary_parse (r := serNat _ ++ [true]) (s := serNat _ ++ [true])
      (by simpa [List.append_assoc] using h)
    exact ⟨hp, (serNat_parse (r := [true]) (s := [true]) h).1⟩

/-! ### The numerals -/

theorem bitsOfNat_two_mul_add_one (v : ℕ) : bitsOfNat (2 * v + 1) = true :: bitsOfNat v := by
  rw [bitsOfNat_succ]
  simp [Nat.mul_add_div]

theorem bitsOfNat_two_mul {n : ℕ} (hn : n ≠ 0) : bitsOfNat (2 * n) = false :: bitsOfNat n := by
  rw [bitsOfNat_eq_ite, if_neg (by omega)]
  simp

/-- The numeral of a gadget fact: its bit string is `false :: gbits g`. -/
def gfNum (g : GF) : ℕ := 2 * natOfBits (gbits g)

theorem isCanon_gbits (g : GF) : IsCanon (gbits g) :=
  isCanon_of_getLast (Or.inr (getLast_gbits g))

theorem bitsOfNat_gfNum (g : GF) : bitsOfNat (gfNum g) = false :: gbits g := by
  rw [gfNum, bitsOfNat_two_mul (natOfBits_ne_zero_of_isCanon (isCanon_gbits g) (gbits_ne_nil g)),
    isCanon_gbits g]

theorem gfNum_injective : Function.Injective gfNum := by
  intro g g' h
  have := congrArg bitsOfNat h
  rw [bitsOfNat_gfNum, bitsOfNat_gfNum, List.cons.injEq] at this
  exact gbits_injective this.2

/-- The gadget fact that shares the data of a gadget action (used to name the actions). -/
def gaFact : GA → GF
  | .pick p x => .lab p x
  | .skip p => .nop p
  | .stop p => .len p

theorem gaFact_injective : Function.Injective gaFact := by
  intro g g' h
  cases g <;> cases g' <;> simp_all [gaFact]

/-- The names of the gadget's actions: above every primitive name the domain mentions. -/
def gaNum (d : DomDesc) (g : GA) : ℕ := (vocA d).sum + 1 + gfNum (gaFact g)

theorem gaNum_injective (d : DomDesc) : Function.Injective (gaNum d) := by
  intro g g' h
  exact gaFact_injective (gfNum_injective (by simpa [gaNum] using h))

theorem gaNum_nmem (d : DomDesc) (g : GA) : gaNum d g ∉ vocA d := by
  intro h
  have := List.le_sum_of_mem h
  simp only [gaNum] at this
  omega

theorem exists_nmem (l : List ℕ) : ∃ n, n ∉ l :=
  ⟨l.sum + 1, fun h => by have := List.le_sum_of_mem h; omega⟩

/-- The least number not in the list. -/
def leastFresh (l : List ℕ) : ℕ := Nat.find (exists_nmem l)

theorem leastFresh_nmem (l : List ℕ) : leastFresh l ∉ l := Nat.find_spec (exists_nmem l)

/-- **The least fresh number is at most the length of the list.** -/
theorem leastFresh_le (l : List ℕ) : leastFresh l ≤ l.length := by
  have hex : ∃ n ≤ l.length, n ∉ l := by
    by_contra hne
    push_neg at hne
    have hsub : Finset.range (l.length + 1) ⊆ l.toFinset := fun n hn =>
      List.mem_toFinset.2 (hne n (by simpa [Nat.lt_succ_iff] using hn))
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le l)
    simp at this
  obtain ⟨n, hn, hnl⟩ := hex
  exact (Nat.find_min' (exists_nmem l) hnl).trans hn

/-- **The concrete encodings of the gadget** for the domain description `d`. -/
def code (d : DomDesc) : Code where
  ρ v := 2 * v + 1
  gf := gfNum
  ga := gaNum d
  S := leastFresh (vocC d)
  ρ_inj a b h := by simp only at h; omega
  gf_inj := gfNum_injective
  ga_inj := gaNum_injective d
  gf_ne_ρ g v h := by
    simp only [gfNum] at h
    omega

@[simp] theorem code_ρ (d : DomDesc) (v : ℕ) : (code d).ρ v = 2 * v + 1 := rfl
@[simp] theorem code_gf (d : DomDesc) (g : GF) : (code d).gf g = gfNum g := rfl
@[simp] theorem code_ga (d : DomDesc) (g : GA) : (code d).ga g = gaNum d g := rfl
@[simp] theorem code_S (d : DomDesc) : (code d).S = leastFresh (vocC d) := rfl

/-- **The encodings are fresh for the domain.** -/
theorem code_fresh (d : DomDesc) : (code d).Fresh d where
  ga_nmem := gaNum_nmem d
  S_nmem := leastFresh_nmem (vocC d)

/-- The fresh compound task is small. -/
theorem code_S_le (d : DomDesc) : (code d).S ≤ (vocC d).length := leastFresh_le _

/-! ### The compiled facts, bit by bit -/

/-- **A compiled fact of the instance**: `4 (2 v + 1) + 2` is `[false, true, true] ++ bits v`. -/
theorem bits_cfact_inst (d : DomDesc) (v : ℕ) :
    bitsOfNat (4 * (code d).ρ v + 2) = [false, true, true] ++ bitsOfNat v := by
  rw [bitsOfNat_four_add_two, code_ρ, bitsOfNat_two_mul_add_one]
  rfl

/-- **A compiled gadget fact**: `4 (gfNum g) + 2` is `[false, true, false] ++ gbits g`. -/
theorem bits_cfact_gad (d : DomDesc) (g : GF) :
    bitsOfNat (4 * (code d).gf g + 2) = [false, true, false] ++ gbits g := by
  rw [bitsOfNat_four_add_two, code_gf, bitsOfNat_gfNum]
  rfl

end SeqM

end Space

end HTN
