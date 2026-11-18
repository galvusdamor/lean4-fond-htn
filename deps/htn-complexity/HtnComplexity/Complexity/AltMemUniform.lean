import HtnComplexity.Complexity.AltMemPrimrec
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Uniform families of alternating machines with a memory, and padded inputs

`HtnComplexity/Complexity/AltMemFamily.lean` turns **one** alternating machine with a
memory into a polynomial-time hardness family.  Two things keep that family from having the
shape of a space-bounded hardness construction:

* the machine is **fixed**, so it has a constant number of memory bits and a constant number of
  transitions, whereas a construction for a space-bounded computation needs both to grow with
  the input length;
* the machine makes **one step per input bit**, so it has only `|w|` steps — it cannot read its
  input twice.

This file removes both restrictions without touching the encoding or its correctness proof.

* `HTN.Syn.padGen f w = w ++ true :: (f |w|` zeros`)` pads the input word.  The marker `true`
  makes the padding invertible, so the padded encoding is still injective
  (`HTN.Syn.padGen_injective`, for a monotone `f`).  A **padding scheme**
  (`HTN.Syn.PadScheme`) is such a padding together with what a hardness family needs of it: its
  length as a function of `|w|`, injectivity, membership in Cobham's class, and a polynomial
  bound.  Two schemes are provided: `HTN.Syn.padLinear c`, which appends `c * |w|` zeros, and
  `HTN.Syn.padPow k`, which appends `|w| ^ k` of them, so that the number of steps may be **any
  power** of the input length.
* Since the machine consumes one bit per step, a padded word of length `|w| + 1 + f |w|` gives
  the machine that many steps: it can copy the input into its memory during the first `|w|`
  steps — the state of a machine of the family may count up to `|w|`, and its memory may have
  `|w|` bits — and then compute for `f |w|` steps with random access to the stored input.
* `HTN.Syn.UniAltMem` bundles a *family* of machines, one per input length, whose components are
  primitive recursive in the length and whose encoding has polynomially bounded size, together
  with a padding scheme, and `HTN.Syn.UniAltMem.family` is the resulting polynomial-time
  hardness family, in `TO-HTN-AC` with a rooted instance and hence in each of the three source
  classes `TO-HTN`, `HTN-TR`, `HTN-AC` of the eight open cells.

As everywhere in `Complexity/`, what is *not* claimed is completeness of the language for a
complexity class; see `NOTES.md` §2.1.
-/

namespace HTN

namespace Syn

open PTime

/-! ### Padding a word -/

/-- **The padded word**: the word itself, a marker bit, and `f |w|` zeros.  The machine of a
uniform family runs one step per bit of the padded word. -/
def padGen (f : ℕ → ℕ) (w : List Bool) : List Bool :=
  w ++ true :: List.replicate (f w.length) false

/-- **The padded word of the linear scheme**: `c` zeros per bit of the word. -/
def padWord (c : ℕ) (w : List Bool) : List Bool := padGen (fun n => c * n) w

/-- The length of a word padded by `f`, as a function of the length of the word. -/
def padLenOf (f : ℕ → ℕ) (n : ℕ) : ℕ := n + 1 + f n

/-- The length of a linearly padded word. -/
def padLen (c n : ℕ) : ℕ := padLenOf (fun n => c * n) n

@[simp] theorem length_padGen (f : ℕ → ℕ) (w : List Bool) :
    (padGen f w).length = padLenOf f w.length := by
  simp [padGen, padLenOf]
  omega

@[simp] theorem length_padWord (c : ℕ) (w : List Bool) :
    (padWord c w).length = padLen c w.length := length_padGen _ w

/-- Padding is injective when the number of padding bits grows monotonically: the marker bit
says where the word ends, and the length of the padded word determines the length of the
word. -/
theorem padGen_injective {f : ℕ → ℕ} (hf : Monotone f) : Function.Injective (padGen f) := by
  intro w w' h
  have hlen : (padGen f w).length = (padGen f w').length := by rw [h]
  rw [length_padGen, length_padGen, padLenOf, padLenOf] at hlen
  have hlen' : w.length = w'.length := by
    rcases lt_trichotomy w.length w'.length with hlt | heq | hgt
    · have := hf hlt.le
      omega
    · exact heq
    · have := hf hgt.le
      omega
  exact (List.append_inj h hlen').1

theorem padWord_injective (c : ℕ) : Function.Injective (padWord c) :=
  padGen_injective (fun _ _ h => Nat.mul_le_mul_left c h)

/-! ### The paddings are functions of Cobham's class -/

theorem flatMap_id_eq (w : List Bool) :
    (w.flatMap fun b => bif b then [true] else [false]) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [List.flatMap_cons, ih]

theorem flatMap_replicate_eq (c : ℕ) (w : List Bool) :
    (w.flatMap fun _ : Bool => List.replicate c false) =
      List.replicate (c * w.length) false := by
  induction w with
  | nil => simp
  | cons b w ih =>
    have hc : c * (w.length + 1) = c + c * w.length := by ring
    simp only [List.flatMap_cons, ih, List.length_cons, hc, List.replicate_add]

/-- The word followed by the marker bit, as a function of Cobham's class. -/
def markFn : Fn := compFn (blockFn [true] [false]) [proj 0, fun _ => [true]]

theorem markFn_apply (args : Args) : markFn args = args.getD 0 [] ++ [true] := by
  simp only [markFn, compFn, List.map_cons, List.map_nil, blockFn_apply, proj,
    List.getD_cons_zero, List.getD_cons_succ, flatMap_id_eq]

theorem cobham_markFn : Cobham markFn := by
  refine Cobham.comp (cobham_blockFn [true] [false]) ?_
  intro h hh
  rcases List.mem_cons.1 hh with rfl | hh
  · exact Cobham.proj 0
  · rw [List.mem_singleton.1 hh]
    exact cobham_const [true]

/-- `c * |x|` zeros, as a function of Cobham's class. -/
def zeroLinFn (c : ℕ) : Fn :=
  compFn (blockFn (List.replicate c false) (List.replicate c false)) [proj 0, fun _ => []]

theorem zeroLinFn_apply (c : ℕ) (args : Args) :
    zeroLinFn c args = List.replicate (c * (args.getD 0 []).length) false := by
  have h : ((args.getD 0 []).flatMap fun b : Bool =>
      bif b then List.replicate c false else List.replicate c false) =
      List.replicate (c * (args.getD 0 []).length) false := by
    rw [← flatMap_replicate_eq c (args.getD 0 [])]
    exact List.flatMap_congr fun b _ => by cases b <;> rfl
  simp only [zeroLinFn, compFn, List.map_cons, List.map_nil, blockFn_apply, proj,
    List.getD_cons_zero, List.getD_cons_succ, h, List.append_nil]

theorem cobham_zeroLinFn (c : ℕ) : Cobham (zeroLinFn c) := by
  refine Cobham.comp (cobham_blockFn (List.replicate c false) (List.replicate c false)) ?_
  intro h hh
  rcases List.mem_cons.1 hh with rfl | hh
  · exact Cobham.proj 0
  · rw [List.mem_singleton.1 hh]
    exact cobham_const []

/-- `|x| ^ k` zeros, as a function of Cobham's class: iterated smash. -/
def zeroPowFn : ℕ → Fn
  | 0 => fun _ => [false]
  | k + 1 => compFn smashFn [proj 0, zeroPowFn k]

theorem zeroPowFn_apply (k : ℕ) (args : Args) :
    zeroPowFn k args = List.replicate ((args.getD 0 []).length ^ k) false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [zeroPowFn, compFn, List.map_cons, List.map_nil, smashFn, proj,
      List.getD_cons_zero, List.getD_cons_succ, ih, List.length_replicate]
    rw [pow_succ, Nat.mul_comm]

theorem cobham_zeroPowFn (k : ℕ) : Cobham (zeroPowFn k) := by
  induction k with
  | zero => exact cobham_const [false]
  | succ k ih =>
    refine Cobham.comp Cobham.smash ?_
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact Cobham.proj 0
    · rw [List.mem_singleton.1 hh]
      exact ih

/-- A padding, before the arguments are fixed: the word, the marker, and the zeros given by the
function `z`. -/
def padWordFn (z : Fn) : Fn := compFn appendFn [markFn, z]

theorem padWordFn_apply {z : Fn} {f : ℕ → ℕ}
    (hz : ∀ args : Args, z args = List.replicate (f (args.getD 0 []).length) false)
    (args : Args) : padWordFn z args = padGen f (args.getD 0 []) := by
  simp only [padWordFn, compFn, List.map_cons, List.map_nil, appendFn, markFn_apply,
    List.getD_cons_zero, List.getD_cons_succ, hz, padGen]
  simp

theorem cobham_padWordFn {z : Fn} (hz : Cobham z) : Cobham (padWordFn z) := by
  refine Cobham.comp cobham_appendFn ?_
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact cobham_markFn
  · rw [List.mem_singleton.1 hg]
    exact hz

/-- **The linear padding is a polynomial-time function of the word.** -/
theorem polyTimeFun_padWord (c : ℕ) : PolyTimeFun (padWord c) :=
  CobhamFun.polyTimeFun ⟨padWordFn (zeroLinFn c), cobham_padWordFn (cobham_zeroLinFn c),
    fun x => by rw [padWordFn_apply (f := fun n => c * n) (zeroLinFn_apply c)]; rfl⟩

/-- **The power padding is a polynomial-time function of the word.** -/
theorem polyTimeFun_padPow (k : ℕ) : PolyTimeFun (padGen fun n => n ^ k) :=
  CobhamFun.polyTimeFun ⟨padWordFn (zeroPowFn k), cobham_padWordFn (cobham_zeroPowFn k),
    fun x => by rw [padWordFn_apply (f := fun n => n ^ k) (zeroPowFn_apply k)]; rfl⟩

/-! ### Padding schemes -/

/-- **A padding scheme**: a padding of the input word together with everything a hardness family
needs of it — its length as a function of the length of the word, injectivity, membership in
Cobham's class, and a polynomial bound on the length. -/
structure PadScheme where
  /-- The padding. -/
  pad : List Bool → List Bool
  /-- The length of a padded word, as a function of the length of the word. -/
  len : ℕ → ℕ
  /-- … which is the length of a padded word. -/
  length_pad : ∀ w : List Bool, (pad w).length = len w.length
  /-- Different words are padded differently. -/
  pad_injective : Function.Injective pad
  /-- The padding is computed in polynomial time. -/
  pad_polyTime : PolyTimeFun pad
  /-- The length is computed by an algorithm. -/
  len_primrec : Primrec len
  /-- A polynomial bounding the length. -/
  lenBound : Polynomial ℕ
  /-- … which does bound it. -/
  len_le : ∀ n, len n ≤ lenBound.eval n

namespace PadScheme

variable (P : PadScheme)

/-- The instance description of a padded word. -/
def enc (w : List Bool) : InstDesc := posEnc (P.pad w)

theorem enc_injective : Function.Injective P.enc := posEnc_injective.comp P.pad_injective

theorem size_enc (w : List Bool) : (P.enc w).size = P.len w.length + 2 := by
  rw [enc, size_posEnc, P.length_pad]

/-- **The padded encoder is polynomial time.** -/
theorem polyTimeCode_enc : PolyTimeCode codingSer P.enc :=
  ⟨fun w => posSer (P.pad w), polyTimeFun_posSer.comp P.pad_polyTime,
    fun w => by rw [codingSer_code, enc, instSer_posEnc]⟩

end PadScheme

theorem primrec_powConst (k : ℕ) : Primrec fun n : ℕ => n ^ k := by
  induction k with
  | zero => simpa using Primrec.const 1
  | succ k ih => exact (Primrec.nat_mul.comp ih Primrec.id).of_eq fun n => (pow_succ n k).symm

/-- **The linear padding scheme**: `c` zeros per bit of the word. -/
noncomputable def padLinear (c : ℕ) : PadScheme where
  pad := padWord c
  len := padLen c
  length_pad := length_padWord c
  pad_injective := padWord_injective c
  pad_polyTime := polyTimeFun_padWord c
  len_primrec :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
      (Primrec.nat_mul.comp (Primrec.const c) Primrec.id)
  lenBound := Polynomial.C (c + 1) * Polynomial.X + Polynomial.C 1
  len_le := fun n => by
    simp only [padLen, padLenOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    nlinarith

/-- **The power padding scheme**: `|w| ^ k` zeros, so that the machine makes `|w| ^ k + |w| + 1`
steps and may compute for a *polynomial* number of steps after having read its input. -/
noncomputable def padPow (k : ℕ) : PadScheme where
  pad := padGen fun n => n ^ k
  len := padLenOf fun n => n ^ k
  length_pad := length_padGen _
  pad_injective := padGen_injective fun _ _ h => Nat.pow_le_pow_left h k
  pad_polyTime := polyTimeFun_padPow k
  len_primrec :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)) (primrec_powConst k)
  lenBound := Polynomial.X ^ k + Polynomial.X + Polynomial.C 1
  len_le := fun n => by
    simp only [padLenOf, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X]
    omega

@[simp] theorem padLinear_pad (c : ℕ) : (padLinear c).pad = padWord c := rfl

@[simp] theorem padLinear_len (c : ℕ) : (padLinear c).len = padLen c := rfl

@[simp] theorem padPow_pad (k : ℕ) : (padPow k).pad = padGen (fun n => n ^ k) := rfl

@[simp] theorem padPow_len (k : ℕ) : (padPow k).len = padLenOf (fun n => n ^ k) := rfl

/-! ### A uniform family of machines -/

/-- **A uniform family of alternating machines with a memory**: one machine per input length,
with primitive recursive components and an encoding of polynomially bounded size, running on the
input padded by the scheme `padding`.  Both the number of memory bits and the number of
transitions of `mach n` may grow with `n`. -/
structure UniAltMem where
  /-- The machine used for the inputs of a given length. -/
  mach : ℕ → BitAltMem
  /-- The padding of the input, which fixes the number of steps the machine makes. -/
  padding : PadScheme
  /-- The polynomial bounding the size of the descriptions. -/
  bound : Polynomial ℕ
  /-- The machines are produced by an algorithm, uniformly in the input length. -/
  mach_primrec : MachFamPrimrec mach
  /-- The encoding has size polynomial in the input length. -/
  dom_size : ∀ n, amCoef (mach n) * padding.len n + amConst (mach n) ≤ bound.eval n

namespace UniAltMem

variable (F : UniAltMem)

/-- **The language of a uniform family**: the machine for the length of the word accepts the
padded word. -/
def L (w : List Bool) : Prop := (F.mach w.length).Accepts (F.padding.pad w)

/-- The domain description of the family: the encoding of the machine for the length `n`, run
for the number of steps the padded word of that length provides. -/
def dom (n : ℕ) : DomDesc := amDom (F.mach n) (F.padding.len n)

theorem computable_dom : Computable F.dom :=
  computable_amDom_fam F.mach_primrec F.padding.len_primrec

theorem solvable_dom_iff (w : List Bool) :
    Solvable (F.dom w.length) (F.padding.enc w) ↔ F.L w := by
  have h := solvable_amDom_iff (M := F.mach w.length) (F.padding.pad w)
  rw [F.padding.length_pad] at h
  exact h

/-- **The polynomial-time hardness family of a uniform family of alternating machines with a
memory**, in `TO-HTN-AC` with a rooted instance. -/
noncomputable def family : Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root F.L where
  dom := F.dom
  inst := F.padding.enc
  bound := F.bound + F.padding.lenBound + Polynomial.C 2
  dom_size := fun n => by
    have h := size_amDom_le (M := F.mach n) (F.padding.len n)
    have h2 := F.dom_size n
    simp only [dom, Polynomial.eval_add, Polynomial.eval_C]
    omega
  inst_size := fun w => by
    have h := F.padding.len_le w.length
    rw [F.padding.size_enc]
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega
  dom_ok := fun _ => amDom_domOk _
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := F.padding.enc_injective
  correct := F.solvable_dom_iff
  dom_computable := F.computable_dom
  inst_polyTime := F.padding.polyTimeCode_enc

/-- **The family, in `TO-HTN`.** -/
theorem nonempty_hardFamilyPT_TO_HTN :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.TO_HTN_root F.L) :=
  ⟨F.family.mono ⟨fun _ h => h.1, fun _ h => h⟩⟩

/-- … in `HTN-TR`. -/
theorem nonempty_hardFamilyPT_HTN_TR :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_TR_root F.L) :=
  ⟨F.family.mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h.2, fun _ h => h⟩⟩

/-- … in `HTN-AC`. -/
theorem nonempty_hardFamilyPT_HTN_AC :
    Nonempty (Coded.HardFamilyPT codingSer SynClass.HTN_AC_root F.L) :=
  ⟨F.family.mono ⟨fun _ h => h.2, fun _ h => h⟩⟩

end UniAltMem

end Syn

end HTN
