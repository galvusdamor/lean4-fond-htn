import ComplexityTheory.Compile.Base
/-!
# The circuit family of a bounded recursion on notation

`HTN.PTime.brnFn g h0 h1` runs the recursion on the bits of its first argument: on `b :: x` it
applies `h0` or `h1`, according to `b`, to the tail `x`, the value on `x` and the remaining
arguments.  Write `x₀` for the first argument, `v` for the remaining ones and

    Vᵢ  =  the value of the recursion on the suffix of `x₀` starting at `i`.

Then `V_{|x₀|} = g v`, and for `i < |x₀|`

    Vᵢ  =  (if x₀[i] then h1 else h0) (x₀.drop (i + 1) :: V_{i+1} :: v),

and the value of the recursion is `V₀`.  On arguments of length at most `n` there are at most
`n` stages, so the circuit is

* the two constants, then
* one copy of the circuit of `g`, giving `V_n`, then
* `n` **stages**, the `s`-th computing `V_{n-1-s}` from `V_{n-s}`: a copy of the circuit of `h0`
  and a copy of the circuit of `h1`, both reading the suffix of `x₀`, the previous value and the
  remaining arguments, and then one two-level multiplexer per output cell, selecting between the
  two copies on the bit `x₀[i]` and between that and the previous value on the presence bit of
  the cell `i` of `x₀` — the previous value being passed on unchanged once `i` has run past the
  end of `x₀`.

Every intermediate value is a value of the recursion, so the bound `bd` of Cobham's class keeps
all of them inside one polynomial: the stages all have the same width `M`, and a copy of a
circuit is fed by naming the wires its inputs are to be read off (`HTN.Compile.relocGates`),
so no gates are needed to move the encodings into place.

The data of the construction is bundled in `HTN.Compile.Brn.Data`, its well-formedness in
`HTN.Compile.Brn.Data.Ok`, and what the three copied circuits compute in
`HTN.Compile.Brn.Spec`.  The result is `HTN.Compile.circFam_brn`.
-/

namespace HTN

namespace Compile

open PTime

namespace Brn

/-! ### The data of the construction -/

/-- The first `m` entries of a list of wires, written so as to be visibly an algorithm. -/
def trunc (l : List ℕ) (m : ℕ) : List ℕ := (List.range m).map l.getI

@[simp] theorem length_trunc (l : List ℕ) (m : ℕ) : (trunc l m).length = m := by simp [trunc]

theorem trunc_eq_take {l : List ℕ} {m : ℕ} (h : m ≤ l.length) : trunc l m = l.take m := by
  refine List.ext_getElem (by simp [List.length_take]; omega) ?_
  intro c h1 h2
  simp only [trunc, List.getElem_map, List.getElem_range, List.getElem_take]
  exact List.getI_eq_getElem _ (by simp [trunc] at h1; omega)

/-- The data the stages are built from: the bound `n` on the arguments, the arity `k`, the
common width `M` of the values, and the three circuits that are copied. -/
structure Data where
  /-- The bound on the length of the arguments. -/
  n : ℕ
  /-- The arity. -/
  k : ℕ
  /-- The common width of the intermediate values. -/
  M : ℕ
  /-- The circuit of `g`, at the arity `k - 1` and the bound `M`. -/
  CG : Circ
  /-- The circuit of `h0`, at the arity `k + 1` and the bound `M`. -/
  C0 : Circ
  /-- The circuit of `h1`, at the arity `k + 1` and the bound `M`. -/
  C1 : Circ

namespace Data

variable (D : Data)

/-- The number of input wires: the `k` arguments at the bound `n`. -/
def nin : ℕ := 2 * D.n * D.k

/-- The wire carrying `false`. -/
def wF : ℕ := wFalse D.nin

/-- The two wires of the cell `j` of the input block starting at `bb`; past the bound `n` the
cell is empty, and both wires are the constant `false`. -/
def cellSrc (bb j : ℕ) : List ℕ :=
  if j < D.n then [bb + 2 * j, bb + 2 * j + 1] else [D.wF, D.wF]

/-- The wires carrying the cell encoding at the bound `M` of the `r`-th argument. -/
def argSrc (r : ℕ) : List ℕ := (List.range D.M).flatMap fun j => D.cellSrc (2 * D.n * r) j

/-- The wires carrying the cell encoding at the bound `M` of the suffix of the first argument
starting at `a`. -/
def xSrc (a : ℕ) : List ℕ := (List.range D.M).flatMap fun j => D.cellSrc 0 (a + j)

/-- The wires carrying the cell encoding at the bound `M` of the arguments after the first. -/
def tailSrc : List ℕ := (List.range (D.k - 1)).flatMap fun r => D.argSrc (r + 1)

/-- Where the copy of the circuit of `g` starts. -/
def baseG : ℕ := D.nin + 2

/-- Where the stages start. -/
def baseS : ℕ := D.baseG + D.CG.gates.length

/-- The number of gates of one stage. -/
def L : ℕ := D.C0.gates.length + D.C1.gates.length + 32 * D.M

/-- Where the `s`-th stage starts. -/
def baseOf (s : ℕ) : ℕ := D.baseS + D.L * s

/-- Where the copy of the circuit of `h1` of the `s`-th stage starts. -/
def base1 (s : ℕ) : ℕ := D.baseOf s + D.C0.gates.length

/-- Where the multiplexers of the `s`-th stage start. -/
def baseMux (s : ℕ) : ℕ := D.base1 s + D.C1.gates.length

/-- The wires carrying the value the copy of the circuit of `g` computes. -/
def gOut : List ℕ := trunc (relocOut D.CG D.baseG D.tailSrc) (2 * D.M)

/-- The wires carrying the value the `s`-th stage computes. -/
def muxOut (s : ℕ) : List ℕ :=
  (List.range (2 * D.M)).map fun c => D.baseMux s + 16 * c + 15

/-- The wires carrying the value the `s`-th stage reads. -/
def pv (D : Data) : ℕ → List ℕ
  | 0 => D.gOut
  | (s + 1) => D.muxOut s

/-- The wires the two copies of the `s`-th stage read: the suffix of the first argument, the
previous value, and the arguments after the first. -/
def srcS (s : ℕ) : List ℕ := D.xSrc (D.n - s) ++ (D.pv s ++ D.tailSrc)

/-- The wires carrying the value the copy of the circuit of `h0` computes. -/
def a0w (s : ℕ) : List ℕ := trunc (relocOut D.C0 (D.baseOf s) (D.srcS s)) (2 * D.M)

/-- The wires carrying the value the copy of the circuit of `h1` computes. -/
def a1w (s : ℕ) : List ℕ := trunc (relocOut D.C1 (D.base1 s) (D.srcS s)) (2 * D.M)

/-- The two multiplexers of the cell `c` of the `s`-th stage: the inner one selects between the
two copies on the bit of the cell, the outer one between that and the previous value on the
presence bit of the cell. -/
def muxG (s c b : ℕ) : List Gate :=
  gMux b (2 * (D.n - 1 - s) + 1) ((D.a1w s).getI c) ((D.a0w s).getI c)
    ++ gMux (b + 8) (2 * (D.n - 1 - s)) (b + 7) ((D.pv s).getI c)

/-- The gates of the `s`-th stage. -/
def stage (s : ℕ) (_b : ℕ) : List Gate :=
  relocGates D.C0 (D.baseOf s) (D.srcS s) ++ relocGates D.C1 (D.base1 s) (D.srcS s)
    ++ blkG (D.muxG s) 16 (D.baseMux s) (2 * D.M)

/-- The gates of the whole circuit. -/
def gates : List Gate :=
  gTF D.nin ++ (relocGates D.CG D.baseG D.tailSrc ++ blkG D.stage D.L D.baseS D.n)

/-- **The circuit of the recursion.** -/
def circ : Circ := (D.nin, D.gates, D.pv D.n)

/-- The wires after the two constants. -/
def wires1 (args : Args) : List Bool := encArgs D.k D.n args ++ [true, false]

/-- The wires after the copy of the circuit of `g`. -/
def wiresPre (args : Args) : List Bool :=
  runGates (D.wires1 args) (relocGates D.CG D.baseG D.tailSrc)

/-- The wires after the first `s` stages. -/
def wiresSt (args : Args) (s : ℕ) : List Bool :=
  runGates (D.wiresPre args) (blkG D.stage D.L D.baseS s)

/-- **The data is well formed**: the three circuits have the arities and the bound the
construction reads them at, and they have enough output wires. -/
structure Ok (D : Data) : Prop where
  /-- The arity is at least one. -/
  k_pos : 1 ≤ D.k
  /-- The values are at least as wide as the arguments. -/
  n_le : D.n ≤ D.M
  /-- The circuit of `g` has the arity `k - 1` at the bound `M`. -/
  ninG : D.CG.nin = 2 * D.M * (D.k - 1)
  /-- The circuit of `h0` has the arity `k + 1` at the bound `M`. -/
  nin0 : D.C0.nin = 2 * D.M * (D.k + 1)
  /-- The circuit of `h1` has the arity `k + 1` at the bound `M`. -/
  nin1 : D.C1.nin = 2 * D.M * (D.k + 1)
  /-- The circuit of `g` has at least `2 * M` output wires. -/
  outG : 2 * D.M ≤ D.CG.out.length
  /-- The circuit of `h0` has at least `2 * M` output wires. -/
  out0 : 2 * D.M ≤ D.C0.out.length
  /-- The circuit of `h1` has at least `2 * M` output wires. -/
  out1 : 2 * D.M ≤ D.C1.out.length
  /-- Every output wire of the circuit of `g` is a wire it has. -/
  outG_lt : ∀ j ∈ D.CG.out, j < D.CG.nin + D.CG.gates.length
  /-- Every output wire of the circuit of `h0` is a wire it has. -/
  out0_lt : ∀ j ∈ D.C0.out, j < D.C0.nin + D.C0.gates.length
  /-- Every output wire of the circuit of `h1` is a wire it has. -/
  out1_lt : ∀ j ∈ D.C1.out, j < D.C1.nin + D.C1.gates.length

end Data

/-- **What the three copied circuits compute.** -/
structure Spec (D : Data) (g h0 h1 : Fn) where
  /-- The output bound of the circuit of `g`. -/
  BG : ℕ
  /-- The output bound of the circuit of `h0`. -/
  B0 : ℕ
  /-- The output bound of the circuit of `h1`. -/
  B1 : ℕ
  /-- The output bound of the circuit of `g` is at least the width of the values. -/
  le_BG : D.M ≤ BG
  /-- The output bound of the circuit of `h0` is at least the width of the values. -/
  le_B0 : D.M ≤ B0
  /-- The output bound of the circuit of `h1` is at least the width of the values. -/
  le_B1 : D.M ≤ B1
  /-- The circuit of `g` computes `g`. -/
  evalG : ∀ as : Args, as.length = D.k - 1 → (∀ a ∈ as, a.length ≤ D.M) →
      D.CG.eval (encArgs (D.k - 1) D.M as) = encStr BG (g as)
  /-- The circuit of `h0` computes `h0`. -/
  eval0 : ∀ as : Args, as.length = D.k + 1 → (∀ a ∈ as, a.length ≤ D.M) →
      D.C0.eval (encArgs (D.k + 1) D.M as) = encStr B0 (h0 as)
  /-- The circuit of `h1` computes `h1`. -/
  eval1 : ∀ as : Args, as.length = D.k + 1 → (∀ a ∈ as, a.length ≤ D.M) →
      D.C1.eval (encArgs (D.k + 1) D.M as) = encStr B1 (h1 as)

/-- The value of the recursion on the suffix of the first argument starting at `i`. -/
def Vv (g h0 h1 : Fn) (args : Args) (i : ℕ) : List Bool :=
  brnAux g h0 h1 ((args.getD 0 []).drop i) args.tail

/-! ### The elementary lengths -/

namespace Data

variable (D : Data)

@[simp] theorem length_cellSrc (bb j : ℕ) : (D.cellSrc bb j).length = 2 := by
  rw [cellSrc]; split_ifs <;> rfl

@[simp] theorem length_argSrc (r : ℕ) : (D.argSrc r).length = 2 * D.M := by
  rw [argSrc, List.length_flatMap]
  have h : ((List.range D.M).map fun j => (D.cellSrc (2 * D.n * r) j).length)
      = (List.range D.M).map fun _ => 2 := List.map_congr_left fun j _ => by simp
  rw [h]
  simp [mul_comm]

@[simp] theorem length_xSrc (a : ℕ) : (D.xSrc a).length = 2 * D.M := by
  rw [xSrc, List.length_flatMap]
  have h : ((List.range D.M).map fun j => (D.cellSrc 0 (a + j)).length)
      = (List.range D.M).map fun _ => 2 := List.map_congr_left fun j _ => by simp
  rw [h]
  simp [mul_comm]

@[simp] theorem length_tailSrc : D.tailSrc.length = 2 * D.M * (D.k - 1) := by
  rw [tailSrc, List.length_flatMap]
  have h : ((List.range (D.k - 1)).map fun r => (D.argSrc (r + 1)).length)
      = (List.range (D.k - 1)).map fun _ => 2 * D.M := List.map_congr_left fun r _ => by simp
  rw [h]
  simp [mul_comm]

@[simp] theorem length_muxOut (s : ℕ) : (D.muxOut s).length = 2 * D.M := by simp [muxOut]

@[simp] theorem pv_zero : D.pv 0 = D.gOut := rfl

@[simp] theorem pv_succ (s : ℕ) : D.pv (s + 1) = D.muxOut s := rfl

theorem length_gOut (hD : D.Ok) : D.gOut.length = 2 * D.M := by
  rw [gOut, length_trunc]

theorem length_pv (hD : D.Ok) : ∀ s, (D.pv s).length = 2 * D.M
  | 0 => D.length_gOut hD
  | (_ + 1) => D.length_muxOut _

theorem length_srcS (hD : D.Ok) (s : ℕ) : (D.srcS s).length = 2 * D.M * (D.k + 1) := by
  rw [srcS, List.length_append, List.length_append, length_xSrc, D.length_pv hD,
    length_tailSrc]
  have hkp := hD.k_pos
  set m := D.k - 1 with hm
  have hk : D.k = m + 1 := by omega
  rw [hk]
  ring

theorem length_a0w (hD : D.Ok) (s : ℕ) : (D.a0w s).length = 2 * D.M := by
  rw [a0w, length_trunc]

theorem length_a1w (hD : D.Ok) (s : ℕ) : (D.a1w s).length = 2 * D.M := by
  rw [a1w, length_trunc]

@[simp] theorem length_muxG (s c b : ℕ) : (D.muxG s c b).length = 16 := by
  rw [muxG, List.length_append, length_gMux, length_gMux]

theorem length_stage (s b : ℕ) : (D.stage s b).length = D.L := by
  rw [stage, List.length_append, List.length_append, length_relocGates, length_relocGates,
    length_blkG (fun c b => D.length_muxG s c b), L]
  ring

theorem length_gates : D.gates.length
    = 2 + (D.CG.gates.length + D.L * D.n) := by
  rw [gates, List.length_append, List.length_append, length_gTF, length_relocGates,
    length_blkG (fun s b => D.length_stage s b)]

end Data

/-! ### The recursion, read off the stages -/

section Vv

variable {g h0 h1 : Fn} {args : Args}

theorem Vv_zero : Vv g h0 h1 args 0 = brnFn g h0 h1 args := by
  rw [Vv, brnFn, List.drop_zero]

theorem Vv_of_le {i : ℕ} (hi : (args.getD 0 []).length ≤ i) :
    Vv g h0 h1 args i = g args.tail := by
  rw [Vv, List.drop_eq_nil_of_le hi, brnAux]

theorem Vv_succ {i : ℕ} (hi : i < (args.getD 0 []).length) :
    Vv g h0 h1 args i = (bif (args.getD 0 []).getI i then h1 else h0)
      ((args.getD 0 []).drop (i + 1) :: Vv g h0 h1 args (i + 1) :: args.tail) := by
  rw [Vv, Vv, List.drop_eq_getElem_cons hi, brnAux, List.getI_eq_getElem _ hi]

theorem Vv_eq_brnFn (i : ℕ) :
    Vv g h0 h1 args i = brnFn g h0 h1 ((args.getD 0 []).drop i :: args.tail) := by
  rw [Vv, brnFn]
  rfl

end Vv

/-! ### The values the source wires carry -/

theorem getD_tail {α : Type*} (l : List α) (d : α) (r : ℕ) :
    l.tail.getD r d = l.getD (r + 1) d := by
  cases l with
  | nil => simp [List.getD]
  | cons a l => rfl

theorem getI_drop (l : List Bool) (a j : ℕ) : (l.drop a).getI j = l.getI (a + j) := by
  by_cases h : a + j < l.length
  · rw [List.getI_eq_getElem _ (by simp; omega), List.getI_eq_getElem _ h, List.getElem_drop]
  · rw [getI_of_le_length (by simp; omega), getI_of_le_length (by omega)]

section Src

variable {D : Data} {args : Args}

/-- The wire carrying `false` carries `false`. -/
theorem getI_wF : (D.wires1 args).getI D.wF = false := by
  have h := getI_wFalse (encArgs D.k D.n args)
  rw [runGates_gTF, length_encArgs] at h
  rw [Data.wires1, Data.wF, Data.nin]
  exact h

/-- **The two wires of a cell of an input block carry that cell of the suffix.** -/
theorem getI_cellSrc_val (hD : D.Ok) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) {r : ℕ} (hr : r < D.k) (a : ℕ) {j c : ℕ}
    (hc : c < 2) :
    (D.wires1 args).getI ((D.cellSrc (2 * D.n * r) (a + j)).getI c)
      = ([decide (j < ((args.getD r []).drop a).length),
          ((args.getD r []).drop a).getI j]).getI c := by
  have hsl : (args.getD r []).length ≤ D.n := by
    refine hlen _ ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hinp : (encArgs D.k D.n args).length = D.nin := by rw [length_encArgs, Data.nin]
  by_cases hjn : a + j < D.n
  · have hidx : (D.cellSrc (2 * D.n * r) (a + j)).getI c = 2 * D.n * r + (2 * (a + j) + c) := by
      rw [Data.cellSrc, if_pos hjn]
      interval_cases c
      · rw [List.getI_eq_getElem _ (by simp)]
        simp only [List.getElem_cons_zero]
        ring
      · rw [List.getI_eq_getElem _ (by simp)]
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        ring
    have hrk : 2 * D.n * r + 2 * D.n ≤ 2 * D.n * D.k := by
      have h1 : 2 * D.n * (r + 1) ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ (by omega)
      nlinarith
    rw [hidx, Data.wires1,
      List.getI_append _ _ _ (by rw [hinp, Data.nin]; omega),
      getI_encArgs hr (by omega)]
    interval_cases c
    · rw [Nat.add_zero, getI_encStr_pres _ hjn]
      show _ = decide (j < ((args.getD r []).drop a).length)
      rw [List.length_drop]
      exact decide_eq_decide.2 (by omega)
    · rw [getI_encStr_val _ hjn]
      show _ = ((args.getD r []).drop a).getI j
      rw [getI_drop]
  · have hidx : (D.cellSrc (2 * D.n * r) (a + j)).getI c = D.wF := by
      rw [Data.cellSrc, if_neg hjn]
      interval_cases c
      · rw [List.getI_eq_getElem _ (by simp)]; rfl
      · rw [List.getI_eq_getElem _ (by simp)]; rfl
    rw [hidx, getI_wF]
    interval_cases c
    · show false = decide (j < ((args.getD r []).drop a).length)
      rw [List.length_drop]
      exact (decide_eq_false (by omega)).symm
    · show false = ((args.getD r []).drop a).getI j
      rw [getI_drop]
      exact (getI_of_le_length (by omega)).symm

/-- **The wires of an input block carry the cell encoding of the argument at the bound `M`.** -/
theorem getI_argSrc_val (hD : D.Ok) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) {r : ℕ} (hr : r < D.k) :
    ∀ c < 2 * D.M,
      (D.wires1 args).getI ((D.argSrc r).getI c) = (encStr D.M (args.getD r [])).getI c := by
  intro c hc
  have key := getI_src_flatMap (W := D.wires1 args) (m := 2) (K := D.M)
    (f := fun j => D.cellSrc (2 * D.n * r) j)
    (e := fun j => [decide (j < (args.getD r []).length), (args.getD r []).getI j])
    (fun j => by simp) (fun j => rfl) ?_ c hc
  · exact key
  · intro j _ c' hc'
    have h := getI_cellSrc_val hD hargs hlen hr 0 (j := j) hc'
    simpa using h

/-- **The wires of the suffix of the first argument carry its cell encoding at the bound `M`.** -/
theorem getI_xSrc_val (hD : D.Ok) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) (a : ℕ) :
    ∀ c < 2 * D.M,
      (D.wires1 args).getI ((D.xSrc a).getI c)
        = (encStr D.M ((args.getD 0 []).drop a)).getI c := by
  intro c hc
  have hz : (2 : ℕ) * D.n * 0 = 0 := by simp
  have key := getI_src_flatMap (W := D.wires1 args) (m := 2) (K := D.M)
    (f := fun j => D.cellSrc 0 (a + j))
    (e := fun j => [decide (j < ((args.getD 0 []).drop a).length),
      ((args.getD 0 []).drop a).getI j])
    (fun j => by simp) (fun j => rfl) ?_ c hc
  · exact key
  · intro j _ c' hc'
    have h := getI_cellSrc_val hD hargs hlen hD.k_pos a (j := j) hc'
    rw [hz] at h
    exact h

/-- **The wires of the arguments after the first carry their cell encoding at the bound `M`.** -/
theorem getI_tailSrc_val (hD : D.Ok) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) :
    ∀ c < 2 * D.M * (D.k - 1),
      (D.wires1 args).getI (D.tailSrc.getI c) = (encArgs (D.k - 1) D.M args.tail).getI c := by
  intro c hc
  refine getI_src_flatMap (W := D.wires1 args) (m := 2 * D.M) (K := D.k - 1)
    (f := fun r => D.argSrc (r + 1)) (e := fun r => encStr D.M (args.tail.getD r []))
    (fun r => by simp) (fun r => by simp) ?_ c hc
  intro r hr c' hc'
  show (D.wires1 args).getI ((D.argSrc (r + 1)).getI c')
      = (encStr D.M (args.tail.getD r [])).getI c'
  rw [getD_tail]
  exact getI_argSrc_val hD hargs hlen (by omega) c' hc'

/-! ### The source wires are wires the circuit already has -/

theorem cellSrc_lt (hD : D.Ok) {bb j : ℕ} (hbb : bb + 2 * D.n ≤ D.nin) :
    ∀ w ∈ D.cellSrc bb j, w < D.baseG := by
  intro w hw
  rw [Data.cellSrc] at hw
  split_ifs at hw with h
  · rcases List.mem_cons.1 hw with rfl | hw
    · rw [Data.baseG]; omega
    · rw [List.mem_singleton] at hw
      subst hw
      rw [Data.baseG]; omega
  · have : w = D.wF := by
      rcases List.mem_cons.1 hw with rfl | hw
      · rfl
      · rw [List.mem_singleton] at hw; exact hw
    rw [this, Data.wF, wFalse, Data.baseG]
    omega

theorem tailSrc_lt (hD : D.Ok) : ∀ w ∈ D.tailSrc, w < D.baseG := by
  intro w hw
  rw [Data.tailSrc, List.mem_flatMap] at hw
  obtain ⟨r, hr, hw⟩ := hw
  rw [List.mem_range] at hr
  rw [Data.argSrc, List.mem_flatMap] at hw
  obtain ⟨j, _, hw⟩ := hw
  refine cellSrc_lt hD ?_ w hw
  have h1 : 2 * D.n * (r + 1) + 2 * D.n = 2 * D.n * (r + 2) := by ring
  have h2 : 2 * D.n * (r + 2) ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ (by omega)
  rw [Data.nin]
  omega

theorem xSrc_lt (hD : D.Ok) (a : ℕ) : ∀ w ∈ D.xSrc a, w < D.baseG := by
  intro w hw
  rw [Data.xSrc, List.mem_flatMap] at hw
  obtain ⟨j, _, hw⟩ := hw
  refine cellSrc_lt hD ?_ w hw
  have h2 : 2 * D.n * 1 ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ hD.k_pos
  rw [Data.nin]
  omega

theorem baseG_le_baseOf (s : ℕ) : D.baseG ≤ D.baseOf s := by
  rw [Data.baseOf, Data.baseS]
  omega

theorem gOut_lt (hD : D.Ok) : ∀ w ∈ D.gOut, w < D.baseS := by
  intro w hw
  rw [Data.gOut, trunc_eq_take (by rw [length_relocOut]; exact hD.outG)] at hw
  have hw' : w ∈ relocOut D.CG D.baseG D.tailSrc := List.mem_of_mem_take hw
  rw [relocOut, List.mem_map] at hw'
  obtain ⟨u, hu, rfl⟩ := hw'
  have hlt := hD.outG_lt u hu
  rw [wsh]
  split_ifs with h
  · have : D.tailSrc.getI u < D.baseG := by
      refine tailSrc_lt hD _ ?_
      rw [List.getI_eq_getElem _ (by rw [Data.length_tailSrc, ← hD.ninG]; exact h)]
      exact List.getElem_mem _
    rw [Data.baseS]
    omega
  · rw [Data.baseS]
    omega

theorem pv_lt (hD : D.Ok) : ∀ s, ∀ w ∈ D.pv s, w < D.baseOf s
  | 0 => by
      intro w hw
      have := gOut_lt hD w hw
      rw [Data.baseOf]
      omega
  | (s + 1) => by
      intro w hw
      rw [Data.pv_succ, Data.muxOut, List.mem_map] at hw
      obtain ⟨c, hc, rfl⟩ := hw
      rw [List.mem_range] at hc
      have e1 : D.baseOf (s + 1) = D.baseOf s + D.L := by
        rw [Data.baseOf, Data.baseOf]; ring
      rw [e1, Data.baseMux, Data.base1, Data.L]
      omega

theorem srcS_lt (hD : D.Ok) (s : ℕ) : ∀ w ∈ D.srcS s, w < D.baseOf s := by
  intro w hw
  rw [Data.srcS, List.mem_append] at hw
  rcases hw with hw | hw
  · exact lt_of_lt_of_le (xSrc_lt hD _ w hw) (baseG_le_baseOf s)
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact pv_lt hD s w hw
    · exact lt_of_lt_of_le (tailSrc_lt hD w hw) (baseG_le_baseOf s)

end Src

/-! ### The stages -/

section Stage

variable {D : Data} {g h0 h1 : Fn} {args : Args}

theorem length_wires1 (hargs : args.length = D.k) :
    (D.wires1 args).length = D.baseG := by
  rw [Data.wires1, List.length_append, length_encArgs, Data.baseG, Data.nin]
  rfl

theorem length_wiresPre (hargs : args.length = D.k) :
    (D.wiresPre args).length = D.baseS := by
  rw [Data.wiresPre, length_runGates, length_wires1 hargs, length_relocGates, Data.baseS]

theorem length_wiresSt (hargs : args.length = D.k) (s : ℕ) :
    (D.wiresSt args s).length = D.baseOf s := by
  rw [Data.wiresSt, length_runGates, length_wiresPre hargs,
    length_blkG (fun s b => D.length_stage s b), Data.baseOf]

/-- The wires of the input are unchanged by the stages. -/
theorem getI_wiresSt_wires1 (hargs : args.length = D.k) (s : ℕ) {w : ℕ} (hw : w < D.baseG) :
    (D.wiresSt args s).getI w = (D.wires1 args).getI w := by
  rw [Data.wiresSt, getI_runGates_of_lt (by rw [length_wiresPre hargs, Data.baseS]; omega),
    Data.wiresPre, getI_runGates_of_lt (by rw [length_wires1 hargs]; exact hw)]

/-- The wires of the copy of the circuit of `h0` are wires of the stage. -/
theorem a0w_lt (hD : D.Ok) (s : ℕ) : ∀ w ∈ D.a0w s, w < D.base1 s := by
  intro w hw
  rw [Data.a0w, trunc_eq_take (by rw [length_relocOut]; exact hD.out0)] at hw
  have hw' : w ∈ relocOut D.C0 (D.baseOf s) (D.srcS s) := List.mem_of_mem_take hw
  rw [relocOut, List.mem_map] at hw'
  obtain ⟨u, hu, rfl⟩ := hw'
  have hlt := hD.out0_lt u hu
  rw [wsh]
  split_ifs with h
  · have : (D.srcS s).getI u < D.baseOf s := by
      refine srcS_lt hD s _ ?_
      rw [List.getI_eq_getElem _ (by rw [D.length_srcS hD, ← hD.nin0]; exact h)]
      exact List.getElem_mem _
    rw [Data.base1]
    omega
  · rw [Data.base1]
    omega

/-- The wires of the copy of the circuit of `h1` are wires of the stage. -/
theorem a1w_lt (hD : D.Ok) (s : ℕ) : ∀ w ∈ D.a1w s, w < D.baseMux s := by
  intro w hw
  rw [Data.a1w, trunc_eq_take (by rw [length_relocOut]; exact hD.out1)] at hw
  have hw' : w ∈ relocOut D.C1 (D.base1 s) (D.srcS s) := List.mem_of_mem_take hw
  rw [relocOut, List.mem_map] at hw'
  obtain ⟨u, hu, rfl⟩ := hw'
  have hlt := hD.out1_lt u hu
  rw [wsh]
  split_ifs with h
  · have h1 : (D.srcS s).getI u < D.baseOf s := by
      refine srcS_lt hD s _ ?_
      rw [List.getI_eq_getElem _ (by rw [D.length_srcS hD, ← hD.nin1]; exact h)]
      exact List.getElem_mem _
    rw [Data.baseMux, Data.base1]
    omega
  · rw [Data.baseMux]
    omega

/-- **The copy of the circuit of `g` computes the value the recursion starts from.** -/
theorem gOut_correct (hD : D.Ok) (S : Spec D g h0 h1) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) (hM : (g args.tail).length ≤ D.M) :
    ∀ c < 2 * D.M,
      (D.wiresPre args).getI (D.gOut.getI c) = (encStr D.M (g args.tail)).getI c := by
  have hvlen : args.tail.length = D.k - 1 := by rw [List.length_tail, hargs]
  have hvle : ∀ a ∈ args.tail, a.length ≤ D.M :=
    fun a ha => le_trans (hlen a (List.mem_of_mem_tail ha)) hD.n_le
  have hinp : (encArgs (D.k - 1) D.M args.tail).length = D.CG.nin := by
    rw [length_encArgs, hD.ninG]
  have hW1 : (D.wires1 args).length = D.baseG := length_wires1 hargs
  have hlt : ∀ i, i < D.CG.nin → D.tailSrc.getI i < (D.wires1 args).length := by
    intro i hi
    rw [hW1]
    refine tailSrc_lt hD _ ?_
    rw [List.getI_eq_getElem _ (by rw [Data.length_tailSrc, ← hD.ninG]; exact hi)]
    exact List.getElem_mem _
  have hval : ∀ i, i < D.CG.nin →
      (D.wires1 args).getI (D.tailSrc.getI i) = (encArgs (D.k - 1) D.M args.tail).getI i := by
    intro i hi
    exact getI_tailSrc_val hD hargs hlen i (by rw [hD.ninG] at hi; exact hi)
  have hmap := values_after (D.wires1 args) D.CG D.tailSrc (encArgs (D.k - 1) D.M args.tail)
    hlt hinp hval
  rw [S.evalG args.tail hvlen hvle] at hmap
  have htake : D.gOut.map (D.wiresPre args).getI = encStr D.M (g args.tail) := by
    rw [Data.gOut, trunc_eq_take (by rw [length_relocOut]; exact hD.outG), List.map_take,
      Data.wiresPre, ← hW1, hmap]
    exact take_encStr hM S.le_BG
  intro c hc
  have hc' : c < D.gOut.length := by rw [D.length_gOut hD]; exact hc
  rw [← htake, getI_map _ _ hc']

/-- **The source wires of a stage carry the arguments of the recursive call.** -/
theorem srcS_val (hD : D.Ok) (hargs : args.length = D.k) (hlen : ∀ a ∈ args, a.length ≤ D.n)
    {s : ℕ} (ih : ∀ c < 2 * D.M, (D.wiresSt args s).getI ((D.pv s).getI c)
      = (encStr D.M (Vv g h0 h1 args (D.n - s))).getI c) :
    ∀ c < 2 * D.M * (D.k + 1),
      (D.wiresSt args s).getI ((D.srcS s).getI c)
        = (encArgs (D.k + 1) D.M ((args.getD 0 []).drop (D.n - s) ::
            Vv g h0 h1 args (D.n - s) :: args.tail)).getI c := by
  have hk : D.k - 1 + 1 = D.k := by have := hD.k_pos; omega
  have henc : encArgs (D.k + 1) D.M ((args.getD 0 []).drop (D.n - s) ::
      Vv g h0 h1 args (D.n - s) :: args.tail)
      = encStr D.M ((args.getD 0 []).drop (D.n - s))
        ++ (encStr D.M (Vv g h0 h1 args (D.n - s))
          ++ encArgs (D.k - 1) D.M args.tail) := by
    rw [encArgs_cons D.k D.M, ← hk, encArgs_cons (D.k - 1) D.M, hk]
  have hA : ∀ c < (D.xSrc (D.n - s)).length,
      (D.wiresSt args s).getI ((D.xSrc (D.n - s)).getI c)
        = (encStr D.M ((args.getD 0 []).drop (D.n - s))).getI c := by
    intro c hc
    rw [D.length_xSrc] at hc
    rw [getI_wiresSt_wires1 hargs s (xSrc_lt hD _ _ (by
      rw [List.getI_eq_getElem _ (by rw [D.length_xSrc]; exact hc)]
      exact List.getElem_mem _))]
    exact getI_xSrc_val hD hargs hlen _ c hc
  have hC : ∀ c < D.tailSrc.length,
      (D.wiresSt args s).getI (D.tailSrc.getI c)
        = (encArgs (D.k - 1) D.M args.tail).getI c := by
    intro c hc
    rw [D.length_tailSrc] at hc
    rw [getI_wiresSt_wires1 hargs s (tailSrc_lt hD _ (by
      rw [List.getI_eq_getElem _ (by rw [D.length_tailSrc]; exact hc)]
      exact List.getElem_mem _))]
    exact getI_tailSrc_val hD hargs hlen c hc
  have hB : ∀ c < (D.pv s).length,
      (D.wiresSt args s).getI ((D.pv s).getI c)
        = (encStr D.M (Vv g h0 h1 args (D.n - s))).getI c := by
    intro c hc
    rw [D.length_pv hD] at hc
    exact ih c hc
  have key := getI_src_append (W := D.wiresSt args s)
    (s1 := D.xSrc (D.n - s)) (s2 := D.pv s ++ D.tailSrc)
    (e1 := encStr D.M ((args.getD 0 []).drop (D.n - s)))
    (e2 := encStr D.M (Vv g h0 h1 args (D.n - s)) ++ encArgs (D.k - 1) D.M args.tail)
    (by rw [D.length_xSrc, length_encStr]) hA
    (getI_src_append (by rw [D.length_pv hD, length_encStr]) hB hC)
  intro c hc
  rw [henc, Data.srcS]
  refine key c ?_
  rw [List.length_append, List.length_append, D.length_xSrc, D.length_pv hD, D.length_tailSrc]
  have hk2 : D.k + 1 = (D.k - 1) + 2 := by omega
  calc c < 2 * D.M * (D.k + 1) := hc
    _ = 2 * D.M + (2 * D.M + 2 * D.M * (D.k - 1)) := by rw [hk2]; ring

/-- One stage, as a state transformation. -/
theorem wiresSt_succ (hargs : args.length = D.k) (s : ℕ) :
    D.wiresSt args (s + 1) = runGates (D.wiresSt args s) (D.stage s (D.baseOf s)) := by
  rw [Data.wiresSt, Data.wiresSt, blkG_succ, runGates_append, Data.baseOf]

/-- **A stage computes the next value of the recursion.** -/
theorem stage_correct (hD : D.Ok) (S : Spec D g h0 h1) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) (hM : ∀ i, (Vv g h0 h1 args i).length ≤ D.M)
    {s : ℕ} (hs : s < D.n)
    (ih : ∀ c < 2 * D.M, (D.wiresSt args s).getI ((D.pv s).getI c)
      = (encStr D.M (Vv g h0 h1 args (D.n - s))).getI c) :
    ∀ c < 2 * D.M, (D.wiresSt args (s + 1)).getI ((D.pv (s + 1)).getI c)
      = (encStr D.M (Vv g h0 h1 args (D.n - (s + 1)))).getI c := by
  intro c hc
  have hkp : 1 ≤ D.k := hD.k_pos
  obtain ⟨i, hi⟩ : ∃ i, D.n - (s + 1) = i := ⟨_, rfl⟩
  have hns : D.n - s = i + 1 := by omega
  have hin : i < D.n := by omega
  have hsrc0 := srcS_val hD hargs hlen ih
  rw [hi]
  rw [hns] at ih hsrc0
  -- the arguments of the recursive call
  have hx0n : (args.getD 0 []).length ≤ D.n := by
    refine hlen _ ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hvlen : args.tail.length = D.k - 1 := by rw [List.length_tail, hargs]
  have hinnerlen : ((args.getD 0 []).drop (i + 1) :: Vv g h0 h1 args (i + 1)
      :: args.tail).length = D.k + 1 := by
    have := hD.k_pos
    simp only [List.length_cons, hvlen]
    omega
  have hinnerle : ∀ a ∈ ((args.getD 0 []).drop (i + 1) :: Vv g h0 h1 args (i + 1)
      :: args.tail), a.length ≤ D.M := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact le_trans (le_trans (by simp) hx0n) hD.n_le
    rcases List.mem_cons.1 ha with rfl | ha
    · exact hM _
    · exact le_trans (hlen a (List.mem_of_mem_tail ha)) hD.n_le
  have hencl : (encArgs (D.k + 1) D.M ((args.getD 0 []).drop (i + 1)
      :: Vv g h0 h1 args (i + 1) :: args.tail)).length = 2 * D.M * (D.k + 1) := by simp
  have hsrc : ∀ u < 2 * D.M * (D.k + 1),
      (D.wiresSt args s).getI ((D.srcS s).getI u)
        = (encArgs (D.k + 1) D.M ((args.getD 0 []).drop (i + 1)
            :: Vv g h0 h1 args (i + 1) :: args.tail)).getI u := by
    exact hsrc0
  -- the state before the stage
  have hWlen : (D.wiresSt args s).length = D.baseOf s := length_wiresSt hargs s
  have hsrclt : ∀ u, u < 2 * D.M * (D.k + 1) → (D.srcS s).getI u < (D.wiresSt args s).length := by
    intro u hu
    rw [hWlen]
    refine srcS_lt hD s _ ?_
    rw [List.getI_eq_getElem _ (by rw [D.length_srcS hD]; exact hu)]
    exact List.getElem_mem _
  -- the copy of the circuit of `h0`
  obtain ⟨WA, hWA⟩ : ∃ WA, WA = runGates (D.wiresSt args s)
      (relocGates D.C0 (D.baseOf s) (D.srcS s)) := ⟨_, rfl⟩
  have hWAlen : WA.length = D.base1 s := by
    rw [hWA, length_runGates, hWlen, length_relocGates, Data.base1]
  have hA : (relocOut D.C0 (D.baseOf s) (D.srcS s)).map WA.getI
      = encStr S.B0 (h0 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail)) := by
    have h := values_after (D.wiresSt args s) D.C0 (D.srcS s)
      (encArgs (D.k + 1) D.M ((args.getD 0 []).drop (i + 1)
        :: Vv g h0 h1 args (i + 1) :: args.tail))
      (fun u hu => hsrclt u (by rw [← hD.nin0]; exact hu))
      (by rw [hencl, hD.nin0])
      (fun u hu => hsrc u (by rw [← hD.nin0]; exact hu))
    rw [S.eval0 _ hinnerlen hinnerle] at h
    rw [hWlen] at h
    rw [hWA]
    exact h
  -- the copy of the circuit of `h1`
  obtain ⟨WB, hWB⟩ : ∃ WB, WB = runGates WA
      (relocGates D.C1 (D.base1 s) (D.srcS s)) := ⟨_, rfl⟩
  have hWBlen : WB.length = D.baseMux s := by
    rw [hWB, length_runGates, hWAlen, length_relocGates, Data.baseMux]
  have hWAlow : ∀ w, w < D.baseOf s → WA.getI w = (D.wiresSt args s).getI w := by
    intro w hw
    rw [hWA]
    exact getI_runGates_of_lt (by rw [hWlen]; exact hw)
  have hWBlow : ∀ w, w < D.base1 s → WB.getI w = WA.getI w := by
    intro w hw
    rw [hWB]
    exact getI_runGates_of_lt (by rw [hWAlen]; exact hw)
  have hB : (relocOut D.C1 (D.base1 s) (D.srcS s)).map WB.getI
      = encStr S.B1 (h1 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail)) := by
    have h := values_after WA D.C1 (D.srcS s)
      (encArgs (D.k + 1) D.M ((args.getD 0 []).drop (i + 1)
        :: Vv g h0 h1 args (i + 1) :: args.tail))
      (fun u hu => by
        rw [hWAlen]
        exact lt_of_lt_of_le (by
          have := hsrclt u (by rw [← hD.nin1]; exact hu)
          rwa [hWlen] at this) (by rw [Data.base1]; omega))
      (by rw [hencl, hD.nin1])
      (fun u hu => by
        have hlt := hsrclt u (by rw [← hD.nin1]; exact hu)
        rw [hWlen] at hlt
        rw [hWAlow _ hlt]
        exact hsrc u (by rw [← hD.nin1]; exact hu))
    rw [S.eval1 _ hinnerlen hinnerle] at h
    rw [hWAlen] at h
    rw [hWB]
    exact h
  -- the values the two copies leave on their wires
  have hA0 : ∀ d < 2 * D.M, WA.getI ((D.a0w s).getI d)
      = ((encStr S.B0 (h0 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M)).getI d := by
    intro d hd
    have hmap : (D.a0w s).map WA.getI
        = (encStr S.B0 (h0 ((args.getD 0 []).drop (i + 1)
            :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M) := by
      rw [Data.a0w, trunc_eq_take (by rw [length_relocOut]; exact hD.out0), List.map_take, hA]
    rw [← hmap, getI_map _ _ (by rw [D.length_a0w hD]; exact hd)]
  have hA1 : ∀ d < 2 * D.M, WB.getI ((D.a1w s).getI d)
      = ((encStr S.B1 (h1 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M)).getI d := by
    intro d hd
    have hmap : (D.a1w s).map WB.getI
        = (encStr S.B1 (h1 ((args.getD 0 []).drop (i + 1)
            :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M) := by
      rw [Data.a1w, trunc_eq_take (by rw [length_relocOut]; exact hD.out1), List.map_take, hB]
    rw [← hmap, getI_map _ _ (by rw [D.length_a1w hD]; exact hd)]
  -- the multiplexers
  obtain ⟨Wc, hWc⟩ : ∃ Wc, Wc = runGates WB (blkG (D.muxG s) 16 (D.baseMux s) c) := ⟨_, rfl⟩
  have hWclen : Wc.length = D.baseMux s + 16 * c := by
    rw [hWc, length_runGates, hWBlen, length_blkG (fun d b => D.length_muxG s d b)]
  have hWclow : ∀ w, w < D.baseMux s → Wc.getI w = WB.getI w := by
    intro w hw
    rw [hWc]
    exact getI_runGates_of_lt (by rw [hWBlen]; exact hw)
  -- the three inputs of the multiplexers
  have hbaseG : D.baseG ≤ D.baseOf s := baseG_le_baseOf s
  have hnin2 : 2 * i + 1 < D.baseG := by
    have h2 : 2 * D.n * 1 ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ hD.k_pos
    rw [Data.baseG, Data.nin]
    omega
  have hlow : ∀ w, w < D.baseG → Wc.getI w = (D.wires1 args).getI w := by
    intro w hw
    rw [hWclow w (by rw [Data.baseMux, Data.base1]; omega),
      hWBlow w (by rw [Data.base1]; omega), hWAlow w (by omega),
      getI_wiresSt_wires1 hargs s hw]
  have hpres : Wc.getI (2 * i) = decide (i < (args.getD 0 []).length) := by
    rw [hlow _ (by omega), Data.wires1,
      List.getI_append _ _ _ (by
        rw [length_encArgs]
        have h2 : 2 * D.n * 1 ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ hD.k_pos
        omega)]
    have h := getI_encArgs (k := D.k) (n := D.n) (j := 0) (r := 2 * i) (args := args)
      (by omega) (by omega)
    rw [show 2 * D.n * 0 + 2 * i = 2 * i by ring] at h
    rw [h, getI_encStr_pres _ hin]
  have hbit : Wc.getI (2 * i + 1) = (args.getD 0 []).getI i := by
    rw [hlow _ hnin2, Data.wires1,
      List.getI_append _ _ _ (by
        rw [length_encArgs]
        have h2 : 2 * D.n * 1 ≤ 2 * D.n * D.k := Nat.mul_le_mul_left _ hD.k_pos
        omega)]
    have h := getI_encArgs (k := D.k) (n := D.n) (j := 0) (r := 2 * i + 1) (args := args)
      (by omega) (by omega)
    rw [show 2 * D.n * 0 + (2 * i + 1) = 2 * i + 1 by ring] at h
    rw [h, getI_encStr_val _ hin]
  have hprev : Wc.getI ((D.pv s).getI c)
      = (encStr D.M (Vv g h0 h1 args (i + 1))).getI c := by
    have hlt : (D.pv s).getI c < D.baseOf s := by
      refine pv_lt hD s _ ?_
      rw [List.getI_eq_getElem _ (by rw [D.length_pv hD]; exact hc)]
      exact List.getElem_mem _
    rw [hWclow _ (by rw [Data.baseMux, Data.base1]; omega),
      hWBlow _ (by rw [Data.base1]; omega), hWAlow _ hlt]
    exact ih c hc
  have h0v : Wc.getI ((D.a0w s).getI c)
      = ((encStr S.B0 (h0 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M)).getI c := by
    have hlt : (D.a0w s).getI c < D.base1 s := by
      refine a0w_lt hD s _ ?_
      rw [List.getI_eq_getElem _ (by rw [D.length_a0w hD]; exact hc)]
      exact List.getElem_mem _
    rw [hWclow _ (by rw [Data.baseMux]; omega), hWBlow _ hlt]
    exact hA0 c hc
  have h1v : Wc.getI ((D.a1w s).getI c)
      = ((encStr S.B1 (h1 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail))).take (2 * D.M)).getI c := by
    have hlt : (D.a1w s).getI c < D.baseMux s := by
      refine a1w_lt hD s _ ?_
      rw [List.getI_eq_getElem _ (by rw [D.length_a1w hD]; exact hc)]
      exact List.getElem_mem _
    rw [hWclow _ hlt]
    exact hA1 c hc
  -- the value the two multiplexers leave
  obtain ⟨W', hW'⟩ : ∃ W', W' = runGates Wc
      (gMux (D.baseMux s + 16 * c) (2 * i + 1) ((D.a1w s).getI c) ((D.a0w s).getI c)) :=
    ⟨_, rfl⟩
  have hW'len : W'.length = D.baseMux s + 16 * c + 8 := by
    rw [hW', length_runGates, hWclen, length_gMux]
  have hmux1 : W'.getI (D.baseMux s + 16 * c + 7)
      = (if Wc.getI (2 * i + 1) = true then Wc.getI ((D.a1w s).getI c)
          else Wc.getI ((D.a0w s).getI c)) := by
    have h := getI_gMux (v := Wc) (s := 2 * i + 1) (a := (D.a1w s).getI c)
      (b := (D.a0w s).getI c)
      (by rw [hWclen, Data.baseMux, Data.base1, Data.baseOf, Data.baseS]; omega)
      (by
        rw [hWclen]
        have hlt : (D.a0w s).getI c < D.base1 s := by
          refine a0w_lt hD s _ ?_
          rw [List.getI_eq_getElem _ (by rw [D.length_a0w hD]; exact hc)]
          exact List.getElem_mem _
        rw [Data.baseMux] at *
        omega)
    rw [hWclen] at h
    rw [hW', wMux] at *
    exact h
  have hW'low : ∀ w, w < D.baseMux s + 16 * c → W'.getI w = Wc.getI w := by
    intro w hw
    rw [hW']
    exact getI_runGates_of_lt (by rw [hWclen]; exact hw)
  -- the second multiplexer
  have hi' : D.n - 1 - s = i := by omega
  have hpvlt : (D.pv s).getI c < D.baseOf s := by
    refine pv_lt hD s _ ?_
    rw [List.getI_eq_getElem _ (by rw [D.length_pv hD]; exact hc)]
    exact List.getElem_mem _
  have hstate : D.wiresSt args (s + 1)
      = runGates WB (blkG (D.muxG s) 16 (D.baseMux s) (2 * D.M)) := by
    rw [wiresSt_succ hargs, Data.stage, runGates_append, runGates_append, ← hWA, ← hWB]
  have hidx : (D.pv (s + 1)).getI c = D.baseMux s + 16 * c + 15 := by
    rw [Data.pv_succ, Data.muxOut, getI_map _ _ (by simpa using hc), getI_range hc]
  have hblk := getI_blkG (v := WB) (g := D.muxG s) (len := 16)
    (fun d b => D.length_muxG s d b) hc (w := D.baseMux s + 16 * c + 15)
    (by rw [hWBlen]; omega)
  rw [hWBlen] at hblk
  have hmux2 := getI_gMux (v := W') (s := 2 * i) (a := D.baseMux s + 16 * c + 7)
    (b := (D.pv s).getI c)
    (by rw [hW'len, Data.baseMux, Data.base1, Data.baseOf, Data.baseS]; omega)
    (by rw [hW'len, Data.baseMux, Data.base1]; omega)
  rw [hW'len, wMux, show D.baseMux s + 16 * c + 8 + 7 = D.baseMux s + 16 * c + 15 by omega]
    at hmux2
  rw [hstate, hidx, hblk, blkG_succ, runGates_append, ← hWc, Data.muxG, hi', runGates_append,
    ← hW', hmux2, hW'low _ (by rw [Data.baseMux, Data.base1]; omega), hpres, hmux1, hbit,
    hW'low _ (by rw [Data.baseMux, Data.base1]; omega), hprev, h0v, h1v]
  -- the case distinction
  by_cases hpos : i < (args.getD 0 []).length
  · rw [decide_eq_true hpos, if_pos rfl]
    have hVv := Vv_succ (g := g) (h0 := h0) (h1 := h1) (args := args) hpos
    rcases hb : (args.getD 0 []).getI i with _ | _
    · rw [if_neg (by simp)]
      have hval : Vv g h0 h1 args i = h0 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail) := by
        rw [hVv, hb]
        rfl
      rw [hval, take_encStr (by rw [← hval]; exact hM i) S.le_B0]
    · rw [if_pos rfl]
      have hval : Vv g h0 h1 args i = h1 ((args.getD 0 []).drop (i + 1)
          :: Vv g h0 h1 args (i + 1) :: args.tail) := by
        rw [hVv, hb]
        rfl
      rw [hval, take_encStr (by rw [← hval]; exact hM i) S.le_B1]
  · rw [decide_eq_false hpos, if_neg (by simp)]
    have h1e : Vv g h0 h1 args i = g args.tail := Vv_of_le (by omega)
    have h2e : Vv g h0 h1 args (i + 1) = g args.tail := Vv_of_le (by omega)
    rw [h1e, h2e]

/-- **After `s` stages the wires of the value carry the value of the recursion.** -/
theorem stages_correct (hD : D.Ok) (S : Spec D g h0 h1) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) (hM : ∀ i, (Vv g h0 h1 args i).length ≤ D.M) :
    ∀ s ≤ D.n, ∀ c < 2 * D.M, (D.wiresSt args s).getI ((D.pv s).getI c)
      = (encStr D.M (Vv g h0 h1 args (D.n - s))).getI c := by
  have hkp : 1 ≤ D.k := hD.k_pos
  have hx0n : (args.getD 0 []).length ≤ D.n := by
    refine hlen _ ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  intro s
  induction s with
  | zero =>
      intro _ c hc
      have hgv : Vv g h0 h1 args (D.n - 0) = g args.tail := by
        rw [Nat.sub_zero]
        exact Vv_of_le hx0n
      have hblk : blkG D.stage D.L D.baseS 0 = [] := by simp [blkG]
      have hw0 : D.wiresSt args 0 = D.wiresPre args := by
        rw [Data.wiresSt, hblk, runGates_nil]
      rw [hw0, hgv, Data.pv_zero]
      exact gOut_correct hD S hargs hlen (by rw [← hgv]; exact hM _) c hc
  | succ s ihs =>
      intro hsn c hc
      exact stage_correct hD S hargs hlen hM (by omega) (ihs (by omega)) c hc

/-- **The circuit computes the recursion.** -/
theorem circ_correct (hD : D.Ok) (S : Spec D g h0 h1) (hargs : args.length = D.k)
    (hlen : ∀ a ∈ args, a.length ≤ D.n) (hM : ∀ i, (Vv g h0 h1 args i).length ≤ D.M) :
    D.circ.eval (encArgs D.k D.n args) = encStr D.M (brnFn g h0 h1 args) := by
  have hinp : (encArgs D.k D.n args).length = D.nin := by rw [length_encArgs]; rfl
  have hgTF : runGates (encArgs D.k D.n args) (gTF D.nin) = D.wires1 args := by
    rw [← hinp, runGates_gTF]
    rfl
  have hwires : D.circ.wires (encArgs D.k D.n args) = D.wiresSt args D.n := by
    rw [Data.circ, Circ.wires, Circ.gates_mk, Data.gates, runGates_append, runGates_append,
      hgTF]
    rfl
  rw [Circ.eval, hwires, Data.circ, Circ.out_mk]
  refine List.ext_getElem (by rw [List.length_map, D.length_pv hD, length_encStr]) ?_
  intro d hd1 hd2
  rw [List.length_map, D.length_pv hD] at hd1
  rw [← List.getI_eq_getElem _ (by rw [List.length_map, D.length_pv hD]; exact hd1),
    ← List.getI_eq_getElem _ (by rw [length_encStr]; exact hd1),
    getI_map _ _ (by rw [D.length_pv hD]; exact hd1)]
  have h := stages_correct hD S hargs hlen hM D.n le_rfl d hd1
  rwa [Nat.sub_self, Vv_zero] at h

end Stage

/-! ### The shape of the circuit -/

theorem circ_nin (D : Data) : D.circ.nin = 2 * D.n * D.k := rfl

theorem circ_out_lt (D : Data) (hD : D.Ok) :
    ∀ j ∈ D.circ.out, j < D.circ.nin + D.circ.gates.length := by
  intro j hj
  rw [Data.circ, Circ.out_mk] at hj
  have h := pv_lt hD D.n j hj
  rw [Data.baseOf, Data.baseS, Data.baseG] at h
  rw [Data.circ, Circ.nin_mk, Circ.gates_mk, D.length_gates]
  omega

/-! ### The construction is an algorithm -/

theorem pv_eq (D : Data) (s : ℕ) : D.pv s = if s = 0 then D.gOut else D.muxOut (s - 1) := by
  cases s with
  | zero => rfl
  | succ s => rfl

section Prim

variable {k : ℕ} {Mf : ℕ → ℕ} {CGf C0f C1f : ℕ → Circ}

/-- The data of the construction, as a function of the bound on the arguments. -/
def mkD (k : ℕ) (Mf : ℕ → ℕ) (CGf C0f C1f : ℕ → Circ) (n : ℕ) : Data :=
  ⟨n, k, Mf n, CGf n, C0f n, C1f n⟩

/-- **The circuit of the recursion is produced by an algorithm.** -/
theorem primrec_circ (hM : Primrec Mf) (hCG : Primrec CGf) (hC0 : Primrec C0f)
    (hC1 : Primrec C1f) : Primrec fun n => (mkD k Mf CGf C0f C1f n).circ := by
  -- the numerical parameters
  have hnin : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).nin := primrec_nin_mul k
  have hwF : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).wF :=
    Primrec.nat_add.comp hnin (Primrec.const 1)
  have hg0 : Primrec fun n : ℕ => (C0f n).gates.length :=
    Primrec.list_length.comp ((Primrec.fst.comp (Primrec.snd.comp hC0)).of_eq fun _ => rfl)
  have hg1 : Primrec fun n : ℕ => (C1f n).gates.length :=
    Primrec.list_length.comp ((Primrec.fst.comp (Primrec.snd.comp hC1)).of_eq fun _ => rfl)
  have hgG : Primrec fun n : ℕ => (CGf n).gates.length :=
    Primrec.list_length.comp ((Primrec.fst.comp (Primrec.snd.comp hCG)).of_eq fun _ => rfl)
  have hbaseG : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).baseG :=
    Primrec.nat_add.comp hnin (Primrec.const 2)
  have hbaseS : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).baseS :=
    Primrec.nat_add.comp hbaseG hgG
  have hL : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).L :=
    Primrec.nat_add.comp (Primrec.nat_add.comp hg0 hg1)
      (Primrec.nat_mul.comp (Primrec.const 32) hM)
  have hbaseOf : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).baseOf p.2 :=
    Primrec.nat_add.comp (hbaseS.comp Primrec.fst)
      (Primrec.nat_mul.comp (hL.comp Primrec.fst) Primrec.snd)
  have hbase1 : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).base1 p.2 :=
    Primrec.nat_add.comp hbaseOf (hg0.comp Primrec.fst)
  have hbaseMux : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).baseMux p.2 :=
    Primrec.nat_add.comp hbase1 (hg1.comp Primrec.fst)
  -- the source wires
  have hcell : Primrec fun q : (ℕ × ℕ) × ℕ =>
      (mkD k Mf CGf C0f C1f q.1.1).cellSrc q.1.2 q.2 := by
    refine Primrec.ite (c := fun q : (ℕ × ℕ) × ℕ => q.2 < q.1.1)
      (PrimrecRel.comp Primrec.nat_lt Primrec.snd (Primrec.fst.comp Primrec.fst)) ?_ ?_
    · have hbb : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 + 2 * q.2 :=
        Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      exact Primrec.list_cons.comp hbb
        (Primrec.list_cons.comp (Primrec.nat_add.comp hbb (Primrec.const 1))
          (Primrec.const []))
    · have hf : Primrec fun q : (ℕ × ℕ) × ℕ => (mkD k Mf CGf C0f C1f q.1.1).wF :=
        hwF.comp (Primrec.fst.comp Primrec.fst)
      exact Primrec.list_cons.comp hf (Primrec.list_cons.comp hf (Primrec.const []))
  have hargSrc : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).argSrc p.2 := by
    refine Primrec.list_flatMap (Primrec.list_range.comp (hM.comp Primrec.fst)) ?_
    refine hcell.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  have hxSrc : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).xSrc p.2 := by
    refine Primrec.list_flatMap (Primrec.list_range.comp (hM.comp Primrec.fst)) ?_
    refine hcell.comp (Primrec.pair (Primrec.pair
      (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))
  have htailSrc : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).tailSrc := by
    refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.const (k - 1))) ?_
    exact hargSrc.comp (Primrec.pair Primrec.fst
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))
  -- the wires of the values
  have hgOut : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).gOut := by
    have hrel : Primrec fun n : ℕ => relocOut (CGf n) (mkD k Mf CGf C0f C1f n).baseG
        ((mkD k Mf CGf C0f C1f n).tailSrc) := primrec_relocOut hCG hbaseG htailSrc
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) hM)) ?_
    exact Primrec.list_getI.comp (hrel.comp Primrec.fst) Primrec.snd
  have hmuxOut : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).muxOut p.2 := by
    refine Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (hM.comp Primrec.fst))) ?_
    exact Primrec.nat_add.comp (Primrec.nat_add.comp (hbaseMux.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 16) Primrec.snd)) (Primrec.const 15)
  have hpv : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).pv p.2 := by
    have h : Primrec fun p : ℕ × ℕ =>
        if p.2 = 0 then (mkD k Mf CGf C0f C1f p.1).gOut
        else (mkD k Mf CGf C0f C1f p.1).muxOut (p.2 - 1) := by
      refine Primrec.ite (c := fun p : ℕ × ℕ => p.2 = 0)
        (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0))
        (hgOut.comp Primrec.fst) ?_
      exact hmuxOut.comp (Primrec.pair Primrec.fst
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
    exact h.of_eq fun p => (pv_eq _ _).symm
  have hsrcS : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).srcS p.2 := by
    refine Primrec.list_append.comp
      (hxSrc.comp (Primrec.pair Primrec.fst
        (Primrec.nat_sub.comp Primrec.fst Primrec.snd)))
      (Primrec.list_append.comp hpv (htailSrc.comp Primrec.fst))
  have ha0w : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).a0w p.2 := by
    have hrel : Primrec fun p : ℕ × ℕ => relocOut (C0f p.1)
        ((mkD k Mf CGf C0f C1f p.1).baseOf p.2) ((mkD k Mf CGf C0f C1f p.1).srcS p.2) :=
      primrec_relocOut (hC0.comp Primrec.fst) hbaseOf hsrcS
    refine Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (hM.comp Primrec.fst))) ?_
    exact Primrec.list_getI.comp (hrel.comp Primrec.fst) Primrec.snd
  have ha1w : Primrec fun p : ℕ × ℕ => (mkD k Mf CGf C0f C1f p.1).a1w p.2 := by
    have hrel : Primrec fun p : ℕ × ℕ => relocOut (C1f p.1)
        ((mkD k Mf CGf C0f C1f p.1).base1 p.2) ((mkD k Mf CGf C0f C1f p.1).srcS p.2) :=
      primrec_relocOut (hC1.comp Primrec.fst) hbase1 hsrcS
    refine Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (hM.comp Primrec.fst))) ?_
    exact Primrec.list_getI.comp (hrel.comp Primrec.fst) Primrec.snd
  -- the multiplexers
  have hmuxG : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
      (mkD k Mf CGf C0f C1f q.1.1.1).muxG q.1.1.2 q.1.2 q.2 := by
    have hns : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ => q.1.1.1 - 1 - q.1.1.2 :=
      Primrec.nat_sub.comp (Primrec.nat_sub.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hpair : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ => (q.1.1.1, q.1.1.2) :=
      Primrec.fst.comp Primrec.fst
    have ha1 : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
        ((mkD k Mf CGf C0f C1f q.1.1.1).a1w q.1.1.2).getI q.1.2 :=
      Primrec.list_getI.comp (ha1w.comp hpair) (Primrec.snd.comp Primrec.fst)
    have ha0 : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
        ((mkD k Mf CGf C0f C1f q.1.1.1).a0w q.1.1.2).getI q.1.2 :=
      Primrec.list_getI.comp (ha0w.comp hpair) (Primrec.snd.comp Primrec.fst)
    have hpvc : Primrec fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
        ((mkD k Mf CGf C0f C1f q.1.1.1).pv q.1.1.2).getI q.1.2 :=
      Primrec.list_getI.comp (hpv.comp hpair) (Primrec.snd.comp Primrec.fst)
    refine Primrec.list_append.comp
      (primrec_gMux Primrec.snd
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hns) (Primrec.const 1))
        ha1 ha0)
      (primrec_gMux (Primrec.nat_add.comp Primrec.snd (Primrec.const 8))
        (Primrec.nat_mul.comp (Primrec.const 2) hns)
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 7)) hpvc)
  -- the stages
  have hstage : Primrec fun p : (ℕ × ℕ) × ℕ =>
      (mkD k Mf CGf C0f C1f p.1.1).stage p.1.2 p.2 := by
    have hpair : Primrec fun p : (ℕ × ℕ) × ℕ => (p.1.1, p.1.2) := Primrec.fst
    refine Primrec.list_append.comp (Primrec.list_append.comp
      (primrec_relocGates (hC0.comp (Primrec.fst.comp Primrec.fst)) (hbaseOf.comp hpair)
        (hsrcS.comp hpair))
      (primrec_relocGates (hC1.comp (Primrec.fst.comp Primrec.fst)) (hbase1.comp hpair)
        (hsrcS.comp hpair))) ?_
    refine primrec_blkG (g := fun p : (ℕ × ℕ) × ℕ =>
        fun c b => (mkD k Mf CGf C0f C1f p.1.1).muxG p.1.2 c b) ?_ (Primrec.const 16)
      (hbaseMux.comp hpair)
      (Primrec.nat_mul.comp (Primrec.const 2) (hM.comp (Primrec.fst.comp Primrec.fst)))
    exact hmuxG.comp (Primrec.pair (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  -- the whole circuit
  have hgates : Primrec fun n : ℕ => (mkD k Mf CGf C0f C1f n).gates := by
    refine Primrec.list_append.comp (primrec_gTF hnin) (Primrec.list_append.comp
      (primrec_relocGates hCG hbaseG htailSrc) ?_)
    exact primrec_blkG (g := fun n : ℕ => fun s b => (mkD k Mf CGf C0f C1f n).stage s b)
      (hstage.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst)) Primrec.snd))
      hL hbaseS Primrec.id
  exact Primrec.pair hnin (Primrec.pair hgates
    (hpv.comp (Primrec.pair Primrec.id Primrec.id)))

end Prim

/-- The data of the construction at the bound `n`, the width of the values being the value of a
polynomial and the three circuits being taken from three families at that width. -/
def dataOf (k : ℕ) (q : Polynomial ℕ) (CGf C0f C1f : ℕ → Circ) (n : ℕ) : Data :=
  mkD k (fun m => q.eval m) (fun m => CGf (q.eval m)) (fun m => C0f (q.eval m))
    (fun m => C1f (q.eval m)) n

theorem argSize_le {l : Args} {n : ℕ} (h : ∀ a ∈ l, a.length ≤ n) : argSize l ≤ n := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [argSize_cons]
      exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem length_getD_le {l : Args} {n : ℕ} (r : ℕ) (h : ∀ a ∈ l, a.length ≤ n) :
    (l.getD r []).length ≤ n := by
  by_cases hr : r < l.length
  · exact h _ (by rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

end Brn

/-! ### The family -/

theorem circFam_brn {g h0 h1 : Fn} (Fg : ∀ k, Nonempty (CircFam g k))
    (F0 : ∀ k, Nonempty (CircFam h0 k)) (F1 : ∀ k, Nonempty (CircFam h1 k))
    {bd : Fn} (hbd : ∀ args, (brnFn g h0 h1 args).length ≤ (bd args).length)
    (pbd : Polynomial ℕ) (hpbd : ∀ args, (bd args).length ≤ pbd.eval (argSize args))
    (k : ℕ) : Nonempty (CircFam (brnFn g h0 h1) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- with no arguments the recursion is the base function
    obtain ⟨FG⟩ := Fg 0
    refine circFam_congr FG ?_
    intro args hargs
    rw [List.length_eq_zero_iff.1 hargs]
    rfl
  -- the three families, widened so that they have at least `2 * M` output wires
  obtain ⟨FG0⟩ := Fg (k - 1)
  obtain ⟨FG, hFGB⟩ := circFam_widen FG0 (FG0.B + Polynomial.X) fun n => by simp
  obtain ⟨FA0⟩ := F0 (k + 1)
  obtain ⟨G0, hG0B⟩ := circFam_widen FA0 (FA0.B + Polynomial.X) fun n => by simp
  obtain ⟨FA1⟩ := F1 (k + 1)
  obtain ⟨G1, hG1B⟩ := circFam_widen FA1 (FA1.B + Polynomial.X) fun n => by simp
  -- the width of the values
  have hqM : ∀ m : ℕ, m ≤ (Polynomial.X + pbd).eval m := fun m => by simp
  have hGB : ∀ m : ℕ, m ≤ FG.B.eval m := fun m => by rw [hFGB]; simp
  have h0B : ∀ m : ℕ, m ≤ G0.B.eval m := fun m => by rw [hG0B]; simp
  have h1B : ∀ m : ℕ, m ≤ G1.B.eval m := fun m => by rw [hG1B]; simp
  -- the data is well formed
  have hOk : ∀ n, (Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).Ok := by
    intro n
    exact
      { k_pos := hk
        n_le := hqM n
        ninG := FG.nin_eq _
        nin0 := G0.nin_eq _
        nin1 := G1.nin_eq _
        outG := by
          show 2 * (Polynomial.X + pbd).eval n
            ≤ (FG.C ((Polynomial.X + pbd).eval n)).out.length
          rw [FG.out_length]
          exact Nat.mul_le_mul_left 2 (hGB _)
        out0 := by
          show 2 * (Polynomial.X + pbd).eval n
            ≤ (G0.C ((Polynomial.X + pbd).eval n)).out.length
          rw [G0.out_length]
          exact Nat.mul_le_mul_left 2 (h0B _)
        out1 := by
          show 2 * (Polynomial.X + pbd).eval n
            ≤ (G1.C ((Polynomial.X + pbd).eval n)).out.length
          rw [G1.out_length]
          exact Nat.mul_le_mul_left 2 (h1B _)
        outG_lt := FG.out_lt _
        out0_lt := G0.out_lt _
        out1_lt := G1.out_lt _ }
  -- every value of the recursion is short
  have hVb : ∀ (n : ℕ) (args : Args), (∀ a ∈ args, a.length ≤ n) → ∀ i,
      (Brn.Vv g h0 h1 args i).length ≤ (Polynomial.X + pbd).eval n := by
    intro n args hlen i
    rw [Brn.Vv_eq_brnFn]
    refine le_trans (hbd _) (le_trans (hpbd _) ?_)
    have hsz : argSize ((args.getD 0 []).drop i :: args.tail) ≤ n := by
      refine Brn.argSize_le ?_
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact le_trans (by simp) (Brn.length_getD_le 0 hlen)
      · exact hlen a (List.mem_of_mem_tail ha)
    refine le_trans (Polynomial.eval_mono_nat _ hsz) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X]
    omega
  refine ⟨{
    C := fun n => (Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).circ
    B := Polynomial.X + pbd
    bnd := Polynomial.C 2 * Polynomial.X * Polynomial.C k + Polynomial.C 2
      + FG.bnd.comp (Polynomial.X + pbd)
      + (G0.bnd.comp (Polynomial.X + pbd) + G1.bnd.comp (Polynomial.X + pbd)
          + Polynomial.C 32 * (Polynomial.X + pbd)) * Polynomial.X
      + Polynomial.C 2 * (Polynomial.X + pbd)
    nin_eq := fun n => rfl
    primC := ?_
    size_le := ?_
    out_lt := fun n => Brn.circ_out_lt _ (hOk n)
    len_le := ?_
    correct := ?_ }⟩
  · exact Brn.primrec_circ (primrec_poly_eval _) (FG.primC.comp (primrec_poly_eval _))
      (G0.primC.comp (primrec_poly_eval _)) (G1.primC.comp (primrec_poly_eval _))
  · intro n
    have hnin : ((Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).circ).nin = 2 * n * k :=
      Brn.circ_nin _
    have hgates : ((Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).circ).gates.length
        = 2 + ((FG.C ((Polynomial.X + pbd).eval n)).gates.length
          + ((G0.C ((Polynomial.X + pbd).eval n)).gates.length
            + (G1.C ((Polynomial.X + pbd).eval n)).gates.length
            + 32 * (Polynomial.X + pbd).eval n) * n) :=
      (Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).length_gates
    have hout : ((Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).circ).out.length
        = 2 * (Polynomial.X + pbd).eval n :=
      (Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n).length_pv (hOk n) n
    have hCGb : (FG.C ((Polynomial.X + pbd).eval n)).gates.length
        ≤ FG.bnd.eval ((Polynomial.X + pbd).eval n) := by
      have h := FG.size_le ((Polynomial.X + pbd).eval n)
      rw [Circ.size] at h
      omega
    have hC0b : (G0.C ((Polynomial.X + pbd).eval n)).gates.length
        ≤ G0.bnd.eval ((Polynomial.X + pbd).eval n) := by
      have h := G0.size_le ((Polynomial.X + pbd).eval n)
      rw [Circ.size] at h
      omega
    have hC1b : (G1.C ((Polynomial.X + pbd).eval n)).gates.length
        ≤ G1.bnd.eval ((Polynomial.X + pbd).eval n) := by
      have h := G1.size_le ((Polynomial.X + pbd).eval n)
      rw [Circ.size] at h
      omega
    have hLn : ((G0.C ((Polynomial.X + pbd).eval n)).gates.length
          + (G1.C ((Polynomial.X + pbd).eval n)).gates.length
          + 32 * (Polynomial.X + pbd).eval n) * n
        ≤ (G0.bnd.eval ((Polynomial.X + pbd).eval n)
          + G1.bnd.eval ((Polynomial.X + pbd).eval n)
          + 32 * (Polynomial.X + pbd).eval n) * n :=
      Nat.mul_le_mul_right n (by omega)
    rw [Circ.size, hnin, hgates, hout]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_comp] at hCGb hC0b hC1b hLn ⊢
    omega
  · intro n args hargs hlen
    have h := hVb n args hlen 0
    rwa [Brn.Vv_zero] at h
  · intro n args hargs hlen
    have S : Brn.Spec (Brn.dataOf k (Polynomial.X + pbd) FG.C G0.C G1.C n) g h0 h1 := by
      refine
        { BG := FG.B.eval ((Polynomial.X + pbd).eval n)
          B0 := G0.B.eval ((Polynomial.X + pbd).eval n)
          B1 := G1.B.eval ((Polynomial.X + pbd).eval n)
          le_BG := hGB _
          le_B0 := h0B _
          le_B1 := h1B _
          evalG := ?_
          eval0 := ?_
          eval1 := ?_ }
      · intro as ha hb
        exact FG.correct _ as ha hb
      · intro as ha hb
        exact G0.correct _ as ha hb
      · intro as ha hb
        exact G1.correct _ as ha hb
    exact Brn.circ_correct (hOk n) S hargs hlen (hVb n args hlen)

end Compile

end HTN
