import ComplexityTheory.Compile.Fam
/-!
# The circuits of Cobham's class: the base cases and the placement lemmas

This file carries the first half of the induction announced in
`ComplexityTheory/Compile/Fam.lean`: the circuit families of the base cases that do not
compute (the constant empty string, the projections and the successors), the widening of the
output bound of a family, and the two ways of placing one circuit next to or on top of another
(`HTN.Compile.stackCirc`, `HTN.Compile.feedCirc`) with their correctness and their
primitive recursiveness.

The remaining cases are in `ComplexityTheory/Compile/Smash.lean` (the smash function),
`ComplexityTheory/Compile/Brn.lean` (bounded recursion on notation) and
`ComplexityTheory/Compile/CobCirc.lean` (composition and the induction itself).
-/


namespace HTN

namespace Compile

open PTime

/-! ### Reading a list off its own indices -/

theorem eq_map_range_getI (l : List Bool) : (List.range l.length).map l.getI = l := by
  refine List.ext_getElem (by simp) ?_
  intro i hi hi'
  rw [List.getElem_map, List.getElem_range, List.getI_eq_getElem _ (by simpa using hi')]

/-! ### Two computations of the cell encoding -/

theorem encStr_nil (B : ℕ) : encStr B [] = List.replicate (2 * B) false := by
  refine List.ext_getElem (by simp) ?_
  intro i hi hi'
  rw [length_encStr] at hi
  have h := getI_flatMap_range (m := 2) (k := B)
    (f := fun j => [decide (j < ([] : List Bool).length), ([] : List Bool).getI j])
    (fun _ => rfl) (j := i / 2) (r := i % 2) (by omega) (by omega)
  rw [show 2 * (i / 2) + i % 2 = i by omega] at h
  rw [List.getElem_replicate]
  rw [← List.getI_eq_getElem _ (by simpa using hi)]
  rw [encStr, h]
  rcases (show i % 2 = 0 ∨ i % 2 = 1 by omega) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

theorem encStr_cons (n : ℕ) (b : Bool) (x : List Bool) :
    encStr (n + 1) (b :: x) = [true, b] ++ encStr n x := by
  rw [encStr, encStr, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  congr 1
  simp

/-! ### Evaluating the two shapes of circuit the base cases use -/

theorem eval_nogates (nin : ℕ) (out : List ℕ) (inp : List Bool) :
    Circ.eval (nin, [], out) inp = out.map inp.getI := rfl

theorem eval_gTF (nin : ℕ) (out : List ℕ) (inp : List Bool) (h : inp.length = nin) :
    Circ.eval (nin, gTF nin, out) inp = out.map (inp ++ [true, false]).getI := by
  have hw : Circ.wires (nin, gTF nin, out) inp = inp ++ [true, false] := by
    rw [Circ.wires, Circ.gates_mk, ← h, runGates_gTF]
  rw [Circ.eval, hw, Circ.out_mk]

/-! ### The family of a function that is always empty -/

/-- **The family of a function whose value on arguments of the right arity is empty.** -/
theorem circFam_nil {f : Fn} {k : ℕ} (hf : ∀ args : Args, args.length = k → f args = []) :
    Nonempty (CircFam f k) := by
  refine ⟨{
    C := fun n => (2 * n * k, [], [])
    B := 0
    bnd := Polynomial.C (2 * k) * Polynomial.X
    nin_eq := fun n => rfl
    primC := ?_
    size_le := ?_
    out_lt := fun n j hj => absurd hj (by simp)
    len_le := ?_
    correct := ?_ }⟩
  · exact Primrec.pair (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const k))
      (Primrec.pair (Primrec.const []) (Primrec.const []))
  · intro n
    simp only [Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk, List.length_nil,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    nlinarith
  · intro n args hargs _
    rw [hf args hargs]
    simp
  · intro n args hargs _
    rw [eval_nogates, hf args hargs]
    simp [encStr]

/-! ### The constant empty string -/

theorem circFam_empty (k : ℕ) : Nonempty (CircFam (fun _ => []) k) :=
  circFam_nil fun _ _ => rfl

/-! ### The projections -/

theorem circFam_proj (m k : ℕ) : Nonempty (CircFam (proj m) k) := by
  by_cases hm : m < k
  · refine ⟨{
      C := fun n => (2 * n * k, [], (List.range (2 * n)).map fun r => 2 * n * m + r)
      B := Polynomial.X
      bnd := Polynomial.C (2 * k) * Polynomial.X + Polynomial.C 2 * Polynomial.X
      nin_eq := fun n => rfl
      primC := ?_
      size_le := ?_
      out_lt := ?_
      len_le := ?_
      correct := ?_ }⟩
    · refine Primrec.pair (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const k))
        (Primrec.pair (Primrec.const []) ?_)
      refine Primrec.list_map
        (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)) ?_
      exact Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
          (Primrec.const m)) Primrec.snd
    · intro n
      simp only [Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk, List.length_nil,
        List.length_map, List.length_range, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      nlinarith
    · intro n j hj
      simp only [Circ.out_mk, Circ.nin_mk, Circ.gates_mk, List.length_nil, List.mem_map,
        List.mem_range] at hj ⊢
      obtain ⟨r, hr, rfl⟩ := hj
      nlinarith
    · intro n args hargs hlen
      simp only [Polynomial.eval_X, proj]
      refine hlen _ ?_
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    · intro n args hargs hlen
      rw [eval_nogates, List.map_map]
      have hx : ∀ r ∈ List.range (2 * n),
          ((encArgs k n args).getI ∘ fun r => 2 * n * m + r) r
            = (encStr n (args.getD m [])).getI r := by
        intro r hr
        rw [List.mem_range] at hr
        show (encArgs k n args).getI (2 * n * m + r) = _
        exact getI_encArgs hm hr
      rw [List.map_congr_left hx]
      have : (encStr n (args.getD m [])).length = 2 * n := length_encStr _ _
      rw [← this, eq_map_range_getI]
      simp [proj]
  · refine circFam_nil fun args hargs => ?_
    rw [proj, List.getD_eq_default]
    omega

/-! ### The successors -/

theorem circFam_cons (b : Bool) (k : ℕ) : Nonempty (CircFam (consFn b) k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- with no arguments the value is the constant `[b]`
    refine ⟨{
      C := fun n => (0, gTF 0, [wTrue 0, if b then wTrue 0 else wFalse 0])
      B := Polynomial.C 1
      bnd := Polynomial.C 4
      nin_eq := fun n => by simp [Circ.nin]
      primC := Primrec.const _
      size_le := fun n => by simp [Circ.size, gTF]
      out_lt := fun n j hj => by
        cases b <;> simp only [Circ.out_mk, List.mem_cons, List.not_mem_nil, or_false] at hj <;>
          rcases hj with rfl | rfl <;> simp [wTrue, wFalse]
      len_le := ?_
      correct := ?_ }⟩
    · intro n args hargs _
      rw [List.length_eq_zero_iff.1 hargs]
      simp [consFn]
    · intro n args hargs _
      rw [List.length_eq_zero_iff.1 hargs]
      have hlen : (encArgs 0 n ([] : Args)).length = 0 := by simp
      rw [eval_gTF 0 _ _ hlen, List.length_eq_zero_iff.1 hlen]
      cases b <;> simp [consFn, encStr, wTrue, wFalse]
  · refine ⟨{
      C := fun n => (2 * n * k, gTF (2 * n * k),
        wTrue (2 * n * k) :: (if b then wTrue (2 * n * k) else wFalse (2 * n * k)) ::
          List.range (2 * n))
      B := Polynomial.X + Polynomial.C 1
      bnd := Polynomial.C (2 * k) * Polynomial.X + Polynomial.C 2 * Polynomial.X +
        Polynomial.C 4
      nin_eq := fun n => rfl
      primC := ?_
      size_le := ?_
      out_lt := ?_
      len_le := ?_
      correct := ?_ }⟩
    · have hnin : Primrec fun n : ℕ => 2 * n * k :=
        Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
          (Primrec.const k)
      have hT : Primrec fun n : ℕ => wTrue (2 * n * k) := hnin
      have hF : Primrec fun n : ℕ => wFalse (2 * n * k) :=
        Primrec.nat_add.comp hnin (Primrec.const 1)
      have hgates : Primrec fun n : ℕ => gTF (2 * n * k) :=
        Primrec.list_cons.comp (Primrec.pair hnin hnin)
          (Primrec.list_cons.comp (Primrec.pair hnin hnin) (Primrec.const []))
      have hmid : Primrec fun n : ℕ =>
          (if b then wTrue (2 * n * k) else wFalse (2 * n * k)) := by
        cases b
        · simpa using hF
        · simpa using hT
      exact Primrec.pair hnin (Primrec.pair hgates
        (Primrec.list_cons.comp hT (Primrec.list_cons.comp hmid
          (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))))
    · intro n
      simp only [Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk, length_gTF,
        List.length_cons, List.length_range, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      nlinarith
    · intro n j hj
      simp only [Circ.out_mk, Circ.nin_mk, Circ.gates_mk, length_gTF, List.mem_cons,
        List.mem_range] at hj ⊢
      have hkn : 2 * n ≤ 2 * n * k := by nlinarith
      rcases hj with rfl | rfl | hj
      · simp [wTrue]
      · cases b <;> simp [wTrue, wFalse]
      · omega
    · intro n args hargs hlen
      have h0 : (args.getD 0 []).length ≤ n := by
        refine hlen _ ?_
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      simp only [consFn, List.length_cons, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_X]
      omega
    · intro n args hargs hlen
      have hnin : (encArgs k n args).length = 2 * n * k := by simp
      rw [eval_gTF _ _ _ hnin]
      have hT : ((encArgs k n args) ++ [true, false]).getI (wTrue (2 * n * k)) = true := by
        have := getI_wTrue (encArgs k n args)
        rwa [runGates_gTF, hnin] at this
      have hF : ((encArgs k n args) ++ [true, false]).getI (wFalse (2 * n * k)) = false := by
        have := getI_wFalse (encArgs k n args)
        rwa [runGates_gTF, hnin] at this
      have hblock : ∀ r ∈ List.range (2 * n),
          ((encArgs k n args) ++ [true, false]).getI r
            = (encStr n (args.getD 0 [])).getI r := by
        intro r hr
        rw [List.mem_range] at hr
        have hlt : r < (encArgs k n args).length := by
          rw [hnin]; nlinarith
        rw [List.getI_append _ _ _ hlt]
        have := getI_encArgs (k := k) (n := n) (j := 0) (r := r) (args := args) (by omega) hr
        simpa using this
      simp only [List.map_cons, hT]
      rw [List.map_congr_left hblock]
      have hlen2 : (encStr n (args.getD 0 [])).length = 2 * n := length_encStr _ _
      rw [← hlen2, eq_map_range_getI]
      have hev : (Polynomial.X + Polynomial.C 1 : Polynomial ℕ).eval n = n + 1 := by simp
      rw [hev, consFn, encStr_cons]
      cases b <;> simp [hT, hF]

/-! ### Widening the output bound of a family -/

theorem flatMap_ff (m : ℕ) :
    (List.range m).flatMap (fun _ => [false, false]) = List.replicate (2 * m) false := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, show 2 * (m + 1) = 2 * m + 2 by ring, List.replicate_add]
      rfl

theorem getI_eval (C : Circ) (inp : List Bool) {i : ℕ} (hi : i < C.out.length) :
    (C.eval inp).getI i = (C.wires inp).getI (C.out.getI i) := by
  rw [Circ.eval, List.getI_eq_getElem _ (by simpa using hi), List.getElem_map,
    List.getI_eq_getElem _ hi]

theorem encArgs_cons (J B : ℕ) (a : List Bool) (as : Args) :
    encArgs (J + 1) B (a :: as) = encStr B a ++ encArgs J B as := by
  rw [encArgs, encArgs, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  congr 1

/-- The wires of a circuit family, as a primitive recursive function of the bound. -/
theorem primrec_gates {f : Fn} {k : ℕ} (F : CircFam f k) :
    Primrec fun n => (F.C n).gates :=
  (Primrec.fst.comp (Primrec.snd.comp F.primC)).of_eq fun _ => rfl

theorem primrec_out {f : Fn} {k : ℕ} (F : CircFam f k) :
    Primrec fun n => (F.C n).out :=
  (Primrec.snd.comp (Primrec.snd.comp F.primC)).of_eq fun _ => rfl

theorem primrec_nin_mul (k : ℕ) : Primrec fun n : ℕ => 2 * n * k :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const k)

/-- **The output bound of a family may be raised.** -/
theorem circFam_widen {f : Fn} {k : ℕ} (F : CircFam f k) (B' : Polynomial ℕ)
    (hB : ∀ n, F.B.eval n ≤ B'.eval n) : ∃ G : CircFam f k, G.B = B' := by
  refine ⟨{
    C := fun n => (2 * n * k,
      (F.C n).gates ++ gTF (2 * n * k + (F.C n).gates.length),
      (F.C n).out ++ (List.range (2 * (B'.eval n - F.B.eval n))).map
        fun _ => wFalse (2 * n * k + (F.C n).gates.length))
    B := B'
    bnd := F.bnd + Polynomial.C 2 * B' + Polynomial.C 2
    nin_eq := fun n => rfl
    primC := ?_
    size_le := ?_
    out_lt := ?_
    len_le := fun n args ha hl => le_trans (F.len_le n args ha hl) (hB n)
    correct := ?_ }, rfl⟩
  · have hnin := primrec_nin_mul k
    have hg := primrec_gates F
    have hbase : Primrec fun n : ℕ => 2 * n * k + (F.C n).gates.length :=
      Primrec.nat_add.comp hnin (Primrec.list_length.comp hg)
    have hgTF : Primrec fun n : ℕ => gTF (2 * n * k + (F.C n).gates.length) :=
      Primrec.list_cons.comp (Primrec.pair hbase hbase)
        (Primrec.list_cons.comp (Primrec.pair hbase hbase) (Primrec.const []))
    have hm : Primrec fun n : ℕ => 2 * (B'.eval n - F.B.eval n) :=
      Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (primrec_poly_eval B') (primrec_poly_eval F.B))
    have hrep : Primrec fun n : ℕ =>
        (List.range (2 * (B'.eval n - F.B.eval n))).map
          fun _ => wFalse (2 * n * k + (F.C n).gates.length) :=
      Primrec.list_map (Primrec.list_range.comp hm)
        ((Primrec.nat_add.comp (hbase.comp Primrec.fst) (Primrec.const 1)).of_eq fun _ => rfl)
    exact Primrec.pair hnin (Primrec.pair (Primrec.list_append.comp hg hgTF)
      (Primrec.list_append.comp (primrec_out F) hrep))
  · intro n
    have hF := F.size_le n
    rw [Circ.size, F.nin_eq n] at hF
    simp only [Circ.size, Circ.nin_mk, Circ.gates_mk, Circ.out_mk, List.length_append,
      length_gTF, List.length_map, List.length_range, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C]
    have : B'.eval n - F.B.eval n ≤ B'.eval n := by omega
    omega
  · intro n j hj
    have hF := F.out_lt n
    rw [F.nin_eq n] at hF
    simp only [Circ.out_mk, Circ.nin_mk, Circ.gates_mk, List.length_append, length_gTF,
      List.mem_append, List.mem_map, List.mem_range] at hj ⊢
    rcases hj with hj | ⟨r, hr, rfl⟩
    · have := hF j hj; omega
    · simp only [wFalse]; omega
  · intro n args hargs hlen
    have hinp : (encArgs k n args).length = (F.C n).nin := by
      rw [F.nin_eq n]; simp
    have hW : ((F.C n).wires (encArgs k n args)).length = 2 * n * k + (F.C n).gates.length := by
      rw [Circ.wires, length_runGates, hinp, F.nin_eq n]
    have hwires : Circ.wires (2 * n * k,
        (F.C n).gates ++ gTF (2 * n * k + (F.C n).gates.length),
        (F.C n).out ++ (List.range (2 * (B'.eval n - F.B.eval n))).map
          fun _ => wFalse (2 * n * k + (F.C n).gates.length)) (encArgs k n args)
        = (F.C n).wires (encArgs k n args) ++ [true, false] := by
      rw [Circ.wires, Circ.gates_mk, runGates_append, ← Circ.wires, ← hW, runGates_gTF]
    rw [Circ.eval, hwires, Circ.out_mk, List.map_append]
    have hfst : ((F.C n).out).map
        (((F.C n).wires (encArgs k n args) ++ [true, false]).getI)
        = (F.C n).eval (encArgs k n args) := by
      rw [Circ.eval]
      refine List.map_congr_left ?_
      intro j hj
      have := F.out_lt n j hj
      rw [F.nin_eq n] at this
      exact List.getI_append _ _ _ (by rw [hW]; omega)
    have hsnd : (((List.range (2 * (B'.eval n - F.B.eval n))).map
        fun _ => wFalse (2 * n * k + (F.C n).gates.length)).map
        (((F.C n).wires (encArgs k n args) ++ [true, false]).getI))
        = List.replicate (2 * (B'.eval n - F.B.eval n)) false := by
      rw [List.map_map]
      have hval : ((F.C n).wires (encArgs k n args) ++ [true, false]).getI
          (wFalse (2 * n * k + (F.C n).gates.length)) = false := by
        rw [wFalse, ← hW, List.getI_eq_getElem _ (by simp)]
        simp
      rw [show ((((F.C n).wires (encArgs k n args) ++ [true, false]).getI) ∘
          fun _ : ℕ => wFalse (2 * n * k + (F.C n).gates.length)) = fun _ => false from
        funext fun _ => hval]
      rw [List.map_const', List.length_range]
    rw [hfst, hsnd, F.correct n args hargs hlen]
    rw [encStr_widen (F.len_le n args hargs hlen) (hB n), flatMap_ff]

/-! ### Placing one circuit on top of another -/

/-- The values the relocated outputs of a circuit carry. -/
theorem values_after (W : List Bool) (C2 : Circ) (srcs : List ℕ) (inp2 : List Bool)
    (hlt : ∀ i, i < C2.nin → srcs.getI i < W.length) (hinp2 : inp2.length = C2.nin)
    (hval : ∀ i, i < C2.nin → W.getI (srcs.getI i) = inp2.getI i) :
    (relocOut C2 W.length srcs).map (runGates W (relocGates C2 W.length srcs)).getI
      = C2.eval inp2 := by
  rw [relocOut, List.map_map, Circ.eval]
  refine List.map_congr_left ?_
  intro j _
  exact getI_relocOut j hlt hinp2 hval

/-- The values the outputs already present keep. -/
theorem values_before (W : List Bool) (C2 : Circ) (srcs : List ℕ) (out1 : List ℕ)
    (h : ∀ j ∈ out1, j < W.length) :
    out1.map (runGates W (relocGates C2 W.length srcs)).getI = out1.map W.getI := by
  refine List.map_congr_left ?_
  intro j hj
  exact getI_runGates_of_lt (h j hj)

theorem getI_range {nin i : ℕ} (h : i < nin) : (List.range nin).getI i = i := by
  rw [List.getI_eq_getElem _ (by simpa using h), List.getElem_range]

/-- **Two circuits side by side**, both reading the same inputs; the outputs are concatenated. -/
def stackCirc (nin : ℕ) (C1 C2 : Circ) : Circ :=
  (nin, C1.gates ++ relocGates C2 (nin + C1.gates.length) (List.range nin),
    C1.out ++ relocOut C2 (nin + C1.gates.length) (List.range nin))

/-- **One circuit fed by another**: the inputs of `C2` are the outputs of `C1`. -/
def feedCirc (nin : ℕ) (C1 C2 : Circ) : Circ :=
  (nin, C1.gates ++ relocGates C2 (nin + C1.gates.length) C1.out,
    relocOut C2 (nin + C1.gates.length) C1.out)

section Place

variable {nin : ℕ} {C1 C2 : Circ} {inp : List Bool}

theorem wires_length (hinp : inp.length = nin) :
    (C1.wires inp).length = nin + C1.gates.length := by
  rw [Circ.wires, length_runGates, hinp]

theorem stackCirc_eval (h1 : C1.nin = nin) (h2 : C2.nin = nin) (hinp : inp.length = nin)
    (hout1 : ∀ j ∈ C1.out, j < C1.nin + C1.gates.length) :
    (stackCirc nin C1 C2).eval inp = C1.eval inp ++ C2.eval inp := by
  have hW : (C1.wires inp).length = nin + C1.gates.length := wires_length hinp
  have hgates : Circ.wires (stackCirc nin C1 C2) inp
      = runGates (C1.wires inp) (relocGates C2 (C1.wires inp).length (List.range nin)) := by
    rw [Circ.wires, stackCirc, Circ.gates_mk, runGates_append, ← Circ.wires, hW]
  have hlt : ∀ i, i < C2.nin → (List.range nin).getI i < (C1.wires inp).length := by
    intro i hi
    rw [h2] at hi
    rw [getI_range hi, hW]
    omega
  have hval : ∀ i, i < C2.nin → (C1.wires inp).getI ((List.range nin).getI i) = inp.getI i := by
    intro i hi
    rw [h2] at hi
    rw [getI_range hi, Circ.wires, getI_runGates_of_lt (by omega)]
  have hout_eq : (stackCirc nin C1 C2).out
      = C1.out ++ relocOut C2 (C1.wires inp).length (List.range nin) := by
    rw [stackCirc, Circ.out_mk, hW]
  rw [Circ.eval, hgates, hout_eq, List.map_append,
    values_before _ _ _ _ (fun j hj => by rw [hW, ← h1]; exact hout1 j hj),
    values_after _ _ _ _ hlt (by rw [h2, hinp]) hval]
  rfl

theorem feedCirc_eval (h1 : C1.nin = nin) (hinp : inp.length = nin)
    (h2 : C2.nin = C1.out.length)
    (hout1 : ∀ j ∈ C1.out, j < C1.nin + C1.gates.length) :
    (feedCirc nin C1 C2).eval inp = C2.eval (C1.eval inp) := by
  have hW : (C1.wires inp).length = nin + C1.gates.length := wires_length hinp
  have hgates : Circ.wires (feedCirc nin C1 C2) inp
      = runGates (C1.wires inp) (relocGates C2 (C1.wires inp).length C1.out) := by
    rw [Circ.wires, feedCirc, Circ.gates_mk, runGates_append, ← Circ.wires, hW]
  have hlt : ∀ i, i < C2.nin → C1.out.getI i < (C1.wires inp).length := by
    intro i hi
    rw [h2] at hi
    have := hout1 (C1.out.getI i) (by
      rw [List.getI_eq_getElem _ hi]; exact List.getElem_mem hi)
    rw [hW, ← h1]
    exact this
  have hval : ∀ i, i < C2.nin →
      (C1.wires inp).getI (C1.out.getI i) = (C1.eval inp).getI i := by
    intro i hi
    rw [h2] at hi
    exact (getI_eval C1 inp hi).symm
  have hout_eq : (feedCirc nin C1 C2).out = relocOut C2 (C1.wires inp).length C1.out := by
    rw [feedCirc, Circ.out_mk, hW]
  rw [Circ.eval, hgates, hout_eq,
    values_after _ _ _ _ hlt (by rw [h2, Circ.eval, List.length_map]) hval]

theorem stackCirc_out_lt (h1 : C1.nin = nin) (h2 : C2.nin = nin)
    (hout1 : ∀ j ∈ C1.out, j < C1.nin + C1.gates.length)
    (hout2 : ∀ j ∈ C2.out, j < C2.nin + C2.gates.length) :
    ∀ j ∈ (stackCirc nin C1 C2).out,
      j < (stackCirc nin C1 C2).nin + (stackCirc nin C1 C2).gates.length := by
  intro j hj
  simp only [stackCirc, Circ.out_mk, Circ.nin_mk, Circ.gates_mk, List.mem_append,
    List.length_append, length_relocGates] at hj ⊢
  rcases hj with hj | hj
  · have := hout1 j hj; omega
  · rw [relocOut, List.mem_map] at hj
    obtain ⟨u, hu, rfl⟩ := hj
    have h := hout2 u hu
    rw [h2] at h
    rw [wsh]
    split_ifs with hc
    · rw [h2] at hc
      rw [getI_range hc]
      omega
    · omega

theorem feedCirc_out_lt (h2 : C2.nin = C1.out.length)
    (hout1 : ∀ j ∈ C1.out, j < C1.nin + C1.gates.length) (h1 : C1.nin = nin)
    (hout2 : ∀ j ∈ C2.out, j < C2.nin + C2.gates.length) :
    ∀ j ∈ (feedCirc nin C1 C2).out,
      j < (feedCirc nin C1 C2).nin + (feedCirc nin C1 C2).gates.length := by
  intro j hj
  simp only [feedCirc, Circ.out_mk, Circ.nin_mk, Circ.gates_mk, List.length_append,
    length_relocGates] at hj ⊢
  rw [relocOut, List.mem_map] at hj
  obtain ⟨u, hu, rfl⟩ := hj
  have h := hout2 u hu
  rw [wsh]
  split_ifs with hc
  · rw [h2] at hc
    have := hout1 (C1.out.getI u) (by
      rw [List.getI_eq_getElem _ hc]; exact List.getElem_mem hc)
    omega
  · omega

end Place

/-! ### Relocation is primitive recursive -/

theorem primrec_wsh : Primrec fun p : ((ℕ × ℕ) × List ℕ) × ℕ =>
    wsh p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  refine Primrec.ite (c := fun p : ((ℕ × ℕ) × List ℕ) × ℕ => p.2 < p.1.1.1)
    (PrimrecRel.comp Primrec.nat_lt Primrec.snd
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) ?_ ?_
  · exact Primrec.list_getI.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  · exact Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.nat_sub.comp Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))

section PrimReloc

variable {α : Type*} [Primcodable α] {Cf : α → Circ} {bf : α → ℕ} {sf : α → List ℕ}

theorem primrec_relocGates (hC : Primrec Cf) (hb : Primrec bf) (hs : Primrec sf) :
    Primrec fun a => relocGates (Cf a) (bf a) (sf a) := by
  have hnin : Primrec fun a => (Cf a).nin := (Primrec.fst.comp hC).of_eq fun _ => rfl
  have hgates : Primrec fun a => (Cf a).gates :=
    (Primrec.fst.comp (Primrec.snd.comp hC)).of_eq fun _ => rfl
  refine Primrec.list_map hgates ?_
  have hpre : Primrec fun q : α × Gate => ((((Cf q.1).nin, bf q.1), sf q.1)) :=
    Primrec.pair (Primrec.pair (hnin.comp Primrec.fst) (hb.comp Primrec.fst))
      (hs.comp Primrec.fst)
  exact Primrec.pair (primrec_wsh.comp (Primrec.pair hpre (Primrec.fst.comp Primrec.snd)))
    (primrec_wsh.comp (Primrec.pair hpre (Primrec.snd.comp Primrec.snd)))

theorem primrec_relocOut (hC : Primrec Cf) (hb : Primrec bf) (hs : Primrec sf) :
    Primrec fun a => relocOut (Cf a) (bf a) (sf a) := by
  have hnin : Primrec fun a => (Cf a).nin := (Primrec.fst.comp hC).of_eq fun _ => rfl
  have hout : Primrec fun a => (Cf a).out :=
    (Primrec.snd.comp (Primrec.snd.comp hC)).of_eq fun _ => rfl
  refine Primrec.list_map hout ?_
  have hpre : Primrec fun q : α × ℕ => ((((Cf q.1).nin, bf q.1), sf q.1)) :=
    Primrec.pair (Primrec.pair (hnin.comp Primrec.fst) (hb.comp Primrec.fst))
      (hs.comp Primrec.fst)
  exact primrec_wsh.comp (Primrec.pair hpre Primrec.snd)

end PrimReloc

/-! ### The gadget blocks are primitive recursive

`HTN.Compile.blkG` and `HTN.Compile.bigOrG` are the two ways the constructions lay gates down,
and every circuit family has to exhibit its circuits as an algorithm in the bound.  The two
lemmas below do that once and for all: a block sequence and a big disjunction are primitive
recursive in whatever their parameters are primitive recursive in. -/

section PrimBlocks

variable {α : Type*} [Primcodable α]

theorem primrec_gOr {b i j : α → ℕ} (hb : Primrec b) (hi : Primrec i) (hj : Primrec j) :
    Primrec fun a => gOr (b a) (i a) (j a) := by
  refine Primrec.list_cons.comp (Primrec.pair hi hi)
    (Primrec.list_cons.comp (Primrec.pair hj hj)
      (Primrec.list_cons.comp (Primrec.pair hb
        (Primrec.nat_add.comp hb (Primrec.const 1))) (Primrec.const [])))

theorem primrec_gAnd {b i j : α → ℕ} (hb : Primrec b) (hi : Primrec i) (hj : Primrec j) :
    Primrec fun a => gAnd (b a) (i a) (j a) :=
  Primrec.list_cons.comp (Primrec.pair hi hj)
    (Primrec.list_cons.comp (Primrec.pair hb hb) (Primrec.const []))

theorem primrec_gTF {b : α → ℕ} (hb : Primrec b) : Primrec fun a => gTF (b a) :=
  Primrec.list_cons.comp (Primrec.pair hb hb)
    (Primrec.list_cons.comp (Primrec.pair hb hb) (Primrec.const []))

theorem primrec_gMux {b s x y : α → ℕ} (hb : Primrec b) (hs : Primrec s) (hx : Primrec x)
    (hy : Primrec y) : Primrec fun a => gMux (b a) (s a) (x a) (y a) := by
  have h1 := primrec_gAnd hb hs hx
  have h2 : Primrec fun a => gNot (s a) :=
    Primrec.list_cons.comp (Primrec.pair hs hs) (Primrec.const [])
  have h3 := primrec_gAnd (Primrec.nat_add.comp hb (Primrec.const 3))
    (Primrec.nat_add.comp hb (Primrec.const 2)) hy
  have h4 := primrec_gOr (Primrec.nat_add.comp hb (Primrec.const 5))
    (Primrec.nat_add.comp hb (Primrec.const 1))
    (Primrec.nat_add.comp hb (Primrec.const 4))
  exact (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp h1 h2) h3) h4).of_eq fun _ => rfl

theorem primrec_accW {fw base : α → ℕ} (hfw : Primrec fw) (hbase : Primrec base) :
    Primrec fun p : α × ℕ => accW (fw p.1) (base p.1) p.2 := by
  refine Primrec.ite (c := fun p : α × ℕ => p.2 = 0)
    (PrimrecRel.comp Primrec.eq Primrec.snd (Primrec.const 0)) (hfw.comp Primrec.fst) ?_
  exact Primrec.nat_sub.comp
    (Primrec.nat_add.comp (hbase.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd)) (Primrec.const 1)

/-- **A big disjunction is primitive recursive** in its parameters. -/
theorem primrec_bigOrG {fw base : α → ℕ} {ws : α → List ℕ} (hfw : Primrec fw)
    (hbase : Primrec base) (hws : Primrec ws) :
    Primrec fun a => bigOrG (fw a) (base a) (ws a) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp hws)) ?_
  refine primrec_gOr (Primrec.nat_add.comp (hbase.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd))
    (Primrec.list_getI.comp (hws.comp Primrec.fst) Primrec.snd)
    (primrec_accW hfw hbase)

/-- **A sequence of blocks of gates is primitive recursive** in its parameters. -/
theorem primrec_blkG {g : α → ℕ → ℕ → List Gate} {len base m : α → ℕ}
    (hg : Primrec fun p : (α × ℕ) × ℕ => g p.1.1 p.1.2 p.2) (hlen : Primrec len)
    (hbase : Primrec base) (hm : Primrec m) :
    Primrec fun a => blkG (g a) (len a) (base a) (m a) := by
  refine Primrec.list_flatMap (Primrec.list_range.comp hm) ?_
  exact hg.comp (Primrec.pair (Primrec.pair Primrec.fst Primrec.snd)
    (Primrec.nat_add.comp (hbase.comp Primrec.fst)
      (Primrec.nat_mul.comp (hlen.comp Primrec.fst) Primrec.snd)))

end PrimBlocks

/-! ### Transferring a family, and reading a source list

The three lemmas below are what the remaining constructions need: a family only depends on the
function at the arity it is stated for; a list of *source wires* carrying a list of values is
read blockwise; and the cell encoding at a wider bound is the cell encoding at the narrower one
followed by empty cells, so the first `2 * M` wires of a wider encoding are the encoding at the
bound `M`. -/

/-- **A family transfers along an equality of the two functions at the given arity.** -/
theorem circFam_congr {f f' : Fn} {k : ℕ} (F : CircFam f k)
    (h : ∀ args : Args, args.length = k → f args = f' args) : Nonempty (CircFam f' k) :=
  ⟨{ F with
      len_le := fun n args ha hl => by rw [← h args ha]; exact F.len_le n args ha hl
      correct := fun n args ha hl => by rw [← h args ha]; exact F.correct n args ha hl }⟩

/-- Reading a concatenation of two source lists. -/
theorem getI_src_append {W : List Bool} {s1 s2 : List ℕ} {e1 e2 : List Bool}
    (h1 : s1.length = e1.length)
    (ha : ∀ c < s1.length, W.getI (s1.getI c) = e1.getI c)
    (hb : ∀ c < s2.length, W.getI (s2.getI c) = e2.getI c) :
    ∀ c < (s1 ++ s2).length, W.getI ((s1 ++ s2).getI c) = (e1 ++ e2).getI c := by
  intro c hc
  rw [List.length_append] at hc
  by_cases h : c < s1.length
  · rw [List.getI_append _ _ _ h, List.getI_append _ _ _ (h1 ▸ h)]
    exact ha c h
  · rw [List.getI_append_right _ _ _ (by omega), List.getI_append_right _ _ _ (by omega), h1]
    exact hb _ (by omega)

/-- Reading a concatenation of blocks of source wires, all of the same width. -/
theorem getI_src_flatMap {W : List Bool} {m K : ℕ} {f : ℕ → List ℕ} {e : ℕ → List Bool}
    (hf : ∀ r, (f r).length = m) (he : ∀ r, (e r).length = m)
    (h : ∀ r < K, ∀ c < m, W.getI ((f r).getI c) = (e r).getI c) :
    ∀ c < m * K, W.getI (((List.range K).flatMap f).getI c) = ((List.range K).flatMap e).getI c
    := by
  intro c hc
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · simp at hc
    · exact h'
  have hdiv : c / m < K := (Nat.div_lt_iff_lt_mul hm).2 (by rw [mul_comm]; exact hc)
  have hmod : c % m < m := Nat.mod_lt _ hm
  have hc' : m * (c / m) + c % m = c := Nat.div_add_mod c m
  rw [← hc', getI_flatMap_range (f := f) hf hdiv hmod,
    getI_flatMap_range (f := e) he hdiv hmod]
  exact h _ hdiv _ hmod

/-- Reading a mapped list. -/
theorem getI_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) {c : ℕ}
    (h : c < l.length) : (l.map f).getI c = f (l.getI c) := by
  rw [List.getI_eq_getElem _ (by simpa using h), List.getElem_map,
    List.getI_eq_getElem _ h]

/-- The first `2 * M` bits of a wider cell encoding. -/
theorem take_encStr {B M : ℕ} {s : List Bool} (hs : s.length ≤ M) (h : M ≤ B) :
    (encStr B s).take (2 * M) = encStr M s := by
  rw [encStr_widen hs h]
  exact List.take_left' (by simp)

end Compile

end HTN
