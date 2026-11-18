import Mathlib

/-!
# Boolean circuits, as straight-line NAND programs

The source bridge of `HtnCompilability/Space/Table3Sep.lean` has to turn the *Cobham
predicates* of an alternating machine with a polynomial memory
(`ComplexityTheory/Collapse/Alt.lean`) into the finite combinatorial data a domain description
can carry.  The intermediate object is a **circuit**: a straight-line program of NAND gates.

A circuit is a triple `(nin, gates, out)`:

* the wires are numbered from `0`; the wires `0 … nin - 1` are the inputs, and the `k`-th gate
  is the wire `nin + k`;
* a gate is a pair of wire indices, and its value is the NAND of the two;
* the output is a list of wire indices.

**No well-formedness is required.**  A wire index that is out of range at the moment the gate is
evaluated reads as `false` (`List.getI`), which is what makes the relocation lemma below
unconditional — and it is also how the two constants are obtained: `NAND` of an index that does
not exist yet is `true`, and `NAND` of that wire with itself is `false`.

The file contains the evaluation, its elementary lemmas, and the one construction everything
else is built from: **relocation** (`HTN.Compile.relocGates`), which inserts a circuit into a
larger wire space, its inputs being read off wires that are already present.  The correctness of
relocation (`HTN.Compile.runGates_relocGates`) is what makes circuits composable.
-/

namespace HTN

namespace Compile

/-- A **gate**: the NAND of the two wires it names. -/
abbrev Gate : Type := ℕ × ℕ

/-- A **circuit**: the number of input wires, the gates, and the output wires. -/
abbrev Circ : Type := ℕ × List Gate × List ℕ

namespace Circ

/-- The number of input wires. -/
def nin (C : Circ) : ℕ := C.1

/-- The gates. -/
def gates (C : Circ) : List Gate := C.2.1

/-- The output wires. -/
def out (C : Circ) : List ℕ := C.2.2

@[simp] theorem nin_mk (n : ℕ) (gs : List Gate) (o : List ℕ) : nin (n, gs, o) = n := rfl

@[simp] theorem gates_mk (n : ℕ) (gs : List Gate) (o : List ℕ) : gates (n, gs, o) = gs := rfl

@[simp] theorem out_mk (n : ℕ) (gs : List Gate) (o : List ℕ) : out (n, gs, o) = o := rfl

end Circ

/-! ### Evaluation -/

/-- Appending the value of one gate to the wires computed so far. -/
def gateStep (v : List Bool) (g : Gate) : List Bool := v ++ [!(v.getI g.1 && v.getI g.2)]

/-- The wires produced by a list of gates, from a starting assignment. -/
def runGates (v : List Bool) (gs : List Gate) : List Bool := gs.foldl gateStep v

/-- The wires of a circuit on an input assignment. -/
def Circ.wires (C : Circ) (inp : List Bool) : List Bool := runGates inp C.gates

/-- The output of a circuit on an input assignment. -/
def Circ.eval (C : Circ) (inp : List Bool) : List Bool := C.out.map (C.wires inp).getI

/-- The size of a circuit: its inputs, its gates and its outputs. -/
def Circ.size (C : Circ) : ℕ := C.nin + C.gates.length + C.out.length

@[simp] theorem runGates_nil (v : List Bool) : runGates v [] = v := rfl

@[simp] theorem runGates_cons (v : List Bool) (g : Gate) (gs : List Gate) :
    runGates v (g :: gs) = runGates (gateStep v g) gs := rfl

theorem runGates_append (v : List Bool) (gs hs : List Gate) :
    runGates v (gs ++ hs) = runGates (runGates v gs) hs := List.foldl_append

theorem runGates_concat (v : List Bool) (gs : List Gate) (g : Gate) :
    runGates v (gs ++ [g]) = gateStep (runGates v gs) g := by
  rw [runGates_append]; rfl

@[simp] theorem length_gateStep (v : List Bool) (g : Gate) :
    (gateStep v g).length = v.length + 1 := by simp [gateStep]

@[simp] theorem length_runGates (v : List Bool) (gs : List Gate) :
    (runGates v gs).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih => simp only [runGates_cons, ih, length_gateStep, List.length_cons]; omega

/-- The starting assignment is a prefix of the wires. -/
theorem runGates_prefix (v : List Bool) (gs : List Gate) :
    ∃ t : List Bool, runGates v gs = v ++ t := by
  induction gs generalizing v with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (gateStep v g)
    exact ⟨(!(v.getI g.1 && v.getI g.2)) :: t, by rw [runGates_cons, ht, gateStep]; simp⟩

/-- Gates do not change the wires already present. -/
theorem getI_runGates_of_lt {v : List Bool} {gs : List Gate} {i : ℕ} (h : i < v.length) :
    (runGates v gs).getI i = v.getI i := by
  obtain ⟨t, ht⟩ := runGates_prefix v gs
  rw [ht, List.getI_eq_getElem _ (by simp; omega), List.getI_eq_getElem _ h,
    List.getElem_append_left h]

theorem getI_of_le_length {l : List Bool} {i : ℕ} (h : l.length ≤ i) : l.getI i = false :=
  List.getI_eq_default _ h

/-! ### Relocation -/

/-- The wire `i` of a circuit with `nin` inputs, read in a larger wire space in which the
inputs sit at the wires `srcs` and the gates start at `base`. -/
def wsh (nin base : ℕ) (srcs : List ℕ) (i : ℕ) : ℕ :=
  if i < nin then srcs.getI i else base + (i - nin)

/-- The gates of a circuit, relocated. -/
def relocGates (C : Circ) (base : ℕ) (srcs : List ℕ) : List Gate :=
  C.gates.map fun g => (wsh C.nin base srcs g.1, wsh C.nin base srcs g.2)

/-- The output wires of a circuit, relocated. -/
def relocOut (C : Circ) (base : ℕ) (srcs : List ℕ) : List ℕ :=
  C.out.map (wsh C.nin base srcs)

@[simp] theorem length_relocGates (C : Circ) (base : ℕ) (srcs : List ℕ) :
    (relocGates C base srcs).length = C.gates.length := by simp [relocGates]

@[simp] theorem length_relocOut (C : Circ) (base : ℕ) (srcs : List ℕ) :
    (relocOut C base srcs).length = C.out.length := by simp [relocOut]

/-- **Relocation is correct**: running the relocated gates on a wire assignment whose `srcs`
carry the input values appends exactly the gate values of the circuit. -/
theorem runGates_map_wsh {nin : ℕ} {srcs : List ℕ} {v inp : List Bool} (gs : List Gate)
    (hlt : ∀ i, i < nin → srcs.getI i < v.length) (hinp : inp.length = nin)
    (hval : ∀ i, i < nin → v.getI (srcs.getI i) = inp.getI i) :
    runGates v (gs.map fun g => (wsh nin v.length srcs g.1, wsh nin v.length srcs g.2))
      = v ++ (runGates inp gs).drop nin := by
  induction gs using List.reverseRecOn with
  | nil => simp [hinp]
  | append_singleton gs g ih =>
    have key : ∀ i : ℕ, (runGates v (gs.map fun g =>
        (wsh nin v.length srcs g.1, wsh nin v.length srcs g.2))).getI
          (wsh nin v.length srcs i) = (runGates inp gs).getI i := by
      intro i
      rw [ih]
      by_cases hi : i < nin
      · rw [wsh, if_pos hi]
        have h1 : srcs.getI i < v.length := hlt i hi
        rw [List.getI_append _ _ _ h1, hval i hi, getI_runGates_of_lt (by omega)]
      · rw [wsh, if_neg hi]
        have hlen : (runGates inp gs).length = nin + gs.length := by simp [hinp]
        by_cases hi2 : i < nin + gs.length
        · have h1 : v.length + (i - nin) < (v ++ (runGates inp gs).drop nin).length := by
            simp only [List.length_append, List.length_drop, hlen]; omega
          rw [List.getI_eq_getElem _ h1, List.getElem_append_right (by omega),
            List.getI_eq_getElem _ (by omega)]
          simp only [List.getElem_drop]
          congr 1
          omega
        · rw [getI_of_le_length (by
            simp only [List.length_append, List.length_drop, hlen]; omega),
            getI_of_le_length (by omega)]
    have hlen : (runGates inp gs).length = nin + gs.length := by simp [hinp]
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil]
    rw [runGates_concat, runGates_concat]
    simp only [gateStep, key]
    rw [ih, List.append_assoc,
      List.drop_append_of_le_length (show nin ≤ (runGates inp gs).length by omega)]

/-- **Relocation is correct**, in the form the constructions use. -/
theorem runGates_relocGates {C : Circ} {v inp : List Bool} {srcs : List ℕ}
    (hlt : ∀ i, i < C.nin → srcs.getI i < v.length) (hinp : inp.length = C.nin)
    (hval : ∀ i, i < C.nin → v.getI (srcs.getI i) = inp.getI i) :
    runGates v (relocGates C v.length srcs) = v ++ (C.wires inp).drop C.nin :=
  runGates_map_wsh C.gates hlt hinp hval

/-- The relocated output wires carry the output values of the circuit. -/
theorem getI_relocOut {C : Circ} {v inp : List Bool} {srcs : List ℕ} (i : ℕ)
    (hlt : ∀ i, i < C.nin → srcs.getI i < v.length) (hinp : inp.length = C.nin)
    (hval : ∀ i, i < C.nin → v.getI (srcs.getI i) = inp.getI i) :
    (runGates v (relocGates C v.length srcs)).getI (wsh C.nin v.length srcs i)
      = (C.wires inp).getI i := by
  rw [runGates_relocGates hlt hinp hval]
  by_cases hin : i < C.nin
  · rw [wsh, if_pos hin]
    have h1 : srcs.getI i < v.length := hlt i hin
    rw [List.getI_append _ _ _ h1, hval i hin, Circ.wires, getI_runGates_of_lt (by omega)]
  · rw [wsh, if_neg hin]
    have hlen : (C.wires inp).length = C.nin + C.gates.length := by
      simp [Circ.wires, hinp]
    by_cases hi2 : i < C.nin + C.gates.length
    · have h1 : v.length + (i - C.nin) < (v ++ (C.wires inp).drop C.nin).length := by
        simp only [List.length_append, List.length_drop, hlen]; omega
      rw [List.getI_eq_getElem _ h1, List.getElem_append_right (by omega),
        List.getI_eq_getElem _ (by omega)]
      simp only [List.getElem_drop]
      congr 1
      omega
    · rw [getI_of_le_length (by
        simp only [List.length_append, List.length_drop, hlen]; omega),
        getI_of_le_length (by omega)]

end Compile

end HTN
