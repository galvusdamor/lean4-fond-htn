import ComplexityTheory.Compile.Enc
/-!
# Gadgets: the small circuits everything is built from

`ComplexityTheory/Compile/Circ.lean` evaluates a list of NAND gates appended to a wire
assignment.  This file writes down the handful of **gadgets** the compilation of Cobham's class
uses, each as a closed-form list of gates together with the index of the wire it computes:

* `HTN.Compile.gTF` — the two constants.  `NAND` of a wire that does not exist yet is `true`,
  and `NAND` of that wire with itself is `false`, so two gates produce both constants without
  any hypothesis;
* `HTN.Compile.gNot`, `HTN.Compile.gAnd`, `HTN.Compile.gOr` — the Boolean connectives;
* `HTN.Compile.gMux` — the two-way multiplexer `if s then a else b`;
* `HTN.Compile.bigOrG` — the disjunction of a list of wires, as a left fold.

Every gadget is stated for a wire assignment `v` whose length is the base at which the gadget is
placed, and every wire it reads is required to be below that length; the value it computes is
then read off the wire whose index the gadget names.  Because later gates never change the
wires already present (`HTN.Compile.getI_runGates_of_lt`), these values survive the rest of the
construction.
-/

namespace HTN

namespace Compile

/-! ### Reading the wires a gadget appends -/

theorem getI_snoc_self (v : List Bool) (x : Bool) : (v ++ [x]).getI v.length = x := by
  rw [List.getI_eq_getElem _ (by simp)]
  simp

theorem getI_snoc_lt {v : List Bool} {x : Bool} {i : ℕ} (h : i < v.length) :
    (v ++ [x]).getI i = v.getI i := List.getI_append _ _ _ h

theorem gateStep_eq (v : List Bool) (i j : ℕ) :
    gateStep v (i, j) = v ++ [!(v.getI i && v.getI j)] := rfl

/-- The value of the wire a gate appends. -/
theorem getI_gateStep_self (v : List Bool) (i j : ℕ) :
    (gateStep v (i, j)).getI v.length = !(v.getI i && v.getI j) := by
  rw [gateStep_eq, getI_snoc_self]

theorem getI_gateStep_lt {v : List Bool} {i j k : ℕ} (h : k < v.length) :
    (gateStep v (i, j)).getI k = v.getI k := by
  rw [gateStep_eq, getI_snoc_lt h]

/-! ### The constants -/

/-- Two gates producing `true` and then `false`. -/
def gTF (base : ℕ) : List Gate := [(base, base), (base, base)]

/-- The wire carrying `true`. -/
def wTrue (base : ℕ) : ℕ := base

/-- The wire carrying `false`. -/
def wFalse (base : ℕ) : ℕ := base + 1

@[simp] theorem length_gTF (base : ℕ) : (gTF base).length = 2 := rfl

theorem runGates_gTF (v : List Bool) : runGates v (gTF v.length) = v ++ [true, false] := by
  have h0 : v.getI v.length = false := getI_of_le_length (le_refl _)
  have e1 : gateStep v (v.length, v.length) = v ++ [true] := by
    rw [gateStep_eq, h0]; simp
  have e2 : gateStep (v ++ [true]) (v.length, v.length) = v ++ [true, false] := by
    rw [gateStep_eq, getI_snoc_self]; simp
  show gateStep (gateStep v (v.length, v.length)) (v.length, v.length) = _
  rw [e1, e2]

theorem getI_wTrue (v : List Bool) :
    (runGates v (gTF v.length)).getI (wTrue v.length) = true := by
  rw [runGates_gTF, wTrue, List.getI_eq_getElem _ (by simp)]
  simp

theorem getI_wFalse (v : List Bool) :
    (runGates v (gTF v.length)).getI (wFalse v.length) = false := by
  rw [runGates_gTF, wFalse, List.getI_eq_getElem _ (by simp)]
  simp

/-! ### The connectives -/

/-- The negation of the wire `i`, placed at the base; its value is at the wire `base`. -/
def gNot (i : ℕ) : List Gate := [(i, i)]

/-- The wire carrying the negation. -/
def wNot (base : ℕ) : ℕ := base

@[simp] theorem length_gNot (i : ℕ) : (gNot i).length = 1 := rfl

theorem getI_gNot (v : List Bool) (i : ℕ) :
    (runGates v (gNot i)).getI (wNot v.length) = !(v.getI i) := by
  show (gateStep v (i, i)).getI (wNot v.length) = _
  rw [wNot, getI_gateStep_self]
  simp

/-- The conjunction of the wires `i` and `j`. -/
def gAnd (base i j : ℕ) : List Gate := [(i, j), (base, base)]

/-- The wire carrying the conjunction. -/
def wAnd (base : ℕ) : ℕ := base + 1

@[simp] theorem length_gAnd (base i j : ℕ) : (gAnd base i j).length = 2 := rfl

theorem getI_gAnd (v : List Bool) (i j : ℕ) :
    (runGates v (gAnd v.length i j)).getI (wAnd v.length) = (v.getI i && v.getI j) := by
  have hl : (gateStep v (i, j)).length = v.length + 1 := by simp
  have h1 : (gateStep v (i, j)).getI v.length = !(v.getI i && v.getI j) :=
    getI_gateStep_self v i j
  show (gateStep (gateStep v (i, j)) (v.length, v.length)).getI (wAnd v.length) = _
  rw [wAnd, show v.length + 1 = (gateStep v (i, j)).length from hl.symm,
    getI_gateStep_self, h1]
  simp

/-- The disjunction of the wires `i` and `j`. -/
def gOr (base i j : ℕ) : List Gate := [(i, i), (j, j), (base, base + 1)]

/-- The wire carrying the disjunction. -/
def wOr (base : ℕ) : ℕ := base + 2

@[simp] theorem length_gOr (base i j : ℕ) : (gOr base i j).length = 3 := rfl

theorem getI_gOr {v : List Bool} {i j : ℕ} (hj : j < v.length) :
    (runGates v (gOr v.length i j)).getI (wOr v.length) = (v.getI i || v.getI j) := by
  have l1 : (gateStep v (i, i)).length = v.length + 1 := by simp
  have l2 : (gateStep (gateStep v (i, i)) (j, j)).length = v.length + 2 := by simp
  have a1 : (gateStep v (i, i)).getI v.length = !(v.getI i) := by
    rw [getI_gateStep_self]; simp
  have a2' : (gateStep v (i, i)).getI j = v.getI j := getI_gateStep_lt hj
  have a2 : (gateStep (gateStep v (i, i)) (j, j)).getI (v.length + 1) = !(v.getI j) := by
    rw [show v.length + 1 = (gateStep v (i, i)).length from l1.symm, getI_gateStep_self, a2']
    simp
  have a1' : (gateStep (gateStep v (i, i)) (j, j)).getI v.length = !(v.getI i) := by
    rw [getI_gateStep_lt (by omega), a1]
  show (gateStep (gateStep (gateStep v (i, i)) (j, j)) (v.length, v.length + 1)).getI
    (wOr v.length) = _
  rw [wOr, show v.length + 2 = (gateStep (gateStep v (i, i)) (j, j)).length from l2.symm,
    getI_gateStep_self, a1', a2]
  cases v.getI i <;> cases v.getI j <;> simp

/-! ### The multiplexer -/

/-- `if s then a else b`. -/
def gMux (base s a b : ℕ) : List Gate :=
  gAnd base s a ++ gNot s ++ gAnd (base + 3) (base + 2) b ++ gOr (base + 5) (base + 1) (base + 4)

/-- The wire carrying the value of the multiplexer. -/
def wMux (base : ℕ) : ℕ := base + 7

@[simp] theorem length_gMux (base s a b : ℕ) : (gMux base s a b).length = 8 := by
  simp [gMux]

theorem getI_gMux {v : List Bool} {s a b : ℕ} (hs : s < v.length) (hb : b < v.length) :
    (runGates v (gMux v.length s a b)).getI (wMux v.length)
      = (if v.getI s = true then v.getI a else v.getI b) := by
  -- the four stages
  have l1 : (runGates v (gAnd v.length s a)).length = v.length + 2 := by simp
  have h1 : (runGates v (gAnd v.length s a)).getI (v.length + 1)
      = (v.getI s && v.getI a) := by
    have := getI_gAnd v s a; rwa [wAnd] at this
  have h2 := getI_gNot (runGates v (gAnd v.length s a)) s
  rw [wNot, l1, getI_runGates_of_lt hs] at h2
  have l2 : (runGates (runGates v (gAnd v.length s a)) (gNot s)).length = v.length + 3 := by
    rw [length_runGates, l1]; simp
  have h3 := getI_gAnd (runGates (runGates v (gAnd v.length s a)) (gNot s)) (v.length + 2) b
  rw [wAnd, l2] at h3
  have hb2 : (runGates (runGates v (gAnd v.length s a)) (gNot s)).getI b = v.getI b := by
    rw [getI_runGates_of_lt (by rw [l1]; omega), getI_runGates_of_lt hb]
  rw [hb2, h2] at h3
  have l3 : (runGates (runGates (runGates v (gAnd v.length s a)) (gNot s))
      (gAnd (v.length + 3) (v.length + 2) b)).length = v.length + 5 := by
    rw [length_runGates, l2]; simp
  have h1' : (runGates (runGates (runGates v (gAnd v.length s a)) (gNot s))
      (gAnd (v.length + 3) (v.length + 2) b)).getI (v.length + 1)
      = (v.getI s && v.getI a) := by
    rw [getI_runGates_of_lt (by rw [l2]; omega), getI_runGates_of_lt (by rw [l1]; omega), h1]
  have h4 := getI_gOr (v := runGates (runGates (runGates v (gAnd v.length s a)) (gNot s))
      (gAnd (v.length + 3) (v.length + 2) b)) (i := v.length + 1) (j := v.length + 4)
      (by rw [l3]; omega)
  rw [wOr, l3, h1', h3] at h4
  have hrun : runGates v (gMux v.length s a b)
      = runGates (runGates (runGates (runGates v (gAnd v.length s a)) (gNot s))
          (gAnd (v.length + 3) (v.length + 2) b))
          (gOr (v.length + 5) (v.length + 1) (v.length + 4)) := by
    rw [gMux, runGates_append, runGates_append, runGates_append]
  rw [hrun, wMux, h4]
  cases hsv : v.getI s <;> cases v.getI a <;> cases v.getI b <;> simp

/-! ### The disjunction of a list of wires -/

/-- The wire carrying the disjunction of the first `j` wires of the list. -/
def accW (fw base j : ℕ) : ℕ := if j = 0 then fw else base + 3 * j - 1

/-- The gates of the disjunction of a list of wires, as a left fold. -/
def bigOrG (fw base : ℕ) (ws : List ℕ) : List Gate :=
  (List.range ws.length).flatMap fun j => gOr (base + 3 * j) (ws.getI j) (accW fw base j)

/-- The wire carrying the disjunction of a list of wires. -/
def bigOrW (fw base : ℕ) (ws : List ℕ) : ℕ := accW fw base ws.length

@[simp] theorem length_bigOrG (fw base : ℕ) (ws : List ℕ) :
    (bigOrG fw base ws).length = 3 * ws.length := by
  rw [bigOrG, List.length_flatMap]
  have h : ((List.range ws.length).map fun j =>
      (gOr (base + 3 * j) (ws.getI j) (accW fw base j)).length)
      = (List.range ws.length).map fun _ => 3 := by
    refine List.map_congr_left ?_
    intro j _
    simp
  rw [h]
  simp [mul_comm]

theorem bigOrG_concat (fw base : ℕ) (ws : List ℕ) (w : ℕ) :
    bigOrG fw base (ws ++ [w]) =
      bigOrG fw base ws ++ gOr (base + 3 * ws.length) w (accW fw base ws.length) := by
  rw [bigOrG, bigOrG, List.length_append, List.length_singleton, List.range_succ,
    List.flatMap_append]
  congr 1
  · refine List.flatMap_congr ?_
    intro j hj
    rw [List.mem_range] at hj
    rw [List.getI_append _ _ _ hj]
  · have hg : (ws ++ [w]).getI ws.length = w := by
      rw [List.getI_eq_getElem _ (by simp)]; simp
    simp [hg]

theorem getI_bigOr {v : List Bool} {fw : ℕ} (ws : List ℕ) (hfw : v.getI fw = false)
    (hfwlt : fw < v.length) (hws : ∀ w ∈ ws, w < v.length) :
    (runGates v (bigOrG fw v.length ws)).getI (bigOrW fw v.length ws)
      = ws.any fun w => v.getI w := by
  induction ws using List.reverseRecOn with
  | nil => simpa [bigOrG, bigOrW, accW] using hfw
  | append_singleton ws w ih =>
      have hws' : ∀ u ∈ ws, u < v.length := fun u hu => hws u (by simp [hu])
      have hwlt : w < v.length := hws w (by simp)
      have hl1 : (runGates v (bigOrG fw v.length ws)).length = v.length + 3 * ws.length := by
        rw [length_runGates, length_bigOrG]
      have hacc : (runGates v (bigOrG fw v.length ws)).getI (accW fw v.length ws.length)
          = ws.any fun u => v.getI u := ih hws'
      have hw1 : (runGates v (bigOrG fw v.length ws)).getI w = v.getI w :=
        getI_runGates_of_lt hwlt
      have hlt2 : accW fw v.length ws.length < v.length + 3 * ws.length := by
        rcases Nat.eq_zero_or_pos ws.length with h0 | hpos
        · rw [accW, if_pos h0]; omega
        · rw [accW, if_neg (by omega)]; omega
      have hor := getI_gOr (v := runGates v (bigOrG fw v.length ws)) (i := w)
        (j := accW fw v.length ws.length) (by rw [hl1]; omega)
      rw [wOr, hl1, hw1, hacc] at hor
      rw [bigOrG_concat, runGates_append]
      rw [bigOrW, List.length_append, List.length_singleton,
        show accW fw v.length (ws.length + 1) = v.length + 3 * ws.length + 2 by
          rw [accW, if_neg (by omega)]; omega]
      rw [hor]
      simp [List.any_append, Bool.or_comm]

/-! ### A sequence of blocks of gates

The constructions place many gadgets of the same size one after another.  `HTN.Compile.blkG`
is the resulting gate list, and `HTN.Compile.getI_blkG` says that a wire the `i`-th block
produces has the value it would have if the construction stopped after that block. -/

/-- `m` blocks of `len` gates each, the `i`-th placed at `base + len * i`. -/
def blkG (g : ℕ → ℕ → List Gate) (len base m : ℕ) : List Gate :=
  (List.range m).flatMap fun i => g i (base + len * i)

theorem blkG_succ (g : ℕ → ℕ → List Gate) (len base m : ℕ) :
    blkG g len base (m + 1) = blkG g len base m ++ g m (base + len * m) := by
  rw [blkG, blkG, List.range_succ, List.flatMap_append]
  simp

@[simp] theorem length_blkG {g : ℕ → ℕ → List Gate} {len : ℕ}
    (hlen : ∀ i b, (g i b).length = len) (base m : ℕ) :
    (blkG g len base m).length = len * m := by
  rw [blkG, List.length_flatMap]
  have h : ((List.range m).map fun i => (g i (base + len * i)).length)
      = (List.range m).map fun _ => len := List.map_congr_left fun i _ => hlen _ _
  rw [h]
  simp [mul_comm]

/-- **A wire of the `i`-th block already has its final value after that block.** -/
theorem getI_blkG {v : List Bool} {g : ℕ → ℕ → List Gate} {len : ℕ}
    (hlen : ∀ i b, (g i b).length = len) {m i : ℕ} (hi : i < m) {w : ℕ}
    (hw : w < v.length + len * (i + 1)) :
    (runGates v (blkG g len v.length m)).getI w
      = (runGates v (blkG g len v.length (i + 1))).getI w := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · rw [blkG_succ, runGates_append, getI_runGates_of_lt (by
          rw [length_runGates, length_blkG hlen]
          have : len * (i + 1) ≤ len * m := Nat.mul_le_mul_left _ (by omega)
          omega)]
        exact ih h
      · rfl

/-- The wires before a sequence of blocks keep their values. -/
theorem getI_blkG_of_lt {v : List Bool} {g : ℕ → ℕ → List Gate} {len m w : ℕ}
    (hw : w < v.length) : (runGates v (blkG g len v.length m)).getI w = v.getI w :=
  getI_runGates_of_lt hw

/-- The state just before the `i`-th block. -/
theorem length_runGates_blkG {v : List Bool} {g : ℕ → ℕ → List Gate} {len : ℕ}
    (hlen : ∀ i b, (g i b).length = len) (i : ℕ) :
    (runGates v (blkG g len v.length i)).length = v.length + len * i := by
  rw [length_runGates, length_blkG hlen]

end Compile

end HTN
