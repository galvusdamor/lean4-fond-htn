import ComplexityTheory.Compile.Base
/-!
# The circuit family of the smash function

The smash function `|smash x y| = |x| * |y|` is the only base case of Cobham's class that
computes.  Its circuit is a disjunction: the `i`-th cell of the value is present exactly when
`|x| * |y| > i`, which happens exactly when there is a pair `(a, b)` with `a * b > i`,
`|x| ≥ a` and `|y| ≥ b`.  Both `a` and `b` may be taken in `1 … n`, so the circuit has one
conjunction per pair — coded by `t = (a - 1) * n + (b - 1)` — and one big disjunction per output
cell.  Every value bit of the output is `false`.
-/

namespace HTN

namespace Compile

open PTime

/-! ### Two list lemmas -/

theorem any_congr_mem {α : Type*} (l : List α) {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.any_cons, List.any_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

theorem any_eq_false_of_mem {α : Type*} {l : List α} {f : α → Bool} (h : ∀ x ∈ l, f x = false) :
    l.any f = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.any_cons, h a (by simp), ih fun x hx => h x (by simp [hx]), Bool.or_self]

theorem getI_replicate_false (m i : ℕ) : (List.replicate m false).getI i = false := by
  by_cases h : i < m
  · rw [List.getI_eq_getElem _ (by simpa using h)]
    simp
  · exact getI_of_le_length (by simpa using Nat.le_of_not_lt h)

/-! ### The smash function -/

section Smash

/-- The conjunction gates of the smash circuit: one per pair of candidate lengths, coded by
`t = (a - 1) * n + (b - 1)`. -/
def smAnd (n : ℕ) (t b : ℕ) : List Gate := gAnd b (2 * (t / n)) (2 * n + 2 * (t % n))

/-- The wire carrying "`|x| ≥ a` and `|y| ≥ b`" for the pair coded by `t`. -/
def smAndW (n k t : ℕ) : ℕ := 2 * n * k + 2 + 2 * t + 1

/-- The wires the `i`-th output cell takes the disjunction of. -/
def smWs (n k i : ℕ) : List ℕ :=
  (List.range (n * n)).map fun t =>
    if i < (t / n + 1) * (t % n + 1) then smAndW n k t else wFalse (2 * n * k)

/-- The disjunction gates of the `i`-th output cell. -/
def smOr (n k i b : ℕ) : List Gate := bigOrG (wFalse (2 * n * k)) b (smWs n k i)

/-- The wire carrying the presence bit of the `i`-th output cell. -/
def smOrW (n k i : ℕ) : ℕ :=
  bigOrW (wFalse (2 * n * k)) (2 * n * k + 2 + 2 * (n * n) + 3 * (n * n) * i) (smWs n k i)

/-- **The smash circuit.** -/
def smCirc (n k : ℕ) : Circ :=
  (2 * n * k,
    gTF (2 * n * k) ++ (blkG (smAnd n) 2 (2 * n * k + 2) (n * n)
      ++ blkG (smOr n k) (3 * (n * n)) (2 * n * k + 2 + 2 * (n * n)) (n * n)),
    (List.range (n * n)).flatMap fun i => [smOrW n k i, wFalse (2 * n * k)])

@[simp] theorem length_smWs (n k i : ℕ) : (smWs n k i).length = n * n := by simp [smWs]

theorem length_smAnd (n : ℕ) (t b : ℕ) : (smAnd n t b).length = 2 := rfl

theorem length_smOr (n k : ℕ) (i b : ℕ) : (smOr n k i b).length = 3 * (n * n) := by
  rw [smOr, length_bigOrG, length_smWs]

theorem length_out_smCirc (n k : ℕ) : (smCirc n k).out.length = 2 * (n * n) := by
  rw [smCirc, Circ.out_mk, List.length_flatMap]
  have h : ((List.range (n * n)).map fun i => ([smOrW n k i, wFalse (2 * n * k)]).length)
      = (List.range (n * n)).map fun _ => 2 := List.map_congr_left fun _ _ => rfl
  rw [h]
  simp [mul_comm]

theorem length_gates_smCirc (n k : ℕ) :
    (smCirc n k).gates.length = 2 + (2 * (n * n) + 3 * (n * n) * (n * n)) := by
  rw [smCirc, Circ.gates_mk, List.length_append, List.length_append, length_gTF,
    length_blkG (length_smAnd n), length_blkG (length_smOr n k)]

/-! ### The conjunctions -/

/-- **The conjunction for the pair `t` is the conjunction of the two presence bits it reads.** -/
theorem getI_smAnd_blk {n k : ℕ} (hk : 2 ≤ k) {v : List Bool} (hv : v.length = 2 * n * k + 2)
    {t : ℕ} (ht : t < n * n) :
    (runGates v (blkG (smAnd n) 2 v.length (n * n))).getI (smAndW n k t)
      = (v.getI (2 * (t / n)) && v.getI (2 * n + 2 * (t % n))) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at ht
    · exact h
  have hdiv : t / n < n := (Nat.div_lt_iff_lt_mul hn).2 ht
  have hmod : t % n < n := Nat.mod_lt _ hn
  have hnk : 2 * n ≤ 2 * n * k := Nat.le_mul_of_pos_right _ (by omega)
  have hnk2 : 4 * n ≤ 2 * n * k := by
    have : 2 * n * 2 ≤ 2 * n * k := Nat.mul_le_mul_left _ hk
    omega
  have hlt1 : 2 * (t / n) < v.length := by rw [hv]; omega
  have hlt2 : 2 * n + 2 * (t % n) < v.length := by rw [hv]; omega
  have hw : smAndW n k t < v.length + 2 * (t + 1) := by rw [hv, smAndW]; omega
  rw [getI_blkG (g := smAnd n) (len := 2) (fun i b => length_smAnd n i b) ht hw, blkG_succ,
    runGates_append]
  have hWlen : (runGates v (blkG (smAnd n) 2 v.length t)).length = v.length + 2 * t :=
    length_runGates_blkG (fun i b => length_smAnd n i b) t
  rw [smAnd, show v.length + 2 * t = (runGates v (blkG (smAnd n) 2 v.length t)).length from
    hWlen.symm,
    show smAndW n k t = wAnd (runGates v (blkG (smAnd n) 2 v.length t)).length by
      rw [wAnd, hWlen, hv, smAndW],
    getI_gAnd, getI_runGates_of_lt hlt1, getI_runGates_of_lt hlt2]

/-! ### The disjunctions -/

/-- **The `i`-th disjunction is the disjunction of the wires it names.** -/
theorem getI_smOr_blk {n k : ℕ} {v : List Bool} (hv : v.length = 2 * n * k + 2 + 2 * (n * n))
    (hfalse : v.getI (wFalse (2 * n * k)) = false) {i : ℕ} (hi : i < n * n) :
    (runGates v (blkG (smOr n k) (3 * (n * n)) v.length (n * n))).getI (smOrW n k i)
      = (smWs n k i).any fun w => v.getI w := by
  have hnn : 0 < n * n := by omega
  have hws : ∀ w ∈ smWs n k i, w < v.length := by
    intro w hw
    rw [smWs, List.mem_map] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [List.mem_range] at ht
    split_ifs
    · rw [smAndW, hv]; omega
    · rw [wFalse, hv]; omega
  have hacc : smOrW n k i
      = accW (wFalse (2 * n * k)) (v.length + 3 * (n * n) * i) (n * n) := by
    rw [smOrW, bigOrW, length_smWs, hv]
  have hbound : smOrW n k i < v.length + 3 * (n * n) * (i + 1) := by
    rw [hacc, accW, if_neg (by omega)]
    have : 3 * (n * n) * (i + 1) = 3 * (n * n) * i + 3 * (n * n) := by ring
    omega
  rw [getI_blkG (g := smOr n k) (len := 3 * (n * n)) (fun a b => length_smOr n k a b) hi hbound,
    blkG_succ, runGates_append]
  have hWlen : (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).length
      = v.length + 3 * (n * n) * i :=
    length_runGates_blkG (fun a b => length_smOr n k a b) i
  have hfwlt : wFalse (2 * n * k) < (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).length
      := by rw [hWlen, wFalse, hv]; omega
  have hfw : (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).getI (wFalse (2 * n * k))
      = false := by
    rw [getI_runGates_of_lt (by rw [wFalse, hv]; omega), hfalse]
  have hwsW : ∀ w ∈ smWs n k i,
      w < (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).length := by
    intro w hw
    have := hws w hw
    omega
  rw [smOr, show v.length + 3 * (n * n) * i
      = (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).length from hWlen.symm,
    show smOrW n k i = bigOrW (wFalse (2 * n * k))
        (runGates v (blkG (smOr n k) (3 * (n * n)) v.length i)).length (smWs n k i) by
      rw [hacc, bigOrW, length_smWs, hWlen],
    getI_bigOr _ hfw hfwlt hwsW]
  exact any_congr_mem _ fun w hw => getI_runGates_of_lt (hws w hw)

/-- **The disjunction computes the presence bit of the `i`-th cell of the value.** -/
theorem any_smWs {n k i : ℕ} (hi : i < n * n) {x y : List Bool} (hx : x.length ≤ n)
    (hy : y.length ≤ n) {v : List Bool} (hfalse : v.getI (wFalse (2 * n * k)) = false)
    (hval : ∀ t < n * n,
      v.getI (smAndW n k t) = (decide (t / n < x.length) && decide (t % n < y.length))) :
    ((smWs n k i).any fun w => v.getI w) = decide (i < x.length * y.length) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hi
    · exact h
  rcases Nat.lt_or_ge i (x.length * y.length) with hlt | hge
  · rw [decide_eq_true hlt]
    have hxpos : 0 < x.length := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h] at hlt; simp at hlt
      · exact h
    have hypos : 0 < y.length := by
      rcases Nat.eq_zero_or_pos y.length with h | h
      · rw [h] at hlt; simp at hlt
      · exact h
    set a := x.length - 1 with ha
    set b := y.length - 1 with hb
    have hbn : b < n := by omega
    have han : a < n := by omega
    have htlt : n * a + b < n * n := by
      have h1 : n * a + n ≤ n * n := by
        have : n * (a + 1) ≤ n * n := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      omega
    have hdiv : (n * a + b) / n = a := by
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hbn, Nat.add_zero]
    have hmod : (n * a + b) % n = b := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hbn]
    have hax : a + 1 = x.length := by omega
    have hby : b + 1 = y.length := by omega
    rw [List.any_eq_true]
    refine ⟨smAndW n k (n * a + b), ?_, ?_⟩
    · rw [smWs, List.mem_map]
      refine ⟨n * a + b, List.mem_range.2 htlt, ?_⟩
      rw [if_pos (by rw [hdiv, hmod, hax, hby]; exact hlt)]
    · rw [hval _ htlt, hdiv, hmod]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
  · rw [decide_eq_false (by omega)]
    refine any_eq_false_of_mem fun w hw => ?_
    rw [smWs, List.mem_map] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [List.mem_range] at ht
    split_ifs with hc
    · rw [hval t ht]
      by_contra hcon
      simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcon
      have h1 : (t / n + 1) * (t % n + 1) ≤ x.length * y.length :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · exact hfalse

/-! ### The family -/

theorem primrec_smCirc (k : ℕ) : Primrec fun n : ℕ => smCirc n k := by
  have hnk : Primrec fun n : ℕ => 2 * n * k := primrec_nin_mul k
  have hnn : Primrec fun n : ℕ => n * n := Primrec.nat_mul.comp Primrec.id Primrec.id
  have hfalse : Primrec fun n : ℕ => wFalse (2 * n * k) :=
    Primrec.nat_add.comp hnk (Primrec.const 1)
  -- the conjunctions
  have hA : Primrec fun n : ℕ => blkG (smAnd n) 2 (2 * n * k + 2) (n * n) := by
    refine primrec_blkG (g := fun n i b => smAnd n i b) ?_ (Primrec.const 2)
      (Primrec.nat_add.comp hnk (Primrec.const 2)) hnn
    refine primrec_gAnd Primrec.snd ?_ ?_
    · exact Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
    · exact Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst))
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)))
  -- the wires of a disjunction
  have hsmAndW : Primrec fun p : (ℕ × ℕ) × ℕ => smAndW p.1.1 k p.2 := by
    refine Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.fst.comp Primrec.fst)) (Primrec.const k))
      (Primrec.const 2)) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))
      (Primrec.const 1)
  have hsmWs : Primrec fun p : ℕ × ℕ => smWs p.1 k p.2 := by
    refine Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_mul.comp Primrec.fst Primrec.fst)) ?_
    refine Primrec.ite (c := fun p : (ℕ × ℕ) × ℕ =>
        p.1.2 < (p.2 / p.1.1 + 1) * (p.2 % p.1.1 + 1)) ?_ hsmAndW ?_
    · refine PrimrecRel.comp Primrec.nat_lt (Primrec.snd.comp Primrec.fst) ?_
      exact Primrec.nat_mul.comp
        (Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.snd
          (Primrec.fst.comp Primrec.fst)) (Primrec.const 1))
        (Primrec.nat_add.comp (Primrec.nat_mod.comp Primrec.snd
          (Primrec.fst.comp Primrec.fst)) (Primrec.const 1))
    · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.fst.comp Primrec.fst)) (Primrec.const k)) (Primrec.const 1)
  -- the disjunctions
  have hB : Primrec fun n : ℕ =>
      blkG (smOr n k) (3 * (n * n)) (2 * n * k + 2 + 2 * (n * n)) (n * n) := by
    refine primrec_blkG (g := fun n i b => smOr n k i b) ?_
      (Primrec.nat_mul.comp (Primrec.const 3) hnn)
      (Primrec.nat_add.comp (Primrec.nat_add.comp hnk (Primrec.const 2))
        (Primrec.nat_mul.comp (Primrec.const 2) hnn)) hnn
    exact primrec_bigOrG (hfalse.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      (hsmWs.comp Primrec.fst)
  -- the output wires
  have hsmOrW : Primrec fun p : ℕ × ℕ => smOrW p.1 k p.2 := by
    refine primrec_accW (fw := fun p : ℕ × ℕ => wFalse (2 * p.1 * k))
      (base := fun p : ℕ × ℕ =>
        2 * p.1 * k + 2 + 2 * (p.1 * p.1) + 3 * (p.1 * p.1) * p.2) ?_ ?_
      |>.comp (Primrec.pair Primrec.id
        (Primrec.nat_mul.comp Primrec.fst Primrec.fst)) |>.of_eq ?_
    · exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2)
        Primrec.fst) (Primrec.const k)) (Primrec.const 1)
    · exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
          (Primrec.const k)) (Primrec.const 2))
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_mul.comp Primrec.fst Primrec.fst)))
        (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 3)
          (Primrec.nat_mul.comp Primrec.fst Primrec.fst)) Primrec.snd)
    · intro p
      simp only [id_eq, smOrW, bigOrW, length_smWs]
  have hout : Primrec fun n : ℕ =>
      (List.range (n * n)).flatMap fun i => [smOrW n k i, wFalse (2 * n * k)] := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hnn) ?_
    exact Primrec.list_cons.comp (hsmOrW.comp (Primrec.pair Primrec.fst Primrec.snd))
      (Primrec.list_cons.comp (hfalse.comp Primrec.fst) (Primrec.const []))
  exact Primrec.pair hnk (Primrec.pair
    (Primrec.list_append.comp (primrec_gTF hnk) (Primrec.list_append.comp hA hB)) hout)

theorem circFam_smash (k : ℕ) : Nonempty (CircFam smashFn k) := by
  by_cases hk : 2 ≤ k
  · refine ⟨{
      C := fun n => smCirc n k
      B := Polynomial.X * Polynomial.X
      bnd := Polynomial.C (2 * k) * Polynomial.X + Polynomial.C 2 +
        Polynomial.C 4 * Polynomial.X * Polynomial.X +
        Polynomial.C 3 * Polynomial.X * Polynomial.X * Polynomial.X * Polynomial.X
      nin_eq := fun n => rfl
      primC := primrec_smCirc k
      size_le := ?_
      out_lt := ?_
      len_le := ?_
      correct := ?_ }⟩
    · intro n
      rw [Circ.size, length_gates_smCirc, length_out_smCirc]
      simp only [smCirc, Circ.nin_mk, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      ring_nf
      omega
    · intro n j hj
      rw [smCirc, Circ.out_mk, List.mem_flatMap] at hj
      obtain ⟨i, hi, hj⟩ := hj
      rw [List.mem_range] at hi
      simp only [smCirc, Circ.nin_mk, Circ.gates_mk, List.length_append, length_gTF,
        length_blkG (length_smAnd n), length_blkG (length_smOr n k)]
      have hnn : 0 < n * n := by omega
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [smOrW, bigOrW, length_smWs, accW, if_neg (by omega)]
        have h1 : 3 * (n * n) * i + 3 * (n * n) ≤ 3 * (n * n) * (n * n) := by
          have : 3 * (n * n) * (i + 1) ≤ 3 * (n * n) * (n * n) :=
            Nat.mul_le_mul_left _ (by omega)
          nlinarith
        omega
      · rw [List.mem_singleton] at hj
        subst hj
        rw [wFalse]
        omega
    · intro n args hargs hlen
      have h0 : (args.getD 0 []).length ≤ n := by
        refine hlen _ ?_
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have h1 : (args.getD 1 []).length ≤ n := by
        refine hlen _ ?_
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      simp only [smashFn, List.length_replicate, Polynomial.eval_mul, Polynomial.eval_X]
      exact Nat.mul_le_mul h0 h1
    · intro n args hargs hlen
      set x := args.getD 0 [] with hxdef
      set y := args.getD 1 [] with hydef
      have hx : x.length ≤ n := by
        refine hlen _ ?_
        rw [hxdef, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have hy : y.length ≤ n := by
        refine hlen _ ?_
        rw [hydef, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      -- the wires, in three stages
      have hinp : (encArgs k n args).length = 2 * n * k := by simp
      set W1 := encArgs k n args ++ [true, false] with hW1def
      have hW1 : runGates (encArgs k n args) (gTF (2 * n * k)) = W1 := by
        rw [← hinp, runGates_gTF]
      have hW1len : W1.length = 2 * n * k + 2 := by
        rw [hW1def, List.length_append, hinp]
        rfl
      set W2 := runGates W1 (blkG (smAnd n) 2 (2 * n * k + 2) (n * n)) with hW2def
      have hW2len : W2.length = 2 * n * k + 2 + 2 * (n * n) := by
        rw [hW2def, length_runGates, hW1len, length_blkG (length_smAnd n)]
      have hwires : (smCirc n k).wires (encArgs k n args)
          = runGates W2 (blkG (smOr n k) (3 * (n * n))
              (2 * n * k + 2 + 2 * (n * n)) (n * n)) := by
        rw [Circ.wires, smCirc, Circ.gates_mk, runGates_append, runGates_append, hW1, hW2def]
      -- the constant `false`
      have hfalse1 : W1.getI (wFalse (2 * n * k)) = false := by
        have h := getI_wFalse (encArgs k n args)
        rw [runGates_gTF, hinp] at h
        rw [hW1def]
        exact h
      have hfalse2 : W2.getI (wFalse (2 * n * k)) = false := by
        rw [hW2def, getI_runGates_of_lt (by rw [hW1len, wFalse]; omega), hfalse1]
      -- the presence bits the conjunctions read
      have hval : ∀ t < n * n,
          W2.getI (smAndW n k t) = (decide (t / n < x.length) && decide (t % n < y.length)) := by
        intro t ht
        have hn : 0 < n := by
          rcases Nat.eq_zero_or_pos n with rfl | h
          · simp at ht
          · exact h
        have hdiv : t / n < n := (Nat.div_lt_iff_lt_mul hn).2 ht
        have hmod : t % n < n := Nat.mod_lt _ hn
        rw [hW2def, show (2 : ℕ) * n * k + 2 = W1.length from hW1len.symm,
          getI_smAnd_blk hk hW1len ht]
        have e1 : W1.getI (2 * (t / n)) = decide (t / n < x.length) := by
          rw [hW1def, List.getI_append _ _ _ (by rw [hinp]; nlinarith)]
          have := getI_encArgs (k := k) (n := n) (j := 0) (r := 2 * (t / n)) (args := args)
            (by omega) (by omega)
          rw [show 2 * n * 0 + 2 * (t / n) = 2 * (t / n) by ring] at this
          rw [this, ← hxdef, getI_encStr_pres _ hdiv]
        have e2 : W1.getI (2 * n + 2 * (t % n)) = decide (t % n < y.length) := by
          rw [hW1def, List.getI_append _ _ _ (by rw [hinp]; nlinarith)]
          have := getI_encArgs (k := k) (n := n) (j := 1) (r := 2 * (t % n)) (args := args)
            (by omega) (by omega)
          rw [show 2 * n * 1 + 2 * (t % n) = 2 * n + 2 * (t % n) by ring] at this
          rw [this, ← hydef, getI_encStr_pres _ hmod]
        rw [e1, e2]
      -- the output
      rw [Circ.eval, hwires, smCirc, Circ.out_mk, List.map_flatMap]
      have hcell : ∀ i ∈ List.range (n * n),
          ([smOrW n k i, wFalse (2 * n * k)]).map
            (runGates W2 (blkG (smOr n k) (3 * (n * n))
              (2 * n * k + 2 + 2 * (n * n)) (n * n))).getI
            = [decide (i < (smashFn args).length), (smashFn args).getI i] := by
        intro i hi
        rw [List.mem_range] at hi
        have hpres : (runGates W2 (blkG (smOr n k) (3 * (n * n))
            (2 * n * k + 2 + 2 * (n * n)) (n * n))).getI (smOrW n k i)
            = decide (i < x.length * y.length) := by
          rw [show (2 : ℕ) * n * k + 2 + 2 * (n * n) = W2.length from hW2len.symm,
            getI_smOr_blk hW2len hfalse2 hi]
          exact any_smWs hi hx hy hfalse2 hval
        have hzero : (runGates W2 (blkG (smOr n k) (3 * (n * n))
            (2 * n * k + 2 + 2 * (n * n)) (n * n))).getI (wFalse (2 * n * k)) = false := by
          rw [show (2 : ℕ) * n * k + 2 + 2 * (n * n) = W2.length from hW2len.symm,
            getI_runGates_of_lt (by rw [hW2len, wFalse]; omega), hfalse2]
        simp only [List.map_cons, List.map_nil, hpres, hzero, smashFn, List.length_replicate,
          getI_replicate_false, ← hxdef, ← hydef]
      rw [List.flatMap_congr hcell]
      rw [Polynomial.eval_mul, Polynomial.eval_X, encStr]
  · refine circFam_nil fun args hargs => ?_
    rw [smashFn]
    interval_cases k
    · rw [List.length_eq_zero_iff.1 hargs]
      simp
    · have : args.getD 1 [] = [] := by
        rw [List.getD_eq_default]
        omega
      rw [this]
      simp

end Smash

end Compile

end HTN
