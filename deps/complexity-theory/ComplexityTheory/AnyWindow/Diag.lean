import ComplexityTheory.Universal.Diag
/-!
# An asymmetric diagonalisation against one computable procedure with advice

This is the combinatorial core of `HtnCompilability/AnyWindow/Main.lean`.  It is the
asymmetric version of `ComplexityTheory/Universal/Diag.lean`: the row advice and the column
advice range over sets of *different* sizes.

Fix computable parameter functions of a length `n`: a procedure `G n a b`, the numbers `NA n`,
`NB n` of row and column advice values, and the numbers `R n`, `C n` of rows and columns.  An
`R × C` Boolean matrix (a number whose bits are the entries) is **realizable** if there are row
advice values `< NA` and column advice values `< NB` such that every entry is `G n (row i)
(col j)`.  When `NA ^ R · NB ^ C < 2 ^ (R · C)` some matrix is not realizable; the bounded
search `mdiagW` finds the first one, and the pair language `bdiagW` writes it on the first `R`
words of length `n` (rows) and the first `C` words of length `mlen n` (columns).

* `computable_bdiagW` — `bdiagW` is computable;
* `bdiagW_padWord` — what `bdiagW` is on the block;
* `no_advice_mdiagW` — no advice reproduces `mdiagW n` through `G n`.
-/

namespace HTN

namespace AnyWindow

open Universal PTime

section Diag

variable (G : ℕ → ℕ → ℕ → Bool) (NA NB R C : ℕ → ℕ)

/-- The test of one entry. -/
def leafW (n M ca cb i j : ℕ) : Bool :=
  decide (cell M (i * C n + j) = G n (digit (NA n) ca i) (digit (NB n) cb j))

/-- The test of one row. -/
def rowW (n M ca cb i : ℕ) : Bool := ball (C n) (leafW G NA NB C n M ca cb i)

/-- The test of all entries. -/
def allW (n M ca cb : ℕ) : Bool := ball (R n) (rowW G NA NB C n M ca cb)

/-- Some column advice works. -/
def colW (n M ca : ℕ) : Bool := bany (NB n ^ C n) (allW G NA NB R C n M ca)

/-- **Realizability** of the `R n × C n` matrix `M` through `G n`, with packed advice. -/
def realW (n M : ℕ) : Bool := bany (NA n ^ R n) (colW G NA NB R C n M)

/-- **The diagonal matrix**: the first `R n × C n` matrix that is not realizable. -/
def mdiagW (n : ℕ) : ℕ :=
  bfind (2 ^ (R n * C n)) fun M => !realW G NA NB R C n M

/-- **The diagonal pair language.**  On the words `x` of length `n` and `y` of length
`mlen n` with values below `R n` and `C n`, the entry of `mdiagW n`; false elsewhere. -/
def bdiagW (mlen : ℕ → ℕ) (x y : List Bool) : Bool :=
  (y.length == mlen x.length) && decide (natOfBits x < R x.length) &&
    decide (natOfBits y < C x.length) &&
      cell (mdiagW G NA NB R C x.length) (natOfBits x * C x.length + natOfBits y)

/-! ### Counting -/

theorem eq_of_cell_eq {L M M' : ℕ} (hM : M < 2 ^ L) (hM' : M' < 2 ^ L)
    (h : ∀ p < L, cell M p = cell M' p) : M = M' := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < L
  · have := h p hp
    rwa [cell_eq_testBit, cell_eq_testBit] at this
  · push_neg at hp
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hp)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hM' (Nat.pow_le_pow_right (by norm_num) hp))]

variable {G NA NB R C}

theorem realW_eq_true {n M : ℕ} : realW G NA NB R C n M = true ↔
    ∃ ca < NA n ^ R n, ∃ cb < NB n ^ C n, ∀ i < R n, ∀ j < C n,
      cell M (i * C n + j) = G n (digit (NA n) ca i) (digit (NB n) cb j) := by
  simp only [realW, colW, allW, rowW, leafW, bany_eq_true, ball_eq_true, decide_eq_true_eq]

theorem exists_not_realW {n : ℕ} (hcount : NA n ^ R n * NB n ^ C n < 2 ^ (R n * C n)) :
    ∃ M < 2 ^ (R n * C n), realW G NA NB R C n M = false := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ M < 2 ^ (R n * C n), realW G NA NB R C n M = true := fun M hM => by
    simpa using hcon M hM
  have hw : ∀ M ∈ Finset.range (2 ^ (R n * C n)),
      ∃ p : ℕ × ℕ, p ∈ Finset.range (NA n ^ R n) ×ˢ Finset.range (NB n ^ C n) ∧
        ∀ i < R n, ∀ j < C n,
          cell M (i * C n + j) = G n (digit (NA n) p.1 i) (digit (NB n) p.2 j) := by
    intro M hM
    obtain ⟨ca, hca, cb, hcb, h⟩ := realW_eq_true.1 (hall M (Finset.mem_range.1 hM))
    exact ⟨(ca, cb), Finset.mem_product.2 ⟨Finset.mem_range.2 hca, Finset.mem_range.2 hcb⟩, h⟩
  choose φ hφ hφeq using hw
  let Φ : ℕ → ℕ × ℕ := fun M => if h : M ∈ Finset.range (2 ^ (R n * C n)) then φ M h else (0, 0)
  have hinj : Set.InjOn Φ (Finset.range (2 ^ (R n * C n)) : Set ℕ) := by
    intro M hM M' hM' he
    simp only [Φ, dif_pos (Finset.mem_coe.1 hM), dif_pos (Finset.mem_coe.1 hM')] at he
    have hM1 := Finset.mem_range.1 (Finset.mem_coe.1 hM)
    have hM1' := Finset.mem_range.1 (Finset.mem_coe.1 hM')
    apply eq_of_cell_eq hM1 hM1'
    intro p hp
    have hC : 0 < C n := by
      rcases Nat.eq_zero_or_pos (C n) with h | h
      · rw [h, Nat.mul_zero] at hp; omega
      · exact h
    have hi : p / C n < R n := by
      rw [Nat.div_lt_iff_lt_mul hC]; exact hp
    have hj : p % C n < C n := Nat.mod_lt _ hC
    have hpe : p = p / C n * C n + p % C n := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod p (C n)).symm
    rw [hpe, hφeq M (Finset.mem_coe.1 hM) _ hi _ hj, hφeq M' (Finset.mem_coe.1 hM') _ hi _ hj, he]
  have hcard := Finset.card_le_card_of_injOn Φ (fun M hM => by
    have hM' := Finset.mem_coe.1 hM
    rw [show Φ M = φ M hM' from dif_pos hM']
    exact Finset.mem_coe.2 (hφ M hM')) hinj
  rw [Finset.card_range, Finset.card_product, Finset.card_range, Finset.card_range] at hcard
  omega

theorem not_realW_mdiagW {n : ℕ} (hcount : NA n ^ R n * NB n ^ C n < 2 ^ (R n * C n)) :
    realW G NA NB R C n (mdiagW G NA NB R C n) = false := by
  obtain ⟨M, hM, hreal⟩ := exists_not_realW (G := G) hcount
  have hspec := bfind_spec (fun M => !realW G NA NB R C n M) (2 ^ (R n * C n))
  have := hspec.1 (hspec.2.1 ⟨M, hM, by simp [hreal]⟩)
  simpa [mdiagW] using this

theorem getD_map_range (f : ℕ → ℕ) {k i : ℕ} (hi : i < k) :
    ((List.range k).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- **No advice reproduces the diagonal matrix.** -/
theorem no_advice_mdiagW {n : ℕ} (hcount : NA n ^ R n * NB n ^ C n < 2 ^ (R n * C n))
    (α β : ℕ → ℕ) (hα : ∀ i < R n, α i < NA n) (hβ : ∀ j < C n, β j < NB n)
    (h : ∀ i < R n, ∀ j < C n, cell (mdiagW G NA NB R C n) (i * C n + j) = G n (α i) (β j)) :
    False := by
  set La := (List.range (R n)).map α
  set Lb := (List.range (C n)).map β
  have hLa : ∀ d ∈ La, d < NA n := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    exact hα i (List.mem_range.1 hi)
  have hLb : ∀ d ∈ Lb, d < NB n := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
    exact hβ j (List.mem_range.1 hj)
  have hreal : realW G NA NB R C n (mdiagW G NA NB R C n) = true := by
    refine realW_eq_true.2 ⟨packL (NA n) La, ?_, packL (NB n) Lb, ?_, fun i hi j hj => ?_⟩
    · simpa [La] using packL_lt hLa
    · simpa [Lb] using packL_lt hLb
    · rw [digit_packL hLa, digit_packL hLb, getD_map_range _ hi, getD_map_range _ hj]
      exact h i hi j hj
  rw [not_realW_mdiagW hcount] at hreal
  exact absurd hreal (by simp)

/-- **The diagonal language on the block.** -/
theorem bdiagW_padWord (mlen : ℕ → ℕ) {n i j : ℕ} (hi : i < R n) (hj : j < C n)
    (hi2 : i < 2 ^ n) (hj2 : j < 2 ^ mlen n) :
    bdiagW G NA NB R C mlen (padWord n i) (padWord (mlen n) j) =
      cell (mdiagW G NA NB R C n) (i * C n + j) := by
  simp [bdiagW, length_padWord hi2, length_padWord hj2, natOfBits_padWord, hi, hj]

/-! ### Computability -/

variable (hG : Computable fun p : ℕ × ℕ × ℕ => G p.1 p.2.1 p.2.2)
  (hNA : Computable NA) (hNB : Computable NB) (hR : Computable R) (hC : Computable C)

include hG hNA hNB hR hC

omit hR in
theorem computable_leafW : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
    leafW G NA NB C q.1.1.1.1.1 q.1.1.1.1.2 q.1.1.1.2 q.1.1.2 q.1.2 q.2 := by
  unfold leafW
  have hn : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
      Computable.fst)))
  have hM : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
      Computable.fst)))
  have hca : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hcb : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2 :=
    Computable.snd.comp Computable.fst
  have hj : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.2 := Computable.snd
  have h1 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      cell q.1.1.1.1.2 (q.1.2 * C q.1.1.1.1.1 + q.2) :=
    computable_cell.comp hM ((Primrec.nat_add.to_comp).comp
      ((Primrec.nat_mul.to_comp).comp hi (hC.comp hn)) hj)
  have hd1 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      digit (NA q.1.1.1.1.1) q.1.1.1.2 q.1.2 :=
    computable_digit.comp ((hNA.comp hn).pair (hca.pair hi))
  have hd2 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      digit (NB q.1.1.1.1.1) q.1.1.2 q.2 :=
    computable_digit.comp ((hNB.comp hn).pair (hcb.pair hj))
  have h2 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      G q.1.1.1.1.1 (digit (NA q.1.1.1.1.1) q.1.1.1.2 q.1.2)
        (digit (NB q.1.1.1.1.1) q.1.1.2 q.2) :=
    (hG.comp (hn.pair (hd1.pair hd2))).of_eq fun _ => rfl
  exact (Primrec.eq.decide.to_comp (α := Bool)).comp h1 h2

omit hR in
theorem computable_rowW : Computable fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
    rowW G NA NB C q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2 :=
  computable_ball (f := fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => C q.1.1.1.1)
    (q := fun q j => leafW G NA NB C q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2 j)
    (hC.comp (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))
    (computable_leafW hG hNA hNB hC)

theorem computable_allW : Computable fun q : ((ℕ × ℕ) × ℕ) × ℕ =>
    allW G NA NB R C q.1.1.1 q.1.1.2 q.1.2 q.2 :=
  computable_ball (f := fun q : ((ℕ × ℕ) × ℕ) × ℕ => R q.1.1.1)
    (q := fun q i => rowW G NA NB C q.1.1.1 q.1.1.2 q.1.2 q.2 i)
    (hR.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
    (computable_rowW hG hNA hNB hC)

theorem computable_colW : Computable fun q : (ℕ × ℕ) × ℕ => colW G NA NB R C q.1.1 q.1.2 q.2 :=
  computable_bany (f := fun q : (ℕ × ℕ) × ℕ => NB q.1.1 ^ C q.1.1)
    (q := fun q cb => allW G NA NB R C q.1.1 q.1.2 q.2 cb)
    ((primrec_pow.to_comp).comp (hNB.comp (Computable.fst.comp Computable.fst))
      (hC.comp (Computable.fst.comp Computable.fst)))
    (computable_allW hG hNA hNB hR hC)

theorem computable_realW : Computable₂ (realW G NA NB R C) :=
  computable_bany (f := fun q : ℕ × ℕ => NA q.1 ^ R q.1)
    (q := fun q ca => colW G NA NB R C q.1 q.2 ca)
    ((primrec_pow.to_comp).comp (hNA.comp Computable.fst) (hR.comp Computable.fst))
    (computable_colW hG hNA hNB hR hC)

theorem computable_mdiagW : Computable (mdiagW G NA NB R C) :=
  computable_bfind (f := fun n => 2 ^ (R n * C n)) (q := fun n M => !realW G NA NB R C n M)
    ((primrec_pow.to_comp).comp (Computable.const 2)
      ((Primrec.nat_mul.to_comp).comp hR hC))
    (Primrec.not.to_comp.comp (computable_realW hG hNA hNB hR hC))

theorem computable_bdiagW {mlen : ℕ → ℕ} (hm : Computable mlen) :
    Computable₂ (bdiagW G NA NB R C mlen) := by
  have hlen : Computable fun p : List Bool × List Bool => p.1.length :=
    Primrec.list_length.to_comp.comp Computable.fst
  have hx : Computable fun p : List Bool × List Bool => natOfBits p.1 :=
    primrec_natOfBits.to_comp.comp Computable.fst
  have hy : Computable fun p : List Bool × List Bool => natOfBits p.2 :=
    primrec_natOfBits.to_comp.comp Computable.snd
  have hand : Computable₂ (· && · : Bool → Bool → Bool) := Primrec.and.to_comp
  have h1 : Computable fun p : List Bool × List Bool => (p.2.length == mlen p.1.length) :=
    (Primrec.beq.to_comp).comp (Primrec.list_length.to_comp.comp Computable.snd) (hm.comp hlen)
  have h2 : Computable fun p : List Bool × List Bool => decide (natOfBits p.1 < R p.1.length) :=
    (Primrec.nat_lt.decide.to_comp).comp hx (hR.comp hlen)
  have h3 : Computable fun p : List Bool × List Bool => decide (natOfBits p.2 < C p.1.length) :=
    (Primrec.nat_lt.decide.to_comp).comp hy (hC.comp hlen)
  have h4 : Computable fun p : List Bool × List Bool =>
      cell (mdiagW G NA NB R C p.1.length) (natOfBits p.1 * C p.1.length + natOfBits p.2) :=
    computable_cell.comp ((computable_mdiagW hG hNA hNB hR hC).comp hlen)
      ((Primrec.nat_add.to_comp).comp ((Primrec.nat_mul.to_comp).comp hx (hC.comp hlen)) hy)
  exact (hand.comp (hand.comp (hand.comp h1 h2) h3) h4 :)

end Diag

end AnyWindow

end HTN
