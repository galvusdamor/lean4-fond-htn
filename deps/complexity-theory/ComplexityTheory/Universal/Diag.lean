import ComplexityTheory.Complexity.Bits
/-!
# A computable pair language that defeats one computable procedure with two-sided advice

This file is the combinatorial heart of the separation `univLang ∉ PairClass 𝒢` for every class
`𝒢` of *computable* pair languages (`RequestProject/HTN/Universal/Separation.lean`).

Fix a computable Boolean procedure `g` on pairs of bit strings and a computable bound `t`.  For a
length `n` put `S = t n`, `N = 2 ^ (S + 1)` (more than the number of bit strings of length at
most `S`) and `K = 2 S + 3`.  A `K × K` Boolean matrix `M` is **realizable** if there are `K` row
advice strings and `K` column advice strings, each of length at most `S`, such that
`M i j = g (row i) (col j)`.  There are at most `N ^ (2 K) < 2 ^ (K · K)` choices of advice, so
some matrix is not realizable (`exists_not_real`); the brute-force search `mdiag` finds the first
one, and the pair language `bdiag g t` writes it on the first `K` words of length `n` (in both
coordinates).

* `computable_bdiag` — `bdiag g t` is computable (everything is a bounded search);
* `not_advice_bdiag` — at every length `n` with `2 t n + 3 ≤ 2 ^ n`, no pair of advice maps of
  length at most `t n` lets `g` decide `bdiag g t` on the words of length at most `n`.

The search is written with numbers only: advice tuples are packed into numbers in base `N`
(`packL`, `digit`), advice strings are numbered by `enc` / `dec`, and matrices are numbers whose
bits are the entries.
-/

namespace HTN

namespace Universal

open PTime

/-! ### Bounded searches and their computability -/

/-- Bounded existential search: is there `i < n` with `q i`? -/
def bany : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n + 1, q => bany n q || q n

theorem bany_eq_true {n : ℕ} {q : ℕ → Bool} : bany n q = true ↔ ∃ i < n, q i = true := by
  induction n with
  | zero => simp [bany]
  | succ n ih =>
    simp only [bany, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem computable_bany {α : Type} [Primcodable α] {f : α → ℕ} {q : α → ℕ → Bool}
    (hf : Computable f) (hq : Computable₂ q) : Computable fun a => bany (f a) (q a) := by
  have h : Computable fun a => (Nat.rec (motive := fun _ => Bool) false
      (fun y IH => (fun (a : α) (p : ℕ × Bool) => p.2 || q a p.1) a (y, IH)) (f a)) :=
    Computable.nat_rec hf (Computable.const false)
      ((Primrec.or.to_comp).comp₂ (Computable.snd.comp Computable.snd).to₂
        (hq.comp Computable.fst (Computable.fst.comp Computable.snd)).to₂)
  refine h.of_eq fun a => ?_
  generalize f a = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [bany, ← ih]

/-- Bounded universal search. -/
def ball (n : ℕ) (q : ℕ → Bool) : Bool := !bany n fun i => !q i

theorem ball_eq_true {n : ℕ} {q : ℕ → Bool} : ball n q = true ↔ ∀ i < n, q i = true := by
  simp only [ball, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h i hi
    by_contra hq
    have : bany n (fun i => !q i) = true := bany_eq_true.2 ⟨i, hi, by simpa using hq⟩
    rw [h] at this
    exact absurd this (by simp)
  · intro h
    by_contra hb
    obtain ⟨i, hi, hq⟩ := bany_eq_true.1 (by simpa using hb)
    simp [h i hi] at hq

theorem computable_ball {α : Type} [Primcodable α] {f : α → ℕ} {q : α → ℕ → Bool}
    (hf : Computable f) (hq : Computable₂ q) : Computable fun a => ball (f a) (q a) :=
  Primrec.not.to_comp.comp (computable_bany hf (Primrec.not.to_comp.comp₂ hq))

/-- Bounded search for the least witness: the least `i < n` with `q i`, and `n` if there is
none. -/
def bfind : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, q => if bfind n q < n then bfind n q else if q n then n else n + 1

theorem bfind_spec (q : ℕ → Bool) (n : ℕ) :
    (bfind n q < n → q (bfind n q) = true) ∧ ((∃ i < n, q i = true) → bfind n q < n) ∧
      bfind n q ≤ n := by
  induction n with
  | zero => simp [bfind]
  | succ n ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    by_cases hlt : bfind n q < n
    · have e : bfind (n + 1) q = bfind n q := by simp only [bfind, if_pos hlt]
      rw [e]
      exact ⟨fun _ => ih1 hlt, fun _ => by omega, by omega⟩
    · by_cases hq : q n = true
      · have e : bfind (n + 1) q = n := by simp only [bfind, if_neg hlt, if_pos hq]
        rw [e]
        exact ⟨fun _ => hq, fun _ => by omega, by omega⟩
      · have e : bfind (n + 1) q = n + 1 := by simp only [bfind, if_neg hlt, if_neg hq]
        rw [e]
        refine ⟨fun h => absurd h (lt_irrefl _), fun ⟨i, hi, hqi⟩ => ?_, le_refl _⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact absurd (ih2 ⟨i, hi, hqi⟩) hlt
        · exact absurd hqi hq

theorem computable_bfind {α : Type} [Primcodable α] {f : α → ℕ} {q : α → ℕ → Bool}
    (hf : Computable f) (hq : Computable₂ q) : Computable fun a => bfind (f a) (q a) := by
  have hstep : Computable₂ fun (a : α) (p : ℕ × ℕ) =>
      bif decide (p.2 < p.1) then p.2 else bif q a p.1 then p.1 else p.1 + 1 := by
    refine Computable.cond ?_ (Computable.snd.comp Computable.snd) ?_
    · exact (Primrec.nat_lt.decide.to_comp).comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.snd)
    · refine Computable.cond (hq.comp Computable.fst (Computable.fst.comp Computable.snd))
        (Computable.fst.comp Computable.snd) ?_
      exact Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
  have h := Computable.nat_rec hf (Computable.const 0) hstep
  refine h.of_eq fun a => ?_
  generalize f a = n
  induction n with
  | zero => rfl
  | succ n ih =>
    have key : ∀ r : ℕ, (bif decide (r < n) then r else bif q a n then n else n + 1) =
        (if r < n then r else if q a n = true then n else n + 1) := by
      intro r
      by_cases h1 : r < n <;> cases h2 : q a n <;> simp [h1]
    change (bif decide (_ < n) then _ else bif q a n then n else n + 1) = _
    rw [ih, key]
    rfl

/-! ### Powers, digits and packing -/

theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
  have h : Primrec fun p : ℕ × ℕ => Nat.rec (motive := fun _ => ℕ) 1
      (fun y IH => (fun (p : ℕ × ℕ) (q : ℕ × ℕ) => p.1 * q.2) p (y, IH)) p.2 :=
    Primrec.nat_rec' Primrec.snd (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  refine Primrec₂.mk (h.of_eq fun p => ?_)
  obtain ⟨a, n⟩ := p
  simp only
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ← ih]; ring

/-- The `i`-th digit of `c` in base `N`. -/
@[irreducible] def digit (N c i : ℕ) : ℕ := c / N ^ i % N

/-- A list of digits packed into a number in base `N`, least significant first. -/
def packL (N : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: L => d + N * packL N L

theorem packL_lt {N : ℕ} : ∀ {L : List ℕ}, (∀ d ∈ L, d < N) → packL N L < N ^ L.length
  | [], _ => by simp [packL]
  | d :: L, h => by
    have hd : d < N := h d (by simp)
    have ih := packL_lt (L := L) fun d' hd' => h d' (by simp [hd'])
    simp only [packL, List.length_cons, pow_succ]
    have : N * packL N L + N ≤ N * N ^ L.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    nlinarith

theorem digit_packL {N : ℕ} : ∀ {L : List ℕ}, (∀ d ∈ L, d < N) → ∀ i : ℕ,
    digit N (packL N L) i = L.getD i 0
  | [], _, i => by simp [digit, packL]
  | d :: L, h, i => by
    have hd : d < N := h d (by simp)
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hd
    have ih := digit_packL (L := L) (fun d' hd' => h d' (by simp [hd']))
    cases i with
    | zero =>
      simp [digit, packL, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ i =>
      have h1 : (d + N * packL N L) / N = packL N L := by
        rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hd, zero_add]
      have h2 : (d + N * packL N L) / N ^ (i + 1) = packL N L / N ^ i := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul, h1]
      simp only [digit, packL, List.getD_cons_succ] at ih ⊢
      rw [h2, ih i]

/-! ### Numbering the bit strings -/

/-- The number of a bit string: its binary value with a leading `1` appended. -/
def enc (z : List Bool) : ℕ := natOfBits (z ++ [true])

/-- The bit string of a number (inverse to `enc` on positive numbers). -/
def dec (m : ℕ) : List Bool := (bitsOfNat m).dropLast

theorem bitsOfNat_natOfBits_append_true : ∀ z : List Bool,
    bitsOfNat (natOfBits (z ++ [true])) = z ++ [true]
  | [] => by simp [natOfBits_cons, bitsOfNat_one]
  | b :: z => by
    have ih := bitsOfNat_natOfBits_append_true z
    have hpos : 0 < natOfBits (z ++ [true]) := by
      rcases h : natOfBits (z ++ [true]) with _ | k
      · rw [h, bitsOfNat_zero] at ih; simp at ih
      · omega
    simp only [List.cons_append, natOfBits_cons]
    obtain ⟨k, hk⟩ : ∃ k, (if b then 1 else 0) + 2 * natOfBits (z ++ [true]) = k + 1 :=
      ⟨(if b then 1 else 0) + 2 * natOfBits (z ++ [true]) - 1, by omega⟩
    rw [hk, bitsOfNat_succ, ← hk]
    have hdiv : ((if b then 1 else 0) + 2 * natOfBits (z ++ [true])) / 2 =
        natOfBits (z ++ [true]) := by
      cases b <;> simp only [Bool.false_eq_true, if_true, if_false] <;> omega
    have hmod : decide (((if b then 1 else 0) + 2 * natOfBits (z ++ [true])) % 2 = 1) = b := by
      cases b <;> simp
    rw [hdiv, hmod, ih]

theorem dec_enc (z : List Bool) : dec (enc z) = z := by
  simp [dec, enc, bitsOfNat_natOfBits_append_true]

theorem natOfBits_lt_two_pow : ∀ l : List Bool, natOfBits l < 2 ^ l.length
  | [] => by simp
  | b :: l => by
    have := natOfBits_lt_two_pow l
    simp only [natOfBits_cons, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

theorem enc_lt (z : List Bool) : enc z < 2 ^ (z.length + 1) := by
  have := natOfBits_lt_two_pow (z ++ [true])
  simpa [enc] using this

theorem primrec_dec : Primrec dec := by
  have h : Primrec fun m : ℕ => ((bitsOfNat m).reverse.tail).reverse :=
    Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp primrec_bitsOfNat))
  refine h.of_eq fun m => ?_
  simp only [dec]
  rw [List.tail_reverse, List.reverse_reverse]

/-! ### Words of a given length with a given value -/

/-- The word of length `n` (for `i < 2 ^ n`) whose value is `i`. -/
def padWord (n i : ℕ) : List Bool := bitsOfNat i ++ List.replicate (n - (bitsOfNat i).length) false

theorem natOfBits_replicate_false (k : ℕ) : natOfBits (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, natOfBits_cons, ih]

theorem natOfBits_append_replicate_false (l : List Bool) (k : ℕ) :
    natOfBits (l ++ List.replicate k false) = natOfBits l := by
  induction l with
  | nil => simp [natOfBits_replicate_false]
  | cons b l ih => simp [natOfBits_cons, ih]

theorem length_bitsOfNat_le {n i : ℕ} (h : i < 2 ^ n) : (bitsOfNat i).length ≤ n := by
  induction n generalizing i with
  | zero =>
    have : i = 0 := by simpa using h
    simp [this]
  | succ n ih =>
    rcases i with _ | i
    · simp
    · rw [bitsOfNat_succ, List.length_cons]
      have : (i + 1) / 2 < 2 ^ n := by
        rw [pow_succ] at h; omega
      have := ih this
      omega

theorem natOfBits_padWord (n i : ℕ) : natOfBits (padWord n i) = i := by
  simp [padWord, natOfBits_append_replicate_false, natOfBits_bitsOfNat]

theorem length_padWord {n i : ℕ} (h : i < 2 ^ n) : (padWord n i).length = n := by
  have := length_bitsOfNat_le h
  simp [padWord]; omega

/-! ### Matrices and their realizability -/

/-- The entry at position `p` of the matrix coded by `M` (its `p`-th bit). -/
@[irreducible] def cell (M p : ℕ) : Bool := decide (M / 2 ^ p % 2 = 1)

theorem cell_eq_testBit (M p : ℕ) : cell M p = M.testBit p := by
  rw [cell, Nat.testBit_eq_decide_div_mod_eq]

/-- The number of advice strings considered at the advice length `S`. -/
@[irreducible] def advN (S : ℕ) : ℕ := 2 ^ (S + 1)

/-- The side of the matrices diagonalised against at the advice length `S`. -/
@[irreducible] def side (S : ℕ) : ℕ := 2 * S + 3

theorem advN_eq (S : ℕ) : advN S = 2 ^ (S + 1) := by unfold advN; rfl

theorem side_eq (S : ℕ) : side S = 2 * S + 3 := by unfold side; rfl

/-- `g` evaluated on numbered advice strings. -/
def gNum (g : List Bool → List Bool → Bool) (u v : ℕ) : Bool := g (dec u) (dec v)

/-- The test at the entry `(i, j)`: the matrix entry agrees with `g` on the advice. -/
def realLeaf (g : List Bool → List Bool → Bool) (S M ca cb i j : ℕ) : Bool :=
  decide (cell M (i * side S + j) = gNum g (digit (advN S) ca i) (digit (advN S) cb j))

/-- The test of the row `i`. -/
def realRow (g : List Bool → List Bool → Bool) (S M ca cb i : ℕ) : Bool :=
  ball (side S) fun j => realLeaf g S M ca cb i j

/-- The test of all entries, for the packed advice `ca`, `cb`. -/
def realAll (g : List Bool → List Bool → Bool) (S M ca cb : ℕ) : Bool :=
  ball (side S) fun i => realRow g S M ca cb i

/-- Some column advice works for the packed row advice `ca`. -/
def realCol (g : List Bool → List Bool → Bool) (S M ca : ℕ) : Bool :=
  bany (advN S ^ side S) fun cb => realAll g S M ca cb

/-- **Realizability**: the `K × K` matrix `M` is `g (row i) (col j)` for some row and column advice
strings, numbered below `N`, packed in base `N` into `ca` and `cb`. -/
def real (g : List Bool → List Bool → Bool) (S M : ℕ) : Bool :=
  bany (advN S ^ side S) fun ca => realCol g S M ca

/-- **The diagonal matrix**: the first `K × K` matrix that is not realizable. -/
def mdiag (g : List Bool → List Bool → Bool) (S : ℕ) : ℕ :=
  bfind (2 ^ (side S * side S)) fun M => !real g S M

/-- **The diagonal pair language**: on the words of length `n` whose values are below `K`, the
matrix `mdiag g (t n)`; false everywhere else. -/
def bdiag (g : List Bool → List Bool → Bool) (t : ℕ → ℕ) (x y : List Bool) : Bool :=
  x.length == y.length && decide (natOfBits x < side (t x.length)) &&
    decide (natOfBits y < side (t x.length)) &&
      cell (mdiag g (t x.length)) (natOfBits x * side (t x.length) + natOfBits y)

/-! ### Counting: some matrix is not realizable -/

theorem eq_of_cells {K M M' : ℕ} (hM : M < 2 ^ (K * K)) (hM' : M' < 2 ^ (K * K))
    (h : ∀ i < K, ∀ j < K, cell M (i * K + j) = cell M' (i * K + j)) : M = M' := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < K * K
  · have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h0 | h0
      · simp [h0] at hp
      · exact h0
    have hi : p / K < K := by
      rw [Nat.div_lt_iff_lt_mul hK]; exact hp
    have hj : p % K < K := Nat.mod_lt _ hK
    have := h (p / K) hi (p % K) hj
    rw [cell_eq_testBit, cell_eq_testBit] at this
    rwa [show p / K * K + p % K = p from Nat.div_add_mod' p K] at this
  · push_neg at hp
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (Nat.pow_le_pow_right (by norm_num) hp)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hM' (Nat.pow_le_pow_right (by norm_num) hp))]

theorem advN_pow_lt (S : ℕ) : advN S ^ side S * advN S ^ side S < 2 ^ (side S * side S) := by
  rw [advN, ← pow_mul, ← pow_add]
  apply Nat.pow_lt_pow_right (by norm_num)
  simp only [side]
  nlinarith

theorem exists_not_real (g : List Bool → List Bool → Bool) (S : ℕ) :
    ∃ M < 2 ^ (side S * side S), (!real g S M) = true := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ M < 2 ^ (side S * side S), real g S M = true := by
    intro M hM
    have := hcon M hM
    simpa using this
  -- choose the advice of every matrix
  have hw : ∀ M ∈ Finset.range (2 ^ (side S * side S)),
      ∃ p ∈ Finset.range (advN S ^ side S) ×ˢ Finset.range (advN S ^ side S),
        ∀ i < side S, ∀ j < side S,
          cell M (i * side S + j) = gNum g (digit (advN S) p.1 i) (digit (advN S) p.2 j) := by
    intro M hM
    have h := hall M (Finset.mem_range.1 hM)
    obtain ⟨ca, hca, h⟩ := bany_eq_true.1 h
    obtain ⟨cb, hcb, h⟩ := bany_eq_true.1 h
    refine ⟨(ca, cb), Finset.mem_product.2 ⟨Finset.mem_range.2 hca, Finset.mem_range.2 hcb⟩, ?_⟩
    intro i hi j hj
    have h1 := ball_eq_true.1 h i hi
    have h2 := ball_eq_true.1 h1 j hj
    simpa [realLeaf] using h2
  choose φ hφ hφeq using hw
  have hinj : Set.InjOn (fun M => if h : M ∈ Finset.range (2 ^ (side S * side S)) then φ M h
      else (0, 0)) (Finset.range (2 ^ (side S * side S)) : Set ℕ) := by
    intro M hM M' hM' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hM hM'
    have hM1 : M ∈ Finset.range (2 ^ (side S * side S)) := Finset.mem_range.2 hM
    have hM1' : M' ∈ Finset.range (2 ^ (side S * side S)) := Finset.mem_range.2 hM'
    simp only [hM1, hM1', dite_true] at heq
    refine eq_of_cells hM hM' fun i hi j hj => ?_
    rw [hφeq M hM1 i hi j hj, hφeq M' hM1' i hi j hj, heq]
  have hcard := Finset.card_le_card_of_injOn _ (fun M hM => by
      have hM1 : M ∈ Finset.range (2 ^ (side S * side S)) := hM
      simp only [hM1, dite_true]
      exact hφ M hM1) hinj
  rw [Finset.card_range, Finset.card_product, Finset.card_range] at hcard
  exact absurd hcard (not_le.2 (advN_pow_lt S))

theorem not_real_mdiag (g : List Bool → List Bool → Bool) (S : ℕ) : real g S (mdiag g S) = false := by
  obtain ⟨M, hM, hreal⟩ := exists_not_real g S
  have hspec := bfind_spec (fun M => !real g S M) (2 ^ (side S * side S))
  have := hspec.1 (hspec.2.1 ⟨M, hM, hreal⟩)
  simpa [mdiag] using this

/-! ### The diagonal language defeats `g` -/

/-- **The diagonal language is not decided by `g` with advice of length `t n`**, at every length
`n` at which the `2 t n + 3` diagonal words exist. -/
theorem not_advice_bdiag (g : List Bool → List Bool → Bool) (t : ℕ → ℕ) {n : ℕ}
    (hn : side (t n) ≤ 2 ^ n) :
    ¬ ∃ a b : List Bool → List Bool, ∀ x y : List Bool, x.length ≤ n → y.length ≤ n →
      (a x).length ≤ t n ∧ (b y).length ≤ t n ∧ (bdiag g t x y = true ↔ g (a x) (b y) = true) := by
  rintro ⟨a, b, hab⟩
  set S := t n with hS
  set K := side S with hK
  set N := advN S with hN
  have hwlen : ∀ i < K, (padWord n i).length = n := fun i hi =>
    length_padWord (lt_of_lt_of_le hi hn)
  have hwval : ∀ i, natOfBits (padWord n i) = i := natOfBits_padWord n
  -- the advice of the rows and of the columns, numbered and packed
  set La : List ℕ := (List.range K).map fun i => enc (a (padWord n i)) with hLa
  set Lb : List ℕ := (List.range K).map fun j => enc (b (padWord n j)) with hLb
  have hencN : ∀ z : List Bool, z.length ≤ S → enc z < N := fun z hz => by
    rw [hN, advN_eq]
    exact lt_of_lt_of_le (enc_lt z) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hLaN : ∀ d ∈ La, d < N := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
    exact hencN _ (hab _ _ (le_of_eq (hwlen i (List.mem_range.1 hi)))
      (le_of_eq (hwlen i (List.mem_range.1 hi)))).1
  have hLbN : ∀ d ∈ Lb, d < N := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
    exact hencN _ (hab _ _ (le_of_eq (hwlen j (List.mem_range.1 hj)))
      (le_of_eq (hwlen j (List.mem_range.1 hj)))).2.1
  have hreal : real g S (mdiag g S) = true := by
    refine bany_eq_true.2 ⟨packL N La, ?_, bany_eq_true.2 ⟨packL N Lb, ?_, ?_⟩⟩
    · have h := packL_lt hLaN
      rwa [hLa, List.length_map, List.length_range] at h
    · have h := packL_lt hLbN
      rwa [hLb, List.length_map, List.length_range] at h
    · refine ball_eq_true.2 fun i hi => ball_eq_true.2 fun j hj => ?_
      simp only [realLeaf]
      rw [digit_packL hLaN, digit_packL hLbN]
      have hiK : i < K := hi
      have hjK : j < K := hj
      have hgi : La.getD i 0 = enc (a (padWord n i)) := by
        simp [hLa, List.getD_eq_getElem?_getD, hiK]
      have hgj : Lb.getD j 0 = enc (b (padWord n j)) := by
        simp [hLb, List.getD_eq_getElem?_getD, hjK]
      rw [hgi, hgj]
      simp only [gNum, dec_enc, decide_eq_true_eq]
      have hx := hwlen i hi
      have hy := hwlen j hj
      have key := (hab (padWord n i) (padWord n j) (le_of_eq hx) (le_of_eq hy)).2.2
      have hbd : bdiag g t (padWord n i) (padWord n j) =
          cell (mdiag g S) (i * K + j) := by
        simp [bdiag, hx, hy, hwval, ← hS, ← hK, hiK, hjK]
      rw [← hbd]
      cases h1 : bdiag g t (padWord n i) (padWord n j) <;>
        cases h2 : g (a (padWord n i)) (b (padWord n j)) <;> simp_all
  rw [not_real_mdiag] at hreal
  exact absurd hreal (by simp)

/-! ### Computability of the diagonal language -/

theorem computable_side : Computable side := by
  unfold side
  exact (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
    (Primrec.const 3)).to_comp

theorem computable_advN : Computable advN := by
  unfold advN
  exact primrec_pow.to_comp.comp (Computable.const 2) Primrec.succ.to_comp

theorem computable_cell : Computable₂ cell := by
  unfold cell
  exact (Primrec.eq.decide.comp (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst
    (primrec_pow.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2))
    (Primrec.const 1)).to_comp.to₂

theorem computable_digit : Computable fun p : ℕ × ℕ × ℕ => digit p.1 p.2.1 p.2.2 := by
  unfold digit
  exact (Primrec.nat_mod.comp (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
    (primrec_pow.comp Primrec.fst (Primrec.snd.comp Primrec.snd))) Primrec.fst).to_comp

section CompReal

variable {g : List Bool → List Bool → Bool}

theorem computable_gNum (hg : Computable₂ g) : Computable₂ (gNum g) :=
  hg.comp (primrec_dec.to_comp.comp Computable.fst) (primrec_dec.to_comp.comp Computable.snd)

theorem computable_realLeaf (hg : Computable₂ g) :
    Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      realLeaf g q.1.1.1.1.1 q.1.1.1.1.2 q.1.1.1.2 q.1.1.2 q.1.2 q.2 := by
  have hS : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.1 :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp Computable.fst)))
  have hM : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp Computable.fst)))
  have hca : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hcb : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.1.2 :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.1.2 :=
    Computable.snd.comp Computable.fst
  have hj : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => q.2 := Computable.snd
  have h1 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      cell q.1.1.1.1.2 (q.1.2 * side q.1.1.1.1.1 + q.2) :=
    computable_cell.comp hM ((Primrec.nat_add.to_comp).comp
      ((Primrec.nat_mul.to_comp).comp hi (computable_side.comp hS)) hj)
  have hN : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ => advN q.1.1.1.1.1 :=
    computable_advN.comp hS
  have hd1 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      digit (advN q.1.1.1.1.1) q.1.1.1.2 q.1.2 :=
    computable_digit.comp (hN.pair (hca.pair hi))
  have hd2 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      digit (advN q.1.1.1.1.1) q.1.1.2 q.2 :=
    computable_digit.comp (hN.pair (hcb.pair hj))
  have h2 : Computable fun q : ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
      gNum g (digit (advN q.1.1.1.1.1) q.1.1.1.2 q.1.2)
        (digit (advN q.1.1.1.1.1) q.1.1.2 q.2) :=
    (computable_gNum hg).comp hd1 hd2
  exact (Primrec.eq.decide.to_comp).comp h1 h2

theorem computable_realRow (hg : Computable₂ g) :
    Computable fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ =>
      realRow g q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2 :=
  computable_ball (f := fun q : (((ℕ × ℕ) × ℕ) × ℕ) × ℕ => side q.1.1.1.1)
    (q := fun q j => realLeaf g q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2 j)
    (computable_side.comp (Computable.fst.comp (Computable.fst.comp
      (Computable.fst.comp Computable.fst)))) (computable_realLeaf hg)

theorem computable_realAll (hg : Computable₂ g) :
    Computable fun q : ((ℕ × ℕ) × ℕ) × ℕ => realAll g q.1.1.1 q.1.1.2 q.1.2 q.2 :=
  computable_ball (f := fun q : ((ℕ × ℕ) × ℕ) × ℕ => side q.1.1.1)
    (q := fun q i => realRow g q.1.1.1 q.1.1.2 q.1.2 q.2 i)
    (computable_side.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
    (computable_realRow hg)

theorem computable_realCol (hg : Computable₂ g) :
    Computable fun q : (ℕ × ℕ) × ℕ => realCol g q.1.1 q.1.2 q.2 :=
  computable_bany (f := fun q : (ℕ × ℕ) × ℕ => advN q.1.1 ^ side q.1.1)
    (q := fun q cb => realAll g q.1.1 q.1.2 q.2 cb)
    (primrec_pow.to_comp.comp (computable_advN.comp (Computable.fst.comp Computable.fst))
      (computable_side.comp (Computable.fst.comp Computable.fst)))
    (computable_realAll hg)

theorem computable_real (hg : Computable₂ g) : Computable₂ (real g) :=
  computable_bany (f := fun q : ℕ × ℕ => advN q.1 ^ side q.1)
    (q := fun q ca => realCol g q.1 q.2 ca)
    (primrec_pow.to_comp.comp (computable_advN.comp Computable.fst)
      (computable_side.comp Computable.fst))
    (computable_realCol hg)

end CompReal

theorem computable_mdiag {g : List Bool → List Bool → Bool} (hg : Computable₂ g) :
    Computable (mdiag g) :=
  computable_bfind (f := fun S => 2 ^ (side S * side S)) (q := fun S M => !real g S M)
    (primrec_pow.to_comp.comp (Computable.const 2)
      ((Primrec.nat_mul.to_comp).comp computable_side computable_side))
    (Primrec.not.to_comp.comp₂ (computable_real hg))

/-- **The diagonal language is computable.** -/
theorem computable_bdiag {g : List Bool → List Bool → Bool} (hg : Computable₂ g) {t : ℕ → ℕ}
    (ht : Computable t) : Computable₂ (bdiag g t) := by
  have hlen : Computable fun p : List Bool × List Bool => p.1.length :=
    Computable.list_length.comp Computable.fst
  have hS : Computable fun p : List Bool × List Bool => side (t p.1.length) :=
    computable_side.comp (ht.comp hlen)
  have hx : Computable fun p : List Bool × List Bool => natOfBits p.1 :=
    computable_natOfBits.comp Computable.fst
  have hy : Computable fun p : List Bool × List Bool => natOfBits p.2 :=
    computable_natOfBits.comp Computable.snd
  have hand : Computable₂ (· && · : Bool → Bool → Bool) := Primrec.and.to_comp
  have h1 : Computable fun p : List Bool × List Bool => (p.1.length == p.2.length) :=
    Primrec.beq.to_comp.comp hlen (Computable.list_length.comp Computable.snd)
  have h2 : Computable fun p : List Bool × List Bool =>
      decide (natOfBits p.1 < side (t p.1.length)) :=
    Primrec.nat_lt.decide.to_comp.comp hx hS
  have h3 : Computable fun p : List Bool × List Bool =>
      decide (natOfBits p.2 < side (t p.1.length)) :=
    Primrec.nat_lt.decide.to_comp.comp hy hS
  have h4 : Computable fun p : List Bool × List Bool =>
      cell (mdiag g (t p.1.length)) (natOfBits p.1 * side (t p.1.length) + natOfBits p.2) :=
    computable_cell.comp ((computable_mdiag hg).comp (ht.comp hlen))
      ((Primrec.nat_add.to_comp).comp ((Primrec.nat_mul.to_comp).comp hx hS) hy)
  exact (hand.comp (hand.comp (hand.comp h1 h2) h3) h4 :)

end Universal

end HTN
