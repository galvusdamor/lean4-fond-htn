import Mathlib

/-!
# Counts as digits of one number

The native regime RA of PROOFIDEAS §15.4 keeps the anonymous configuration of a thread pool —
the number of threads per (class, state) — in **one** register, as the digits of a number in
base `B = N + 1`:

    enc B n c = Σ_{i < n} c i · B ^ i.

* **`HTN.RegRounds.Godel.digit_enc`** — if every count is below `B`, digit `j` of `enc B n c`
  is `c j`;
* **`HTN.RegRounds.Godel.enc_move`** — moving one unit from index `i` to index `j` adds `B ^ j`
  and subtracts `B ^ i` (and `B ^ i ≤ enc B n c` when `c i ≥ 1`);
* `HTN.RegRounds.Godel.enc_lt` — the encoding is below `B ^ n`;
* for multisets (`encM`): **`digit_encM`** — digit `idx a` is the multiplicity of `a`, and
  **`encM_move`** — an anonymous move `m ↦ m.erase a + {a'}` is `X ↦ X - B^(idx a) + B^(idx a')`.

So one anonymous step of the pool is one register update `X ↦ X - B^i + B^j` after the test
"digit `i` is non-zero", and the end-of-round check "no unit of an old class is left" is a test
that the corresponding digits are zero.
-/

namespace HTN

namespace RegRounds

namespace Godel

open Finset

/-- The encoding of the counts `c i`, `i < n`, as digits in base `B`. -/
def enc (B n : ℕ) (c : ℕ → ℕ) : ℕ := ∑ i ∈ range n, c i * B ^ i

theorem enc_lt {B n : ℕ} {c : ℕ → ℕ} (hc : ∀ i < n, c i < B) : enc B n c < B ^ n := by
  induction n with
  | zero => simp [enc]
  | succ n ih =>
    simp only [enc, sum_range_succ]
    have h1 : ∑ i ∈ range n, c i * B ^ i < B ^ n := ih fun i hi => hc i (by omega)
    have h2 : c n ≤ B - 1 := by have := hc n (by omega); omega
    have hB : 1 ≤ B := by have := hc n (by omega); omega
    calc ∑ i ∈ range n, c i * B ^ i + c n * B ^ n
        < B ^ n + c n * B ^ n := by omega
      _ ≤ B ^ n + (B - 1) * B ^ n := Nat.add_le_add_left (Nat.mul_le_mul_right _ h2) _
      _ = B ^ (n + 1) := by
        rw [pow_succ]
        have : B ^ n + (B - 1) * B ^ n = (1 + (B - 1)) * B ^ n := by ring
        rw [this, show 1 + (B - 1) = B by omega, mul_comm]

/-- Splitting the encoding at index `j`. -/
theorem enc_split {B n j : ℕ} (hj : j < n) (c : ℕ → ℕ) :
    enc B n c = enc B j c + c j * B ^ j + B ^ (j + 1) * enc B (n - (j + 1)) (fun i => c (j + 1 + i)) := by
  unfold enc
  have hn : n = (j + 1) + (n - (j + 1)) := by omega
  conv_lhs => rw [hn, sum_range_add, sum_range_succ]
  congr 1
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pow_add]; ring

/-- **Digit extraction.** -/
theorem digit_enc {B n : ℕ} {c : ℕ → ℕ} (hc : ∀ i < n, c i < B) {j : ℕ} (hj : j < n) :
    enc B n c / B ^ j % B = c j := by
  have hB : 0 < B := by have := hc j hj; omega
  have hlow : enc B j c < B ^ j := enc_lt fun i hi => hc i (by omega)
  rw [enc_split hj c]
  set H := enc B (n - (j + 1)) (fun i => c (j + 1 + i))
  have hpos : 0 < B ^ j := pow_pos hB j
  have : enc B j c + c j * B ^ j + B ^ (j + 1) * H = enc B j c + B ^ j * (c j + B * H) := by
    rw [pow_succ]; ring
  rw [this, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc j hj)]

/-- The encoding is additive in the counts. -/
theorem enc_add (B n : ℕ) (c d : ℕ → ℕ) : enc B n (c + d) = enc B n c + enc B n d := by
  unfold enc
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp [add_mul]

/-- The encoding of a unit count at index `j < n`. -/
theorem enc_single {B n j : ℕ} (hj : j < n) : enc B n (Pi.single j 1) = B ^ j := by
  unfold enc
  rw [sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (mem_range.2 hj) h

/-- **Moving one unit from index `i` to index `j`.**  With `c i ≥ 1`, the counts
`c' = c - e_i + e_j` satisfy `enc c' + B^i = enc c + B^j`. -/
theorem enc_move {B n i j : ℕ} (hi : i < n) (hj : j < n) {c : ℕ → ℕ} (hci : 1 ≤ c i) :
    enc B n (Function.update c i (c i - 1) + Pi.single j 1) + B ^ i = enc B n c + B ^ j := by
  have h1 : c = Function.update c i (c i - 1) + Pi.single i 1 := by
    funext x
    by_cases hx : x = i
    · subst hx; simp; omega
    · simp [hx]
  conv_rhs => rw [h1]
  rw [enc_add, enc_add, enc_single hi, enc_single hj]
  ring

/-! ### Multisets as numbers -/

variable {α : Type*} [DecidableEq α]

/-- The number of a multiset of indexed elements. -/
def encM (B : ℕ) (idx : α → ℕ) (m : Multiset α) : ℕ := (m.map fun a => B ^ idx a).sum

/-- The counts per index. -/
def cnt (idx : α → ℕ) (m : Multiset α) (i : ℕ) : ℕ := (m.filter fun a => idx a = i).card

omit [DecidableEq α] in
theorem encM_eq_enc (B n : ℕ) (idx : α → ℕ) (m : Multiset α) (hm : ∀ a ∈ m, idx a < n) :
    encM B idx m = enc B n (cnt idx m) := by
  induction m using Multiset.induction_on with
  | empty => simp [encM, enc, cnt]
  | cons a m ih =>
    have ih' := ih fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have hcnt : cnt idx (a ::ₘ m) = cnt idx m + Pi.single (idx a) 1 := by
      funext i
      simp only [cnt, Multiset.filter_cons, Pi.add_apply, Pi.single_apply]
      split_ifs with h1 h2 h2
      · simp [add_comm]
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    rw [hcnt, enc_add, enc_single (hm a (Multiset.mem_cons_self a m)), ← ih']
    simp [encM, add_comm]

omit [DecidableEq α] in
theorem cnt_le_card (idx : α → ℕ) (m : Multiset α) (i : ℕ) : cnt idx m i ≤ m.card :=
  Multiset.card_le_card (Multiset.filter_le _ _)

/-- With an index that is injective on the elements, the count at `idx a` is the multiplicity
of `a`. -/
theorem cnt_idx {idx : α → ℕ} {m : Multiset α} {a : α}
    (hinj : ∀ b ∈ m, idx b = idx a → b = a) : cnt idx m (idx a) = m.count a := by
  unfold cnt
  rw [Multiset.count_eq_card_filter_eq]
  congr 1
  refine Multiset.filter_congr fun b hb => ⟨fun h => (hinj b hb h).symm, fun h => by rw [h]⟩

/-- **Digit `idx a` of the number of `m` is the multiplicity of `a`**, if the base exceeds the
size of `m` and the index is injective on `m ∪ {a}`. -/
theorem digit_encM {B n : ℕ} {idx : α → ℕ} {m : Multiset α} (hB : m.card < B)
    (hm : ∀ a ∈ m, idx a < n) {a : α} (ha : idx a < n)
    (hinj : ∀ b ∈ m, idx b = idx a → b = a) :
    encM B idx m / B ^ idx a % B = m.count a := by
  rw [encM_eq_enc B n idx m hm, digit_enc (fun i _ => (cnt_le_card idx m i).trans_lt hB) ha,
    cnt_idx hinj]

/-- **One anonymous move is one register update.** -/
theorem encM_move (B : ℕ) (idx : α → ℕ) {m : Multiset α} {a : α} (ha : a ∈ m) (a' : α) :
    encM B idx (m.erase a + {a'}) + B ^ idx a = encM B idx m + B ^ idx a' := by
  have h : m = a ::ₘ m.erase a := (Multiset.cons_erase ha).symm
  conv_rhs => rw [h]
  simp [encM]
  ring

end Godel

end RegRounds

end HTN
