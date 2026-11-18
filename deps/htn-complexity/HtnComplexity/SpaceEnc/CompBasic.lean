import HtnComplexity.SpaceEnc.CompGen
import HtnComplexity.SpaceEnc.SoundLemmas
/-!
# Completeness of the encoding: the planned run

From an accepting run of the machine in space `2 ^ m` (`HTN.SpaceEnc.exists_run`) the
completeness proof plans every word: the chain data `HTN.SpaceEnc.cdOf R k c` of position `c`
in round `k`, the head move `HTN.SpaceEnc.hOf R k`, the block `HTN.SpaceEnc.blk R k` of round
`k`, the future blocks `HTN.SpaceEnc.futB R p k` of the loop `p` and the finish word.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type}

/-! ### Runs as sequences -/

/-- The configuration after a transition. -/
def applyTr (c : Config Q Γ) (t : Q × Γ × Move) : Config Q Γ :=
  ⟨t.1, t.2.2.apply c.head, Function.update c.tape c.head t.2.1⟩

/-- **A run of the machine in space `S`, as a sequence**: `r` steps, configurations `cf`,
transitions `tr`. -/
structure RunSeq (N : NTM Q Γ) (S : ℕ) (c₀ : Config Q Γ) where
  /-- The number of steps. -/
  r : ℕ
  /-- The configurations. -/
  cf : ℕ → Config Q Γ
  /-- The transitions. -/
  tr : ℕ → Q × Γ × Move
  cf_zero : cf 0 = c₀
  tr_mem : ∀ k < r, tr k ∈ N.step (cf k).state ((cf k).tape (cf k).head)
  cf_succ : ∀ k < r, cf (k + 1) = applyTr (cf k) (tr k)
  head_lt : ∀ k ≤ r, (cf k).head < S

theorem exists_runSeq {N : NTM Q Γ} {S : ℕ} : ∀ (n : ℕ) (c₀ c : Config Q Γ),
    N.ReachesSpace S n c₀ c → ∃ R : RunSeq N S c₀, R.r = n ∧ R.cf n = c
  | 0, c₀, c, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨⟨0, fun _ => c₀, fun _ => (c₀.state, c₀.tape 0, Move.stay), rfl,
      fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
      fun k _ => h⟩, rfl, rfl⟩
  | n + 1, c₀, c, h => by
    obtain ⟨h0, d, ⟨q', γ', μ, hmem, rfl⟩, hd⟩ := h
    obtain ⟨R, hr, hcf⟩ := exists_runSeq n _ c hd
    refine ⟨⟨n + 1, fun k => if k = 0 then c₀ else R.cf (k - 1),
      fun k => if k = 0 then (q', γ', μ) else R.tr (k - 1), rfl, ?_, ?_, ?_⟩, rfl, ?_⟩
    · intro k hk
      rcases k with _ | k
      · exact hmem
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact R.tr_mem k (by omega)
    · intro k hk
      rcases k with _ | k
      · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.sub_self, R.cf_zero]
        rfl
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact R.cf_succ k (by omega)
    · intro k hk
      rcases k with _ | k
      · exact h0
      · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact R.head_lt k (by omega)
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      exact hcf

/-! ### Lowest bits -/

/-- The lowest clear bit of a number. -/
def lzb (c : ℕ) : ℕ := Nat.find (⟨c, Nat.testBit_lt_two_pow (Nat.lt_two_pow_self)⟩ :
  ∃ j, c.testBit j = false)

theorem lzb_spec (c : ℕ) : c.testBit (lzb c) = false :=
  Nat.find_spec (⟨c, Nat.testBit_lt_two_pow (Nat.lt_two_pow_self)⟩ : ∃ j, c.testBit j = false)

theorem lzb_min {c j : ℕ} (hj : j < lzb c) : c.testBit j = true := by
  have := Nat.find_min (⟨c, Nat.testBit_lt_two_pow (Nat.lt_two_pow_self)⟩ :
    ∃ j, c.testBit j = false) hj
  simpa using this

theorem lzb_lt {m c : ℕ} (hc : c < 2 ^ m) (hne : c + 1 ≠ 2 ^ m) : lzb c < m := by
  by_contra h
  have := eq_of_all_testBit hc fun j hj => lzb_min (by omega)
  omega

/-- The lowest set bit of a non-zero number. -/
noncomputable def lob (c : ℕ) : ℕ :=
  if h : c = 0 then 0 else Nat.find (Nat.exists_testBit_of_ne_zero h)

theorem lob_spec {c : ℕ} (h : c ≠ 0) : c.testBit (lob c) = true := by
  unfold lob
  rw [dif_neg h]
  exact Nat.find_spec (Nat.exists_testBit_of_ne_zero h)

theorem lob_min {c j : ℕ} (h : c ≠ 0) (hj : j < lob c) : c.testBit j = false := by
  unfold lob at hj
  rw [dif_neg h] at hj
  have := Nat.find_min (Nat.exists_testBit_of_ne_zero h) hj
  simpa using this

theorem lob_lt {m c : ℕ} (hc : c < 2 ^ m) (h : c ≠ 0) : lob c < m := by
  by_contra h'
  exact h (eq_zero_of_all_testBit hc fun j hj => lob_min h (by omega))

/-! ### The plan -/

/-- The writer of round `k`: the loop `A` (`true`) in the even rounds. -/
def parR (k : ℕ) : Bool := decide (k % 2 = 0)

theorem parR_succ (k : ℕ) : parR (k + 1) = !parR k := by
  unfold parR
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have : (k + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (k + 1) % 2 = 0 := by omega
    simp [h, this]

section Plan

variable {N : NTM Q Γ} {S : ℕ} {c₀ : Config Q Γ} (R : RunSeq N S c₀) (m n' : ℕ) (w : List Bool)

/-- **The planned chain data** of position `c` in round `k`. -/
def cdOf (k c : ℕ) : CD Q Γ where
  x := bitsOf c
  e := fun i => (c.testBit i == (R.cf k).head.testBit i)
  rd := if k = 0 then (if c < n' then [.ri c (w.getD c false)] else [.rblank]) else []
  core := if c = (R.cf k).head then
      .tr (parR k) (R.cf k).state ((R.cf k).tape c) (R.tr k).1 (R.tr k).2.1 (R.tr k).2.2
    else .cp (parR k) ((R.cf k).tape c)
  incw := if c + 1 = 2 ^ m then .wrap (parR k) else .inc (parR k) (lzb c)
  val := if c = (R.cf k).head then (R.tr k).2.1 else (R.cf k).tape c

/-- **The planned head move** of round `k`. -/
noncomputable def hOf (k : ℕ) : Act Q Γ :=
  match (R.tr k).2.2 with
  | .right => .hinc (parR k) (lzb (R.cf k).head)
  | .left => if (R.cf k).head = 0 then .hdec0 (parR k) else .hdec (parR k) (lob (R.cf k).head)
  | .stay => .hstay (parR k)

/-- **The planned block** of round `k`: the chain words of the positions in order, then the
head move. -/
noncomputable def blk (k : ℕ) : List (List (Act Q Γ)) :=
  (List.range (2 ^ m)).map (fun c => chainW m (parR k) (cdOf R m n' w k c)) ++ [[hOf R k]]

/-- **The future blocks of the loop `p`** from round `k` on. -/
noncomputable def futB (p : Bool) (k : ℕ) : List (List (List (Act Q Γ))) :=
  ((List.range' k (R.r - k)).filter fun k' => parR k' == p).map (blk R m n' w)

/-- **The planned finish word**: `fin` and one drain per stored tail. -/
def phiOf : List (Act Q Γ) :=
  .fin (R.cf R.r).state :: List.replicate (if R.r = 0 then 0 else 2 ^ m) .drn

theorem futB_of_lt {p : Bool} {k : ℕ} (hk : k < R.r) :
    futB R m n' w p k = if parR k = p then blk R m n' w k :: futB R m n' w p (k + 1)
      else futB R m n' w p (k + 1) := by
  unfold futB
  rw [show R.r - k = (R.r - (k + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
  by_cases h : parR k = p <;> simp [h]

theorem futB_of_ge {p : Bool} {k : ℕ} (hk : R.r ≤ k) : futB R m n' w p k = [] := by
  unfold futB
  rw [show R.r - k = 0 by omega]
  rfl

theorem futB_self {k : ℕ} (hk : k < R.r) :
    futB R m n' w (parR k) k = blk R m n' w k :: futB R m n' w (parR k) (k + 1) := by
  rw [futB_of_lt R m n' w hk, if_pos rfl]

theorem futB_other {p : Bool} {k : ℕ} (hp : parR k ≠ p) :
    futB R m n' w p k = futB R m n' w p (k + 1) := by
  rcases Nat.lt_or_ge k R.r with hk | hk
  · rw [futB_of_lt R m n' w hk, if_neg hp]
  · rw [futB_of_ge R m n' w hk, futB_of_ge R m n' w (by omega)]

theorem msOf_blk (k : ℕ) :
    msOf (blk R m n' w k) = ((List.range' 0 (2 ^ m)).map
      (fun c => chainW m (parR k) (cdOf R m n' w k c)) : Multiset (List (Act Q Γ))) +
        {[hOf R k]} := by
  unfold blk msOf
  rw [← Multiset.coe_add, Multiset.filter_add, List.range_eq_range']
  congr 1
  · rw [Multiset.filter_eq_self.2]
    intro v hv
    simp only [Multiset.mem_coe, List.mem_map] at hv
    obtain ⟨c, -, rfl⟩ := hv
    exact chainW_ne_nil _ _ _

end Plan

end SpaceEnc

end HTN
