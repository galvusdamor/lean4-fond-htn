import ComplexityTheory.RegRounds.Godel
import ComplexityTheory.RegRounds.Anon
/-!
# Register runs are anonymous runs

The native regime RA (PROOFIDEAS §15.4) runs the anonymous thread pool on a single number
`X = encM B idx m` (`Godel.lean`).  A **register step** picks a (class, state) pair `a = (κ,s)`
whose digit is non-zero and a local step `s → s'` (with its change of the shared state), and
replaces `X` by `X - B^(idx a) + B^(idx (κ,s'))`.

* **`HTN.RegRounds.mRun_of_rRun`** — every register run from `encM m` is the image of an
  anonymous run (`Anon.MStep`) from `m`, with the same shared states;
* **`HTN.RegRounds.rRun_of_mRun`** — conversely.

Hypotheses: every pair that can occur lies in a set `U` on which `idx` is injective, and the
base exceeds the number of units.  So the register program of RA is sound and complete for the
rounds (`round_iff_mRun`, `Thr.lean`).
-/

namespace HTN

namespace RegRounds

open Godel

variable {F σ κT : Type*} [DecidableEq σ] [DecidableEq κT]

/-- **A register step.** -/
def RStep (ls : F → σ → F → σ → Prop) (B : ℕ) (idx : κT × σ → ℕ) (U : Set (κT × σ))
    (c c' : F × ℕ) : Prop :=
  ∃ (k : κT) (s s' : σ), (k, s) ∈ U ∧ (k, s') ∈ U ∧ 1 ≤ c.2 / B ^ idx (k, s) % B ∧
    ls c.1 s c'.1 s' ∧ c'.2 + B ^ idx (k, s) = c.2 + B ^ idx (k, s')

/-- The hypotheses: `idx` injective on `U`, all units in `U`, the base above the number of
units. -/
structure RegOK (B : ℕ) (idx : κT × σ → ℕ) (U : Set (κT × σ)) (m : Multiset (κT × σ)) : Prop where
  inj : ∀ a ∈ U, ∀ b ∈ U, idx a = idx b → a = b
  sub : ∀ a ∈ m, a ∈ U
  base : m.card < B

theorem regOK_move {B : ℕ} {idx : κT × σ → ℕ} {U : Set (κT × σ)} {m : Multiset (κT × σ)}
    (h : RegOK B idx U m) {a a' : κT × σ} (ha : a ∈ m) (ha' : a' ∈ U) :
    RegOK B idx U (m.erase a + {a'}) where
  inj := h.inj
  sub := by
    intro b hb
    rcases Multiset.mem_add.1 hb with hb | hb
    · exact h.sub b (Multiset.mem_of_mem_erase hb)
    · rw [Multiset.mem_singleton.1 hb]; exact ha'
  base := by
    have := Multiset.card_erase_of_mem ha
    have h1 : 0 < m.card := Multiset.card_pos_iff_exists_mem.2 ⟨a, ha⟩
    simp only [Multiset.card_add, Multiset.card_singleton, this, Nat.pred_eq_sub_one]
    have := h.base
    omega

theorem digit_pos_iff {B : ℕ} {idx : κT × σ → ℕ} {U : Set (κT × σ)} {m : Multiset (κT × σ)}
    (h : RegOK B idx U m) {a : κT × σ} (ha : a ∈ U) :
    1 ≤ encM B idx m / B ^ idx a % B ↔ a ∈ m := by
  -- all indices below a common bound
  set n := (m.map idx).sup ⊔ idx a + 1 with hn
  have hm : ∀ b ∈ m, idx b < n := by
    intro b hb
    have : idx b ≤ (m.map idx).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hb)
    omega
  have hinj : ∀ b ∈ m, idx b = idx a → b = a := fun b hb hba => h.inj b (h.sub b hb) a ha hba
  rw [digit_encM h.base hm (by omega) hinj]
  exact ⟨fun h1 => Multiset.count_pos.1 (by omega), fun h1 => Multiset.count_pos.2 h1⟩

/-- **Register runs come from anonymous runs.** -/
theorem mRun_of_rRun (ls : F → σ → F → σ → Prop) (B : ℕ) (idx : κT × σ → ℕ) (U : Set (κT × σ))
    {c c' : F × ℕ} (h : Relation.ReflTransGen (RStep ls B idx U) c c') :
    ∀ m : Multiset (κT × σ), RegOK B idx U m → c.2 = encM B idx m →
      ∃ m', Relation.ReflTransGen (Anon.MStep ls) ⟨c.1, m⟩ ⟨c'.1, m'⟩ ∧ RegOK B idx U m' ∧
        c'.2 = encM B idx m' := by
  induction h with
  | refl => exact fun m hm hc => ⟨m, .refl, hm, hc⟩
  | @tail b b' _ hstep ih =>
    intro m hm hc
    obtain ⟨m₁, hr, hm₁, hb⟩ := ih m hm hc
    obtain ⟨k, s, s', hs, hs', hdig, hls, hX⟩ := hstep
    rw [hb] at hdig
    have hmem : (k, s) ∈ m₁ := (digit_pos_iff hm₁ hs).1 hdig
    refine ⟨m₁.erase (k, s) + {(k, s')}, hr.tail (Anon.MStep.mk hmem hls), regOK_move hm₁ hmem hs', ?_⟩
    have hmv := encM_move B idx hmem (k, s')
    rw [hb] at hX
    omega

/-- **Anonymous runs give register runs.** -/
theorem rRun_of_mRun (ls : F → σ → F → σ → Prop) (B : ℕ) (idx : κT × σ → ℕ) (U : Set (κT × σ))
    (hU : ∀ f s f' s' (k : κT), (k, s) ∈ U → ls f s f' s' → (k, s') ∈ U)
    {x x' : Anon.MCfg F σ κT} (h : Relation.ReflTransGen (Anon.MStep ls) x x') (hx : RegOK B idx U x.ms) :
    Relation.ReflTransGen (RStep ls B idx U) (x.sh, encM B idx x.ms) (x'.sh, encM B idx x'.ms) ∧
      RegOK B idx U x'.ms := by
  induction h with
  | refl => exact ⟨.refl, hx⟩
  | @tail b b' _ hstep ih =>
    obtain ⟨hr, hb⟩ := ih
    cases hstep with
    | @mk k s f' s' hm hls =>
      have hs : (k, s) ∈ U := hb.sub _ hm
      have hs' : (k, s') ∈ U := hU _ _ _ _ k hs hls
      refine ⟨hr.tail ⟨k, s, s', hs, hs', (digit_pos_iff hb hs).2 hm, hls, ?_⟩,
        regOK_move hb hm hs'⟩
      exact encM_move B idx hm (k, s')

end RegRounds

end HTN
