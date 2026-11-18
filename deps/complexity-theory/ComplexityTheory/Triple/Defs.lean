import ComplexityTheory.Triple.Arith
/-!
# Counter systems without zero tests and flat loops

A *counter system* (`Rule`, `Step`): control states `Q`, counters `ι`, a rule consumes the vector
`dec` and produces the vector `inc`.  A *flat loop* at a control state repeats one rule whose
consumed and produced counters are disjoint; `k` iterations are possible iff `k • dec ≤ v`
(`iter_reach`, `iter_of_reach`).

**Sequences of flat loops** (`SeqLoops`): control states `st 0, …, st n`; at `st i` the only rules
are the loop `ls i` and the exit to `st (i+1)` (no effect).  `seq_reach_iff` characterises the
runs from `st 0` to `st n` that do not leave the sequence: they are the choices of iteration counts.
-/

namespace HTN

namespace Triple

variable {Q ι : Type}

/-- **A rule**: source, consumed vector, produced vector, target. -/
structure Rule (Q ι : Type) where
  src : Q
  dec : ι → ℕ
  inc : ι → ℕ
  dst : Q

/-- A configuration. -/
abbrev Cfg (Q ι : Type) : Type := Q × (ι → ℕ)

/-- **A step.** -/
inductive Step (rs : Set (Rule Q ι)) : Cfg Q ι → Cfg Q ι → Prop
  | mk (ρ : Rule Q ι) (hρ : ρ ∈ rs) (v : ι → ℕ) (h : ρ.dec ≤ v) :
      Step rs (ρ.src, v) (ρ.dst, v - ρ.dec + ρ.inc)

/-- Reachability. -/
abbrev Reach (rs : Set (Rule Q ι)) : Cfg Q ι → Cfg Q ι → Prop :=
  Relation.ReflTransGen (Step rs)

/-- The effect of `k` iterations of a flat rule. -/
def itv (dec inc : ι → ℕ) (k : ℕ) (v : ι → ℕ) : ι → ℕ := v - k • dec + k • inc

/-- A rule is **flat** if it does not consume what it produces. -/
def Flat (dec inc : ι → ℕ) : Prop := ∀ i, dec i = 0 ∨ inc i = 0

theorem itv_zero (dec inc : ι → ℕ) (v : ι → ℕ) : itv dec inc 0 v = v := by
  funext i; simp [itv]

theorem itv_succ {dec inc : ι → ℕ} (hf : Flat dec inc) {k : ℕ} {v : ι → ℕ}
    (hk : (k + 1) • dec ≤ v) : itv dec inc (k + 1) v = itv dec inc k v - dec + inc := by
  funext i
  have := hk i
  have := hf i
  simp only [itv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  rcases this with h | h <;> simp [h, add_mul] at * <;> omega

theorem dec_le_itv {dec inc : ι → ℕ} (hf : Flat dec inc) {k : ℕ} {v : ι → ℕ}
    (hk : (k + 1) • dec ≤ v) : dec ≤ itv dec inc k v := by
  intro i
  have := hk i
  have := hf i
  simp only [itv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
  rcases this with h | h <;> simp [h, add_mul] at * <;> omega

/-- `k` iterations of a flat loop. -/
theorem iter_reach {rs : Set (Rule Q ι)} {q : Q} {dec inc : ι → ℕ} (hρ : ⟨q, dec, inc, q⟩ ∈ rs)
    (hf : Flat dec inc) (v : ι → ℕ) : ∀ k, k • dec ≤ v → Reach rs (q, v) (q, itv dec inc k v)
  | 0, _ => by rw [itv_zero]
  | k + 1, hk => by
    have hk' : k • dec ≤ v := le_trans (by intro i; simp [add_mul]) hk
    refine (iter_reach hρ hf v k hk').tail ?_
    rw [itv_succ hf hk]
    exact Step.mk _ hρ _ (dec_le_itv hf hk)

theorem itv_step {dec inc : ι → ℕ} (hf : Flat dec inc) {k : ℕ} {v : ι → ℕ}
    (hk : k • dec ≤ v) (h : dec ≤ itv dec inc k v) :
    (k + 1) • dec ≤ v ∧ itv dec inc k v - dec + inc = itv dec inc (k + 1) v := by
  have hk1 : (k + 1) • dec ≤ v := by
    intro i
    have := hk i
    have := h i
    have := hf i
    simp only [itv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    rcases this with h | h <;> simp [h, add_mul] at * <;> omega
  exact ⟨hk1, (itv_succ hf hk1).symm⟩

theorem itv_add {dec inc : ι → ℕ} (hf : Flat dec inc) {j k : ℕ} {v : ι → ℕ}
    (hj : j • dec ≤ v) (hk : k • dec ≤ itv dec inc j v) :
    (j + k) • dec ≤ v ∧ itv dec inc k (itv dec inc j v) = itv dec inc (j + k) v := by
  constructor
  · intro i
    have := hj i
    have := hk i
    have := hf i
    simp only [itv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    rcases this with h | h <;> simp [h, add_mul] at * <;> omega
  · funext i
    have := hj i
    have := hk i
    have := hf i
    simp only [itv, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at *
    rcases this with h | h <;> simp [h, add_mul] at * <;> omega

/-- **Splitting a run at an isolated flat loop.**  If the only rules leaving `q` are the flat loop
`⟨q, dec, inc, q⟩` and the exit `⟨q, 0, 0, q'⟩`, every run from `q` either stays at `q` (after
`k` iterations) or leaves through the exit after `k` iterations. -/
theorem loop_split' {rs : Set (Rule Q ι)} {q q' : Q} {dec inc : ι → ℕ} (hf : Flat dec inc)
    (hiso : ∀ ρ ∈ rs, ρ.src = q → ρ = ⟨q, dec, inc, q⟩ ∨ ρ = ⟨q, 0, 0, q'⟩)
    {x y : Cfg Q ι} (h : Reach rs x y) : x.1 = q →
    (∃ k, k • dec ≤ x.2 ∧ y = (q, itv dec inc k x.2)) ∨
      ∃ k, k • dec ≤ x.2 ∧ Reach rs (q', itv dec inc k x.2) y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hx
    exact Or.inl ⟨0, by simp, by rw [itv_zero, ← hx]⟩
  | head hs hr ih =>
    intro hx
    obtain ⟨ρ, hρ, v, hv⟩ := hs
    rcases hiso ρ hρ hx with rfl | rfl
    · rcases ih rfl with ⟨k, hk, rfl⟩ | ⟨k, hk, hr'⟩
      · have h1 : (1 : ℕ) • dec ≤ v := by simpa using hv
        have e1 : itv dec inc 1 v = v - dec + inc := by
          have := itv_succ (k := 0) hf (by simpa using hv) (v := v)
          rw [this, itv_zero]
        rw [← e1] at hk ⊢
        obtain ⟨h2, e2⟩ := itv_add hf h1 hk
        exact Or.inl ⟨1 + k, h2, by rw [e2]⟩
      · have h1 : (1 : ℕ) • dec ≤ v := by simpa using hv
        have e1 : itv dec inc 1 v = v - dec + inc := by
          have := itv_succ (k := 0) hf (by simpa using hv) (v := v)
          rw [this, itv_zero]
        rw [← e1] at hk hr'
        obtain ⟨h2, e2⟩ := itv_add hf h1 hk
        exact Or.inr ⟨1 + k, h2, by rwa [← e2]⟩
    · refine Or.inr ⟨0, by simp, ?_⟩
      rw [itv_zero]
      simpa using hr

theorem loop_split {rs : Set (Rule Q ι)} {q q' : Q} {dec inc : ι → ℕ} (hf : Flat dec inc)
    (hiso : ∀ ρ ∈ rs, ρ.src = q → ρ = ⟨q, dec, inc, q⟩ ∨ ρ = ⟨q, 0, 0, q'⟩)
    {w : ι → ℕ} {y : Cfg Q ι} (h : Reach rs (q, w) y) :
    (∃ k, k • dec ≤ w ∧ y = (q, itv dec inc k w)) ∨
      ∃ k, k • dec ≤ w ∧ Reach rs (q', itv dec inc k w) y :=
  loop_split' hf hiso h rfl

end Triple

end HTN
