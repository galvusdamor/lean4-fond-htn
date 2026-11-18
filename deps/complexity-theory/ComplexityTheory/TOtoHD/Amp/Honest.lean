import ComplexityTheory.TOtoHD.Amp.Pot
/-!
# The amplifier: every accepting run is honest

By induction on the level `K`: if every step of an accepting run is honest below `K`, the
invariant `Inv K` holds along the run (`inv_step`), so the potential `Psi K` never decreases
(`psi_step`); it is `0` at the start and at the end, hence constant, hence every step is honest at
level `K` as well.
-/

namespace HTN

namespace Amp

variable {Q Φ : Type} [DecidableEq Φ]

/-- The initial configuration. -/
def ainit (s0 : Finset Φ) : ACfg Q Φ := (.start, s0, fun _ => 0)

theorem inv_init {P : CM Q Φ} {L K : ℕ} {s0 : Finset Φ} : Inv P L K s0 (ainit s0) := by
  refine ⟨trivial, fun _ => rfl, fun k _ r _ => ?_, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩
  simp [ainit, E]

theorem psi_init {L K : ℕ} {s0 : Finset Φ} : Psi L K (ainit (Q := Q) s0) = 0 := by
  simp [Psi, ainit, owed, Rz, spawnOf]

theorem psi_done {L K : ℕ} {S : Finset Φ} : Psi L K ((.done, S, fun _ => 0) : ACfg Q Φ) = 0 := by
  simp [Psi, owed, Rz, spawnOf]

/-- **Every accepting run is honest at every level `< K`** (for `K ≤ L + 1`). -/
theorem honest_lt {P : CM Q Φ} {L : ℕ} {s0 S : Finset Φ}
    (h : Relation.ReflTransGen (AStep P L) (ainit s0) (.done, S, fun _ => 0)) :
    ∀ K ≤ L + 1, Relation.ReflTransGen (fun x y => AStep P L x y ∧ ∀ k < K, Hon L k x y)
      (ainit s0) (.done, S, fun _ => 0) := by
  intro K
  induction K with
  | zero => intro _; exact rtg_mono_and h (fun _ _ _ k hk => absurd hk (Nat.not_lt_zero k))
  | succ K ih =>
    intro hK
    have hrun := ih (by omega)
    have hKL : K ≤ L := by omega
    obtain ⟨-, -, hrun'⟩ := rtg_pot (I := Inv P L K s0) (f := Psi L K)
      (fun x y hxy hI => ⟨inv_step hKL hI hxy.2 hxy.1, (psi_step hKL hI hxy.2 hxy.1).1⟩)
      hrun inv_init
    have := hrun' (by rw [psi_init, psi_done])
    refine Relation.ReflTransGen.mono (fun x y hxy => ⟨hxy.1.1, fun k hk => ?_⟩) this
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact hxy.1.2 k hk
    · exact (psi_step hKL hxy.2.1 hxy.1.2 hxy.1.1).2 hxy.2.2

/-- **An accepting run consists of honest steps between configurations satisfying the full
invariant.** -/
theorem honest_run {P : CM Q Φ} {L : ℕ} {s0 S : Finset Φ}
    (h : Relation.ReflTransGen (AStep P L) (ainit s0) (.done, S, fun _ => 0)) :
    Relation.ReflTransGen (fun x y => AStep P L x y ∧ (∀ k ≤ L, Hon L k x y) ∧
      Inv P L L s0 x ∧ Inv P L L s0 y) (ainit s0) (.done, S, fun _ => 0) := by
  have hrun := honest_lt h (L + 1) le_rfl
  have key : ∀ y, Relation.ReflTransGen (fun x y => AStep P L x y ∧ ∀ k < L + 1, Hon L k x y)
      (ainit s0) y → Inv P L L s0 y ∧ Relation.ReflTransGen (fun x y => AStep P L x y ∧
        (∀ k ≤ L, Hon L k x y) ∧ Inv P L L s0 x ∧ Inv P L L s0 y) (ainit s0) y := by
    intro y hy
    induction hy with
    | refl => exact ⟨inv_init, .refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hIb, hr⟩ := ih
      have hIc := inv_step le_rfl hIb (fun k hk => hbc.2 k (by omega)) hbc.1
      exact ⟨hIc, .tail hr ⟨hbc.1, fun k hk => hbc.2 k (by omega), hIb, hIc⟩⟩
  exact (key _ hrun).2

end Amp

end HTN
