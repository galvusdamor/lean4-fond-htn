import HtnComplexity.SpaceEnc.CompDrain
/-!
# Completeness of the encoding: the executable plan

The invariant `HTN.SpaceEnc.CInv` of the planned run always allows one more executable step
until everything is consumed (`HTN.SpaceEnc.cinv_progress`); hence the planned words of an
accepting run have an executable interleaving (`HTN.SpaceEnc.exists_exec_plan`).
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {N : NTM Q Γ}
  {m n' : ℕ} {ι : Bool → Γ} {w : List Bool} (R : RunSeq N (2 ^ m) (N.initConfig (w.map ι)))

/-- **Progress**: the invariant of the planned run allows a step until everything is
consumed. -/
theorem cinv_progress (hn' : n' = w.length) (wd : World (Fct Q Γ) (Act Q Γ))
    (h : CInv R m n' w wd) :
    wd.Final ∨ ∃ wd', WStep (am m n' ι N) wd wd' ∧ CInv R m n' w wd' := by
  rcases h with ⟨k, c, h⟩ | ⟨k, c, j, h⟩ | ⟨k, c, j, h⟩ | ⟨k, c, h⟩ | ⟨k, c, h⟩ | ⟨k, h⟩ | h |
    ⟨S, h⟩ | ⟨S, c, j, h⟩
  · obtain ⟨wd', hs, h'⟩ := step_CP0 (ι := ι) R h
    exact Or.inr ⟨wd', hs, Or.inr (Or.inl ⟨k, c, 0, h'⟩)⟩
  · rcases Nat.lt_or_ge j m with hj | hj
    · obtain ⟨wd', hs, h'⟩ := step_CPW_lt (ι := ι) R h hj
      exact Or.inr ⟨wd', hs, Or.inr (Or.inl ⟨k, c, j + 1, h'⟩)⟩
    · have hjm : j = m := le_antisymm h.2.2.1 hj
      subst hjm
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨wd', hs, h'⟩ := step_CPW_rd (ι := ι) R hn' h
        exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inl ⟨0, c, h'⟩)))⟩
      · obtain ⟨wd', hs, h'⟩ := step_CPW_rv (ι := ι) R h hk0
        exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inl ⟨k, c, 0, h'⟩))⟩
  · rcases Nat.lt_or_ge j m with hj | hj
    · obtain ⟨wd', hs, h'⟩ := step_CPR_lt (ι := ι) R h hj
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inl ⟨k, c, j + 1, h'⟩))⟩
    · have hjm : j = m := le_antisymm h.2.2.2.1 hj
      subst hjm
      obtain ⟨wd', hs, h'⟩ := step_CPC (ι := ι) R (cpc_of_cpr R h)
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, c, h'⟩))))⟩
  · obtain ⟨wd', hs, h'⟩ := step_CPC (ι := ι) R h
    exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, c, h'⟩))))⟩
  · by_cases hcW : c + 1 = 2 ^ m
    · obtain ⟨wd', hs, h'⟩ := step_CPI_wrap (ι := ι) R h hcW
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, h'⟩)))))⟩
    · obtain ⟨wd', hs, h'⟩ := step_CPI_inc (ι := ι) R h hcW
      exact Or.inr ⟨wd', hs, Or.inl ⟨k, c + 1, h'⟩⟩
  · obtain ⟨wd', hs, h' | h'⟩ := step_CPE (ι := ι) R h
    · exact Or.inr ⟨wd', hs, Or.inl ⟨k + 1, 0, h'⟩⟩
    · exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))⟩
  · obtain ⟨wd', hs, S, h'⟩ := step_CFin (n' := n') (ι := ι) R h
    exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨S, h'⟩)))))))⟩
  · rcases S with _ | ⟨c, S⟩
    · exact Or.inl (final_CD1 R h)
    · obtain ⟨wd', hs, h'⟩ := step_CD1 (n' := n') (ι := ι) R h
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨S, c, 0, h'⟩)))))))⟩
  · rcases Nat.lt_or_ge j m with hj | hj
    · obtain ⟨wd', hs, h'⟩ := step_CD2_lt (n' := n') (ι := ι) R h hj
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr ⟨S, c, j + 1, h'⟩)))))))⟩
    · have hjm : j = m := le_antisymm h.2.1 hj
      subst hjm
      obtain ⟨wd', hs, h'⟩ := step_CD2_top (n' := n') (ι := ι) R h
      exact Or.inr ⟨wd', hs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨S, h'⟩)))))))⟩

/-- The record of the state after `boot`. -/
def fs0 (N : NTM Q Γ) : FS Q Γ := ⟨0, 0, 0, N.init, true, true, 0, none, none, true⟩

/-- The world after `boot`: all planned blocks and the planned finish word remain. -/
noncomputable def world0 : World (Fct Q Γ) (Act Q Γ) :=
  ⟨enc m w (fs0 N), fun q => futB R m n' w q 0, phiOf R m⟩

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- The world after `boot` satisfies the invariant. -/
theorem cinv_world0 : CInv R m n' w (world0 (n' := n') R) := by
  have hcf := R.cf_zero
  have hp0 : parR 0 = true := rfl
  by_cases hr : R.r = 0
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨fs0 N, rfl, rfl, rfl,
      by rw [hr, hcf]; rfl, ?_, fun _ => ?_, fun h => absurd hr h, rfl⟩))))))
    · show AllE (futB R m n' w _ 0)
      rw [futB_of_ge R m n' w (by omega)]; simp [AllE]
    · show AllE (futB R m n' w _ 0)
      rw [futB_of_ge R m n' w (by omega)]; simp [AllE]
  · have hk : 0 < R.r := Nat.pos_of_ne_zero hr
    refine Or.inl ⟨0, 0, hk, Nat.two_pow_pos m, fs0 N, rfl,
      ⟨rfl, rfl, by rw [hcf]; rfl, by rw [hp0]; rfl, rfl, fun h => absurd h (Nat.not_lt_zero _),
        fun _ => ⟨by rw [hcf]; rfl, rfl⟩⟩, rfl, fun _ => by simp [fs0], ?_, ?_, rfl⟩
    · refine ⟨[], blk R m n' w 0, ?_, by simp [AllE], msOf_blk' R m n' w 0 _⟩
      show futB R m n' w (parR 0) 0 = _
      rw [futB_self R m n' w hk]; rfl
    · refine ⟨[], futB R m n' w (!parR 0) 0, rfl, by simp [AllE],
        fun _ => futB_other R m n' w (by simp [hp0]), fun h => absurd rfl h⟩

/-- **The planned words of an accepting run have an executable interleaving.** -/
theorem exists_exec_plan (hn' : n' = w.length) :
    ∃ z, G (fun q => futB R m n' w q 0) (phiOf R m) z ∧
      (am m n' ι N).SeqApplicable z (enc m w (fs0 N)) :=
  exists_plan (am m n' ι N) (CInv R m n' w) (cinv_progress R hn') _ (cinv_world0 R)

end SpaceEnc

end HTN
