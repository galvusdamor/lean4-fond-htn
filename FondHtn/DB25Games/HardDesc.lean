import FondHtn.DB25Games.Main
/-!
# The hardness instances as descriptions over `ℕ`

`FOND.DBG.eF` encodes the structured facts injectively into `ℕ`;
`FOND.DBG.hardDesc M m u` is the description of the hardness game, and
**`FOND.DBG.hardDesc_iff`**: for a deterministic machine, `ChosenLen (hardDesc M m u)` iff `M`
accepts `u` in space `2 ^ m`.
-/

namespace FOND

namespace DBG

open TM TM.NTM

variable {k : ℕ}

/-- Symbols as numbers. -/
def eS (s : Sym) : ℕ := bif s.isSome then (bif s.getD false then 2 else 1) else 0

/-- Entries as numbers. -/
def eC (v : CS k) : ℕ := Nat.pair (match v.1 with | none => 0 | some q => q.val + 1) (eS v.2)

/-- Claims as numbers. -/
def eV : V k → ℕ
  | none => 0
  | some v => eC v + 1

/-- **Facts as numbers.** -/
def eF : Fct k → ℕ
  | .ph j => Nat.pair 0 j
  | .ib b => Nat.pair 1 b
  | .x v => Nat.pair 2 (eV v)
  | .pl v => Nat.pair 3 (eC v)
  | .pc v => Nat.pair 4 (eC v)
  | .pr v => Nat.pair 5 (eC v)
  | .sh => Nat.pair 6 0
  | .g => Nat.pair 6 1
  | .gb => Nat.pair 6 2
  | .gj j => Nat.pair 7 j

theorem eS_inj : Function.Injective eS := by
  intro a b h
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [eS]

theorem eC_inj : Function.Injective (eC (k := k)) := by
  rintro ⟨o1, s1⟩ ⟨o2, s2⟩ h
  simp only [eC, Nat.pair_eq_pair] at h
  obtain ⟨h1, h2⟩ := h
  have := eS_inj h2
  subst this
  congr 1
  rcases o1 with _ | q1 <;> rcases o2 with _ | q2 <;> simp_all [Fin.ext_iff]

theorem eV_inj : Function.Injective (eV (k := k)) := by
  intro a b h
  rcases a with _ | a <;> rcases b with _ | b <;> simp_all [eV]
  exact eC_inj h

theorem eF_inj : Function.Injective (eF (k := k)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [eF, Nat.pair_eq_pair] <;>
    first | exact eV_inj h | exact eC_inj h

variable (M : NTM (Fin k) Sym)

/-- **The hardness description.** -/
noncomputable def hardDesc (m : ℕ) (u : List Sym) : GDesc :=
  ((acts M m u).map (mapAct eF), (init : List (Fct k)).map eF, (goal : List (Fct k)).map eF)

/-- **The reduction is correct** (deterministic machines). -/
theorem hardDesc_iff (hdet : ∀ q γ, (M.step q γ).Subsingleton) (m : ℕ) (u : List Sym) :
    ChosenLen (hardDesc M m u) ↔ M.AcceptsInSpace u (2 ^ m) := by
  rw [← chosen_iff_accepts M u m hdet]
  unfold ChosenLen EloWins hardDesc
  refine exists_congr fun r => ?_
  rw [win_map eF_inj, stOf_map eF_inj]

/-- All winning lengths are multiples of `4`, hence even. -/
theorem hardDesc_even (m : ℕ) (u : List Sym) (r : ℕ) (h : EloWins (hardDesc M m u) r) : 4 ∣ r := by
  unfold EloWins hardDesc at h
  rw [win_map eF_inj, stOf_map eF_inj, stOf_init] at h
  rw [(win_main M u m r).1 0 (Nat.two_pow_pos m) none .none trivial] at h
  rcases h with ⟨-, h⟩ | ⟨t, rfl, -⟩
  · exact absurd rfl h
  · exact ⟨t + 1, by ring⟩

end DBG

end FOND
