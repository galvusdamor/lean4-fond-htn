import HtnComplexity.SpaceEnc.SoundCore
/-!
# Soundness of the encoding

**`HTN.SpaceEnc.accepts_of_solvable`**: if the planning problem `HTN.SpaceEnc.prob` of the
input `w` is solvable, the machine accepts `w` (the input symbols being `ι`) in space `2 ^ m`.

The proof reads an executable refinement action by action, keeping the invariant
`HTN.SpaceEnc.Inv` (`inv_step`, assembled from the phase steps); the finish word is never
consumed before `fin`, and `fin` can only fire at the start of a round in an accepting state.
-/

namespace HTN

namespace SpaceEnc

open TM

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] {m n' : ℕ}
  {ι : Bool → Γ} {N : NTM Q Γ} {w : List Bool}

/-- **One step of the invariant.** -/
theorem inv_step (hn' : n' = w.length) {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))}
    {φ : List (Act Q Γ)} {a : Act Q Γ} {z : List (Act Q Γ)}
    (hI : Inv m n' ι N w fs bs φ) (hG : G bs φ (a :: z))
    (happ : (am m n' ι N).Applicable a (enc m w fs)) :
    N.AcceptsInSpace (w.map ι) (2 ^ m) ∨
      ∃ fs' bs', (am m n' ι N).transition a (enc m w fs) = enc m w fs' ∧ G bs' φ z ∧
        Inv m n' ι N w fs' bs' φ := by
  obtain ⟨p, cfg, first, nv, ⟨c, h⟩ | ⟨c, k, h⟩ | ⟨hf, c, j, h⟩ | ⟨c, h⟩ | ⟨c, h⟩ | h⟩ := hI
  · rcases step_P0 h hG happ with h' | ⟨bs', htr, hG', h'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨_, bs', htr, hG', p, cfg, first, nv, Or.inr (Or.inl ⟨c, 0, h'⟩)⟩
  · have hkm : k ≤ m := h.2.2.2.1
    rcases Nat.lt_or_ge k m with hk | hk
    · obtain ⟨fs', bs', htr, hG', h'⟩ := step_PW hk h hG happ
      exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv, Or.inr (Or.inl ⟨c, k + 1, h'⟩)⟩
    · have hk' : k = m := by omega
      subst hk'
      obtain ⟨fs', bs', htr, hG', ⟨hf, h'⟩ | h'⟩ := step_PWm hn' h hG happ
      · exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv,
          Or.inr (Or.inr (Or.inl ⟨hf, c, 0, h'⟩))⟩
      · exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv,
          Or.inr (Or.inr (Or.inr (Or.inl ⟨c, h'⟩)))⟩
  · subst hf
    have hjm : j ≤ m := h.2.2.2.1
    rcases Nat.lt_or_ge j m with hj | hj
    · obtain ⟨fs', bs', htr, hG', h'⟩ := step_PR hj h hG happ
      exact Or.inr ⟨fs', bs', htr, hG', p, cfg, false, nv,
        Or.inr (Or.inr (Or.inl ⟨rfl, c, j + 1, h'⟩))⟩
    · have hj' : j = m := by omega
      subst hj'
      obtain ⟨fs', bs', nv', htr, hG', h'⟩ := step_PC (invPC_of_invPR h) hG happ
      exact Or.inr ⟨fs', bs', htr, hG', p, cfg, false, nv',
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, h'⟩))))⟩
  · obtain ⟨fs', bs', nv', htr, hG', h'⟩ := step_PC h hG happ
    exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv',
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, h'⟩))))⟩
  · obtain ⟨fs', bs', htr, hG', h' | h'⟩ := step_PI h hG happ
    · exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv, Or.inl ⟨c + 1, h'⟩⟩
    · exact Or.inr ⟨fs', bs', htr, hG', p, cfg, first, nv,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))⟩
  · obtain ⟨fs', bs', cfg', htr, hG', h'⟩ := step_PE h hG happ
    exact Or.inr ⟨fs', bs', htr, hG', !p, cfg', false, cfg'.tape, Or.inl ⟨0, h'⟩⟩

omit [DecidableEq Q] [DecidableEq Γ] in
/-- The invariant keeps the finish word unconsumed. -/
theorem Inv.finW {fs : FS Q Γ} {bs : Bool → List (List (List (Act Q Γ)))} {φ : List (Act Q Γ)}
    (hI : Inv m n' ι N w fs bs φ) : FinW N φ := by
  obtain ⟨p, cfg, first, nv, ⟨c, h⟩ | ⟨c, k, h⟩ | ⟨hf, c, j, h⟩ | ⟨c, h⟩ | ⟨c, h⟩ | h⟩ := hI
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.1

/-- **An executable continuation from an invariant state accepts.** -/
theorem accepts_of_inv (hn' : n' = w.length) : ∀ (z : List (Act Q Γ)) (fs : FS Q Γ)
    (bs : Bool → List (List (List (Act Q Γ)))) (φ : List (Act Q Γ)),
    Inv m n' ι N w fs bs φ → G bs φ z → (am m n' ι N).SeqApplicable z (enc m w fs) →
    N.AcceptsInSpace (w.map ι) (2 ^ m)
  | [], fs, bs, φ, hI, hG, _ => by
    obtain ⟨q, -, rest, h⟩ := hI.finW
    rw [g_nil hG] at h
    simp at h
  | a :: z, fs, bs, φ, hI, hG, hseq => by
    rcases inv_step hn' hI hG hseq.1 with h | ⟨fs', bs', htr, hG', hI'⟩
    · exact h
    · have hseq' := hseq.2
      rw [htr] at hseq'
      exact accepts_of_inv hn' z fs' bs' φ hI' hG' hseq'

omit [Fintype Q] [DecidableEq Q] [DecidableEq Γ] in
/-- The state after `boot`. -/
theorem trans_boot :
    (am m n' ι N).transition .boot {f | f ∈ (Fct.boot0 : Fct Q Γ) :: inpL w} =
      enc m w ⟨0, 0, 0, N.init, true, true, 0, none, none, true⟩ := by
  ext f
  rw [mem_transition]
  cases f with
  | inp i b =>
    simp only [Set.mem_setOf_eq, List.mem_cons, inpL, List.mem_map, List.mem_range, delL, addL,
      mem_enc, Holds]
    constructor
    · rintro (⟨h1 | ⟨i', hi', h2⟩, -⟩ | h3)
      · cases h1
      · cases h2; exact ⟨hi', rfl⟩
      · simp at h3
    · rintro ⟨h1, rfl⟩
      exact Or.inl ⟨Or.inr ⟨i, h1, rfl⟩, by simp⟩
  | cb k x => simp [delL, addL, inpL, Holds, eq_comm]
  | hb k x => simp [delL, addL, inpL, Holds, eq_comm]
  | _ => simp [delL, addL, inpL, Holds, eq_comm]

/-- **Soundness**: a solvable encoding means acceptance in space `2 ^ m`. -/
theorem accepts_of_solvable (hn' : n' = w.length) (h : (prob m n' ι N w).Solvable) :
    N.AcceptsInSpace (w.map ι) (2 ^ m) := by
  classical
  obtain ⟨as, hy, happ, -⟩ := Problem.solvable_iff_netYield.1 h
  obtain ⟨z', bA, bB, φ, rfl, hgen, hA, hB, hφ⟩ := netYield_prob_gen ι w hy
  obtain ⟨-, hseq⟩ := happ
  have htr : (prob m n' ι N w).transition .boot (prob m n' ι N w).init =
      enc m w ⟨0, 0, 0, N.init, true, true, 0, none, none, true⟩ := trans_boot
  rw [htr] at hseq
  refine accepts_of_inv hn' z' _ (fun q => if q then bA else bB) φ ?_ hgen hseq
  refine ⟨true, N.initConfig (w.map ι), true, fun _ => N.blank, Or.inl ⟨0, ?_⟩⟩
  refine ⟨⟨⟨0, rfl, Nat.two_pow_pos m⟩, fun _ => ⟨rfl, rfl⟩⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl,
    Nat.two_pow_pos m, fun _ => by simp, fun c' hc' => by omega,
    ⟨fun h' => by omega, fun _ => ⟨rfl, rfl⟩⟩, hφ, fun _ => ⟨[], bA, rfl, by simp [AllE], hA⟩,
    fun h' => by omega, fun _ => hB, fun h' => by simp at h'⟩

end SpaceEnc

end HTN
