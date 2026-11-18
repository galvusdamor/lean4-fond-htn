import HtnComplexity.SpaceEnc.Render
/-!
# The rendered encoding is tail recursive and rooted

* `HTN.SpaceEnc.isTailRec_domDesc_rend` — the described domain is tail recursive, by the rank
  `HTN.SpaceEnc.rkC`: every compound subtask decreases it, except the recursive last cells of
  the loops `Loop p → [Block p, Loop p]` and `Drain → [drn, Drain]`;
* `HTN.SpaceEnc.isRooted_instDesc_rend` — the described instance is rooted.
-/

namespace HTN

namespace SpaceEnc

open TM Syn TaskNetwork

variable {Q Γ : Type} [Fintype Q] [Fintype Γ] (m n' : ℕ) (ι : Bool → Γ) (N : NTM Q Γ)

/-- **The rank of the compound tasks.** -/
def rkC (m : ℕ) : Cmp → ℕ
  | .root => 2 * m + 7
  | .main => 2 * m + 6
  | .loop _ => 2 * m + 5
  | .block _ => 2 * m + 4
  | .tree _ k => m + 3 + k
  | .bit _ k => 2 + (m - k)
  | .rd0 => 0
  | .core _ => 1
  | .incT _ => 0
  | .reT _ => 0
  | .finish => 1
  | .drainT => 0

theorem bodies_drainT {b : Cmp × List (List (Act Q Γ ⊕ Cmp))} (hb : b ∈ bodies m n' N)
    (h1 : b.1 = .drainT) : b.2 = [[aT .drn, cT .drainT]] ∨ b.2 = [] := by
  rcases b with ⟨c, ls⟩
  subst h1
  simp [bodies, bodiesP] at hb
  aesop

omit [Fintype Q] [Fintype Γ] in
/-- The compound cells of a body whose cells all decrease the rank. -/
theorem cells_lt {ls : List (List (Act Q Γ ⊕ Cmp))} {r : ℕ}
    (h : ∀ c, Sum.inr c ∈ ls.flatten → rkC m c < r) :
    ∀ i j : ℕ, i < ls.length → j < (ls.getD i []).length → ∀ c : Cmp,
      (ls.getD i []).getD j (Sum.inl default) = Sum.inr c → rkC m c < r := by
  intro i j hi hj c hc
  have := mem_flatten_of_cell (d := (Sum.inl default : Act Q Γ ⊕ Cmp)) hi hj
  rw [hc] at this
  exact h c this

omit [Fintype Q] [Fintype Γ] in
/-- The cells of a loop body `[x, cT t]` with `x` an action or a task of smaller rank. -/
theorem cells_loop {x : Act Q Γ ⊕ Cmp} {t : Cmp} (hx : ∀ c, x = Sum.inr c → rkC m c < rkC m t) :
    ∀ i j : ℕ, i < [[x, cT t]].length → j < ([[x, cT t]].getD i []).length → ∀ c : Cmp,
      ([[x, cT t]].getD i []).getD j (Sum.inl default) = Sum.inr c →
        rkC m c < rkC m t ∨ (rkC m c ≤ rkC m t ∧ (0 : ℕ) = 0 ∧ [[x, cT t]].length = 1 ∧
          j + 1 = ([[x, cT t]].getD i []).length) := by
  intro i j hi hj c hc
  simp only [List.length_singleton, Nat.lt_one_iff] at hi
  subst hi
  simp only [List.getD_cons_zero, List.length_cons, List.length_nil] at hj hc
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact Or.inl (hx c (by simpa using hc))
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
    cases hc
    exact Or.inr ⟨le_rfl, rfl, rfl, rfl⟩

/-- **Every method body respects the rank** in the sense of tail recursion. -/
theorem rank_ok : ∀ b ∈ bodies m n' N, ∀ i j : ℕ, i < b.2.length →
    j < (b.2.getD i []).length → ∀ c : Cmp,
    (b.2.getD i []).getD j (Sum.inl default) = Sum.inr c →
      rkC m c < rkC m b.1 ∨ (rkC m c ≤ rkC m b.1 ∧ (0 : ℕ) = 0 ∧ b.2.length = 1 ∧
        j + 1 = (b.2.getD i []).length) := by
  intro b hb
  have strict : (∀ c, Sum.inr c ∈ b.2.flatten → rkC m c < rkC m b.1) →
      ∀ i j : ℕ, i < b.2.length → j < (b.2.getD i []).length → ∀ c : Cmp,
        (b.2.getD i []).getD j (Sum.inl default) = Sum.inr c →
          rkC m c < rkC m b.1 ∨ (rkC m c ≤ rkC m b.1 ∧ (0 : ℕ) = 0 ∧ b.2.length = 1 ∧
            j + 1 = (b.2.getD i []).length) :=
    fun h i j hi hj c hc => Or.inl (cells_lt m h i j hi hj c hc)
  rcases b with ⟨t, ls⟩
  change ∀ i j : ℕ, i < ls.length → j < (ls.getD i []).length → ∀ c : Cmp,
    (ls.getD i []).getD j (Sum.inl default) = Sum.inr c →
      rkC m c < rkC m t ∨ (rkC m c ≤ rkC m t ∧ (0 : ℕ) = 0 ∧ ls.length = 1 ∧
        j + 1 = (ls.getD i []).length)
  replace strict : (∀ c, Sum.inr c ∈ ls.flatten → rkC m c < rkC m t) →
      ∀ i j : ℕ, i < ls.length → j < (ls.getD i []).length → ∀ c : Cmp,
        (ls.getD i []).getD j (Sum.inl default) = Sum.inr c →
          rkC m c < rkC m t ∨ (rkC m c ≤ rkC m t ∧ (0 : ℕ) = 0 ∧ ls.length = 1 ∧
            j + 1 = (ls.getD i []).length) := strict
  cases t with
  | root =>
    have h := bodies_root hb rfl; simp only at h; subst h
    exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
  | main =>
    have h := bodies_main hb rfl; simp only at h; subst h
    exact strict (fun c hc => by
      simp at hc; rcases hc with rfl | rfl | rfl <;> simp [rkC])
  | loop q =>
    rcases bodies_loop hb rfl with h | h <;> simp only at h <;> subst h
    · exact cells_loop m (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
    · exact strict (by simp)
  | block q =>
    have h := bodies_block hb rfl; simp only at h; subst h
    exact strict (fun c hc => by
      simp at hc; rcases hc with rfl | rfl <;> simp [rkC]; omega)
  | tree q k =>
    cases k with
    | zero =>
      have h := bodies_tree0 hb rfl; simp only at h; subst h
      exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
    | succ k =>
      have h := bodies_treeS hb rfl; simp only at h; subst h
      exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
  | bit q k =>
    rcases bodies_bit hb rfl with ⟨hk, x, e, h⟩ | ⟨rfl, h⟩ <;> simp only at h <;> subst h
    · exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; omega)
    · cases q
      · exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
      · exact strict (fun c hc => by
          simp at hc; rcases hc with rfl | rfl <;> simp [rkC])
  | rd0 =>
    rcases bodies_rd0 hb rfl with h | h | ⟨i, b', -, h⟩ <;> simp only at h <;> subst h <;>
      exact strict (by simp)
  | core q =>
    rcases bodies_core hb rfl with ⟨g, h⟩ | ⟨d, -, h⟩ <;> simp only at h <;> subst h <;>
      exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
  | incT q =>
    rcases bodies_incT hb rfl with ⟨k, -, h⟩ | h <;> simp only at h <;> subst h <;>
      exact strict (by simp)
  | reT q =>
    obtain ⟨a, -, h⟩ := bodies_reT hb rfl
    simp only at h; subst h
    exact strict (by simp)
  | finish =>
    obtain ⟨q, -, h⟩ := bodies_finish hb rfl
    simp only at h; subst h
    exact strict (fun c hc => by simp at hc; subst hc; simp [rkC]; try omega)
  | drainT =>
    rcases bodies_drainT m n' N hb rfl with h | h <;> simp only at h <;> subst h
    · exact cells_loop m (fun c hc => absurd hc (by simp))
    · exact strict (by simp)

/-- **The described domain of the encoding is tail recursive.** -/
theorem isTailRec_domDesc_rend (n : ℕ) (w : List Bool) :
    DomDesc.IsTailRec (rend m n' ι N n w).domDesc := by
  refine (rend m n' ι N n w).isTailRec_domDesc_of (rkC m) ?_
  intro p hp
  simp only [rend, List.mem_map] at hp
  obtain ⟨b, hb, rfl⟩ := hp
  exact rank_ok m n' N b hb

/-- **The described instance of the encoding is rooted.** -/
theorem isRooted_instDesc_rend (n : ℕ) (w : List Bool) :
    InstDesc.IsRooted (rend m n' ι N n w).instDesc :=
  (rend m n' ι N n w).isRooted_instDesc rfl

end SpaceEnc

end HTN
