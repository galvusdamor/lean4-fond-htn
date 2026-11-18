import ComplexityTheory.RegRounds.Anon
/-!
# Short runs in a finite reachable space

* **`HTN.RegRounds.exists_steps_le_card`** — if every configuration reachable from `c₀` lies in
  a finite set `S`, then every reachable configuration is reached in at most `|S|` steps.

The proof is breadth first: the configurations reached in at most `i` steps form an increasing
chain of subsets of `S`; once it stops growing it is stable for ever, and it can grow at most
`|S|` times.
-/

namespace HTN

namespace RegRounds

open Classical

variable {α : Type*} (r : α → α → Prop) (c₀ : α)

theorem steps_of_rtg {a b : α} (h : Relation.ReflTransGen r a b) : ∃ n, Steps r n a b := by
  induction h with
  | refl => exact ⟨0, Steps.zero⟩
  | tail _ hbc ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, Steps.succ hn hbc⟩

/-- The configurations reached in at most `i` steps. -/
def Within (i : ℕ) (c : α) : Prop := ∃ m ≤ i, Steps r m c₀ c

theorem within_mono {i j : ℕ} (hij : i ≤ j) {c : α} (h : Within r c₀ i c) : Within r c₀ j c := by
  obtain ⟨m, hm, hs⟩ := h
  exact ⟨m, by omega, hs⟩

/-- **Stability**: if one more step adds nothing, nothing is ever added. -/
theorem within_stable {i : ℕ} (hst : ∀ c, Within r c₀ (i + 1) c → Within r c₀ i c) :
    ∀ j c, Within r c₀ j c → Within r c₀ i c := by
  intro j
  induction j with
  | zero => intro c h; exact within_mono r c₀ (by omega) h
  | succ j ih =>
    intro c ⟨m, hm, hs⟩
    rcases Nat.lt_or_ge m (j + 1) with hlt | hge
    · exact ih c ⟨m, by omega, hs⟩
    · have hmj : m = j + 1 := by omega
      subst hmj
      cases hs with
      | @succ _ _ b _ hsb hbc =>
        obtain ⟨m', hm', hs'⟩ := ih b ⟨j, le_rfl, hsb⟩
        exact hst c ⟨m' + 1, by omega, Steps.succ hs' hbc⟩

variable (S : Finset α)

/-- **Short runs in a finite reachable space.** -/
theorem exists_steps_le_card (hS : ∀ c, Relation.ReflTransGen r c₀ c → c ∈ S) {c : α}
    (h : Relation.ReflTransGen r c₀ c) : ∃ n ≤ S.card, Steps r n c₀ c := by
  -- the layers as subsets of `S`
  let L : ℕ → Finset α := fun i => S.filter (Within r c₀ i)
  have hmemL : ∀ i c, c ∈ L i ↔ Within r c₀ i c := by
    intro i c
    simp only [L, Finset.mem_filter, and_iff_right_iff_imp]
    rintro ⟨m, -, hs⟩
    exact hS c hs.rtg
  have hsub : ∀ i, L i ⊆ L (i + 1) := fun i c hc =>
    (hmemL _ c).2 (within_mono r c₀ (by omega) ((hmemL i c).1 hc))
  -- either some layer is stable, or the layers grow strictly up to `|S|`
  by_cases hex : ∃ i < S.card, ∀ c, Within r c₀ (i + 1) c → Within r c₀ i c
  · obtain ⟨i, hi, hst⟩ := hex
    obtain ⟨n, hn⟩ := steps_of_rtg r h
    obtain ⟨m, hm, hs⟩ := within_stable r c₀ hst n c ⟨n, le_rfl, hn⟩
    exact ⟨m, by omega, hs⟩
  · push_neg at hex
    have hgrow : ∀ i, i ≤ S.card → i + 1 ≤ (L i).card := by
      intro i
      induction i with
      | zero =>
        intro _
        have : c₀ ∈ L 0 := (hmemL 0 c₀).2 ⟨0, le_rfl, Steps.zero⟩
        exact Finset.card_pos.2 ⟨c₀, this⟩
      | succ i ih =>
        intro hi
        obtain ⟨c', hc1, hc2⟩ := hex i (by omega)
        have hss : L i ⊂ L (i + 1) := by
          refine Finset.ssubset_iff_subset_ne.2 ⟨hsub i, fun heq => hc2 ?_⟩
          have : c' ∈ L (i + 1) := (hmemL _ c').2 hc1
          rw [← heq] at this
          exact (hmemL i c').1 this
        have := Finset.card_lt_card hss
        have := ih (by omega)
        omega
    have h1 := hgrow S.card le_rfl
    have h2 : (L S.card).card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega

end RegRounds

end HTN
