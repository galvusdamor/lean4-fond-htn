import FondHtn.HardTR.WGame
/-!
# CB22 Thm 5: pulling the word game back along an encoding

**`FOND.HardTR.lwin_pull`**: a won word game on encoded states (facts) whose words consist of
action names gives a won word game on the abstract states (records), provided applicability and
outcomes commute with the encoding on good states.
-/

namespace FOND

namespace HardTR

variable {A B S T : Type} {appA : A → S → Prop} {outsA : A → S → Set S}
  {appB : B → T → Prop} {outsB : B → T → Set T}

/-- The word game on the empty language is lost (when applicable actions have outcomes). -/
theorem LWin.false_of_empty (hne : ∀ a s, appA a s → (outsA a s).Nonempty) {L : Set (List A)} {s : S}
    (h : LWin appA outsA L s) (hL : L = ∅) : False := by
  induction h with
  | nil h => rw [hL] at h; exact h
  | @step L s a ha h ih =>
    obtain ⟨s', hs'⟩ := hne a s ha
    exact ih s' hs' (by rw [hL]; ext w; simp)

/-- **Pulling the word game back.** -/
theorem lwin_pull (nm : B → A) (hnm : Function.Injective nm) (enc : T → S) (Good : T → Prop)
    (Dec : B → Prop) (hne : ∀ a s, appA a s → (outsA a s).Nonempty)
    (happ : ∀ b t, Dec b → Good t → (appA (nm b) (enc t) ↔ appB b t))
    (hout : ∀ b t, Dec b → Good t → appB b t → outsA (nm b) (enc t) = enc '' outsB b t)
    (hgood : ∀ b t t', Good t → appB b t → t' ∈ outsB b t → Good t') :
    ∀ {L : Set (List A)} {s : S}, LWin appA outsA L s → (∀ w ∈ L, ∀ x ∈ w, ∃ b, Dec b ∧ x = nm b) →
      ∀ {t : T}, Good t → s = enc t → LWin appB outsB {u | u.map nm ∈ L} t := by
  intro L s h
  induction h with
  | nil h => exact fun _ t _ _ => .nil (by simpa using h)
  | @step L s x hx h ih =>
    intro hL t hG hs
    subst hs
    by_cases hres : ∃ w, x :: w ∈ L
    · obtain ⟨w, hw⟩ := hres
      obtain ⟨b, hdb, rfl⟩ := hL _ hw x (by simp)
      have hb := (happ b t hdb hG).1 hx
      refine .step b hb fun t' ht' => ?_
      have hmem : enc t' ∈ outsA (nm b) (enc t) := by
        rw [hout b t hdb hG hb]; exact ⟨t', ht', rfl⟩
      have := ih (enc t') hmem (fun w hw y hy => hL _ hw y (by simp [hy])) (hgood b t t' hG hb ht') rfl
      refine this.mono ?_
      intro u hu
      simpa using hu
    · exfalso
      obtain ⟨s', hs'⟩ := hne _ _ hx
      have h' := h s' hs'
      exact LWin.false_of_empty hne h' (by
        ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hw => hres ⟨w, hw⟩)

theorem exists_map_of_dec (nm : B → A) (Dec : B → Prop) :
    ∀ w : List A, (∀ x ∈ w, ∃ b, Dec b ∧ x = nm b) → ∃ u : List B, u.map nm = w
  | [], _ => ⟨[], rfl⟩
  | x :: w, h => by
    obtain ⟨b, -, rfl⟩ := h x (by simp)
    obtain ⟨u, hu⟩ := exists_map_of_dec nm Dec w fun y hy => h y (by simp [hy])
    exact ⟨b :: u, by simp [hu]⟩

/-- **Pulling the safe word game back.** -/
theorem lsafe_pull (nm : B → A) (enc : T → S) (Good : T → Prop)
    (Dec : B → Prop) (hne : ∀ a s, appA a s → (outsA a s).Nonempty)
    (happ : ∀ b t, Dec b → Good t → (appA (nm b) (enc t) ↔ appB b t))
    (hout : ∀ b t, Dec b → Good t → appB b t → outsA (nm b) (enc t) = enc '' outsB b t)
    (hgood : ∀ b t t', Good t → appB b t → t' ∈ outsB b t → Good t')
    {L : Set (List A)} {s : S} (h : LSafe appA outsA L s)
    (hL : ∀ w ∈ L, ∀ x ∈ w, ∃ b, Dec b ∧ x = nm b) {t : T} (hG : Good t) (hs : s = enc t) :
    LSafe appB outsB {u | u.map nm ∈ L} t := by
  obtain ⟨R, hR, hcl⟩ := h
  refine ⟨{p | Good p.2 ∧ ∃ L', (L', enc p.2) ∈ R ∧ (∀ w ∈ L', ∀ x ∈ w, ∃ b, Dec b ∧ x = nm b) ∧
    p.1 = {u | u.map nm ∈ L'}}, ⟨hG, L, hs ▸ hR, hL, rfl⟩, ?_⟩
  rintro ⟨LB, t'⟩ ⟨hG', L', hL', hdec, rfl⟩
  obtain ⟨⟨w, hw⟩, h⟩ := hcl _ hL'
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu⟩ := exists_map_of_dec nm Dec w (hdec w hw)
    exact ⟨u, by simp only [Set.mem_setOf_eq, hu]; exact hw⟩
  · rcases h with hnil | ⟨a, ha, hs'⟩
    · exact Or.inl (by simpa using hnil)
    · obtain ⟨s₀, hs₀⟩ := hne _ _ ha
      obtain ⟨⟨w₀, hw₀⟩, -⟩ := hcl _ (hs' s₀ hs₀)
      obtain ⟨b, hdb, rfl⟩ := hdec _ hw₀ a (by simp)
      have hb := (happ b t' hdb hG').1 ha
      refine Or.inr ⟨b, hb, fun t'' ht'' => ⟨hgood b t' t'' hG' hb ht'', {w | nm b :: w ∈ L'}, ?_,
        fun w hw x hx => hdec _ hw x (by simp [hx]), ?_⟩⟩
      · apply hs'
        rw [hout b t' hdb hG' hb]; exact ⟨t'', ht'', rfl⟩
      · ext u; simp

end HardTR

end FOND
