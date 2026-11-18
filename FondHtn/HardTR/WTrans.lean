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

end HardTR

end FOND
