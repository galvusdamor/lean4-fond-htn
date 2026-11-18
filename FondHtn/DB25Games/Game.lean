import HtnComplexity.PT.Lang
/-!
# [DB25] Planning games and the chosen-length problem

[DB25, §2]: a STRIPS problem `P = (P, A, I, G)`; an action `a = (Π⁺, Π⁻, E⁺, E⁻)` is applicable
in `S` iff `Π⁺ ⊆ S` and `Π⁻ ∩ S = ∅`, and `γ(S, a) = (S \ E⁻) ∪ E⁺`.

**The planning game `G(P, r)`**: Éloise and Abélard alternate, Éloise first, starting in `I`;
each move applies an applicable action of `A`; a player without applicable action loses; after
`r` actions Éloise wins iff `G ⊆ S`.  **The chosen-length problem**: is there an `r` such that
Éloise has a winning strategy in `G(P, r)`?

* `FOND.DBG.Win A G k e s` — the player `e` (`true` = Éloise) is to move in `s`, `k` actions
  remain, and Éloise wins (by backward induction; the game is finite and of perfect information,
  so this is the existence of a winning strategy).
* `FOND.DBG.EloWins d r` — Éloise wins `G(P, r)` for the description `d = (A, I, G)` with facts
  in `ℕ`; `FOND.DBG.ChosenLen d` — `∃ r, EloWins d r`; `FOND.DBG.chosenLang` — the language of
  the codes of the positive instances.
* `FOND.DBG.win_map` — the game is invariant under injective renaming of facts (used to build
  instances over structured fact types).
-/

namespace FOND

namespace DBG

open HTN HTN.Syn HTN.Syn.PolyDom

/-- A STRIPS action `(Π⁺, Π⁻, E⁺, E⁻)` over facts `α`. -/
abbrev Act (α : Type) : Type := List α × List α × List α × List α

section Sem

set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]

/-- Applicability. -/
def App (a : Act α) (s : α → Bool) : Prop :=
  (∀ p ∈ a.1, s p = true) ∧ ∀ p ∈ a.2.1, s p = false

/-- The successor state `(S \ E⁻) ∪ E⁺`. -/
def eff (a : Act α) (s : α → Bool) : α → Bool :=
  fun p => if p ∈ a.2.2.1 then true else if p ∈ a.2.2.2 then false else s p

/-- The goal holds. -/
def Sat (G : List α) (s : α → Bool) : Prop := ∀ p ∈ G, s p = true

/-- **The game value**: `Win A G k e s` — `k` actions remain, player `e` (`true`: Éloise) moves. -/
def Win (A : List (Act α)) (G : List α) : ℕ → Bool → (α → Bool) → Prop
  | 0, _, s => Sat G s
  | k + 1, true, s => ∃ a ∈ A, App a s ∧ Win A G k false (eff a s)
  | k + 1, false, s => ∀ a ∈ A, App a s → Win A G k true (eff a s)

@[simp] theorem win_zero (A : List (Act α)) (G : List α) (e : Bool) (s : α → Bool) :
    Win A G 0 e s ↔ Sat G s := Iff.rfl

theorem win_succ_true (A : List (Act α)) (G : List α) (k : ℕ) (s : α → Bool) :
    Win A G (k + 1) true s ↔ ∃ a ∈ A, App a s ∧ Win A G k false (eff a s) := Iff.rfl

theorem win_succ_false (A : List (Act α)) (G : List α) (k : ℕ) (s : α → Bool) :
    Win A G (k + 1) false s ↔ ∀ a ∈ A, App a s → Win A G k true (eff a s) := Iff.rfl

/-- The state of a list of facts. -/
def stOf (I : List α) : α → Bool := fun p => decide (p ∈ I)

/-! ### Renaming facts -/

variable {β : Type} [DecidableEq β]

/-- Renaming an action. -/
def mapAct (f : α → β) (a : Act α) : Act β := (a.1.map f, a.2.1.map f, a.2.2.1.map f, a.2.2.2.map f)

theorem app_map {f : α → β} (a : Act α) (s : β → Bool) : App (mapAct f a) s ↔ App a (s ∘ f) := by
  simp [App, mapAct]

theorem eff_map {f : α → β} (hf : Function.Injective f) (a : Act α) (s : β → Bool) :
    eff (mapAct f a) s ∘ f = eff a (s ∘ f) := by
  funext p
  simp [eff, mapAct, hf.eq_iff]

theorem sat_map {f : α → β} (G : List α) (s : β → Bool) : Sat (G.map f) s ↔ Sat G (s ∘ f) := by
  simp [Sat]

/-- **Renaming invariance.** -/
theorem win_map {f : α → β} (hf : Function.Injective f) (A : List (Act α)) (G : List α) :
    ∀ k e (s : β → Bool), Win (A.map (mapAct f)) (G.map f) k e s ↔ Win A G k e (s ∘ f) := by
  intro k
  induction k with
  | zero => intro e s; exact sat_map G s
  | succ k ih =>
    intro e s
    cases e
    · simp only [win_succ_false, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, app_map, ih, eff_map hf]
    · simp only [win_succ_true, List.mem_map, ih]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩; exact ⟨a, ha, by rwa [app_map, eff_map hf] at h⟩
      · rintro ⟨a, ha, h⟩; exact ⟨_, ⟨a, ha, rfl⟩, by rwa [app_map, eff_map hf]⟩

theorem stOf_map {f : α → β} (hf : Function.Injective f) (I : List α) :
    stOf (I.map f) ∘ f = stOf I := by
  funext p; simp [stOf, hf.eq_iff]

/-! ### Locality -/

/-- The facts mentioned by an action. -/
def Act.facts (a : Act α) : List α := a.1 ++ a.2.1 ++ a.2.2.1 ++ a.2.2.2

/-- **The game only depends on the mentioned facts.** -/
theorem win_congr (A : List (Act α)) (G : List α) :
    ∀ k e (s s' : α → Bool), (∀ p, (p ∈ G ∨ ∃ a ∈ A, p ∈ a.facts) → s p = s' p) →
      (Win A G k e s ↔ Win A G k e s') := by
  intro k
  induction k with
  | zero =>
    intro e s s' h
    simp only [win_zero, Sat]
    exact forall₂_congr fun p hp => by rw [h p (Or.inl hp)]
  | succ k ih =>
    intro e s s' h
    have happ : ∀ a ∈ A, (App a s ↔ App a s') := fun a ha => by
      unfold App
      refine and_congr (forall₂_congr fun p hp => ?_) (forall₂_congr fun p hp => ?_)
      · rw [h p (Or.inr ⟨a, ha, by simp [Act.facts, hp]⟩)]
      · rw [h p (Or.inr ⟨a, ha, by simp [Act.facts, hp]⟩)]
    have heff : ∀ a ∈ A, (Win A G k (!e) (eff a s) ↔ Win A G k (!e) (eff a s')) := fun a _ =>
      ih _ _ _ fun p hp => by
        simp only [eff]
        split_ifs
        · rfl
        · rfl
        · exact h p hp
    cases e
    · simp only [win_succ_false]
      exact forall₂_congr fun a ha => imp_congr (happ a ha) (heff a ha)
    · simp only [win_succ_true]
      exact exists_congr fun a => and_congr_right fun ha => and_congr (happ a ha) (heff a ha)

end Sem

/-! ## Descriptions and the language -/

/-- **A planning-game description** `(A, I, G)` with facts in `ℕ`. -/
abbrev GDesc : Type := List (Act ℕ) × List ℕ × List ℕ

/-- **Éloise wins `G(P, r)`.** -/
def EloWins (d : GDesc) (r : ℕ) : Prop := Win d.1 d.2.2 r true (stOf d.2.1)

/-- **The chosen-length problem**: `∃ r, Éloise wins G(P, r)`. -/
def ChosenLen (d : GDesc) : Prop := ∃ r, EloWins d r

/-- The language of the chosen-length problem. -/
def chosenLang : Cx.Language := codeLang GDesc ChosenLen

/-- The pass action `✓ = (∅, ∅, ∅, ∅)`. -/
def pass : Act ℕ := ([], [], [], [])

/-- Chosen length restricted to even lengths. -/
def ChosenEven (d : GDesc) : Prop := ∃ r, Even r ∧ EloWins d r

/-- Chosen length restricted to odd lengths. -/
def ChosenOdd (d : GDesc) : Prop := ∃ r, Odd r ∧ EloWins d r

end DBG

end FOND
