import ComplexityTheory.TM.Theory.Guess
/-!
# Guessing a witness behind a separator

`ComplexityTheory/TM/Theory/Guess.lean` shows that guessing an exponentially long witness written directly
behind the input is free.  The base machines of the exponential scale
(`HtnCompilability/Space/ExpScale.lean`) read a tape in which the input and the quantified
strings are separated by one blank cell:

  `x.map some ++ none :: z.map some`.

The separator is what makes the input readable: without it, the machine cannot tell where the
input ends and the layout of the strings begins.  This file shows that guessing `z` is still free.

The *separator-guessing variant* `TM.NTM.sepGuess M` runs `M` on the input alone, with one extra
bit of state recording whether the separator has already been met:

* before that, it behaves exactly as `M` — in particular, the first blank it reads (which is the
  cell just behind the input, because the head starts at cell `0`, moves by one cell per step and
  `M` never writes a blank) is treated as the separator, i.e. as a genuine blank;
* after that, it behaves as the guessing variant `TM.NTM.guess M`: every further blank is a still
  unread cell of `z`, and its content is guessed.

`TM.NTM.relabel` transports a machine along a bijection of its states, so that the variant, whose
states are `Q × Bool`, can be presented with states `Fin (2 * k)`.

## Main results

* `TM.NTM.acceptsWithin_sepGuess_iff` —
  `(sepGuess M).AcceptsWithin (x.map some) K ↔
     ∃ z, z.length = K + 1 ∧ M.AcceptsWithin (x.map some ++ none :: z.map some) K`;
* `TM.NTM.acceptsWithin_sep_congr`, `TM.NTM.acceptsWithin_sep_take` — only the first `K + 1`
  cells of `z` matter for a run of `K` steps;
* `TM.NTM.acceptsWithin_relabel_iff` — relabelling the states does not change acceptance.
-/

namespace TM

namespace NTM

variable {Q : Type*}

/-! ### Tapes with a separator -/

/-- **The tape with a separator**: the input `x`, one blank cell, then the bits of `z`. -/
def sepTape (x z : List Bool) : List (Option Bool) := x.map some ++ none :: z.map some

lemma getD_sepTape_lt {x z : List Bool} {i : ℕ} (hi : i < x.length) :
    (sepTape x z).getD i none = (x.map some).getD i none := by
  unfold sepTape
  rw [List.getD_append _ _ _ _ (by simpa using hi)]

lemma getD_sepTape_sep (x z : List Bool) : (sepTape x z).getD x.length none = none := by
  unfold sepTape
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

lemma getD_sepTape_right (x z : List Bool) (j : ℕ) :
    (sepTape x z).getD (x.length + 1 + j) none = (z.map some).getD j none := by
  unfold sepTape
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map]; omega)]
  simp only [List.length_map]
  rw [show x.length + 1 + j - x.length = j + 1 by omega]
  simp

/-- **Only the first `K + 1` cells behind the separator matter** for a run of `K` steps. -/
theorem acceptsWithin_sep_congr (M : NTM Q (Option Bool)) (hblank : M.blank = none)
    {x z z' : List Bool} {K : ℕ}
    (h : ∀ j < K, (z.map some).getD j none = (z'.map some).getD j none)
    (hz : M.AcceptsWithin (sepTape x z) K) : M.AcceptsWithin (sepTape x z') K := by
  refine acceptsWithin_congr_input M (fun i hi => ?_) hz
  rw [hblank]
  rcases lt_trichotomy i x.length with hix | rfl | hix
  · rw [getD_sepTape_lt hix, getD_sepTape_lt hix]
  · rw [getD_sepTape_sep, getD_sepTape_sep]
  · obtain ⟨j, rfl⟩ : ∃ j, i = x.length + 1 + j := ⟨i - x.length - 1, by omega⟩
    rw [getD_sepTape_right, getD_sepTape_right]
    exact h j (by omega)

lemma getD_map_some_take (z : List Bool) {j n : ℕ} (hj : j < n) :
    (z.map some).getD j none = ((z.take n).map some).getD j none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, if_pos hj]

/-- Truncating the part behind the separator to `K + 1` cells does not change a run of `K`
steps. -/
theorem acceptsWithin_sep_take (M : NTM Q (Option Bool)) (hblank : M.blank = none)
    (x z : List Bool) (K : ℕ) :
    M.AcceptsWithin (sepTape x z) K ↔ M.AcceptsWithin (sepTape x (z.take (K + 1))) K :=
  ⟨acceptsWithin_sep_congr M hblank fun j hj => getD_map_some_take z (by omega),
    acceptsWithin_sep_congr M hblank fun j hj => (getD_map_some_take z (by omega)).symm⟩

/-- A trailing blank does not change the tape. -/
theorem acceptsWithin_append_none (M : NTM Q (Option Bool)) (hblank : M.blank = none)
    (w : List (Option Bool)) (K : ℕ) :
    M.AcceptsWithin (w ++ [none]) K ↔ M.AcceptsWithin w K := by
  have key : ∀ i, (w ++ [none]).getD i M.blank = w.getD i M.blank := by
    intro i
    rw [hblank]
    rcases lt_or_ge i w.length with hi | hi
    · rw [List.getD_append _ _ _ _ hi]
    · rw [List.getD_append_right _ _ _ _ hi, List.getD_eq_default _ _ hi]
      rcases Nat.eq_or_lt_of_le hi with h | h
      · subst h; simp
      · rw [List.getD_eq_default _ _ (by simp; omega)]
  exact ⟨acceptsWithin_congr_input M fun i _ => key i,
    acceptsWithin_congr_input M fun i _ => (key i).symm⟩

/-! ### The separator-guessing variant -/

/-- **The separator-guessing variant of `M`.**  The extra bit of state records whether the
separator has been met.  Before that, the machine is `M`, and the first blank it reads is taken
for the separator; afterwards it is the guessing variant of `M`. -/
def sepGuess (M : NTM Q (Option Bool)) : NTM (Q × Bool) (Option Bool) where
  step q γ := match q.2, γ with
    | false, none => (fun t : Q × Option Bool × Move => ((t.1, true), t.2)) '' M.step q.1 none
    | false, some b => (fun t : Q × Option Bool × Move => ((t.1, false), t.2)) '' M.step q.1 (some b)
    | true, γ => (fun t : Q × Option Bool × Move => ((t.1, true), t.2)) '' (guess M).step q.1 γ
  init := (M.init, false)
  accept := {q | q.1 ∈ M.accept}
  blank := M.blank

lemma sepGuess_step_false_none (M : NTM Q (Option Bool)) (q : Q) (q' : Q × Bool)
    (γ' : Option Bool) (m : Move) :
    (q', γ', m) ∈ (sepGuess M).step (q, false) none ↔ q'.2 = true ∧ (q'.1, γ', m) ∈ M.step q none := by
  obtain ⟨q', f'⟩ := q'
  simp only [sepGuess, Set.mem_image]
  constructor
  · rintro ⟨⟨a, b, c⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := he
    exact ⟨rfl, h⟩
  · rintro ⟨hf, h⟩
    obtain rfl : f' = _ := hf
    exact ⟨_, h, rfl⟩

lemma sepGuess_step_false_some (M : NTM Q (Option Bool)) (q : Q) (b : Bool) (q' : Q × Bool)
    (γ' : Option Bool) (m : Move) :
    (q', γ', m) ∈ (sepGuess M).step (q, false) (some b) ↔
      q'.2 = false ∧ (q'.1, γ', m) ∈ M.step q (some b) := by
  obtain ⟨q', f'⟩ := q'
  simp only [sepGuess, Set.mem_image]
  constructor
  · rintro ⟨⟨a, b, c⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := he
    exact ⟨rfl, h⟩
  · rintro ⟨hf, h⟩
    obtain rfl : f' = _ := hf
    exact ⟨_, h, rfl⟩

lemma sepGuess_step_true (M : NTM Q (Option Bool)) (q : Q) (γ : Option Bool) (q' : Q × Bool)
    (γ' : Option Bool) (m : Move) :
    (q', γ', m) ∈ (sepGuess M).step (q, true) γ ↔
      q'.2 = true ∧ (q'.1, γ', m) ∈ (guess M).step q γ := by
  obtain ⟨q', f'⟩ := q'
  simp only [sepGuess, Set.mem_image]
  constructor
  · rintro ⟨⟨a, b, c⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := he
    exact ⟨rfl, h⟩
  · rintro ⟨hf, h⟩
    obtain rfl : f' = _ := hf
    exact ⟨_, h, rfl⟩

/-- **The separator-guessing machine can mirror a run of `M` on a tape with separator.**  The
separator sits at cell `n0`.  Before it has been met, the two tapes agree except behind the
separator, which the head has not reached yet; afterwards the variant's tape refines `M`'s. -/
theorem sepGuess_reaches_of_reaches {M : NTM Q (Option Bool)} (hba : BlankAvoiding M) (n0 : ℕ) :
    ∀ {n : ℕ} {c c' : Config Q (Option Bool)} {d : Config (Q × Bool) (Option Bool)},
      M.Reaches n c c' → d.state.1 = c.state → d.head = c.head →
      (∀ i, d.tape i = none ∨ d.tape i = c.tape i) →
      (d.state.2 = false → d.head ≤ n0 ∧ d.tape n0 = none ∧ c.tape n0 = none ∧
        (∀ i < n0, d.tape i ≠ none) ∧ ∀ i ≤ c.head + n, i ≠ n0 → c.tape i ≠ none) →
      (d.state.2 = true → ∀ i ≤ c.head + n, c.tape i ≠ none) →
      ∃ d', (sepGuess M).Reaches n d d' ∧ d'.state.1 = c'.state := by
  intro n
  induction n with
  | zero =>
      intro c c' d h hs _ _ _ _
      exact ⟨d, rfl, by rw [hs, show c = c' from h]⟩
  | succ n ih =>
      intro c c' d h hs hh href hF hT
      obtain ⟨e, hstep, he⟩ := h
      obtain ⟨q', γ', m, hmem, rfl⟩ := hstep
      have hγ' : γ' ≠ none := hba _ _ _ hmem
      obtain ⟨⟨q, f⟩, dh, dt⟩ := d
      simp only at hs hh href hF hT
      subst hs hh
      -- the tape after the step, on both sides
      have hupd : ∀ i, (Function.update dt c.head γ') i = none ∨
          (Function.update dt c.head γ') i = (Function.update c.tape c.head γ') i := by
        intro i
        by_cases hic : i = c.head
        · subst hic; simp
        · simp only [Function.update_of_ne hic]; exact href i
      cases f with
      | true =>
          have hnb := hT rfl
          obtain ⟨b, hb⟩ : ∃ b : Bool, c.tape c.head = some b := by
            cases hc : c.tape c.head with
            | none => exact absurd hc (hnb _ (by omega))
            | some b => exact ⟨b, rfl⟩
          have hmem' : ((q', true), γ', m) ∈ (sepGuess M).step (c.state, true) (dt c.head) := by
            rw [sepGuess_step_true]
            refine ⟨rfl, ?_⟩
            rcases href c.head with hd | hd
            · rw [hd, guess_step_none]
              exact ⟨b, by rw [← hb]; exact hmem⟩
            · rw [hd, hb]; rw [hb] at hmem; exact hmem
          obtain ⟨d', hr, hd'⟩ := ih (d := ⟨(q', true), m.apply c.head,
              Function.update dt c.head γ'⟩) he rfl rfl hupd (by simp) (by
            intro _ i hi
            by_cases hic : i = c.head
            · subst hic; simpa using hγ'
            · simp only [Function.update_of_ne hic]
              have := m.apply_le c.head
              exact hnb i (by simp only at hi; omega))
          exact ⟨d', ⟨_, ⟨_, γ', m, hmem', rfl⟩, hr⟩, hd'⟩
      | false =>
          obtain ⟨hle, hdn0, hcn0, hdlt, hcnb⟩ := hF rfl
          by_cases hc0 : c.head = n0
          · subst hc0
            have hmem' : ((q', true), γ', m) ∈ (sepGuess M).step (c.state, false) (dt c.head) := by
              rw [hdn0, sepGuess_step_false_none]
              exact ⟨rfl, by rw [← hcn0]; exact hmem⟩
            obtain ⟨d', hr, hd'⟩ := ih (d := ⟨(q', true), m.apply c.head,
                Function.update dt c.head γ'⟩) he rfl rfl hupd (by simp) (by
              intro _ i hi
              by_cases hic : i = c.head
              · subst hic; simpa using hγ'
              · simp only [Function.update_of_ne hic]
                have := m.apply_le c.head
                exact hcnb i (by simp only at hi; omega) hic)
            exact ⟨d', ⟨_, ⟨_, γ', m, hmem', rfl⟩, hr⟩, hd'⟩
          · have hlt : c.head < n0 := by omega
            obtain ⟨b, hb⟩ : ∃ b : Bool, c.tape c.head = some b := by
              cases hc : c.tape c.head with
              | none => exact absurd hc (hcnb _ (by omega) hc0)
              | some b => exact ⟨b, rfl⟩
            have hdb : dt c.head = some b := by
              rcases href c.head with hd | hd
              · exact absurd hd (hdlt _ hlt)
              · rw [hd, hb]
            have hmem' : ((q', false), γ', m) ∈ (sepGuess M).step (c.state, false) (dt c.head) := by
              rw [hdb, sepGuess_step_false_some]
              exact ⟨rfl, by rw [← hb]; exact hmem⟩
            have hne : n0 ≠ c.head := fun h => hc0 h.symm
            obtain ⟨d', hr, hd'⟩ := ih (d := ⟨(q', false), m.apply c.head,
                Function.update dt c.head γ'⟩) he rfl rfl hupd (by
              intro _
              refine ⟨?_, by simpa [Function.update_of_ne hne] using hdn0,
                by simpa [Function.update_of_ne hne] using hcn0, ?_, ?_⟩
              · have := m.apply_le c.head
                simp only
                omega
              · intro i hi
                by_cases hic : i = c.head
                · subst hic; simpa using hγ'
                · simpa [Function.update_of_ne hic] using hdlt i hi
              · intro i hi hin
                by_cases hic : i = c.head
                · subst hic; simpa using hγ'
                · simp only [Function.update_of_ne hic]
                  have := m.apply_le c.head
                  exact hcnb i (by simp only at hi; omega) hin) (by simp)
            exact ⟨d', ⟨_, ⟨_, γ', m, hmem', rfl⟩, hr⟩, hd'⟩

/-- **Every run of the separator-guessing machine is explained by a tape with separator.**  From a
configuration that has not met the separator yet (head not beyond cell `n0`, bits before it, a
blank at it), every run of the variant comes from a run of `M` on a tape that refines the starting
one and is blank exactly at the separator; from a configuration that has met it, on a tape without
blanks. -/
theorem exists_completion_of_sepGuess_reaches {M : NTM Q (Option Bool)} (hba : BlankAvoiding M)
    (n0 : ℕ) :
    ∀ {n : ℕ} {d d' : Config (Q × Bool) (Option Bool)}, (sepGuess M).Reaches n d d' →
      (d.state.2 = false → d.head ≤ n0 ∧ (∀ i < n0, d.tape i ≠ none) ∧ d.tape n0 = none) →
      ∃ c c' : Config Q (Option Bool), c.state = d.state.1 ∧ c.head = d.head ∧
        (∀ i, d.tape i = none ∨ d.tape i = c.tape i) ∧
        (∀ i, c.tape i = none ↔ (d.state.2 = false ∧ i = n0)) ∧
        M.Reaches n c c' ∧ c'.state = d'.state.1 := by
  intro n
  induction n with
  | zero =>
      intro d d' h hJ
      subst h
      classical
      refine ⟨⟨d.state.1, d.head, fun i => if d.state.2 = false ∧ i = n0 then none
        else some ((d.tape i).getD false)⟩, _, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · intro i
        by_cases hc : d.state.2 = false ∧ i = n0
        · left
          obtain ⟨h1, rfl⟩ := hc
          exact (hJ h1).2.2
        · simp only [if_neg hc]
          cases hi : d.tape i with
          | none => exact Or.inl rfl
          | some b => exact Or.inr rfl
      · intro i
        by_cases hc : d.state.2 = false ∧ i = n0
        · simp [hc]
        · simp [hc]
  | succ n ih =>
      intro d d' h hJ
      obtain ⟨e, hstep, he⟩ := h
      obtain ⟨q'', γ', m, hmem, rfl⟩ := hstep
      obtain ⟨⟨q, f⟩, dh, dt⟩ := d
      simp only at hJ hmem ⊢
      -- the symbol `M` acts on, the new flag, and the facts about the step
      obtain ⟨β, hβmem, hβref, hβ, hJe, hflag⟩ : ∃ β : Option Bool,
          (q''.1, γ', m) ∈ M.step q β ∧ (dt dh = none ∨ dt dh = β) ∧
          (f = true → β ≠ none) ∧
          (q''.2 = false → m.apply dh ≤ n0 ∧
            (∀ i < n0, Function.update dt dh γ' i ≠ none) ∧ Function.update dt dh γ' n0 = none) ∧
          (f = false → dh ≤ n0 ∧ dt dh = β ∧ (q''.2 = false ↔ dh ≠ n0) ∧ (β = none ↔ dh = n0)) := by
        cases f with
        | true =>
            rw [sepGuess_step_true] at hmem
            obtain ⟨hq, hmem⟩ := hmem
            cases hd : dt dh with
            | some b =>
                rw [hd] at hmem
                exact ⟨some b, hmem, Or.inr rfl, fun _ => by simp, fun h => by
                  rw [hq] at h; exact absurd h (by simp), fun h => absurd h (by simp)⟩
            | none =>
                rw [hd, guess_step_none] at hmem
                obtain ⟨b, hb⟩ := hmem
                exact ⟨some b, hb, Or.inl rfl, fun _ => by simp, fun h => by
                  rw [hq] at h; exact absurd h (by simp), fun h => absurd h (by simp)⟩
        | false =>
            obtain ⟨hle, hlt, hn0⟩ := hJ rfl
            cases hd : dt dh with
            | some b =>
                rw [hd, sepGuess_step_false_some] at hmem
                obtain ⟨hq, hmem⟩ := hmem
                have hne : dh ≠ n0 := by rintro rfl; rw [hd] at hn0; simp at hn0
                have hγ' : γ' ≠ none := hba _ _ _ hmem
                refine ⟨some b, hmem, Or.inr rfl, fun h => absurd h (by simp), fun _ => ?_,
                  fun _ => ⟨hle, rfl, by simp [hq, hne], by simp [hne]⟩⟩
                refine ⟨by have := m.apply_le dh; omega, ?_, ?_⟩
                · intro i hi
                  by_cases hid : i = dh
                  · subst hid; simpa using hγ'
                  · simpa [Function.update_of_ne hid] using hlt i hi
                · rw [Function.update_of_ne (Ne.symm hne)]; exact hn0
            | none =>
                rw [hd, sepGuess_step_false_none] at hmem
                obtain ⟨hq, hmem⟩ := hmem
                have heq : dh = n0 := by
                  by_contra hne
                  exact hlt dh (by omega) hd
                refine ⟨none, hmem, Or.inl rfl, fun h => absurd h (by simp), fun h => ?_,
                  fun _ => ⟨hle, rfl, by simp [hq, heq], by simp [heq]⟩⟩
                rw [hq] at h; exact absurd h (by simp)
      have hγ' : γ' ≠ none := hba _ _ _ hβmem
      obtain ⟨ce, c', hces, hceh, hceref, hcenone, hreach, hstate⟩ := ih he hJe
      simp only at hces hceh hceref hcenone
      have hce : ce.tape dh = γ' := by
        rcases hceref dh with h | h
        · simp at h; exact absurd h hγ'
        · simpa using h.symm
      refine ⟨⟨q, dh, Function.update ce.tape dh β⟩, c', rfl, rfl, ?_, ?_, ?_, hstate⟩
      · intro i
        by_cases hid : i = dh
        · subst hid; simpa using hβref
        · have := hceref i
          simpa [Function.update_of_ne hid] using this
      · intro i
        by_cases hid : i = dh
        · subst hid
          simp only [Function.update_self]
          cases f with
          | true => simp [hβ rfl]
          | false =>
              obtain ⟨-, -, -, h⟩ := hflag rfl
              simp [h]
        · simp only [Function.update_of_ne hid]
          rw [hcenone i]
          cases f with
          | true =>
              simp only [Bool.true_eq_false, false_and, iff_false, not_and]
              intro h
              cases hq : q''.2 with
              | true => rw [hq] at h; exact absurd h (by simp)
              | false =>
                  exfalso
                  -- a machine that has met the separator never forgets it
                  rw [sepGuess_step_true] at hmem
                  rw [hq] at hmem
                  exact absurd hmem.1 (by simp)
          | false =>
              obtain ⟨-, -, h1, -⟩ := hflag rfl
              constructor
              · rintro ⟨h2, rfl⟩
                exact ⟨rfl, rfl⟩
              · rintro ⟨-, rfl⟩
                refine ⟨h1.2 ?_, rfl⟩
                exact fun h => hid h.symm
      · refine ⟨ce, ⟨q''.1, γ', m, by simpa using hβmem, ?_⟩, hreach⟩
        have htape : Function.update (Function.update ce.tape dh β) dh γ' = ce.tape := by
          funext i
          by_cases hid : i = dh
          · subst hid; simp [hce]
          · simp [Function.update_of_ne hid]
        cases ce with
        | mk st hd tp =>
            simp only at hces hceh htape
            subst hces hceh
            simp [htape]

/-- **Guessing the part behind the separator is free.**  A machine that never writes a blank
accepts `x`, the separator and some string `z` of length `K + 1` within `K` steps if and only if
its separator-guessing variant accepts `x` alone within `K` steps. -/
theorem acceptsWithin_sepGuess_iff {M : NTM Q (Option Bool)} (hba : BlankAvoiding M)
    (hblank : M.blank = none) (x : List Bool) (K : ℕ) :
    (sepGuess M).AcceptsWithin (x.map some) K ↔
      ∃ z : List Bool, z.length = K + 1 ∧ M.AcceptsWithin (sepTape x z) K := by
  have hd0 : ∀ i, ((sepGuess M).initConfig (x.map some)).tape i = (x.map some).getD i none := by
    intro i; simp [initConfig, sepGuess, hblank]
  constructor
  · rintro ⟨n, hn, d', hreach, hacc⟩
    obtain ⟨c, c', hcs, hch, href, hnone, hrun, hstate⟩ :=
      exists_completion_of_sepGuess_reaches hba x.length hreach (by
        intro _
        refine ⟨by simp [initConfig], fun i hi => ?_, ?_⟩
        · rw [hd0, getD_map_some (by simpa using hi)]; simp
        · rw [hd0, getD_map_some_of_le le_rfl])
    simp only [initConfig, sepGuess] at hcs hch hnone
    set z := (List.range (K + 1)).map (fun j => (c.tape (x.length + 1 + j)).getD false) with hz
    refine ⟨z, by simp [hz], ?_⟩
    have hag : ∀ i ≤ c.head + n, (M.initConfig (sepTape x z)).tape i = c.tape i := by
      intro i hi
      simp only [initConfig, hblank]
      rcases lt_trichotomy i x.length with hix | rfl | hix
      · rw [getD_sepTape_lt hix]
        rcases href i with h | h
        · rw [hd0, getD_map_some (by simpa using hix)] at h; simp at h
        · rw [hd0] at h; exact h
      · rw [getD_sepTape_sep]; exact ((hnone _).2 (by simp)).symm
      · obtain ⟨j, rfl⟩ : ∃ j, i = x.length + 1 + j := ⟨i - x.length - 1, by omega⟩
        rw [getD_sepTape_right, getD_map_some (by simp [hz]; omega)]
        simp only [hz, List.getElem_map, List.getElem_range]
        cases hc : c.tape (x.length + 1 + j) with
        | none =>
            have := (hnone _).1 hc
            simp at this
            omega
        | some b => rfl
    obtain ⟨e', hreach', hstate'⟩ := reaches_congr M hrun (by simp [initConfig, hcs])
      (by simp [initConfig, hch]) hag
    refine ⟨n, hn, e', hreach', ?_⟩
    rw [hstate', hstate]; exact hacc
  · rintro ⟨z, hzlen, n, hn, c', hrun, hacc⟩
    have hc0 : ∀ i, (M.initConfig (sepTape x z)).tape i = (sepTape x z).getD i none := by
      intro i; simp [initConfig, hblank]
    obtain ⟨d', hr, hd'⟩ := sepGuess_reaches_of_reaches hba x.length hrun
      (d := (sepGuess M).initConfig (x.map some)) rfl rfl (by
        intro i
        rw [hd0, hc0]
        rcases lt_or_ge i x.length with hix | hix
        · right; rw [getD_sepTape_lt hix]
        · left; exact getD_map_some_of_le (by simpa using hix)) (by
        intro _
        refine ⟨by simp [initConfig], by rw [hd0, getD_map_some_of_le le_rfl],
          by rw [hc0, getD_sepTape_sep], fun i hi => ?_, fun i hi hin => ?_⟩
        · rw [hd0, getD_map_some (by simpa using hi)]; simp
        · rw [hc0]
          rcases lt_or_gt_of_ne hin with hix | hix
          · rw [getD_sepTape_lt hix, getD_map_some (by simpa using hix)]; simp
          · obtain ⟨j, rfl⟩ : ∃ j, i = x.length + 1 + j := ⟨i - x.length - 1, by omega⟩
            simp only [initConfig] at hi
            rw [getD_sepTape_right, getD_map_some (by omega)]; simp) (by simp [initConfig, sepGuess])
    refine ⟨n, hn, d', hr, ?_⟩
    show d'.state.1 ∈ M.accept
    rw [hd']; exact hacc

/-- The separator-guessing variant never writes a blank either. -/
lemma BlankAvoiding.sepGuess {M : NTM Q (Option Bool)} (h : BlankAvoiding M) :
    BlankAvoiding (NTM.sepGuess M) := by
  rintro ⟨q, f⟩ γ ⟨q', γ', m⟩ ht
  cases f with
  | true =>
      rw [sepGuess_step_true] at ht
      exact h.guess q γ _ ht.2
  | false =>
      cases γ with
      | none => exact h q none _ ((sepGuess_step_false_none M q q' γ' m).1 ht).2
      | some b => exact h q (some b) _ ((sepGuess_step_false_some M q b q' γ' m).1 ht).2

@[simp] lemma sepGuess_blank (M : NTM Q (Option Bool)) : (sepGuess M).blank = M.blank := rfl

/-! ### Relabelling the states -/

/-- **Relabel the states of a machine along a bijection.** -/
def relabel {Q' Γ : Type*} (e : Q ≃ Q') (N : NTM Q Γ) : NTM Q' Γ where
  step q γ := (fun t : Q × Γ × Move => (e t.1, t.2)) '' N.step (e.symm q) γ
  init := e N.init
  accept := e.symm ⁻¹' N.accept
  blank := N.blank

/-- A configuration with relabelled state. -/
def Config.relabel {Q' Γ : Type*} (e : Q ≃ Q') (c : Config Q Γ) : Config Q' Γ :=
  ⟨e c.state, c.head, c.tape⟩

lemma relabel_reaches {Q' Γ : Type*} (e : Q ≃ Q') (N : NTM Q Γ) :
    ∀ {n : ℕ} {c c' : Config Q Γ}, N.Reaches n c c' →
      (relabel e N).Reaches n (Config.relabel e c) (Config.relabel e c') := by
  intro n
  induction n with
  | zero => intro c c' h; rw [show c = c' from h]; rfl
  | succ n ih =>
      intro c c' h
      obtain ⟨d, ⟨q', γ', m, hmem, rfl⟩, hd⟩ := h
      refine ⟨_, ⟨e q', γ', m, ?_, rfl⟩, ih hd⟩
      exact ⟨(q', γ', m), by simpa [Config.relabel] using hmem, rfl⟩

lemma reaches_of_relabel {Q' Γ : Type*} (e : Q ≃ Q') (N : NTM Q Γ) :
    ∀ {n : ℕ} {c c' : Config Q' Γ}, (relabel e N).Reaches n c c' →
      N.Reaches n (Config.relabel e.symm c) (Config.relabel e.symm c') := by
  intro n
  induction n with
  | zero => intro c c' h; rw [show c = c' from h]; rfl
  | succ n ih =>
      intro c c' h
      obtain ⟨d, ⟨q', γ', m, hmem, rfl⟩, hd⟩ := h
      obtain ⟨⟨a, b, c₀⟩, hmem, hq⟩ := hmem
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      refine ⟨_, ⟨a, b, c₀, by simpa [Config.relabel] using hmem, ?_⟩, ih hd⟩
      simp [Config.relabel]

/-- **Relabelling the states does not change acceptance.** -/
theorem acceptsWithin_relabel_iff {Q' Γ : Type*} (e : Q ≃ Q') (N : NTM Q Γ) (w : List Γ)
    (K : ℕ) : (relabel e N).AcceptsWithin w K ↔ N.AcceptsWithin w K := by
  constructor
  · rintro ⟨n, hn, c, hc, hacc⟩
    have := reaches_of_relabel e N hc
    exact ⟨n, hn, Config.relabel e.symm c, by simpa [Config.relabel, initConfig, relabel] using this,
      hacc⟩
  · rintro ⟨n, hn, c, hc, hacc⟩
    refine ⟨n, hn, _, relabel_reaches e N hc, ?_⟩
    simpa [Config.relabel, relabel] using hacc

end NTM

end TM
