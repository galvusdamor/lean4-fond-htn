import FondHtn.DB25.WinK
/-!
# Networks ordered by phases

A network is **phase ordered** by `ph : I → ℕ` if `a ≺ b ↔ ph a < ph b` on its tasks: the tasks of
one phase are unordered, and every phase precedes the next.  Executing it is executing the phases
one after the other (`FOND.Problem.winK_phases`).
-/

namespace FOND

open HTN FOND.TaskNetwork

namespace Problem

variable {F A C I : Type} [DecidableEq I] (P : Problem F A C I)

/-- Phase order. -/
def PhaseOrd (tn : HTN.TaskNetwork I A C) (ph : I → ℕ) : Prop :=
  ∀ a ∈ tn.T, ∀ b ∈ tn.T, tn.ord a b ↔ ph a < ph b

/-- Executing the phases `i, …, i + c - 1` one after the other. -/
def nestW (tn : HTN.TaskNetwork I A C) (ph : I → ℕ) : ℕ → ℕ → (Set F → Prop) → Set F → Prop
  | _, 0, K => K
  | i, c + 1, K => P.WinK (nestW tn ph (i + 1) c K) (restr tn fun x => ph x = i)

variable {P}

theorem winK_phases_aux {tn : HTN.TaskNetwork I A C} {ph : I → ℕ} (hph : PhaseOrd tn ph) :
    ∀ (c i : ℕ) (K : Set F → Prop) (s : Set F), (∀ x ∈ tn.T, ph x < i + c) →
      (P.WinK K (restr tn fun x => i ≤ ph x) s ↔ P.nestW tn ph i c K s) := by
  intro c
  induction c with
  | zero =>
    intro i K s hlt
    have hE : (restr tn fun x => i ≤ ph x).T = ∅ := by
      ext x; simp only [mem_restr_T, Finset.notMem_empty, iff_false, not_and, not_le]
      intro hx; simpa using hlt x hx
    rw [winK_empty_iff hE]; rfl
  | succ c ih =>
    intro i K s hlt
    have hB : Before (fun x => ph x = i) (restr tn fun x => i ≤ ph x) := by
      refine ⟨fun a ha b hb hSa hSb => ?_, fun a ha b hb hSa hSb hab => ?_⟩
      · obtain ⟨ha1, ha2⟩ := (mem_restr_T _ _).1 ha
        obtain ⟨hb1, hb2⟩ := (mem_restr_T _ _).1 hb
        exact ⟨(hph a ha1 b hb1).2 (by omega), ha2, hb2⟩
      · obtain ⟨ha1, ha2⟩ := (mem_restr_T _ _).1 ha
        obtain ⟨hb1, hb2⟩ := (mem_restr_T _ _).1 hb
        have := (hph a ha1 b hb1).1 hab.1; omega
    rw [winK_split _ hB]
    have h1 : SameOn (restr (restr tn fun x => i ≤ ph x) fun x => ph x = i)
        (restr tn fun x => ph x = i) := by
      refine ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩
      · ext x; simp only [mem_restr_T]; constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
      · simp only [mem_restr_T] at ha hb
        simp only [restr]
        constructor
        · rintro ⟨⟨h, -, -⟩, h2, h3⟩; exact ⟨h, h2, h3⟩
        · rintro ⟨h, h2, h3⟩; exact ⟨⟨h, by omega, by omega⟩, h2, h3⟩
    have h2 : SameOn (restr (restr tn fun x => i ≤ ph x) fun x => ¬ ph x = i)
        (restr tn fun x => i + 1 ≤ ph x) := by
      refine ⟨?_, fun a ha b hb => ?_, fun _ _ => rfl⟩
      · ext x; simp only [mem_restr_T]; constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
      · simp only [mem_restr_T] at ha hb
        simp only [restr]
        constructor
        · rintro ⟨⟨h, -, -⟩, -, -⟩; exact ⟨h, by omega, by omega⟩
        · rintro ⟨h, -, -⟩; exact ⟨⟨h, by omega, by omega⟩, by omega, by omega⟩
    have hK : P.WinK K (restr (restr tn fun x => i ≤ ph x) fun x => ¬ ph x = i) =
        P.nestW tn ph (i + 1) c K := funext fun s' => propext
          ((show P.WinK K (restr (restr tn fun x => i ≤ ph x) fun x => ¬ ph x = i) s' ↔
              P.WinK K (restr tn fun x => i + 1 ≤ ph x) s' from
            ⟨fun h => h.congr h2, fun h => h.congr h2.symm'⟩).trans
            (ih (i + 1) K s' fun x hx => by have := hlt x hx; omega))
    rw [hK, nestW]
    exact ⟨fun h => h.congr h1, fun h => h.congr h1.symm'⟩

/-- **Executing a phase-ordered network** is executing its phases one after the other. -/
theorem winK_phases {tn : HTN.TaskNetwork I A C} {ph : I → ℕ} (hph : PhaseOrd tn ph) {c : ℕ}
    (hlt : ∀ x ∈ tn.T, ph x < c) (K : Set F → Prop) (s : Set F) :
    P.WinK K tn s ↔ P.nestW tn ph 0 c K s := by
  rw [← winK_phases_aux hph c 0 K s (by simpa using hlt)]
  have : SameOn tn (restr tn fun x => 0 ≤ ph x) :=
    ⟨by ext x; simp, fun a _ b _ => by simp [restr], fun _ _ => rfl⟩
  exact ⟨fun h => h.congr this, fun h => h.congr this.symm'⟩

end Problem

end FOND

/-! ## Unordered phases as games on lists of actions -/

namespace FOND

namespace Problem

variable {F : Type}

/-- The game on an unordered list of actions: execute them all, in an order chosen online. -/
def setWin (K : Set F → Prop) : List (Action F) → Set F → Prop
  | [], s => K s
  | a :: as, s => ∃ i, ∃ h : i < (a :: as).length, ((a :: as)[i]).Applicable s ∧
      ∀ s' ∈ ((a :: as)[i]).outcomes s, setWin K ((a :: as).eraseIdx i) s'
termination_by l => l.length
decreasing_by all_goals (simp only [List.length_cons] at h; simp only [List.length_eraseIdx, List.length_cons]; split_ifs <;> omega)

theorem setWin_nil (K : Set F → Prop) (s : Set F) : setWin K [] s ↔ K s := by
  rw [setWin]

theorem setWin_ne_nil (K : Set F → Prop) {l : List (Action F)} (hl : l ≠ []) (s : Set F) :
    setWin K l s ↔ ∃ i, ∃ h : i < l.length, (l[i]).Applicable s ∧
      ∀ s' ∈ (l[i]).outcomes s, setWin K (l.eraseIdx i) s' := by
  obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [setWin]

theorem setWin_single (K : Set F → Prop) (a : Action F) (s : Set F) :
    setWin K [a] s ↔ a.Applicable s ∧ ∀ s' ∈ a.outcomes s, K s' := by
  rw [setWin_ne_nil K (by simp)]
  constructor
  · rintro ⟨i, hi, happ, hall⟩
    obtain rfl : i = 0 := by simpa using hi
    exact ⟨happ, fun s' hs' => (setWin_nil K s').1 (by simpa using hall s' hs')⟩
  · rintro ⟨happ, hall⟩
    exact ⟨0, by simp, happ, fun s' hs' => by simpa [setWin_nil] using hall s' hs'⟩

theorem setWin_pair (K : Set F → Prop) (a b : Action F) (s : Set F) :
    setWin K [a, b] s ↔
      (a.Applicable s ∧ ∀ s' ∈ a.outcomes s, b.Applicable s' ∧ ∀ s'' ∈ b.outcomes s', K s'') ∨
      (b.Applicable s ∧ ∀ s' ∈ b.outcomes s, a.Applicable s' ∧ ∀ s'' ∈ a.outcomes s', K s'') := by
  rw [setWin_ne_nil K (by simp)]
  constructor
  · rintro ⟨i, hi, happ, hall⟩
    have : i = 0 ∨ i = 1 := by simp at hi; omega
    rcases this with rfl | rfl
    · exact Or.inl ⟨happ, fun s' hs' => (setWin_single K b s').1 (by simpa using hall s' hs')⟩
    · exact Or.inr ⟨happ, fun s' hs' => (setWin_single K a s').1 (by simpa using hall s' hs')⟩
  · rintro (⟨happ, hall⟩ | ⟨happ, hall⟩)
    · exact ⟨0, by simp, happ, fun s' hs' => by simpa using (setWin_single K b s').2 (hall s' hs')⟩
    · exact ⟨1, by simp, happ, fun s' hs' => by simpa using (setWin_single K a s').2 (hall s' hs')⟩

variable {A C I : Type} [DecidableEq I] {P : Problem F A C I}

/-- **An unordered network is the game on the list of its actions.** -/
theorem winK_iff_setWin {K : Set F → Prop} : ∀ (n : ℕ) (tn : HTN.TaskNetwork I A C)
    (ids : List I) (acts : List (Action F)) (s : Set F), ids.length = n →
    (∀ a b, ¬ tn.ord a b) → ids.Nodup → tn.T = ids.toFinset → (hlen : ids.length = acts.length) →
    (∀ i (hi : i < ids.length), ∃ a, tn.α ids[i] = Sum.inl a ∧ P.δ a = acts[i]) →
    (P.WinK K tn s ↔ setWin K acts s) := by
  intro n
  induction n with
  | zero =>
    intro tn ids acts s hn _ _ hT hlen _
    have hids : ids = [] := List.eq_nil_of_length_eq_zero hn
    have hacts : acts = [] := List.eq_nil_of_length_eq_zero (by rw [← hlen, hn])
    subst hids hacts
    rw [setWin_nil, winK_empty_iff (by simp [hT])]
  | succ n ih =>
    intro tn ids acts s hn hno hnd hT hlen hact
    have hne : acts ≠ [] := fun h => by subst h; simp at hlen; subst hlen; simp at hn
    rw [setWin_ne_nil K hne]
    -- progress by `ids[i]`
    have hprog : ∀ i (hi : i < ids.length), ∀ s', P.WinK K (tn.progress ids[i]) s' ↔
        setWin K (acts.eraseIdx i) s' := fun i hi s' =>
      ih _ (ids.eraseIdx i) _ s' (by simp [List.length_eraseIdx, hi]; omega)
        (fun a b h => hno a b h.1) (hnd.eraseIdx i)
        (by rw [HTN.TaskNetwork.progress_T, hT, ← List.Nodup.erase_getElem hnd i hi]
            ext x; simp [hnd.mem_erase_iff])
        (by simp [List.length_eraseIdx, hi, hlen])
        (fun j hj => by
          have hj' : j < ids.length - 1 := by simpa [List.length_eraseIdx, hi] using hj
          simp only [HTN.TaskNetwork.progress]
          by_cases h1 : j < i
          · rw [List.getElem_eraseIdx_of_lt _ h1, List.getElem_eraseIdx_of_lt _ h1]
            exact hact j (by omega)
          · rw [List.getElem_eraseIdx_of_ge _ (by omega), List.getElem_eraseIdx_of_ge _ (by omega)]
            exact hact (j + 1) (by omega))
    constructor
    · intro hw
      cases hw with
      | empty h => rw [hT] at h; simp at h; subst h; simp at hn
      | @step _ _ t a hu hα happ hall =>
        have htm : t ∈ ids := by have := hu.1; rw [hT] at this; simpa using this
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem htm
        obtain ⟨a', hα', hδ⟩ := hact i hi
        rw [hα] at hα'; cases hα'
        refine ⟨i, by omega, hδ ▸ happ, fun s' hs' => (hprog i hi s').1 (hall s' (hδ ▸ hs'))⟩
    · rintro ⟨i, hi, happ, hall⟩
      have hi' : i < ids.length := by omega
      obtain ⟨a, hα, hδ⟩ := hact i hi'
      refine .step (t := ids[i]) (a := a) ⟨by rw [hT]; simp, fun t' _ h => hno _ _ h⟩ hα
        (hδ ▸ happ) fun s' hs' => (hprog i hi' s').2 (hall s' (hδ ▸ hs'))

end Problem

end FOND
