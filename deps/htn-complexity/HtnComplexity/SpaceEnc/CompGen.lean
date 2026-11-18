import HtnComplexity.SpaceEnc.SoundInv
/-!
# Completeness of the encoding: building a plan step by step

The completeness proof builds an executable refinement backwards: a *world* (a state, the
remaining words of the two loops, the remaining finish word) from which an invariant always
allows one more executable step (`HTN.SpaceEnc.WStep`) until everything is consumed has an
executable interleaving of its words (`HTN.SpaceEnc.exists_plan`).
-/

namespace HTN

namespace SpaceEnc

variable {F α : Type*}

/-! ### Converse step lemmas for the interleavings -/

theorem cs_allE {bs : List (List (List α))} (h : AllE bs) : CS bs [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    exact ⟨[], [], InterleaveList.of_forall_nil (h b (List.mem_cons_self ..)),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx), rfl⟩

theorem cs_append_allE {e bs : List (List (List α))} {z : List α} (he : AllE e) (h : CS bs z) :
    CS (e ++ bs) z := by
  induction e with
  | nil => exact h
  | cons b e ih =>
    exact ⟨[], z, InterleaveList.of_forall_nil (he b (List.mem_cons_self ..)),
      ih fun x hx => he x (List.mem_cons_of_mem _ hx), rfl⟩

theorem cs_cons_of {e rest : List (List (List α))} {bl : List (List α)} {i : ℕ} {a : α}
    {t z : List α} (he : AllE e) (hi : bl[i]? = some (a :: t)) (h : CS (bl.set i t :: rest) z) :
    CS (e ++ bl :: rest) (a :: z) := by
  refine cs_append_allE he ?_
  obtain ⟨z₁, z₂, h₁, h₂, rfl⟩ := h
  exact ⟨a :: z₁, z₂, interleaveList_cons_of hi h₁, h₂, rfl⟩

theorem g_cons_of {bs : Bool → List (List (List α))} {φ : List α} {q : Bool}
    {e rest : List (List (List α))} {bl : List (List α)} {i : ℕ} {a : α} {t z : List α}
    (hbq : bs q = e ++ bl :: rest) (he : AllE e) (hi : bl[i]? = some (a :: t))
    (h : G (Function.update bs q (bl.set i t :: rest)) φ z) : G bs φ (a :: z) := by
  obtain ⟨zA, zB, zBF, hA, hB, h3, h4⟩ := h
  cases q
  · simp only [Function.update_self, ne_eq, Bool.true_eq_false, not_false_eq_true,
      Function.update_of_ne] at hA hB
    refine ⟨zA, a :: zB, a :: zBF, hA, ?_, Interleave.left a h3, Interleave.right a h4⟩
    rw [hbq]; exact cs_cons_of he hi hB
  · simp only [Function.update_self, ne_eq, Bool.false_eq_true, not_false_eq_true,
      Function.update_of_ne] at hA hB
    refine ⟨a :: zA, zB, zBF, ?_, hB, h3, Interleave.left a h4⟩
    rw [hbq]; exact cs_cons_of he hi hA

theorem g_cons_phi {bs : Bool → List (List (List α))} {φ : List α} {a : α} {z : List α}
    (h : G bs φ z) : G bs (a :: φ) (a :: z) := by
  obtain ⟨zA, zB, zBF, hA, hB, h3, h4⟩ := h
  exact ⟨zA, zB, a :: zBF, hA, hB, Interleave.right a h3, Interleave.right a h4⟩

theorem g_final {bs : Bool → List (List (List α))} (h : ∀ q, AllE (bs q)) : G bs [] [] :=
  ⟨[], [], [], cs_allE (h true), cs_allE (h false), Interleave.nil, Interleave.nil⟩

/-! ### Worlds -/

/-- A world: a state, the remaining words of the two loops and the remaining finish word. -/
structure World (F α : Type*) where
  /-- The state. -/
  s : Set F
  /-- The remaining blocks of the two loops. -/
  bs : Bool → List (List (List α))
  /-- The remaining finish word. -/
  φ : List α

/-- The number of remaining actions of a list of blocks. -/
def blocksSize (bs : List (List (List α))) : ℕ := (bs.map fun bl => (bl.map List.length).sum).sum

/-- The number of remaining actions of a world. -/
def World.size (wd : World F α) : ℕ :=
  blocksSize (wd.bs true) + blocksSize (wd.bs false) + wd.φ.length

/-- A world is consumed. -/
def World.Final (wd : World F α) : Prop := (∀ q, AllE (wd.bs q)) ∧ wd.φ = []

/-- **One executable step of a world**: an applicable action that is the head of a word of the
first unfinished block of a loop, or of the finish word. -/
def WStep (δ : ActionModel F α) (wd wd' : World F α) : Prop :=
  ∃ a, δ.Applicable a wd.s ∧ wd'.s = δ.transition a wd.s ∧
    ((∃ q E bl rest i t, wd.bs q = E ++ bl :: rest ∧ AllE E ∧ bl[i]? = some (a :: t) ∧
        wd'.bs = Function.update wd.bs q (bl.set i t :: rest) ∧ wd'.φ = wd.φ) ∨
      (wd.φ = a :: wd'.φ ∧ wd'.bs = wd.bs))

theorem blocksSize_allE {E : List (List (List α))} (h : AllE E) : blocksSize E = 0 := by
  induction E with
  | nil => rfl
  | cons b E ih =>
    have hb : (b.map List.length).sum = 0 := by
      have := h b (List.mem_cons_self ..)
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      simp [this v hv]
    simp only [blocksSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [hb, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem sum_set_length {bl : List (List α)} {i : ℕ} {a : α} {t : List α}
    (hi : bl[i]? = some (a :: t)) :
    ((bl.set i t).map List.length).sum + 1 = (bl.map List.length).sum := by
  induction bl generalizing i with
  | nil => simp at hi
  | cons v bl ih =>
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simp; omega
    · simp only [List.getElem?_cons_succ] at hi
      have := ih hi
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

theorem blocksSize_step {bs E rest : List (List (List α))} {bl : List (List α)} {i : ℕ} {a : α}
    {t : List α} (hbq : bs = E ++ bl :: rest) (hE : AllE E) (hi : bl[i]? = some (a :: t)) :
    blocksSize (bl.set i t :: rest) + 1 = blocksSize bs := by
  subst hbq
  have h1 := blocksSize_allE hE
  have h2 := sum_set_length hi
  simp only [blocksSize, List.map_append, List.sum_append, List.map_cons, List.sum_cons] at h1 ⊢
  omega

theorem WStep.size_lt {δ : ActionModel F α} {wd wd' : World F α} (h : WStep δ wd wd') :
    wd'.size < wd.size := by
  obtain ⟨a, -, -, ⟨q, E, bl, rest, i, t, hbq, hE, hi, hbs, hφ⟩ | ⟨hφ, hbs⟩⟩ := h
  · have := blocksSize_step hbq hE hi
    unfold World.size
    rw [hbs, hφ]
    cases q
    · simp only [Function.update_self, ne_eq, Bool.true_eq_false, not_false_eq_true,
        Function.update_of_ne]
      omega
    · simp only [Function.update_self, ne_eq, Bool.false_eq_true, not_false_eq_true,
        Function.update_of_ne]
      omega
  · unfold World.size
    rw [hbs, hφ]
    simp

/-- **A world from which an invariant always allows an executable step has an executable
interleaving of all its words.** -/
theorem exists_plan (δ : ActionModel F α) (P : World F α → Prop)
    (hP : ∀ wd, P wd → wd.Final ∨ ∃ wd', WStep δ wd wd' ∧ P wd') :
    ∀ wd, P wd → ∃ z, G wd.bs wd.φ z ∧ δ.SeqApplicable z wd.s := by
  intro wd
  induction h : wd.size using Nat.strong_induction_on generalizing wd with
  | _ n ih =>
    intro hwd
    rcases hP wd hwd with ⟨hall, hφ⟩ | ⟨wd', hstep, hwd'⟩
    · exact ⟨[], by rw [hφ]; exact g_final hall, trivial⟩
    · obtain ⟨z, hG, hseq⟩ := ih wd'.size (h ▸ hstep.size_lt) wd' rfl hwd'
      obtain ⟨a, happ, hs, ⟨q, E, bl, rest, i, t, hbq, hE, hi, hbs, hφ⟩ | ⟨hφ, hbs⟩⟩ := hstep
      · refine ⟨a :: z, g_cons_of hbq hE hi ?_, happ, ?_⟩
        · rw [← hbs, ← hφ]; exact hG
        · rw [← hs]; exact hseq
      · refine ⟨a :: z, ?_, happ, ?_⟩
        · rw [hφ, ← hbs]; exact g_cons_phi hG
        · rw [← hs]; exact hseq

end SpaceEnc

end HTN
