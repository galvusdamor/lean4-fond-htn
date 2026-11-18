import HtnComplexity.AcVerify.VerSem1
import HtnComplexity.AcVerify.Complete
/-!
# Semantics of the verifier, part 2: the record test is `EntryOK`

`HTN.Syn.AcVer.recs_iff_entryOK0`: the condition `recsB_iff` puts on the step list of an entry is
exactly `EntryOK`, together with the normalisation that the dummy step of an empty leaf has the
task identifier `0`.
-/

namespace HTN

namespace Syn

namespace AcVer

variable {d : DomDesc} {q : InstDesc}

/-- **A well-formed entry with a normalised dummy step.** -/
def EntryOK0 (d : DomDesc) (q : InstDesc) (u : Entry) : Prop :=
  EntryOK d q u ∧ (u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)])

theorem mIdx_ne_zero {k : ℕ} (hk : k ∈ mIdx d) : k ≠ 0 := by
  have := (mem_mIdx.1 hk).1; omega

theorem netOf_of_ne {k : ℕ} (hk : k ≠ 0) : netOf d q k = (methodAt d k).2 := by
  simp [netOf, hk]

theorem stepIn_of_mstep {x : PStep} (h : IsMStep d x) : StepIn d q x := by
  unfold StepIn; rw [netOf_of_ne (mIdx_ne_zero h.1)]; exact h.2

theorem mIdx_of_link {x y : PStep} (hl : Link d q x y) : y.1 ∈ mIdx d :=
  mem_mIdx.2 ⟨hl.1, hl.2.1⟩

theorem mstep_of_link {x y : PStep} (hl : Link d q x y) (hs : StepIn d q y) : IsMStep d y := by
  have hk := mIdx_of_link hl
  refine ⟨hk, ?_⟩
  have := hs; unfold StepIn at this; rwa [netOf_of_ne (mIdx_ne_zero hk)] at this

theorem dummy_of_link {x y : PStep} (hl : Link d q x y) (he : (netOf d q y.1).ids = [])
    (h0 : y.2 = 0) : IsDummy d y := by
  have hk := mIdx_of_link hl
  refine ⟨hk, ?_, h0⟩
  rwa [netOf_of_ne (mIdx_ne_zero hk)] at he

theorem stepIn_root {i : ℕ} (hi : i ∈ q.tnI.ids) : StepIn d q (0, i) := by
  unfold StepIn; simpa [netOf] using hi

theorem snoc_split {P : List PStep} {y : PStep} {l₁ l₂ : List PStep} {x : PStep}
    (h : P ++ [y] = l₁ ++ x :: l₂) :
    (l₂ = [] ∧ l₁ = P ∧ x = y) ∨ (∃ l₂', l₂ = l₂' ++ [y] ∧ P = l₁ ++ x :: l₂') := by
  rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂', z, rfl⟩
  · left
    have h' : P ++ [y] = l₁ ++ [x] := h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    exact ⟨rfl, h1.symm, (List.cons.inj h2).1.symm⟩
  · right
    have h' : P ++ [y] = (l₁ ++ x :: l₂') ++ [z] := by simpa using h
    obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
    obtain rfl := (List.cons.inj h2).1
    exact ⟨l₂', by simp, h1⟩

/-- **The record test is `EntryOK`** (with normalised dummy steps). -/
theorem recs_iff_entryOK0 (p : List PStep) (f : Bool) :
    ((∃ i ∈ q.tnI.ids, ∃ s, p = (0, i) :: s) ∧
        ∀ l₁ x l₂, p = l₁ ++ x :: l₂ → RecBody d q f l₁ x l₂) ↔ EntryOK0 d q (p, f) := by
  constructor
  · rintro ⟨⟨i, hi, s, hps⟩, hb⟩
    have hchain : p.IsChain (Link d q) := isChain_of_splits fun l₁ a b l₂ he =>
      (hb l₁ a (b :: l₂) he).2.1 b l₂ rfl
    have hstep : ∀ l₁ x l₂, p = l₁ ++ x :: l₂ → (l₂ ≠ [] ∨ f = false) → StepIn d q x := by
      intro l₁ x l₂ he hne
      rcases (hb l₁ x l₂ he).1 with rfl | hm | ⟨h2, hf, -⟩
      · rw [hps] at he
        simp only [List.nil_append, List.cons.injEq] at he
        rw [← he.1]; exact stepIn_root hi
      · exact stepIn_of_mstep hm
      · rcases hne with h | h
        · exact absurd h2 h
        · rw [h] at hf; exact absurd hf (by simp)
    obtain ⟨p', x, rfl⟩ : ∃ p' x, p = p' ++ [x] := by
      rcases List.eq_nil_or_concat p with h | ⟨p', x, h⟩
      · rw [hps] at h; exact absurd h (by simp)
      · exact ⟨p', x, by simpa using h⟩
    obtain ⟨hl1, hl2⟩ := (hb p' x [] rfl).2.2 rfl
    cases f
    · refine ⟨?_, fun h => absurd h (by simp)⟩
      simp only [EntryOK, Bool.false_eq_true, if_false]
      refine ⟨⟨⟨i, s, hps⟩, hchain, fun y hy => ?_⟩, ?_⟩
      · obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hy
        exact hstep l₁ y l₂ he (Or.inr rfl)
      · rw [lastLabel_snoc]
        rcases hl1 with h | h
        · exact absurd h (by simp)
        · rcases hlb : stepLabel d q x with a | c
          · exact ⟨a, rfl⟩
          · rw [hlb] at h; simp [lTag] at h
    · rcases hl2 with h | ⟨hp', hdum⟩
      · exact absurd h (by simp)
      refine ⟨?_, fun _ => ⟨p', x.1, by rw [← hdum.2.2]⟩⟩
      simp only [EntryOK, if_true]
      refine ⟨p', x, rfl, hp', ⟨?_, ?_, ?_⟩, hchain, ?_⟩
      · rcases p' with _ | ⟨y, p''⟩
        · exact absurd rfl hp'
        · simp only [List.cons_append, List.cons.injEq] at hps
          exact ⟨i, p'', by rw [hps.1]⟩
      · exact isChain_of_splits fun l₁ a b l₂ he =>
          splits_of_isChain hchain l₁ a b (l₂ ++ [x]) (by rw [he]; simp)
      · intro y hy
        obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hy
        exact hstep l₁ y (l₂ ++ [x]) (by rw [he]; simp) (Or.inl (by simp))
      · rw [netOf_of_ne (mIdx_ne_zero hdum.1)]; exact hdum.2.1
  · rintro ⟨hok, hnorm⟩
    cases f
    · simp only [EntryOK, Bool.false_eq_true, if_false] at hok
      obtain ⟨⟨⟨i, s, hps⟩, hchain, hin⟩, a, ha⟩ := hok
      have hi : i ∈ q.tnI.ids := by
        have := hin (0, i) (by rw [hps]; simp)
        simpa [StepIn, netOf] using this
      refine ⟨⟨i, hi, s, hps⟩, fun l₁ x l₂ he => ⟨?_, ?_, ?_⟩⟩
      · rcases List.eq_nil_or_concat l₁ with rfl | ⟨l₁', w, rfl⟩
        · exact Or.inl rfl
        · refine Or.inr (Or.inl (mstep_of_link (x := w) ?_ (hin x (by rw [he]; simp))))
          exact splits_of_isChain hchain l₁' w x l₂ (by rw [he]; simp)
      · rintro y l₂' rfl
        exact splits_of_isChain hchain l₁ x y l₂' he
      · rintro rfl
        refine ⟨Or.inr ?_, Or.inl rfl⟩
        rw [he, lastLabel_snoc] at ha
        rw [ha]; rfl
    · simp only [EntryOK, if_true] at hok
      obtain ⟨P, y, hpy, hP, ⟨⟨i, s, hPs⟩, hcP, hinP⟩, hchain, hemp⟩ := hok
      obtain ⟨P', k, hP'⟩ := hnorm rfl
      have hy0 : y.2 = 0 := by
        rw [hpy] at hP'
        obtain ⟨-, h⟩ := List.append_inj' hP' rfl
        rw [(List.cons.inj h).1]
      have hi : i ∈ q.tnI.ids := by
        have := hinP (0, i) (by rw [hPs]; simp)
        simpa [StepIn, netOf] using this
      have hlast : Link d q (P.getLast hP) y := by
        obtain ⟨P₀, w, hw⟩ := List.eq_nil_or_concat P |>.resolve_left hP
        have : P.getLast hP = w := by simp [hw]
        rw [this]
        exact splits_of_isChain hchain P₀ w y [] (by rw [hpy, hw]; simp)
      refine ⟨⟨i, hi, s ++ [y], by rw [hpy, hPs]; simp⟩, fun l₁ x l₂ he => ?_⟩
      rw [hpy] at he hchain
      rcases snoc_split he with ⟨rfl, rfl, rfl⟩ | ⟨l₂', rfl, rfl⟩
      · have hd := dummy_of_link hlast hemp hy0
        exact ⟨Or.inr (Or.inr ⟨rfl, rfl, hd⟩), fun _ _ h => absurd h (by simp),
          fun _ => ⟨Or.inl rfl, Or.inr ⟨hP, hd⟩⟩⟩
      · refine ⟨?_, ?_, fun h => absurd h (by simp)⟩
        · rcases List.eq_nil_or_concat l₁ with rfl | ⟨l₁', w, rfl⟩
          · exact Or.inl rfl
          · refine Or.inr (Or.inl (mstep_of_link (x := w) ?_ (hinP x (by simp))))
            exact splits_of_isChain hcP l₁' w x l₂' (by simp)
        · intro z l₂'' hz
          exact splits_of_isChain hchain l₁ x z l₂'' (by rw [he]; simp [hz])

end AcVer

end Syn

end HTN
