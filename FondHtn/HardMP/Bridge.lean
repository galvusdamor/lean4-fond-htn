import FondHtn.HardMP.ListGame
/-!
# From the AND/OR game to the leftmost list game

For a well-formed problem all of whose methods are totally ordered, and whose initial task
network is a sequence network with labels `xs`, strong method-based solvability ([CB22]) is the
leftmost list game `FOND.Problem.LRunH` on `xs` (`FOND.Problem.mpStrongSolvable_iff_lrunH`).

* Soundness: induction on the graded AND/OR game; a decomposition at an arbitrary position is
  moved to the front in the list world (`FOND.Problem.lrunH_undelay`).
* Completeness: the leftmost moves are moves of the AND/OR game (fresh copies exist).
-/

namespace FOND

open HTN HTN.TaskNetwork

universe u v w x

variable {F : Type u} {A : Type v} {C : Type w} {I : Type x}

namespace Problem

/-! ### Sequence networks and progression -/

section Seq

variable [DecidableEq I]

theorem isSeqNet_progress {tn : TaskNetwork I A C} {t : I} {l : List I} {y : A ⊕ C}
    {xs : List (A ⊕ C)} (h : tn.IsSeqNet (t :: l) (y :: xs)) : (tn.progress t).IsSeqNet l xs := by
  have hnd := List.nodup_cons.1 h.nodup
  refine ⟨hnd.2, fun z => ?_, ?_, fun a b => ?_⟩
  · rw [mem_progress_T, h.memT z, List.mem_cons]
    constructor
    · rintro ⟨hz, rfl | hz'⟩
      · exact absurd rfl hz
      · exact hz'
    · intro hz; exact ⟨fun e => hnd.1 (e ▸ hz), Or.inr hz⟩
  · have := h.labels
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2
  · rw [progress_ord, h.ord a b]
    constructor
    · rintro ⟨⟨ha, hb, hlt⟩, hat⟩
      have ha' : a ∈ l := (List.mem_cons.1 ha).resolve_left hat
      rw [List.idxOf_cons_ne _ (fun e => hat e.symm)] at hlt
      by_cases hbt : b = t
      · subst hbt; simp at hlt
      · have hb' : b ∈ l := (List.mem_cons.1 hb).resolve_left hbt
        rw [List.idxOf_cons_ne _ (fun e => hbt e.symm)] at hlt
        exact ⟨ha', hb', by omega⟩
    · rintro ⟨ha, hb, hlt⟩
      have hat : a ≠ t := fun e => hnd.1 (e ▸ ha)
      have hbt : b ≠ t := fun e => hnd.1 (e ▸ hb)
      refine ⟨⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, ?_⟩, hat⟩
      rw [List.idxOf_cons_ne _ (fun e => hat e.symm), List.idxOf_cons_ne _ (fun e => hbt e.symm)]
      omega

theorem eq_cons_of_unconstrained {tn : TaskNetwork I A C} {l : List I} {xs : List (A ⊕ C)}
    (h : tn.IsSeqNet l xs) {t : I} (hu : tn.Unconstrained t) : ∃ l', l = t :: l' := by
  have htl : t ∈ l := (h.memT t).1 hu.1
  rcases l with _ | ⟨y, l'⟩
  · simp at htl
  · by_cases hty : t = y
    · exact ⟨l', by rw [hty]⟩
    · exfalso
      apply hu.2 y (h.mem_of_mem (by simp))
      refine (h.ord y t).2 ⟨by simp, htl, ?_⟩
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (fun e => hty e.symm)]
      omega

theorem unconstrained_head {tn : TaskNetwork I A C} {t : I} {l : List I} {xs : List (A ⊕ C)}
    (h : tn.IsSeqNet (t :: l) xs) : tn.Unconstrained t := by
  refine ⟨h.mem_of_mem (by simp), fun t' _ hord => ?_⟩
  have := ((h.ord t' t).1 hord).2.2
  rw [List.idxOf_cons_self] at this
  omega

end Seq

/-! ### Undelaying decompositions in the list world -/

variable {P : Problem F A C I}

theorem lrunH_undelay {c : C} {bs xs₂ : List (A ⊕ C)} (hb : P.SeqBodyF c bs)
    {n : ℕ} {l : List (A ⊕ C)} {s : Set F} {Φ : Set (Set F)} (h : P.LRunH n l s Φ) :
    ∀ xs₁ : List (A ⊕ C), l = xs₁ ++ bs ++ xs₂ →
      P.LRunH (n + 1) (xs₁ ++ Sum.inr c :: xs₂) s Φ := by
  induction h with
  | @nil n s Φ hs =>
    intro xs₁ he
    have h1 := List.append_eq_nil_iff.1 he.symm
    obtain ⟨h2, h3⟩ := List.append_eq_nil_iff.1 h1.1
    subst h2 h3; rw [h1.2]
    exact .comp hb (.nil hs)
  | @prim n a l s Φ happ hall ih =>
    intro xs₁ he
    rcases xs₁ with _ | ⟨z, xs₁⟩
    · exact .comp hb (by rw [List.nil_append] at he; rw [← he]; exact .prim happ hall)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .prim happ fun s' hs' => ih s' hs' xs₁ (by rw [List.append_assoc])
  | @comp n c' bs' l s Φ hb' h ih =>
    intro xs₁ he
    rcases xs₁ with _ | ⟨z, xs₁⟩
    · exact .comp hb (by rw [List.nil_append] at he; rw [← he]; exact .comp hb' h)
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .comp hb' (by
        have := ih (bs' ++ xs₁) (by simp [List.append_assoc])
        simpa [List.append_assoc] using this)

/-! ### Soundness and completeness -/

variable [DecidableEq I]

theorem lrunH_of_mpAndOrH [Nonempty I] (hP : P.WF)
    (hM : ∀ m ∈ P.methods, m.subtasks.IsTotallyOrdered) {n : ℕ} {tn : TaskNetwork I A C}
    {s : Set F} (h : P.MPAndOrH n tn s) :
    ∀ {l : List I} {xs : List (A ⊕ C)}, tn.IsSeqNet l xs → P.LRunH n xs s Set.univ := by
  induction h with
  | @empty n tn s he =>
    intro l xs hs
    have hl : l = [] := List.eq_nil_iff_forall_not_mem.2 fun z hz => by
      have := hs.mem_of_mem hz; rw [he] at this; simp at this
    have := hs.labels
    subst hl
    rw [← this]
    exact .nil trivial
  | @prim n tn s t a hu hα happ _ ih =>
    intro l xs hs
    obtain ⟨l', rfl⟩ := eq_cons_of_unconstrained hs hu
    obtain rfl := hs.labels
    rw [List.map_cons, hα] at hs ⊢
    exact .prim happ fun s' hs' => ih s' hs' (isSeqNet_progress hs)
  | @decomp n tn tn' s t m hd _ ih =>
    intro l xs hs
    obtain ⟨hm, htT, hα, tn'', hw'', hiso, hdisj, rfl⟩ := hd
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ((hs.memT t).1 htT)
    obtain rfl := hs.labels
    obtain ⟨lm₀, bs, hbody⟩ := exists_isSeqNet (hP.methods m hm) (hM m hm)
    obtain ⟨lm, hlm⟩ := hbody.iso hw'' hiso.symm
    have hs' : tn.IsSeqNet (l₁ ++ t :: l₂)
        (l₁.map tn.α ++ Sum.inr m.abstractTask :: l₂.map tn.α) := by
      have := hs; rwa [List.map_append, List.map_cons, hα] at this
    have hnew := isSeqNet_decomposeWith hs' (by simp) hlm hdisj
    have hb : P.SeqBodyF m.abstractTask bs := ⟨m, hm, rfl, Method.hasSeqBody_of_isSeqNet hbody⟩
    rw [List.map_append, List.map_cons, hα]
    exact lrunH_undelay hb (ih hnew) _ rfl

theorem mpAndOr_of_lrunH [Infinite I] (hP : P.WF) {n : ℕ} {xs : List (A ⊕ C)} {s : Set F}
    {Φ : Set (Set F)} (h : P.LRunH n xs s Φ) :
    ∀ {tn : TaskNetwork I A C} {l : List I}, tn.IsSeqNet l xs → P.MPAndOr tn s := by
  induction h with
  | nil =>
    intro tn l hs
    have hl : l = [] := by
      have := congrArg List.length hs.labels; simpa using this
    subst hl
    refine .empty (Finset.eq_empty_of_forall_notMem fun z hz => ?_)
    simpa using (hs.memT z).1 hz
  | @prim n a xs s Φ happ _ ih =>
    intro tn l hs
    rcases l with _ | ⟨t, l'⟩
    · simpa using hs.labels
    · have hlab := hs.labels
      simp only [List.map_cons, List.cons.injEq] at hlab
      exact .prim (unconstrained_head hs) hlab.1 happ fun s' hs' => ih s' hs' (isSeqNet_progress hs)
  | @comp n c bs xs s Φ hb _ ih =>
    intro tn l hs
    rcases l with _ | ⟨t, l'⟩
    · simpa using hs.labels
    · have hlab := hs.labels
      simp only [List.map_cons, List.cons.injEq] at hlab
      obtain ⟨m, hm, rfl, hbody⟩ := hb
      obtain ⟨lm₀, hlm₀⟩ := Method.exists_isSeqNet_of_hasSeqBody (hP.methods m hm) hbody
      obtain ⟨tn'', hw'', hiso, hdisj⟩ := exists_fresh_iso_copy m.subtasks (hP.methods m hm) tn.T
      obtain ⟨lm, hlm⟩ := hlm₀.iso hw'' hiso.symm
      have hs' : tn.IsSeqNet ([] ++ t :: l') ([] ++ Sum.inr m.abstractTask :: xs) := by
        simpa [hlab.1] using hs
      have hnew := isSeqNet_decomposeWith hs' rfl hlm hdisj
      refine .decomp ⟨hm, hs.mem_of_mem (by simp), hlab.1, tn'', hw'', hiso, hdisj, rfl⟩
        (ih (by simpa using hnew))

/-- **Strong method-based solvability as the leftmost list game.** -/
theorem mpStrongSolvable_iff_lrunH [Infinite I] (hP : P.WF)
    (hM : ∀ m ∈ P.methods, m.subtasks.IsTotallyOrdered)
    {l : List I} {xs : List (A ⊕ C)} (h : P.tnI.IsSeqNet l xs) :
    P.MPStrongSolvable ↔ ∃ n, P.LRunH n xs P.init Set.univ := by
  rw [mpStrongSolvable_iff_mpAndOr hP, mpAndOr_iff_exists_H hP.actions]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, lrunH_of_mpAndOrH hP hM hn h⟩
  · rintro ⟨n, hn⟩
    exact (mpAndOr_of_lrunH hP hn h).toH hP.actions

end Problem

end FOND
