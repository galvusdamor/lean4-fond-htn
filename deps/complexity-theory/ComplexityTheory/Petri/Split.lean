import ComplexityTheory.Petri.Run
/-!
# Replacing a block under a bound from the characteristic system

`solvable_replace_of_bound`: if every solution of the characteristic system satisfies a
property `Q` at the block `b`, and every run through `b` whose data satisfy `Q` is a run of one
of the alternatives `As`, then the generalised problem is solvable iff one of the replaced
problems is.  This is used for the steps that bound an edge count or an `ω`-coordinate.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*}

/-- The last output of a list of run data. -/
def LastOK (M' : ι → ℤ) (ts : List (Tri ι)) : Prop := ∀ t ∈ ts.getLast?, t.M' = M'

theorem linkedBy_cons_iff {f : (ι → ℤ) → (ι → ℤ) → (ι → ℤ)} {b : Block ι} {l : List (Block ι)}
    {t : Tri ι} {m : List (Tri ι)} :
    LinkedBy f (b :: l) (t :: m) ↔
      (∀ b' ∈ l.head?, ∀ t' ∈ m.head?, t'.M₁ = f t.M' b'.pre) ∧ LinkedBy f l m := by
  cases l with
  | nil => cases m <;> simp [LinkedBy]
  | cons b' l =>
    cases m with
    | nil => simp [LinkedBy]
    | cons t' m => simp [LinkedBy]

theorem listRun_data' : ∀ {bs : List (Block ι)} {M M' : ι → ℤ}, ListRun bs M M' →
    ∃ ts, List.Forall₂ RunData bs ts ∧ LinkedBy (fun M a => M + a) bs ts ∧ HeadOK M bs ts ∧
      LastOK M' ts ∧ (bs = [] → M = M')
  | [], _, _, h => ⟨[], List.Forall₂.nil, trivial, trivial, by simp [LastOK], fun _ => h⟩
  | b :: bs, M, M', h => by
    obtain ⟨M₁, hb, hbs⟩ := h
    obtain ⟨ψ, hψ⟩ := blockRun_iff.1 hb
    obtain ⟨ts, h1, h2, h3, h4, h5⟩ := listRun_data' hbs
    refine ⟨⟨M + b.pre, ψ, M₁⟩ :: ts, List.Forall₂.cons hψ h1, ?_, rfl, ?_, by simp⟩
    · rw [linkedBy_cons_iff]
      refine ⟨fun b' hb' t' ht' => ?_, h2⟩
      cases bs with
      | nil => simp at hb'
      | cons b'' bs =>
        cases ts with
        | nil => simp at ht'
        | cons t'' ts =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb' ht'
          subst hb' ht'
          exact h3
    · cases bs with
      | nil =>
        cases h1
        simp only [LastOK, List.getLast?_singleton, Option.mem_def, Option.some.injEq]
        rintro t rfl
        exact h5 rfl
      | cons b'' bs =>
        cases h1 with
        | cons _ _ =>
          intro t ht
          apply h4
          simpa [List.getLast?_cons_cons] using ht

theorem linkedBy_append {f : (ι → ℤ) → (ι → ℤ) → (ι → ℤ)} : ∀ (l₁ : List (Block ι))
    (m₁ : List (Tri ι)) (l₂ : List (Block ι)) (m₂ : List (Tri ι)), l₁.length = m₁.length →
    LinkedBy f l₁ m₁ → LinkedBy f l₂ m₂ →
    (∀ t ∈ m₁.getLast?, ∀ b ∈ l₂.head?, ∀ t' ∈ m₂.head?, t'.M₁ = f t.M' b.pre) →
    LinkedBy f (l₁ ++ l₂) (m₁ ++ m₂)
  | [], [], _, _, _, _, h, _ => h
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | [b], [t], l₂, m₂, _, _, h2, hb => by
    simp only [List.cons_append, List.nil_append]
    rw [linkedBy_cons_iff]
    exact ⟨fun b' hb' t' ht' => hb t (by simp) b' hb' t' ht', h2⟩
  | b :: b₂ :: l, [t], _, _, h, _, _, _ => by simp at h
  | [b], t :: t₂ :: m, _, _, h, _, _, _ => by simp at h
  | b :: b₂ :: l, t :: t₂ :: m, l₂, m₂, hlen, h1, h2, hb => by
    simp only [List.cons_append]
    rw [linkedBy_cons_iff] at h1 ⊢
    refine ⟨fun b' hb' t' ht' => ?_, ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb' ht'
      subst hb' ht'
      exact h1.1 b₂ (by simp) t₂ (by simp)
    · have := linkedBy_append (b₂ :: l) (t₂ :: m) l₂ m₂ (by simpa using hlen) h1.2 h2
        (fun t'' ht'' => hb t'' (by simpa [List.getLast?_cons_cons] using ht''))
      simpa using this

/-- A run through `pre ++ b :: post` yields a solution of the characteristic system whose entry
at `b` is the run data of the block. -/
theorem exists_charSol_at {pre post : List (Block ι)} {b : Block ι} {t : Tri ι}
    {M M₁ M' : ι → ℤ} (h1 : ListRun pre M M₁) (h2 : RunData b t) (ht : t.M₁ = M₁ + b.pre)
    (h3 : ListRun post t.M' M') :
    ∃ ts, CharSol (pre ++ b :: post) ts ∧ List.Forall₂ RunData (pre ++ b :: post) ts ∧
      ts[pre.length]? = some t := by
  obtain ⟨tsP, hP1, hP2, -, hP4, hP5⟩ := listRun_data' h1
  obtain ⟨tsQ, hQ1, hQ2, hQ3, -, -⟩ := listRun_data' h3
  have hlen : pre.length = tsP.length := hP1.length_eq
  have hall : List.Forall₂ RunData (pre ++ b :: post) (tsP ++ t :: tsQ) :=
    List.rel_append hP1 (List.Forall₂.cons h2 hQ1)
  refine ⟨tsP ++ t :: tsQ, ⟨hall.imp fun _ _ h => h.charOK, ?_⟩, hall, ?_⟩
  · refine linkedBy_append pre tsP (b :: post) (t :: tsQ) hlen hP2 ?_ ?_
    · rw [linkedBy_cons_iff]
      refine ⟨fun b' hb' t' ht' => ?_, hQ2⟩
      cases post with
      | nil => simp at hb'
      | cons b'' post =>
        cases tsQ with
        | nil => simp at ht'
        | cons t'' tsQ =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb' ht'
          subst hb' ht'
          exact hQ3
    · intro t' ht' b' hb' t'' ht''
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb' ht''
      subst hb' ht''
      rw [ht, hP4 t' ht']
  · rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
    rfl

/-- **Replacing a block under a bound** coming from the characteristic system. -/
theorem solvable_replace_of_bound (pre post : List (Block ι)) (b : Block ι)
    (As : List (List (Block ι))) (Q : Tri ι → Prop)
    (hQ : ∀ ts, CharSol (pre ++ b :: post) ts → ∀ t ∈ ts[pre.length]?, Q t)
    (hloc : ∀ t, RunData b t → Q t → ∃ A ∈ As, ListRun A (t.M₁ - b.pre) t.M')
    (hloc' : ∀ A ∈ As, ∀ M M', ListRun A M M' → BlockRun b M M') :
    Solvable (pre ++ b :: post) ↔ ∃ A ∈ As, Solvable (pre ++ A ++ post) := by
  constructor
  · rintro ⟨M, M', hr⟩
    rw [listRun_append] at hr
    obtain ⟨M₁, h1, M₂, h2, h3⟩ := hr
    obtain ⟨ψ, hψ⟩ := blockRun_iff.1 h2
    obtain ⟨ts, hts, -, hat⟩ := exists_charSol_at h1 hψ rfl h3
    have hq := hQ ts hts _ hat
    obtain ⟨A, hA, hAr⟩ := hloc _ hψ hq
    have e : M₁ + b.pre - b.pre = M₁ := by abel
    simp only [e] at hAr
    exact ⟨A, hA, M, M', listRun_append.2 ⟨M₂, listRun_append.2 ⟨M₁, h1, hAr⟩, h3⟩⟩
  · rintro ⟨A, hA, M, M', hr⟩
    rw [listRun_append] at hr
    obtain ⟨M₂, hr, h3⟩ := hr
    rw [listRun_append] at hr
    obtain ⟨M₁, h1, h2⟩ := hr
    exact ⟨M, M', listRun_append.2 ⟨M₁, h1, M₂, hloc' A hA _ _ h2, h3⟩⟩

end KLM

end Petri

end HTN
