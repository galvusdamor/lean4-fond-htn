import ComplexityTheory.Petri.Lambert
/-!
# Runs of generalised problems as data; replacing a block

* `RunData b t`: `t` records a run through the block `b` (input, edge multiplicities of an index
  walk, output).  `RunData.charOK`: such data solve the characteristic constraints.
* `blockRun_iff`, `solvable_iff`: runs ↔ lists of run data linked by the `pre` vectors.
* `listRun_append`, `solvable_replace`: replacing a block by finitely many alternatives that
  have the same runs.
-/

namespace HTN

namespace Petri

namespace KLM

open Euler Finset Comp

variable {ι : Type*}

/-- `t` records a run through the block `b`. -/
def RunData (b : Block ι) (t : Tri ι) : Prop :=
  Agree t.M₁ b.inp ∧ Agree t.M' b.out ∧ ∃ π, Walk b.comp b.comp.entry π b.comp.exit ∧
    TFires (fun _ => True) t.M₁ (π.map b.comp.edge) ∧
    TLab b.comp (fun _ => True) b.comp.entry t.M₁ (π.map b.comp.edge) ∧
    t.M' = t.M₁ + teff (π.map b.comp.edge) ∧ ∀ k < b.comp.edges.length, t.ψ k = π.count k

theorem outF_congr (E : List (ℕ × ℕ)) {φ ψ : ℕ → ℕ} (h : ∀ k < E.length, φ k = ψ k) (w : ℕ) :
    outF E φ w = outF E ψ w :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)]

theorem inF_congr (E : List (ℕ × ℕ)) {φ ψ : ℕ → ℕ} (h : ∀ k < E.length, φ k = ψ k) (w : ℕ) :
    inF E φ w = inF E ψ w :=
  Finset.sum_congr rfl fun k hk => by rw [h k (Finset.mem_range.1 hk)]

theorem kirch_congr {E : List (ℕ × ℕ)} {φ ψ : ℕ → ℕ} (h : ∀ k < E.length, φ k = ψ k) {s t : ℕ}
    (hK : Kirch E φ s t) : Kirch E ψ s t := by
  intro w
  rw [← outF_congr E h, ← inF_congr E h]
  exact hK w

theorem RunData.charOK {b : Block ι} {t : Tri ι} (h : RunData b t) : CharOK b t := by
  obtain ⟨hA, hA', π, hw, hf, -, he, hψ⟩ := h
  refine ⟨fun j => hf.start j trivial, hA, ?_, ?_, fun j => ?_, hA'⟩
  · exact kirch_congr (fun k hk => (hψ k (by rwa [gr_length] at hk)).symm) (kirch_walk hw)
  · rw [he, teff_map_edge, eff_eq_psum hw, psum_congr _ fun k hk => (hψ k hk).symm]
  · rw [he]; exact hf.end_ok j trivial

theorem blockRun_iff {b : Block ι} {M M' : ι → ℤ} :
    BlockRun b M M' ↔ ∃ ψ, RunData b ⟨M + b.pre, ψ, M'⟩ := by
  constructor
  · rintro ⟨hA, es, hw, hf, hl, he, hA'⟩
    obtain ⟨π, hπ, rfl⟩ := hw.toIdx
    exact ⟨fun k => π.count k, hA, hA', π, hπ, hf, hl, he, fun _ _ => rfl⟩
  · rintro ⟨ψ, hA, hA', π, hπ, hf, hl, he, -⟩
    exact ⟨hA, _, hπ.toT, hf, hl, he, hA'⟩

theorem listRun_append {bs bs' : List (Block ι)} {M M' : ι → ℤ} :
    ListRun (bs ++ bs') M M' ↔ ∃ M₁, ListRun bs M M₁ ∧ ListRun bs' M₁ M' := by
  induction bs generalizing M with
  | nil => simp [ListRun]
  | cons b bs ih =>
    simp only [List.cons_append, ListRun, ih]
    constructor
    · rintro ⟨M₂, h1, M₁, h2, h3⟩; exact ⟨M₁, ⟨M₂, h1, h2⟩, h3⟩
    · rintro ⟨M₁, ⟨M₂, h1, h2⟩, h3⟩; exact ⟨M₂, h1, M₁, h2, h3⟩

/-- **Replacing a block** by alternatives with the same runs. -/
theorem solvable_replace (pre post : List (Block ι)) (b : Block ι) (As : List (List (Block ι)))
    (h : ∀ M M', BlockRun b M M' ↔ ∃ A ∈ As, ListRun A M M') :
    Solvable (pre ++ b :: post) ↔ ∃ A ∈ As, Solvable (pre ++ A ++ post) := by
  constructor
  · rintro ⟨M, M', hr⟩
    rw [listRun_append] at hr
    obtain ⟨M₁, h1, M₂, h2, h3⟩ := hr
    obtain ⟨A, hA, hAr⟩ := (h _ _).1 h2
    exact ⟨A, hA, M, M', listRun_append.2 ⟨M₂, listRun_append.2 ⟨M₁, h1, hAr⟩, h3⟩⟩
  · rintro ⟨A, hA, M, M', hr⟩
    rw [listRun_append] at hr
    obtain ⟨M₂, hr, h3⟩ := hr
    rw [listRun_append] at hr
    obtain ⟨M₁, h1, h2⟩ := hr
    exact ⟨M, M', listRun_append.2 ⟨M₁, h1, M₂, (h _ _).2 ⟨A, hA, h2⟩, h3⟩⟩

/-- The first input of a list of run data. -/
def HeadOK (M : ι → ℤ) : List (Block ι) → List (Tri ι) → Prop
  | b :: _, t :: _ => t.M₁ = M + b.pre
  | _, _ => True

theorem listRun_data : ∀ {bs : List (Block ι)} {M M' : ι → ℤ}, ListRun bs M M' →
    ∃ ts, List.Forall₂ RunData bs ts ∧ LinkedBy (fun M a => M + a) bs ts ∧ HeadOK M bs ts
  | [], _, _, _ => ⟨[], List.Forall₂.nil, trivial, trivial⟩
  | b :: bs, M, M', h => by
    obtain ⟨M₁, hb, hbs⟩ := h
    obtain ⟨ψ, hψ⟩ := blockRun_iff.1 hb
    obtain ⟨ts, h1, h2, h3⟩ := listRun_data hbs
    refine ⟨⟨M + b.pre, ψ, M₁⟩ :: ts, List.Forall₂.cons hψ h1, ?_, rfl⟩
    cases bs with
    | nil => cases ts <;> simp [LinkedBy]
    | cons b' bs =>
      cases ts with
      | nil => simp [LinkedBy]
      | cons t' ts => exact ⟨h3, h2⟩

theorem data_listRun : ∀ {bs : List (Block ι)} {ts : List (Tri ι)}, List.Forall₂ RunData bs ts →
    LinkedBy (fun M a => M + a) bs ts → ∀ M, HeadOK M bs ts → ∃ M', ListRun bs M M'
  | [], _, _, _, M, _ => ⟨M, rfl⟩
  | b :: bs, _, List.Forall₂.cons (b := t) (l₂ := ts) ht hts, hL, M, hH => by
    have hH' : t.M₁ = M + b.pre := hH
    have hb : BlockRun b M t.M' := blockRun_iff.2 ⟨t.ψ, by rw [← hH']; exact ht⟩
    obtain ⟨M', hM'⟩ := data_listRun hts hL.tail t.M' (by
      cases hts with
      | nil => trivial
      | cons _ _ => exact hL.1)
    exact ⟨M', t.M', hb, hM'⟩

/-- Solvability through run data. -/
theorem solvable_iff {bs : List (Block ι)} :
    Solvable bs ↔ ∃ ts, List.Forall₂ RunData bs ts ∧ LinkedBy (fun M a => M + a) bs ts := by
  constructor
  · rintro ⟨M, M', h⟩
    obtain ⟨ts, h1, h2, -⟩ := listRun_data h
    exact ⟨ts, h1, h2⟩
  · rintro ⟨ts, h1, h2⟩
    cases bs with
    | nil => exact ⟨0, 0, rfl⟩
    | cons b bs =>
      cases h1 with
      | cons ht hts =>
        rename_i t ts
        obtain ⟨M', hM'⟩ := data_listRun (List.Forall₂.cons ht hts) h2 (t.M₁ - b.pre)
          (show t.M₁ = t.M₁ - b.pre + b.pre by abel)
        exact ⟨_, _, hM'⟩

/-- A solvable generalised problem has a solution of its characteristic system. -/
theorem charSol_of_solvable {bs : List (Block ι)} (h : Solvable bs) :
    ∃ ts, CharSol bs ts ∧ List.Forall₂ RunData bs ts := by
  obtain ⟨ts, h1, h2⟩ := solvable_iff.1 h
  exact ⟨ts, ⟨h1.imp fun _ _ h => h.charOK, h2⟩, h1⟩

end KLM

end Petri

end HTN
