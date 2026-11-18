import FondHtn.AcycHard.Assembly
/-!
# Automaton queue games

A cell specification (`FOND.AcycHard.FSpec`) whose data facts are the states of an automaton and
whose options are its transitions (`FOND.AcycHard.autSpec`): an option `(a, σ, τ, a')` reads `σ`,
writes `τ` and moves from state `a` to `a'`.  From a singleton data state `{st a}` a step of the
supply-free queue game is a transition of the automaton (`FOND.AcycHard.qi_step`), and a sweep of
`n` steps in which the state is determined by the position is a list of writes
(`FOND.AcycHard.qi_sweep`).
-/

namespace FOND

namespace AcycHard

/-- The data facts: automaton states and the transient read/write reports. -/
inductive Fct (A Sym : Type)
  | st (a : A)
  | rd (σ : Sym)
  | wr (σ : Sym)
  deriving DecidableEq

variable {A Sym P : Type} [DecidableEq Sym]

/-- **The specification of an automaton queue game.** -/
def autSpec (S : ℕ) (pp : P → Set (Fct A Sym)) (pe : P → Set (Set (Fct A Sym) × Set (Fct A Sym))) :
    FSpec Sym (A × Sym × Sym × A) (Fct A Sym) P where
  S := S
  rd := Fct.rd
  wr := Fct.wr
  opre o := {Fct.st o.1, Fct.rd o.2.1, Fct.wr o.2.2.1}
  oadd o := {Fct.st o.2.2.2}
  odel o := {Fct.st o.1, Fct.rd o.2.1, Fct.wr o.2.2.1}
  ppre := pp
  peffs := pe

variable {S : ℕ} {pp : P → Set (Fct A Sym)} {pe : P → Set (Set (Fct A Sym) × Set (Fct A Sym))}

/-- **A step from a singleton state** is a transition of the automaton. -/
theorem qi_step (aS : Sym → Prop) (Δ : Set (A × Sym × Sym × A)) (r : List (Option P)) (σ : Sym)
    (q : List Sym) (a : A) :
    (autSpec S pp pe).QI aS (· ∈ Δ) (none :: r) (σ :: q) {Fct.st a} ↔
      ∃ τ a', aS τ ∧ (a, σ, τ, a') ∈ Δ ∧ (autSpec S pp pe).QI aS (· ∈ Δ) r (q ++ [τ]) {Fct.st a'} := by
  simp only [FSpec.QI]
  constructor
  · rintro ⟨τ, hτ, ⟨a₀, σ₀, τ₀, a₁⟩, hΔ, hpre, h⟩
    simp only [autSpec, Set.insert_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      reduceCtorEq, false_or, or_false, Fct.st.injEq, Fct.rd.injEq, Fct.wr.injEq,
      Set.singleton_subset_iff] at hpre
    obtain ⟨e1, e2, e3⟩ := hpre
    subst a₀ σ₀ τ₀
    refine ⟨τ, a₁, hτ, hΔ, ?_⟩
    convert h using 1
    ext f
    simp only [autSpec, WSys.upd, Set.mem_union, Set.mem_diff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    cases f <;> simp <;> tauto
  · rintro ⟨τ, a', hτ, hΔ, h⟩
    refine ⟨τ, hτ, (a, σ, τ, a'), hΔ, ?_, ?_⟩
    · intro f hf
      simp only [autSpec, Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
      tauto
    · convert h using 1
      ext f
      simp only [autSpec, WSys.upd, Set.mem_union, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      cases f <;> simp <;> tauto

omit [DecidableEq Sym] in
/-- A plain action. -/
theorem qi_plain (aS : Sym → Prop) (Δ : Set (A × Sym × Sym × A)) (p : P) (r : List (Option P))
    (q : List Sym) (d : Set (Fct A Sym)) :
    (autSpec S pp pe).QI aS (· ∈ Δ) (some p :: r) q d ↔
      pp p ⊆ d ∧ ∀ e ∈ pe p, (autSpec S pp pe).QI aS (· ∈ Δ) r q (WSys.upd d e.1 e.2) := Iff.rfl

/-- **A sweep** whose transitions are given by the position: at position `j` from state `st j`
the writes `W j σ τ` are allowed and the state becomes `st (j + 1)`. -/
theorem qi_sweep (aS : Sym → Prop) (Δ : Set (A × Sym × Sym × A)) (stt : ℕ → A)
    (W : ℕ → Sym → Sym → Prop)
    (hΔ : ∀ j σ τ a', aS τ ∧ (stt j, σ, τ, a') ∈ Δ ↔ W j σ τ ∧ a' = stt (j + 1))
    (r : List (Option P)) :
    ∀ (q q' : List Sym) (j : ℕ),
      (autSpec S pp pe).QI aS (· ∈ Δ) (List.replicate q.length none ++ r) (q ++ q') {Fct.st (stt j)} ↔
      ∃ ts : List Sym, ts.length = q.length ∧ (∀ i (h : i < q.length) (h' : i < ts.length), W (j + i) q[i] ts[i]) ∧
        (autSpec S pp pe).QI aS (· ∈ Δ) r (q' ++ ts) {Fct.st (stt (j + q.length))} := by
  intro q
  induction q with
  | nil =>
    intro q' j
    simp only [List.length_nil, List.replicate_zero, List.nil_append, add_zero]
    constructor
    · intro h; exact ⟨[], rfl, fun i h => absurd h (Nat.not_lt_zero _), by simpa using h⟩
    · rintro ⟨ts, hts, -, h⟩
      rw [List.length_eq_zero_iff.1 hts] at h; simpa using h
  | cons σ q ih =>
    intro q' j
    rw [show List.replicate (σ :: q).length none = none :: List.replicate q.length none from rfl,
      List.cons_append, List.cons_append, qi_step]
    constructor
    · rintro ⟨τ, a', h1, h2, h⟩
      obtain ⟨hW, rfl⟩ := (hΔ j σ τ a').1 ⟨h1, h2⟩
      rw [List.append_assoc] at h
      obtain ⟨ts, hl, hts, h⟩ := (ih (q' ++ [τ]) (j + 1)).1 h
      refine ⟨τ :: ts, by simp [hl], fun i hi hi' => ?_, ?_⟩
      · rcases i with _ | i
        · simpa using hW
        · have := hts i (by simp at hi; omega) (by simp at hi'; omega)
          simpa [show j + (i + 1) = j + 1 + i by omega] using this
      · simpa [show j + (q.length + 1) = j + 1 + q.length by omega, List.append_assoc] using h
    · rintro ⟨ts, hl, hts, h⟩
      obtain ⟨τ, ts, rfl⟩ : ∃ τ ts', ts = τ :: ts' := by
        cases ts with
        | nil => simp at hl
        | cons τ ts => exact ⟨τ, ts, rfl⟩
      have hW := hts 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero, add_zero] at hW
      refine ⟨τ, stt (j + 1), (hΔ j σ τ _).2 ⟨hW, rfl⟩ |>.1, (hΔ j σ τ _).2 ⟨hW, rfl⟩ |>.2, ?_⟩
      rw [List.append_assoc]
      refine (ih (q' ++ [τ]) (j + 1)).2 ⟨ts, by simpa using hl, fun i hi hi' => ?_, ?_⟩
      · have := hts (i + 1) (by simp; omega) (by simp; omega)
        simpa [show j + (i + 1) = j + 1 + i by omega] using this
      · simpa [show j + 1 + q.length = j + (q.length + 1) by omega, List.append_assoc] using h

end AcycHard

end FOND
