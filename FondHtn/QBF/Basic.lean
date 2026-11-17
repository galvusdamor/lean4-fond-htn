import HtnComplexity.PT.Lang
/-!
# Quantified Boolean formulas (TQBF)

The source problem of the repaired PSPACE-hardness proof of [CB21, Thm. 5.1].  A QBF is given in
prenex form with a CNF matrix:

* a **prefix** `[(q₀, v₀), …, (q_{m-1}, v_{m-1})]`, where `qᵢ = true` means `∀ vᵢ` and
  `qᵢ = false` means `∃ vᵢ` (variables are natural numbers, repetitions are allowed: an inner
  quantifier shadows an outer one);
* a **matrix**: a list of clauses, each a list of literals `(v, b)` (`b = true`: the positive
  literal `v`, `b = false`: `¬v`).

Variables not bound by the prefix are free and read as `false` (`FOND.QBF.Holds`).  This is a
harmless convention: a formula with free variables is equivalent to the one in which they are
existentially quantified only after fixing them, and the reductions below never produce free
variables that matter.

* `FOND.QBF.Eval q cls σ` — the truth value of `q. cls` under the assignment `σ` of the free
  variables;
* `FOND.QBF.TQBF` — the codes of true QBFs.

General lemmas: `FOND.QBF.eval_exBlock` (a block of existential quantifiers is an existential
quantifier over assignments), `FOND.QBF.eval_append_indep` (clauses not mentioning the
quantified variables can be pulled out of the scope of the quantifiers).
-/

namespace FOND

namespace QBF

open HTN.Syn.PolyDom

/-- A literal `(v, b)`: the variable `v` with polarity `b`. -/
abbrev Lit : Type := ℕ × Bool

/-- A clause: a disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- A quantifier prefix: `(true, v)` is `∀ v`, `(false, v)` is `∃ v`. -/
abbrev Prefix : Type := List (Bool × ℕ)

/-- **A QBF**: a prefix and a CNF matrix. -/
abbrev Formula : Type := Prefix × List Clause

/-- The CNF `cls` is satisfied by `σ`. -/
def Sat (cls : List Clause) (σ : ℕ → Bool) : Prop := ∀ c ∈ cls, ∃ l ∈ c, σ l.1 = l.2

/-- **Truth of a QBF** under an assignment of the free variables. -/
def Eval : Prefix → List Clause → (ℕ → Bool) → Prop
  | [], cls, σ => Sat cls σ
  | (true, v) :: q, cls, σ => ∀ b, Eval q cls (Function.update σ v b)
  | (false, v) :: q, cls, σ => ∃ b, Eval q cls (Function.update σ v b)

/-- A QBF is **true** (free variables read as `false`). -/
def Holds (φ : Formula) : Prop := Eval φ.1 φ.2 fun _ => false

/-- **TQBF**: the codes of true QBFs. -/
def TQBF : HTN.Cx.Language := codeLang Formula Holds

@[simp] theorem eval_nil (cls : List Clause) (σ : ℕ → Bool) : Eval [] cls σ ↔ Sat cls σ :=
  Iff.rfl

@[simp] theorem eval_forall (v : ℕ) (q : Prefix) (cls : List Clause) (σ : ℕ → Bool) :
    Eval ((true, v) :: q) cls σ ↔ ∀ b, Eval q cls (Function.update σ v b) := Iff.rfl

@[simp] theorem eval_exists (v : ℕ) (q : Prefix) (cls : List Clause) (σ : ℕ → Bool) :
    Eval ((false, v) :: q) cls σ ↔ ∃ b, Eval q cls (Function.update σ v b) := Iff.rfl

theorem sat_append (G H : List Clause) (σ : ℕ → Bool) : Sat (G ++ H) σ ↔ Sat G σ ∧ Sat H σ := by
  unfold Sat
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

theorem sat_update_of_not_mem {G : List Clause} {v : ℕ} (hv : ∀ c ∈ G, ∀ l ∈ c, l.1 ≠ v)
    (σ : ℕ → Bool) (b : Bool) : Sat G (Function.update σ v b) ↔ Sat G σ := by
  unfold Sat
  constructor
  · intro h c hc
    obtain ⟨l, hl, h'⟩ := h c hc
    exact ⟨l, hl, by rwa [Function.update_of_ne (hv c hc l hl)] at h'⟩
  · intro h c hc
    obtain ⟨l, hl, h'⟩ := h c hc
    exact ⟨l, hl, by rwa [Function.update_of_ne (hv c hc l hl)]⟩

/-- **Clauses that do not mention the quantified variables** can be pulled out. -/
theorem eval_append_indep (Q : Prefix) {G : List Clause}
    (hG : ∀ c ∈ G, ∀ l ∈ c, ∀ x ∈ Q, l.1 ≠ x.2) (H : List Clause) (σ : ℕ → Bool) :
    Eval Q (G ++ H) σ ↔ Sat G σ ∧ Eval Q H σ := by
  induction Q generalizing σ with
  | nil => exact sat_append G H σ
  | cons x Q ih =>
    obtain ⟨q, v⟩ := x
    have hG' : ∀ c ∈ G, ∀ l ∈ c, ∀ x ∈ Q, l.1 ≠ x.2 :=
      fun c hc l hl x hx => hG c hc l hl x (List.mem_cons_of_mem _ hx)
    have hv : ∀ c ∈ G, ∀ l ∈ c, l.1 ≠ v := fun c hc l hl => hG c hc l hl _ List.mem_cons_self
    cases q
    · simp only [eval_exists, ih hG', sat_update_of_not_mem hv]
      constructor
      · rintro ⟨b, h1, h2⟩; exact ⟨h1, b, h2⟩
      · rintro ⟨h1, b, h2⟩; exact ⟨b, h1, h2⟩
    · simp only [eval_forall, ih hG', sat_update_of_not_mem hv]
      constructor
      · intro h; exact ⟨(h true).1, fun b => (h b).2⟩
      · rintro ⟨h1, h2⟩ b; exact ⟨h1, h2 b⟩

/-- **A block of existential quantifiers** quantifies over assignments of its variables. -/
theorem eval_exBlock (l : List ℕ) (Q : Prefix) (cls : List Clause) (σ : ℕ → Bool) :
    Eval (l.map (fun v => (false, v)) ++ Q) cls σ ↔
      ∃ τ : ℕ → Bool, Eval Q cls (fun x => if x ∈ l then τ x else σ x) := by
  induction l generalizing σ with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.cons_append, eval_exists, ih, List.mem_cons]
    constructor
    · rintro ⟨b, τ, h⟩
      refine ⟨fun x => if x ∈ l then τ x else b, ?_⟩
      convert h using 2 with x
      by_cases hx : x ∈ l
      · simp [hx]
      · by_cases hxv : x = v
        · subst hxv; simp [hx]
        · simp [hx, hxv]
    · rintro ⟨τ, h⟩
      refine ⟨τ v, τ, ?_⟩
      convert h using 2 with x
      by_cases hx : x ∈ l
      · simp [hx]
      · by_cases hxv : x = v
        · subst hxv; simp [hx]
        · simp [hx, hxv]

end QBF

end FOND
