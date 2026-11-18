import Mathlib
/-!
# Context-free grammars

Context-free grammars over the terminals `ℕ` and the nonterminals `ℕ`, in the form needed for
the undecidability of HTN planning (Bercher et al., Thm. 4.1.1, which reduces the intersection
problem of context-free grammars to plan existence).

* `HTN.CFG.Grammar` — a start symbol and a list of rules `X → α`, `α` a word over terminals
  (`Sum.inl`) and nonterminals (`Sum.inr`); a plain product type, hence `Primcodable`;
* `HTN.CFG.Gen g α w` — the sentential form `α` derives the terminal word `w` (inductively,
  expanding the leftmost symbol);
* `HTN.CFG.Grammar.Lang g` — the language of `g`, `HTN.CFG.Inter g₁ g₂` — the two languages
  intersect;
* `HTN.CFG.Grammar.IsBinary` — every right-hand side has at most two symbols;
* `HTN.CFG.gen_append_iff` — a concatenation derives exactly the concatenations of what the
  parts derive.
-/

namespace HTN

namespace CFG

/-- A symbol: a terminal (`Sum.inl`) or a nonterminal (`Sum.inr`). -/
abbrev Sym : Type := ℕ ⊕ ℕ

/-- A rule `X → α`. -/
abbrev Rule : Type := ℕ × List Sym

/-- **A context-free grammar**: the start symbol and the rules. -/
abbrev Grammar : Type := ℕ × List Rule

namespace Grammar

/-- The start symbol. -/
def start (g : Grammar) : ℕ := g.1

/-- The rules. -/
def rules (g : Grammar) : List Rule := g.2

/-- Every right-hand side has at most two symbols. -/
def IsBinary (g : Grammar) : Prop := ∀ r ∈ g.rules, r.2.length ≤ 2

end Grammar

/-- **Derivation**: the sentential form `α` derives the terminal word `w`. -/
inductive Gen (g : Grammar) : List Sym → List ℕ → Prop
  | nil : Gen g [] []
  | term {a : ℕ} {α : List Sym} {w : List ℕ} : Gen g α w → Gen g (Sum.inl a :: α) (a :: w)
  | nonterm {X : ℕ} {β α : List Sym} {w : List ℕ} :
      (X, β) ∈ g.rules → Gen g (β ++ α) w → Gen g (Sum.inr X :: α) w

/-- The language of a grammar. -/
def Grammar.Lang (g : Grammar) (w : List ℕ) : Prop := Gen g [Sum.inr g.start] w

/-- **The intersection problem**: the languages of the two grammars have a common word. -/
def Inter (g₁ g₂ : Grammar) : Prop := ∃ w, g₁.Lang w ∧ g₂.Lang w

variable {g : Grammar}

theorem gen_append {α β : List Sym} {u v : List ℕ} (hα : Gen g α u) (hβ : Gen g β v) :
    Gen g (α ++ β) (u ++ v) := by
  induction hα with
  | nil => simpa using hβ
  | term _ ih => exact Gen.term ih
  | nonterm hr _ ih => exact Gen.nonterm hr (by simpa using ih)

theorem gen_split {γ : List Sym} {w : List ℕ} (h : Gen g γ w) :
    ∀ α β, γ = α ++ β → ∃ u v, w = u ++ v ∧ Gen g α u ∧ Gen g β v := by
  induction h with
  | nil =>
    intro α β h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h.symm
    exact ⟨[], [], rfl, Gen.nil, Gen.nil⟩
  | @term a γ w _ ih =>
    intro α β h
    cases α with
    | nil =>
      subst h
      exact ⟨[], a :: w, rfl, Gen.nil, Gen.term (by assumption)⟩
    | cons x α =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨u, v, rfl, hu, hv⟩ := ih α β rfl
      exact ⟨a :: u, v, rfl, Gen.term hu, hv⟩
  | @nonterm X δ γ w hr hg ih =>
    intro α β h
    cases α with
    | nil =>
      subst h
      exact ⟨[], w, rfl, Gen.nil, Gen.nonterm hr hg⟩
    | cons x α =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨u, v, rfl, hu, hv⟩ := ih (δ ++ α) β (by simp)
      exact ⟨u, v, rfl, Gen.nonterm hr hu, hv⟩

/-- **A concatenation derives exactly the concatenations of what its parts derive.** -/
theorem gen_append_iff {α β : List Sym} {w : List ℕ} :
    Gen g (α ++ β) w ↔ ∃ u v, w = u ++ v ∧ Gen g α u ∧ Gen g β v := by
  constructor
  · intro h; exact gen_split h α β rfl
  · rintro ⟨u, v, rfl, hu, hv⟩; exact gen_append hu hv

theorem gen_cons_iff {x : Sym} {α : List Sym} {w : List ℕ} :
    Gen g (x :: α) w ↔ ∃ u v, w = u ++ v ∧ Gen g [x] u ∧ Gen g α v :=
  gen_append_iff (α := [x])

/-- A single terminal derives itself only. -/
theorem gen_term_iff {a : ℕ} {w : List ℕ} : Gen g [Sum.inl a] w ↔ w = [a] := by
  constructor
  · intro h
    cases h with
    | term h => cases h; rfl
  · rintro rfl; exact Gen.term Gen.nil

/-- A single nonterminal derives what the right-hand side of one of its rules derives. -/
theorem gen_nonterm_iff {X : ℕ} {w : List ℕ} :
    Gen g [Sum.inr X] w ↔ ∃ β, (X, β) ∈ g.rules ∧ Gen g β w := by
  constructor
  · intro h
    cases h with
    | nonterm hr h => exact ⟨_, hr, by simpa using h⟩
  · rintro ⟨β, hr, h⟩
    exact Gen.nonterm hr (by simpa using h)

theorem gen_nil_iff {w : List ℕ} : Gen g [] w ↔ w = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Gen.nil

end CFG

end HTN
