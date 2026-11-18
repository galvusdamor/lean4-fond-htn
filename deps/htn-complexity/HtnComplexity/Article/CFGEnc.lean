import ComplexityTheory.CFG.Undec
import HtnPlanning.Interleave.ChainSeqYield
import HtnPlanning.Interleave.NetYield
/-!
# The encoding of two context-free grammars (Bercher et al., proof of Thm. 4.1.1)

For two context-free grammars `G`, `G'` the article builds an HTN problem that has a solution iff
`L(G) ∩ L(G') ≠ ∅`:

* a primitive task `σ` and `σ'` for each terminal `σ`, with
  `δ(σ) = ({turn_G}, ∅, {turn_G', v_σ}, {turn_G})` and
  `δ(σ') = ({turn_G', v_σ}, ∅, {turn_G}, {turn_G', v_σ})`;
* a compound task per nonterminal of either grammar, and a totally ordered method per rule;
* the initial task network: the two start symbols, unordered; initial state and goal `{turn_G}`.

A solution interleaves a word of `G` (the unprimed actions) with a word of `G'` (the primed
ones); the state forces strict alternation `σ₁ σ₁' σ₂ σ₂' …` with equal letters, so the two
words are equal.

Here, over the identifiers `ℕ × ℕ` of grids (as everywhere in the development):

* the facts are `0` (`turn_G`), `1` (`turn_G'`) and `σ + 2` (`v_σ`);
* the actions are `2σ` (`σ`) and `2σ + 1` (`σ'`), for the terminals `σ < bnd G G'`;
* the compound tasks are `2X` for the nonterminals `X` of `G` and `2X + 1` for those of `G'`
  (this is the renaming that makes the two sets of nonterminals disjoint).

Main result: **`HTN.Article.CFGEnc.solvable_semProblem_iff`** — the problem is solvable iff the
grammars have a common word.  The rules of the grammars are arbitrary (also `ε`-rules); the
article's assumption of Chomsky normal form is not needed.
-/

namespace HTN

namespace Article

namespace CFGEnc

open CFG TaskNetwork Domain

/-- The terminals occurring in the rules of a grammar. -/
def terms (g : Grammar) : List ℕ :=
  g.2.flatMap fun r => r.2.flatMap fun x => Sum.elim (fun a => [a]) (fun _ => []) x

/-- A bound on the terminals of two grammars. -/
def bnd (g₁ g₂ : Grammar) : ℕ := (terms g₁ ++ terms g₂).foldr max 0 + 1

/-- The renaming of the symbols of the grammar `k ∈ {0, 1}`. -/
def trS (k : ℕ) : Sym → ℕ ⊕ ℕ
  | Sum.inl a => Sum.inl (2 * a + k)
  | Sum.inr X => Sum.inr (2 * X + k)

variable (g₁ g₂ : Grammar)

/-- **The domain of the encoding.** -/
def semDom : Domain ℕ ℕ ℕ (ℕ × ℕ) where
  prec n := if n / 2 < bnd g₁ g₂ then (if n % 2 = 0 then {0} else {1, n / 2 + 2}) else ∅
  add n := if n / 2 < bnd g₁ g₂ then (if n % 2 = 0 then {1, n / 2 + 2} else {0}) else ∅
  del n := if n / 2 < bnd g₁ g₂ then (if n % 2 = 0 then {0} else {1, n / 2 + 2}) else ∅
  methods := {m | (∃ r ∈ g₁.rules, m = ⟨2 * r.1, grid [r.2.map (trS 0)]⟩) ∨
    (∃ r ∈ g₂.rules, m = ⟨2 * r.1 + 1, grid [r.2.map (trS 1)]⟩)}

/-- **The instance of the encoding.** -/
def semInst : Instance ℕ ℕ ℕ (ℕ × ℕ) where
  init := {0}
  goal := {0}
  tnI := grid [[Sum.inr (2 * g₁.start)], [Sum.inr (2 * g₂.start + 1)]]

/-- The problem of the encoding. -/
def semProblem : HTN.Problem ℕ ℕ ℕ (ℕ × ℕ) := (semDom g₁ g₂).mkProblem (semInst g₁ g₂)

variable {g₁ g₂}

theorem semDom_grid : ∀ m ∈ (semDom g₁ g₂).methods, ∃ ls, m.subtasks = grid ls := by
  rintro m (⟨r, -, rfl⟩ | ⟨r, -, rfl⟩) <;> exact ⟨_, rfl⟩

/-! ### Bodies -/

theorem seqBody_iff {c : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    (semDom g₁ g₂).SeqBody c bs ↔
      (∃ r ∈ g₁.rules, c = 2 * r.1 ∧ bs = r.2.map (trS 0)) ∨
        (∃ r ∈ g₂.rules, c = 2 * r.1 + 1 ∧ bs = r.2.map (trS 1)) := by
  constructor
  · rintro ⟨m, (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩), rfl, hb⟩
    · exact Or.inl ⟨r, hr, rfl, (Method.hasSeqBody_of_subtasks_grid_single rfl).1 hb⟩
    · exact Or.inr ⟨r, hr, rfl, (Method.hasSeqBody_of_subtasks_grid_single rfl).1 hb⟩
  · rintro (⟨r, hr, rfl, rfl⟩ | ⟨r, hr, rfl, rfl⟩)
    · exact ⟨_, Or.inl ⟨r, hr, rfl⟩, rfl, (Method.hasSeqBody_of_subtasks_grid_single rfl).2 rfl⟩
    · exact ⟨_, Or.inr ⟨r, hr, rfl⟩, rfl, (Method.hasSeqBody_of_subtasks_grid_single rfl).2 rfl⟩

theorem chainClosed : (semDom g₁ g₂).ChainClosed Set.univ := by
  rintro c _ ls ⟨m, hm, -, hsub⟩
  rcases hm with ⟨r, -, rfl⟩ | ⟨r, -, rfl⟩
  · exact ⟨_, hsub.symm, fun _ _ => trivial⟩
  · exact ⟨_, hsub.symm, fun _ _ => trivial⟩

/-- The bodies of the compound task `2X + k`, for the grammar `k`. -/
theorem seqBody_k_iff {k : ℕ} (hk : k < 2) {g : Grammar}
    (hg : g = if k = 0 then g₁ else g₂) {X : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    (semDom g₁ g₂).SeqBody (2 * X + k) bs ↔ ∃ β, (X, β) ∈ g.rules ∧ bs = β.map (trS k) := by
  rw [seqBody_iff]
  interval_cases k
  · simp only [if_true] at hg
    subst hg
    constructor
    · rintro (⟨r, hr, hc, rfl⟩ | ⟨r, -, hc, -⟩)
      · obtain rfl : X = r.1 := by omega
        exact ⟨r.2, hr, rfl⟩
      · omega
    · rintro ⟨β, hr, rfl⟩
      exact Or.inl ⟨(X, β), hr, by simp, rfl⟩
  · simp only [one_ne_zero, if_false] at hg
    subst hg
    constructor
    · rintro (⟨r, -, hc, -⟩ | ⟨r, hr, hc, rfl⟩)
      · omega
      · obtain rfl : X = r.1 := by omega
        exact ⟨r.2, hr, rfl⟩
    · rintro ⟨β, hr, rfl⟩
      exact Or.inr ⟨(X, β), hr, rfl, rfl⟩

/-- **The totally ordered refinements of the renamed sentential forms of a grammar are the
renamed words it derives.** -/
theorem yieldSeq_iff {k : ℕ} (hk : k < 2) {g : Grammar} (hg : g = if k = 0 then g₁ else g₂)
    {α : List Sym} {as : List ℕ} :
    (semDom g₁ g₂).YieldSeq (α.map (trS k)) as ↔ ∃ w, Gen g α w ∧ as = w.map (2 * · + k) := by
  constructor
  · intro h
    suffices H : ∀ xs as, (semDom g₁ g₂).YieldSeq xs as → ∀ α : List Sym, xs = α.map (trS k) →
        ∃ w, Gen g α w ∧ as = w.map (2 * · + k) from H _ _ h α rfl
    intro xs as h
    induction h with
    | nil =>
      intro α hα
      obtain rfl : α = [] := List.map_eq_nil_iff.1 hα.symm
      exact ⟨[], Gen.nil, rfl⟩
    | @prim a xs as _ ih =>
      intro α hα
      obtain ⟨x, α', rfl, hx, rfl⟩ := List.map_eq_cons_iff.1 hα.symm
      rcases x with a' | X
      · obtain ⟨w, hw, rfl⟩ := ih α' rfl
        simp only [trS, Sum.inl.injEq] at hx
        exact ⟨a' :: w, Gen.term hw, by simp [hx]⟩
      · simp [trS] at hx
    | @comp c bs xs as hm _ ih =>
      intro α hα
      obtain ⟨x, α', rfl, hx, rfl⟩ := List.map_eq_cons_iff.1 hα.symm
      rcases x with a' | X
      · simp [trS] at hx
      · simp only [trS, Sum.inr.injEq] at hx
        subst hx
        obtain ⟨β, hr, rfl⟩ := (seqBody_k_iff hk hg).1 hm
        obtain ⟨w, hw, rfl⟩ := ih (β ++ α') (by simp)
        exact ⟨w, Gen.nonterm hr hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    induction hw with
    | nil => exact YieldSeq.nil
    | term _ ih => exact YieldSeq.prim ih
    | @nonterm X β α w hr _ ih =>
      refine YieldSeq.comp ((seqBody_k_iff hk hg).2 ⟨β, hr, rfl⟩) ?_
      simpa using ih

/-! ### The initial network -/

theorem chainYield_start_iff {k : ℕ} (hk : k < 2) {g : Grammar}
    (hg : g = if k = 0 then g₁ else g₂) {as : List ℕ} :
    (semDom g₁ g₂).ChainYield [Sum.inr (2 * g.start + k)] as ↔
      ∃ w, g.Lang w ∧ as = w.map (2 * · + k) := by
  rw [chainYield_iff_yieldSeq semDom_grid chainClosed (fun _ _ => trivial)]
  exact yieldSeq_iff (α := [Sum.inr g.start]) hk hg

/-- **The initial network refines into the interleavings of a renamed word of `G` and a renamed
word of `G'`.** -/
theorem gridYield_tnI_iff {cs : List ℕ} :
    (semDom g₁ g₂).GridYield [[Sum.inr (2 * g₁.start)], [Sum.inr (2 * g₂.start + 1)]] cs ↔
      ∃ w w', g₁.Lang w ∧ g₂.Lang w' ∧
        Interleave (w.map (2 * · + 0)) (w'.map (2 * · + 1)) cs := by
  rw [gridYield_cons_iff]
  constructor
  · rintro ⟨as, bs, h₁, h₂, hint⟩
    obtain ⟨w, hw, rfl⟩ := (chainYield_start_iff (k := 0) (by omega) (by simp)).1 h₁
    obtain ⟨w', hw', rfl⟩ :=
      (chainYield_start_iff (k := 1) (by omega) (by simp)).1 (gridYield_singleton_iff.1 h₂)
    exact ⟨w, w', hw, hw', hint⟩
  · rintro ⟨w, w', hw, hw', hint⟩
    exact ⟨_, _, (chainYield_start_iff (k := 0) (by omega) (by simp)).2 ⟨w, hw, rfl⟩,
      gridYield_singleton_iff.2 ((chainYield_start_iff (k := 1) (by omega) (by simp)).2
        ⟨w', hw', rfl⟩), hint⟩

/-! ### Executions -/

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem mem_or_terms {g : Grammar} {α : List Sym} {w : List ℕ} (h : Gen g α w) :
    ∀ a ∈ w, Sum.inl a ∈ α ∨ a ∈ terms g := by
  induction h with
  | nil => simp
  | @term a α w _ ih =>
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Or.inl List.mem_cons_self
    · rcases ih b hb with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  | @nonterm X β α w hr _ ih =>
    intro b hb
    rcases ih b hb with h | h
    · rcases List.mem_append.1 h with h | h
      · refine Or.inr (List.mem_flatMap.2 ⟨(X, β), hr, List.mem_flatMap.2 ⟨Sum.inl b, h, ?_⟩⟩)
        simp
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem lt_bnd₁ {w : List ℕ} (h : g₁.Lang w) : ∀ a ∈ w, a < bnd g₁ g₂ := by
  intro a ha
  rcases mem_or_terms h a ha with h | h
  · simp at h
  · have := le_foldr_max (l := terms g₁ ++ terms g₂) (List.mem_append_left _ h)
    unfold bnd; omega

theorem lt_bnd₂ {w : List ℕ} (h : g₂.Lang w) : ∀ a ∈ w, a < bnd g₁ g₂ := by
  intro a ha
  rcases mem_or_terms h a ha with h | h
  · simp at h
  · have := le_foldr_max (l := terms g₁ ++ terms g₂) (List.mem_append_right _ h)
    unfold bnd; omega

theorem applicable_even {σ : ℕ} (hσ : σ < bnd g₁ g₂) {s : Set ℕ} :
    (semDom g₁ g₂).Applicable (2 * σ + 0) s ↔ 0 ∈ s := by
  have h1 : (2 * σ + 0) / 2 = σ := by omega
  have h2 : (2 * σ + 0) % 2 = 0 := by omega
  simp [ActionModel.Applicable, semDom, h1, h2, hσ]

theorem applicable_odd {σ : ℕ} (hσ : σ < bnd g₁ g₂) {s : Set ℕ} :
    (semDom g₁ g₂).Applicable (2 * σ + 1) s ↔ 1 ∈ s ∧ σ + 2 ∈ s := by
  have h1 : (2 * σ + 1) / 2 = σ := by omega
  have h2 : (2 * σ + 1) % 2 = 1 := by omega
  simp [ActionModel.Applicable, semDom, h1, h2, hσ, Set.insert_subset_iff]

theorem transition_even {σ : ℕ} (hσ : σ < bnd g₁ g₂) :
    (semDom g₁ g₂).transition (2 * σ + 0) {0} = {1, σ + 2} := by
  have h1 : (2 * σ + 0) / 2 = σ := by omega
  have h2 : (2 * σ + 0) % 2 = 0 := by omega
  simp only [ActionModel.transition, semDom, h1, h2, hσ, if_true]
  ext x; simp

theorem transition_odd {σ : ℕ} (hσ : σ < bnd g₁ g₂) :
    (semDom g₁ g₂).transition (2 * σ + 1) {1, σ + 2} = {0} := by
  have h1 : (2 * σ + 1) / 2 = σ := by omega
  have h2 : (2 * σ + 1) % 2 = 1 := by omega
  simp only [ActionModel.transition, semDom, h1, h2, hσ, if_true, one_ne_zero, if_false]
  ext x; simp

theorem interleave_cons_inv {u v cs : List ℕ} {c : ℕ} (h : Interleave u v (c :: cs)) :
    (∃ u', u = c :: u' ∧ Interleave u' v cs) ∨ (∃ v', v = c :: v' ∧ Interleave u v' cs) := by
  cases h with
  | left _ h => exact Or.inl ⟨_, rfl, h⟩
  | right _ h => exact Or.inr ⟨_, rfl, h⟩

/-- **The state forces the zipper**: an executable interleaving of a renamed word of `G` with a
renamed word of `G'` that returns to the goal is a zipper of two equal words. -/
theorem eq_of_exec {w w' cs : List ℕ} (hw : ∀ a ∈ w, a < bnd g₁ g₂) (hw' : ∀ a ∈ w', a < bnd g₁ g₂)
    (hint : Interleave (w.map (2 * · + 0)) (w'.map (2 * · + 1)) cs)
    (happ : (semDom g₁ g₂).SeqApplicable cs {0})
    (hgoal : ({0} : Set ℕ) ⊆ (semDom g₁ g₂).transitionSeq cs {0}) : w = w' := by
  induction w generalizing w' cs with
  | nil =>
    simp only [List.map_nil] at hint
    rw [hint.eq_of_nil_left] at happ
    cases w' with
    | nil => rfl
    | cons τ w' =>
      exfalso
      obtain ⟨h, -⟩ := happ
      simp only [List.map_cons] at h
      have := ((applicable_odd (hw' τ List.mem_cons_self)).1 h).1
      simp at this
  | cons σ w ih =>
    have hσ := hw σ List.mem_cons_self
    cases cs with
    | nil => exact absurd hint.length (by simp only [List.length_map, List.length_cons, List.length_nil]; omega)
    | cons c cs =>
      rcases interleave_cons_inv hint with ⟨u', hu, hint₁⟩ | ⟨v', hv, hint₁⟩
      · simp only [List.map_cons, List.cons.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        obtain ⟨-, happ₁⟩ := happ
        rw [transition_even hσ] at happ₁
        rw [ActionModel.transitionSeq_cons, transition_even hσ] at hgoal
        cases cs with
        | nil => simp at hgoal
        | cons c' cs =>
          rcases interleave_cons_inv hint₁ with ⟨u'', hu', -⟩ | ⟨v', hv', hint₂⟩
          · exfalso
            obtain ⟨σ', w₁, rfl, rfl⟩ : ∃ σ' w₁, w = σ' :: w₁ ∧ c' = 2 * σ' + 0 := by
              cases w with
              | nil => simp at hu'
              | cons σ' w₁ => simp only [List.map_cons, List.cons.injEq] at hu'; exact ⟨σ', w₁, rfl, hu'.1.symm⟩
            have := (applicable_even (hw σ' (by simp))).1 happ₁.1
            simp at this
          · obtain ⟨τ, w'₁, rfl, rfl⟩ : ∃ τ w'₁, w' = τ :: w'₁ ∧ c' = 2 * τ + 1 := by
              cases w' with
              | nil => simp at hv'
              | cons τ w'₁ => simp only [List.map_cons, List.cons.injEq] at hv'; exact ⟨τ, w'₁, rfl, hv'.1.symm⟩
            simp only [List.map_cons, List.cons.injEq] at hv'
            obtain ⟨-, rfl⟩ := hv'
            have hτ := hw' τ List.mem_cons_self
            obtain ⟨hap, happ₂⟩ := happ₁
            have h2 := ((applicable_odd hτ).1 hap).2
            obtain rfl : τ = σ := by simp at h2; omega
            rw [transition_odd hσ] at happ₂
            rw [ActionModel.transitionSeq_cons, transition_odd hσ] at hgoal
            rw [ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
              (fun a ha => hw' a (List.mem_cons_of_mem _ ha)) hint₂ happ₂ hgoal]
      · exfalso
        obtain ⟨τ, w'₁, rfl, rfl⟩ : ∃ τ w'₁, w' = τ :: w'₁ ∧ c = 2 * τ + 1 := by
          cases w' with
          | nil => simp at hv
          | cons τ w'₁ => simp only [List.map_cons, List.cons.injEq] at hv; exact ⟨τ, w'₁, rfl, hv.1.symm⟩
        have := ((applicable_odd (hw' τ List.mem_cons_self)).1 happ.1).1
        simp at this

/-- The zipper of a word with itself. -/
def zipper (w : List ℕ) : List ℕ := w.flatMap fun σ => [2 * σ + 0, 2 * σ + 1]

theorem interleave_zipper (w : List ℕ) :
    Interleave (w.map (2 * · + 0)) (w.map (2 * · + 1)) (zipper w) := by
  induction w with
  | nil => exact Interleave.nil
  | cons σ w ih => exact Interleave.left _ (Interleave.right _ ih)

theorem exec_zipper {w : List ℕ} (hw : ∀ a ∈ w, a < bnd g₁ g₂) :
    (semDom g₁ g₂).SeqApplicable (zipper w) {0} ∧
      (semDom g₁ g₂).transitionSeq (zipper w) {0} = {0} := by
  induction w with
  | nil => exact ⟨trivial, rfl⟩
  | cons σ w ih =>
    have hσ := hw σ List.mem_cons_self
    obtain ⟨h₁, h₂⟩ := ih fun a ha => hw a (List.mem_cons_of_mem _ ha)
    simp only [zipper, List.flatMap_cons, List.cons_append, List.nil_append] at h₁ h₂ ⊢
    refine ⟨⟨(applicable_even hσ).2 rfl, ?_⟩, ?_⟩
    · rw [transition_even hσ]
      exact ⟨(applicable_odd hσ).2 ⟨by simp, by simp⟩, by rw [transition_odd hσ]; exact h₁⟩
    · rw [ActionModel.transitionSeq_cons, transition_even hσ, ActionModel.transitionSeq_cons,
        transition_odd hσ]
      exact h₂

/-- **Correctness of the encoding (Thm. 4.1.1).** -/
theorem solvable_semProblem_iff : (semProblem g₁ g₂).Solvable ↔ Inter g₁ g₂ := by
  rw [semProblem, HTN.Problem.solvable_iff_netYield]
  have key : ∀ cs, (semDom g₁ g₂).NetYield
      (grid [[Sum.inr (2 * g₁.start)], [Sum.inr (2 * g₂.start + 1)]]) cs ↔
      ∃ w w', g₁.Lang w ∧ g₂.Lang w' ∧ Interleave (w.map (2 * · + 0)) (w'.map (2 * · + 1)) cs :=
    fun cs => (netYield_grid_iff semDom_grid).trans gridYield_tnI_iff
  constructor
  · rintro ⟨cs, hy, happ, hgoal⟩
    obtain ⟨w, w', hw, hw', hint⟩ := (key cs).1 hy
    obtain rfl := eq_of_exec (lt_bnd₁ hw) (lt_bnd₂ hw') hint happ hgoal
    exact ⟨w, hw, hw'⟩
  · rintro ⟨w, hw, hw'⟩
    obtain ⟨happ, hst⟩ := exec_zipper (g₁ := g₁) (g₂ := g₂) (lt_bnd₁ hw)
    refine ⟨zipper w, (key _).2 ⟨w, w, hw, hw', interleave_zipper w⟩, happ, ?_⟩
    show ({0} : Set ℕ) ⊆ (semDom g₁ g₂).transitionSeq (zipper w) {0}
    rw [hst]

end CFGEnc

end Article

end HTN
