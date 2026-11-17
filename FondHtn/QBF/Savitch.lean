import FondHtn.QBF.Basic
import HtnComplexity.Article.StripsShort
/-!
# STRIPS plan existence reduces to TQBF (Savitch's construction): the formula

For a STRIPS description `d` (`HTN.Article.StripsDesc`) let `F = f₀, …, f_{n-1}` be the
(deduplicated) list of all facts mentioned by `d` (`FOND.QBF.Savitch.allF`) and `A` the number of
actions.  States are bit vectors of length `n`; the variables of the vector `w` are
`vv w i = ⟨w, i⟩` (Cantor pairing), `i < n`.  With `K = n` levels:

* `X_r = vec(3r)`, `Y_r = vec(3r+1)`, `Z_r = vec(3r+2)`; `X_{r+1}`, `Y_{r+1}` are `vec(3r+3)`,
  `vec(3r+4)`; `b_r = ⟨3K+2, r⟩`; the choice variables `c_j = ⟨3K+3, j⟩`, `j ≤ A`;
* prefix: `∃X₀ ∃Y₀`, then for `r < K`: `∃Z_r ∀b_r ∃X_{r+1} ∃Y_{r+1}`, then `∃c₀ … ∃c_A`;
* matrix: `X₀ = s_I`, `Y₀ ⊨ goal`; for `r < K`: `b_r = 0 → X_{r+1} = X_r ∧ Y_{r+1} = Z_r` and
  `b_r = 1 → X_{r+1} = Z_r ∧ Y_{r+1} = Y_r` (`FOND.QBF.Savitch.stepCl`); at the bottom
  (`FOND.QBF.Savitch.baseCl`): some `c_j` holds, `c₀ → X_K = Y_K`, and
  `c_{j+1} → ` action `j` is applicable in `X_K` and `Y_K` is its result.

The bottom level states `Reach₀(X, Y)` ("`Y = X` or one action leads from `X` to `Y`"), each step
level `Reach_{k+1}(X, Y) ≡ ∃Z. Reach_k(X, Z) ∧ Reach_k(Z, Y)` with the usual universal choice of
the half.  The matrix is already in CNF (each implication is a set of clauses guarded by a
literal of `b_r` or `c_j`), so no Tseitin transformation is needed.

**Deviation from [CB21]:** this is the source problem of the repaired proof of Thm. 5.1 (TQBF,
proved PSPACE-hard here from Bylander's STRIPS hardness in the library).
-/

namespace FOND

namespace QBF

namespace Savitch

open HTN HTN.Article

/-! ## Clause gadgets -/

/-- Add the literal `g` to every clause (`g ∨ cls`). -/
def guard (g : Lit) (cls : List Clause) : List Clause := cls.map (g :: ·)

/-- `x ↔ y`. -/
def eq2 (x y : ℕ) : List Clause := [[(x, false), (y, true)], [(x, true), (y, false)]]

theorem sat_guard (g : Lit) (cls : List Clause) (σ : ℕ → Bool) :
    Sat (guard g cls) σ ↔ σ g.1 = g.2 ∨ Sat cls σ := by
  unfold Sat guard
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    List.mem_cons, exists_eq_or_imp]
  constructor
  · intro h
    by_cases hg : σ g.1 = g.2
    · exact Or.inl hg
    · exact Or.inr fun c hc => (h c hc).resolve_left hg
  · rintro (h | h) c hc
    · exact Or.inl h
    · exact Or.inr (h c hc)

theorem sat_eq2 (x y : ℕ) (σ : ℕ → Bool) : Sat (eq2 x y) σ ↔ σ x = σ y := by
  unfold Sat eq2
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    exists_eq_or_imp, exists_eq_left]
  cases σ x <;> cases σ y <;> simp

theorem sat_flatMap {β : Type} (l : List β) (f : β → List Clause) (σ : ℕ → Bool) :
    Sat (l.flatMap f) σ ↔ ∀ x ∈ l, Sat (f x) σ := by
  unfold Sat
  simp only [List.mem_flatMap, forall_exists_index, and_imp]
  exact ⟨fun h x hx c hc => h c x hx hc, fun h c x hx hc => h x hx c hc⟩

theorem sat_unit (l : Lit) (σ : ℕ → Bool) : Sat [[l]] σ ↔ σ l.1 = l.2 := by
  simp only [Sat, List.mem_singleton, forall_eq, exists_eq_left]

theorem sat_nil (σ : ℕ → Bool) : Sat [] σ := by simp [Sat]

theorem sat_ite (p : Prop) [Decidable p] (a b : List Clause) (σ : ℕ → Bool) :
    Sat (if p then a else b) σ ↔ (p → Sat a σ) ∧ (¬ p → Sat b σ) := by
  split_ifs with h <;> simp [h]

/-! ## Variables -/

/-- The variable `i` of the vector `w`. -/
def vv (w i : ℕ) : ℕ := Nat.pair w i

theorem vv_inj {w i w' i' : ℕ} : vv w i = vv w' i' ↔ w = w' ∧ i = i' := Nat.pair_eq_pair

/-- The variables of the vector `w`. -/
def vars (n w : ℕ) : List ℕ := (List.range n).map (vv w)

theorem vv_mem_vars {n w w' i : ℕ} : vv w' i ∈ vars n w ↔ w' = w ∧ i < n := by
  simp only [vars, List.mem_map, List.mem_range, vv_inj]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨rfl, hj⟩
  · rintro ⟨rfl, hi⟩; exact ⟨i, hi, rfl, rfl⟩

/-- An existential block. -/
def exB (l : List ℕ) : Prefix := l.map fun v => (false, v)

/-- The assignment `σ` with the variables of `l` overwritten by `τ`. -/
def updL (l : List ℕ) (τ σ : ℕ → Bool) : ℕ → Bool := fun x => if x ∈ l then τ x else σ x

theorem eval_exB (l : List ℕ) (Q : Prefix) (cls : List Clause) (σ : ℕ → Bool) :
    Eval (exB l ++ Q) cls σ ↔ ∃ τ, Eval Q cls (updL l τ σ) := eval_exBlock l Q cls σ

theorem updL_vars_self {n w i : ℕ} (hi : i < n) (τ σ : ℕ → Bool) :
    updL (vars n w) τ σ (vv w i) = τ (vv w i) := by
  simp [updL, vv_mem_vars, hi]

theorem updL_vars_ne {n w w' i : ℕ} (hw : w' ≠ w) (τ σ : ℕ → Bool) :
    updL (vars n w) τ σ (vv w' i) = σ (vv w' i) := by
  simp [updL, vv_mem_vars, hw]

/-- The vector `w` under `σ`. -/
def read (σ : ℕ → Bool) (w : ℕ) : ℕ → Bool := fun i => σ (vv w i)

/-- `vec U = vec V` (componentwise, `i < n`). -/
def eqs (n U V : ℕ) : List Clause := (List.range n).flatMap fun i => eq2 (vv U i) (vv V i)

theorem sat_eqs (n U V : ℕ) (σ : ℕ → Bool) :
    Sat (eqs n U V) σ ↔ ∀ i < n, σ (vv U i) = σ (vv V i) := by
  simp only [eqs, sat_flatMap, sat_eq2, List.mem_range]

/-- Quantifying over the values of a vector. -/
theorem exists_vec (w : ℕ) (P : (ℕ → Bool) → Prop) :
    (∃ τ : ℕ → Bool, P fun i => τ (vv w i)) ↔ ∃ V, P V := by
  constructor
  · rintro ⟨τ, h⟩; exact ⟨_, h⟩
  · rintro ⟨V, h⟩
    refine ⟨fun x => V (Nat.unpair x).2, ?_⟩
    simpa [vv, Nat.unpair_pair] using h

/-! ## The formula -/

variable (d : StripsDesc)

/-- All facts mentioned by the description. -/
def allF : List ℕ :=
  (d.init ++ d.goalPos ++ d.goalNeg ++
    d.actions.flatMap fun a => a.2.1 ++ a.2.2.1 ++ a.2.2.2.1 ++ a.2.2.2.2).dedup

/-- The number of facts. -/
abbrev nF : ℕ := (allF d).length

/-- The number of actions. -/
abbrev nA : ℕ := d.actions.length

/-- The universal variable of level `r`. -/
def bV (K r : ℕ) : ℕ := vv (3 * K + 2) r

/-- The choice variables. -/
def cV (K j : ℕ) : ℕ := vv (3 * K + 3) j

/-- The prefix of level `r`: `∃Z_r ∀b_r ∃X_{r+1} ∃Y_{r+1}`. -/
def stepPre (K r : ℕ) : Prefix :=
  exB (vars (nF d) (3 * r + 2)) ++ ((true, bV K r) ::
    (exB (vars (nF d) (3 * r + 3)) ++ exB (vars (nF d) (3 * r + 4))))

/-- The clauses of level `r`. -/
def stepCl (K r : ℕ) : List Clause :=
  guard (bV K r, true) (eqs (nF d) (3 * r + 3) (3 * r) ++ eqs (nF d) (3 * r + 4) (3 * r + 2)) ++
  guard (bV K r, false) (eqs (nF d) (3 * r + 3) (3 * r + 2) ++ eqs (nF d) (3 * r + 4) (3 * r + 1))

/-- The prefixes of the levels `r, …, r + c - 1`. -/
def steps (K : ℕ) : ℕ → ℕ → Prefix
  | _, 0 => []
  | r, c + 1 => stepPre d K r ++ steps K (r + 1) c

/-- The clauses of the levels `r, …, r + c - 1`. -/
def stepsCl (K : ℕ) : ℕ → ℕ → List Clause
  | _, 0 => []
  | r, c + 1 => stepCl d K r ++ stepsCl K (r + 1) c

/-- The prefix of the bottom: the choice variables. -/
def basePre (K : ℕ) : Prefix := exB ((List.range (nA d + 1)).map (cV K))

/-- "`a` leads from `vec X` to `vec Y`" (unguarded). -/
def actBody (a : ActDesc) (X Y : ℕ) : List Clause :=
  (List.range (nF d)).flatMap fun i =>
    (if (allF d).getI i ∈ a.2.1 then [[(vv X i, true)]] else []) ++
    (if (allF d).getI i ∈ a.2.2.1 then [[(vv X i, false)]] else []) ++
    (if (allF d).getI i ∈ a.2.2.2.1 then [[(vv Y i, true)]]
      else if (allF d).getI i ∈ a.2.2.2.2 then [[(vv Y i, false)]] else eq2 (vv X i) (vv Y i))

/-- The clauses of the bottom. -/
def baseCl (K : ℕ) : List Clause :=
  [(List.range (nA d + 1)).map fun j => (cV K j, true)] ++
  guard (cV K 0, false) (eqs (nF d) (3 * K) (3 * K + 1)) ++
  (List.range (nA d)).flatMap fun j =>
    guard (cV K (j + 1), false) (actBody d (d.actions.getI j) (3 * K) (3 * K + 1))

/-- `X₀ = s_I` and `Y₀ ⊨ goal`. -/
def initCl : List Clause :=
  (List.range (nF d)).flatMap fun i =>
    [[(vv 0 i, decide ((allF d).getI i ∈ d.init))]] ++
    (if (allF d).getI i ∈ d.goalPos then [[(vv 1 i, true)]] else []) ++
    (if (allF d).getI i ∈ d.goalNeg then [[(vv 1 i, false)]] else [])

/-- **The QBF of Savitch's construction** (with `K = n` levels). -/
def formula : Formula :=
  (exB (vars (nF d) 0) ++ (exB (vars (nF d) 1) ++ (steps d (nF d) 0 (nF d) ++ basePre d (nF d))),
    initCl d ++ (stepsCl d (nF d) 0 (nF d) ++ baseCl d (nF d)))

/-! ## Semantics of the levels -/

/-- The fact with index `i`. -/
abbrev fI (i : ℕ) : ℕ := (allF d).getI i

/-- "`a` leads from the state `X` to the state `Y`" on bit vectors. -/
def ActSem (a : ActDesc) (X Y : ℕ → Bool) : Prop :=
  (∀ i < nF d, fI d i ∈ a.2.1 → X i = true) ∧ (∀ i < nF d, fI d i ∈ a.2.2.1 → X i = false) ∧
  ∀ i < nF d, Y i = (decide (fI d i ∈ a.2.2.2.1) || (X i && !decide (fI d i ∈ a.2.2.2.2)))

/-- **Reachability in at most `2 ^ k` steps** on bit vectors. -/
def ReachV : ℕ → (ℕ → Bool) → (ℕ → Bool) → Prop
  | 0, X, Y => (∀ i < nF d, X i = Y i) ∨ ∃ j < nA d, ActSem d (d.actions.getI j) X Y
  | k + 1, X, Y => ∃ Z, ReachV k X Z ∧ ReachV k Z Y

theorem actSem_congr {a : ActDesc} {X Y X' Y' : ℕ → Bool} (hX : ∀ i < nF d, X i = X' i)
    (hY : ∀ i < nF d, Y i = Y' i) (h : ActSem d a X Y) : ActSem d a X' Y' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi hf => ?_, fun i hi hf => ?_, fun i hi => ?_⟩
  · rw [← hX i hi]; exact h1 i hi hf
  · rw [← hX i hi]; exact h2 i hi hf
  · rw [← hX i hi, ← hY i hi]; exact h3 i hi

theorem reachV_congr : ∀ (k : ℕ) {X Y X' Y' : ℕ → Bool}, (∀ i < nF d, X i = X' i) →
    (∀ i < nF d, Y i = Y' i) → ReachV d k X Y → ReachV d k X' Y'
  | 0, X, Y, X', Y', hX, hY, h => by
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl fun i hi => by rw [← hX i hi, ← hY i hi]; exact h i hi
    · exact Or.inr ⟨j, hj, actSem_congr d hX hY h⟩
  | k + 1, X, Y, X', Y', hX, hY, ⟨Z, h1, h2⟩ =>
    ⟨Z, reachV_congr k hX (fun _ _ => rfl) h1, reachV_congr k (fun _ _ => rfl) hY h2⟩

theorem sat_actBody (a : ActDesc) (X Y : ℕ) (σ : ℕ → Bool) :
    Sat (actBody d a X Y) σ ↔ ActSem d a (read σ X) (read σ Y) := by
  simp only [actBody, sat_flatMap, sat_append, sat_ite, sat_unit, sat_nil, sat_eq2,
    List.mem_range, ActSem, read, imp_true_iff, and_true]
  constructor
  · intro h
    refine ⟨fun i hi hf => (h i hi).1.1 hf, fun i hi hf => (h i hi).1.2 hf, fun i hi => ?_⟩
    obtain ⟨-, h3, h4⟩ := h i hi
    by_cases ha : fI d i ∈ a.2.2.2.1
    · simp [ha, h3 ha]
    · by_cases hd : fI d i ∈ a.2.2.2.2
      · simp [ha, hd, (h4 ha).1 hd]
      · simp [ha, hd, (h4 ha).2 hd]
  · rintro ⟨h1, h2, h3⟩ i hi
    refine ⟨⟨h1 i hi, h2 i hi⟩, fun ha => ?_, fun ha => ⟨fun hd => ?_, fun hd => ?_⟩⟩
    · simp [h3 i hi, ha]
    · simp [h3 i hi, ha, hd]
    · simp [h3 i hi, ha, hd]

end Savitch

end QBF

end FOND
