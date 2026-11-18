import Mathlib.Computability.TMComputable
import ComplexityTheory.Complexity.CobhamTM.Codes
/-!
# A TM2 machine, one elementary operation at a time

A step of a `Turing.FinTM2` executes a whole statement tree (`Turing.TM2.stepAux`).  For the
simulation inside Cobham's class it is more convenient to execute one elementary operation at a
time: the *micro machine* `TMSim.μ` keeps the statement still to be executed in its
configuration and performs its first operation.  Every operation changes each stack by at most
one push or one pop, decided by finitely much information (the current statement, the internal
state and the tops of the stacks).

* `TMSim.micro_run` — if the machine goes from `c` to `h` in `s` steps, the micro machine goes
  from `c` to `h` in at most `s * depthMax` operations;
* `TMSim.Inv` — the invariant: the current statement is one of the finitely many statements of
  the program (`TMSim.Q`), and every symbol on a stack belongs to a finite set `TMSim.symFin`
  (the symbols the program can push, and the input symbols).
-/

namespace HTN.PTime.CobhamTM

namespace TMSim

open Turing

attribute [local instance] FinTM2.ΛFin FinTM2.σFin FinTM2.kFin FinTM2.Γk₀Fin

variable (tm : FinTM2)

open Classical in
/-- The statements of the program: all sub-statements of the bodies of the labels. -/
noncomputable def Q : Finset tm.Stmt :=
  Finset.univ.biUnion fun l => TM2.stmts₁ (tm.m l)

theorem m_mem_Q (l : tm.Λ) : tm.m l ∈ Q tm := by
  classical
  simp only [Q, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨l, TM2.stmts₁_self⟩

theorem mem_Q_of_sub {q q' : tm.Stmt} (hq : q ∈ Q tm) (h : q' ∈ TM2.stmts₁ q) : q' ∈ Q tm := by
  classical
  simp only [Q, Finset.mem_biUnion, Finset.mem_univ, true_and] at hq ⊢
  obtain ⟨l, hl⟩ := hq
  exact ⟨l, TM2.stmts₁_trans hl h⟩

/-! ### The micro machine -/

/-- A configuration of the micro machine: the statement still to execute (`none` once halted),
the internal state, the stacks. -/
structure MCfg where
  q : Option tm.Stmt
  v : tm.σ
  S : ∀ k, List (tm.Γ k)

/-- What an elementary operation does to one stack. -/
inductive Act (α : Type) where
  | keep
  | pop
  | push (a : α)

/-- Applying an action to a stack. -/
def Act.apply {α : Type} : Act α → List α → List α
  | .keep, l => l
  | .pop, l => l.tail
  | .push a, l => a :: l

/-- The action that pushes on stack `k` only. -/
def actAt {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) (a : Act (Γ k)) : ∀ k', Act (Γ k') :=
  Function.update (fun _ => .keep) k a

/-- One elementary operation, at the level of the control: the new statement, the new internal
state and the actions on the stacks, given the tops of the stacks. -/
def mstep : Option tm.Stmt → tm.σ → (∀ k, Option (tm.Γ k)) →
    Option tm.Stmt × tm.σ × (∀ k, Act (tm.Γ k))
  | none, v, _ => (none, v, fun _ => .keep)
  | some (.push k f q), v, _ => (some q, v, actAt k (.push (f v)))
  | some (.peek k f q), v, h => (some q, f v (h k), fun _ => .keep)
  | some (.pop k f q), v, h => (some q, f v (h k), actAt k .pop)
  | some (.load a q), v, _ => (some q, a v, fun _ => .keep)
  | some (.branch p q₁ q₂), v, _ => (some (cond (p v) q₁ q₂), v, fun _ => .keep)
  | some (.goto l), v, _ => (some (tm.m (l v)), v, fun _ => .keep)
  | some .halt, v, _ => (none, v, fun _ => .keep)

/-- The micro machine. -/
def μ (c : MCfg tm) : MCfg tm :=
  let r := mstep tm c.q c.v fun k => (c.S k).head?
  ⟨r.1, r.2.1, fun k => (r.2.2 k).apply (c.S k)⟩

/-- A configuration of the machine as a configuration of the micro machine. -/
def toM (c : tm.Cfg) : MCfg tm := ⟨c.l.map tm.m, c.var, c.stk⟩

/-- The depth of a statement: the number of elementary operations along its longest branch. -/
def depth : tm.Stmt → ℕ
  | .push _ _ q => depth q + 1
  | .peek _ _ q => depth q + 1
  | .pop _ _ q => depth q + 1
  | .load _ q => depth q + 1
  | .branch _ q₁ q₂ => max (depth q₁) (depth q₂) + 1
  | .goto _ => 1
  | .halt => 1

/-- The largest depth of a body. -/
noncomputable def depthMax : ℕ := Finset.univ.sup fun l => depth tm (tm.m l)

theorem actAt_apply_update {K : Type} [DecidableEq K] {Γ : K → Type} (k : K) (a : Act (Γ k))
    (S : ∀ k, List (Γ k)) :
    (fun k' => (actAt k a k').apply (S k')) = Function.update S k (a.apply (S k)) := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [actAt]
  · simp [actAt, h, Act.apply]

theorem μ_halted (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    μ tm ⟨none, v, S⟩ = ⟨none, v, S⟩ := rfl

theorem iterate_μ_halted (v : tm.σ) (S : ∀ k, List (tm.Γ k)) (n : ℕ) :
    (μ tm)^[n] ⟨none, v, S⟩ = ⟨none, v, S⟩ :=
  Function.iterate_fixed (μ_halted tm v S) n

/-- **One statement, operation by operation.** -/
theorem micro_stepAux (q : tm.Stmt) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    ∃ n ≤ depth tm q, (μ tm)^[n] ⟨some q, v, S⟩ = toM tm (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    obtain ⟨n, hn, h⟩ := ih v (Function.update S k (f v :: S k))
    refine ⟨n + 1, by simp [depth]; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simp only [TM2.stepAux]
    rw [← h]
    simp only [μ, mstep]
    rw [actAt_apply_update]
    rfl
  | peek k f q ih =>
    obtain ⟨n, hn, h⟩ := ih (f v (S k).head?) S
    refine ⟨n + 1, by simp [depth]; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simp only [TM2.stepAux]
    rw [← h]
    rfl
  | pop k f q ih =>
    obtain ⟨n, hn, h⟩ := ih (f v (S k).head?) (Function.update S k (S k).tail)
    refine ⟨n + 1, by simp [depth]; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simp only [TM2.stepAux]
    rw [← h]
    simp only [μ, mstep]
    rw [actAt_apply_update]
    rfl
  | load a q ih =>
    obtain ⟨n, hn, h⟩ := ih (a v) S
    refine ⟨n + 1, by simp [depth]; omega, ?_⟩
    rw [Function.iterate_succ_apply]
    simp only [TM2.stepAux]
    rw [← h]
    rfl
  | branch p q₁ q₂ ih₁ ih₂ =>
    cases hp : p v
    · obtain ⟨n, hn, h⟩ := ih₂ v S
      refine ⟨n + 1, by simp [depth]; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simp only [TM2.stepAux, hp, cond_false]
      rw [← h]
      simp [μ, mstep, hp, Act.apply]
    · obtain ⟨n, hn, h⟩ := ih₁ v S
      refine ⟨n + 1, by simp [depth]; omega, ?_⟩
      rw [Function.iterate_succ_apply]
      simp only [TM2.stepAux, hp, cond_true]
      rw [← h]
      simp [μ, mstep, hp, Act.apply]
  | goto l =>
    exact ⟨1, le_rfl, rfl⟩
  | halt =>
    exact ⟨1, le_rfl, rfl⟩

theorem depth_le_depthMax (l : tm.Λ) : depth tm (tm.m l) ≤ depthMax tm :=
  Finset.le_sup (f := fun l => depth tm (tm.m l)) (Finset.mem_univ l)

theorem iterate_bind_none {α : Type*} (f : α → Option α) (n : ℕ) :
    (flip Option.bind f)^[n] none = none :=
  Function.iterate_fixed rfl n

/-- **A run of the machine, operation by operation.** -/
theorem micro_run : ∀ (s : ℕ) (c h : tm.Cfg),
    (flip Option.bind tm.step)^[s] (some c) = some h →
      ∃ n ≤ s * depthMax tm, (μ tm)^[n] (toM tm c) = toM tm h
  | 0, c, h, e => by
    simp only [Function.iterate_zero, id_eq, Option.some.injEq] at e
    exact ⟨0, Nat.zero_le _, by rw [e]; rfl⟩
  | s + 1, c, h, e => by
    rw [Function.iterate_succ_apply] at e
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none =>
      simp only [flip, Option.bind_some, FinTM2.step, TM2.step] at e
      rw [iterate_bind_none] at e
      cases e
    | some l =>
      simp only [flip, Option.bind_some, FinTM2.step, TM2.step] at e
      obtain ⟨n₁, hn₁, h₁⟩ := micro_stepAux tm (tm.m l) v S
      obtain ⟨n₂, hn₂, h₂⟩ := micro_run s _ h e
      refine ⟨n₂ + n₁, ?_, ?_⟩
      · have := depth_le_depthMax tm l
        rw [Nat.succ_mul]; omega
      · rw [Function.iterate_add_apply]
        change (μ tm)^[n₂] ((μ tm)^[n₁] ⟨some (tm.m l), v, S⟩) = _
        rw [h₁, h₂]

/-! ### The finite set of stack symbols, and the invariant -/

/-- The symbols that can be on stack `k`: those the program pushes, and the input symbols. -/
def symSet (k : tm.K) : Set (tm.Γ k) :=
  {γ | (∃ q ∈ Q tm, ∃ (f : tm.σ → tm.Γ k) (q' : tm.Stmt) (v : tm.σ),
      q = TM2.Stmt.push k f q' ∧ γ = f v) ∨
    ∃ (h : tm.k₀ = k) (g : tm.Γ tm.k₀), γ = h ▸ g}

theorem symSet_finite (k : tm.K) : (symSet tm k).Finite := by
  have h1 : {γ : tm.Γ k | ∃ q ∈ Q tm, ∃ (f : tm.σ → tm.Γ k) (q' : tm.Stmt) (v : tm.σ),
      q = TM2.Stmt.push k f q' ∧ γ = f v}.Finite := by
    have : {γ : tm.Γ k | ∃ q ∈ Q tm, ∃ (f : tm.σ → tm.Γ k) (q' : tm.Stmt) (v : tm.σ),
        q = TM2.Stmt.push k f q' ∧ γ = f v} ⊆
        ⋃ q ∈ (Q tm : Set tm.Stmt), ⋃ v : tm.σ,
          {γ | ∃ (f : tm.σ → tm.Γ k) (q' : tm.Stmt), q = TM2.Stmt.push k f q' ∧ γ = f v} := by
      rintro γ ⟨q, hq, f, q', v, rfl, rfl⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨_, hq, v, f, q', rfl, rfl⟩
    refine Set.Finite.subset ?_ this
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun q _ => Set.finite_iUnion fun v => ?_
    refine Set.Subsingleton.finite ?_
    rintro γ ⟨f, q', rfl, rfl⟩ γ' ⟨f', q'', e, rfl⟩
    cases e
    rfl
  have h2 : {γ : tm.Γ k | ∃ (h : tm.k₀ = k) (g : tm.Γ tm.k₀), γ = h ▸ g}.Finite := by
    by_cases h : tm.k₀ = k
    · subst h
      exact Set.toFinite _
    · convert Set.finite_empty
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h', -⟩
      exact h h'
  exact (h1.union h2).subset fun γ hγ => hγ

/-- The finite set of symbols of stack `k`. -/
noncomputable def symFin (k : tm.K) : Finset (tm.Γ k) := (symSet_finite tm k).toFinset

theorem mem_symFin_push {k : tm.K} {f : tm.σ → tm.Γ k} {q' : tm.Stmt}
    (hq : TM2.Stmt.push k f q' ∈ Q tm) (v : tm.σ) : f v ∈ symFin tm k := by
  simp only [symFin, Set.Finite.mem_toFinset]
  exact Or.inl ⟨_, hq, f, q', v, rfl, rfl⟩

theorem mem_symFin_input (g : tm.Γ tm.k₀) : g ∈ symFin tm tm.k₀ := by
  simp only [symFin, Set.Finite.mem_toFinset]
  exact Or.inr ⟨rfl, g, rfl⟩

/-- The invariant of the micro machine. -/
def Inv (c : MCfg tm) : Prop :=
  (∀ q, c.q = some q → q ∈ Q tm) ∧ ∀ k, ∀ γ ∈ c.S k, γ ∈ symFin tm k

theorem mem_apply_of {α : Type} {P : α → Prop} {a : Act α} {l : List α}
    (hl : ∀ γ ∈ l, P γ) (ha : ∀ x, a = .push x → P x) : ∀ γ ∈ a.apply l, P γ := by
  cases a with
  | keep => exact hl
  | pop => exact fun γ hγ => hl γ (List.mem_of_mem_tail hγ)
  | push x =>
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact ha _ rfl
    · exact hl γ hγ

theorem sub_mem_Q {q q' : tm.Stmt} (hq : q ∈ Q tm)
    (h : q' ∈ TM2.stmts₁ q) : q' ∈ Q tm := mem_Q_of_sub tm hq h

/-- The actions of an operation push only symbols of the finite sets. -/
theorem mstep_push_mem {q : tm.Stmt} (hq : q ∈ Q tm) (v : tm.σ) (h : ∀ k, Option (tm.Γ k))
    (k : tm.K) (x : tm.Γ k) (hx : (mstep tm (some q) v h).2.2 k = .push x) : x ∈ symFin tm k := by
  cases q with
  | push k' f q' =>
    simp only [mstep, actAt] at hx
    by_cases hk : k = k'
    · subst hk
      simp only [Function.update_self, Act.push.injEq] at hx
      rw [← hx]
      exact mem_symFin_push tm hq v
    · simp [Function.update_of_ne hk] at hx
  | pop k' f q' =>
    simp only [mstep, actAt] at hx
    by_cases hk : k = k'
    · subst hk; simp at hx
    · simp [Function.update_of_ne hk] at hx
  | peek => simp [mstep] at hx
  | load => simp [mstep] at hx
  | branch => simp [mstep] at hx
  | goto => simp [mstep] at hx
  | halt => simp [mstep] at hx

theorem mstep_q_mem {q : tm.Stmt} (hq : q ∈ Q tm) (v : tm.σ) (h : ∀ k, Option (tm.Γ k))
    (q' : tm.Stmt) (hq' : (mstep tm (some q) v h).1 = some q') : q' ∈ Q tm := by
  classical
  cases q with
  | push k f q₀ =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    exact sub_mem_Q tm hq (by simp only [TM2.stmts₁, Finset.mem_insert]; exact Or.inr TM2.stmts₁_self)
  | peek k f q₀ =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    exact sub_mem_Q tm hq (by simp only [TM2.stmts₁, Finset.mem_insert]; exact Or.inr TM2.stmts₁_self)
  | pop k f q₀ =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    exact sub_mem_Q tm hq (by simp only [TM2.stmts₁, Finset.mem_insert]; exact Or.inr TM2.stmts₁_self)
  | load a q₀ =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    exact sub_mem_Q tm hq (by simp only [TM2.stmts₁, Finset.mem_insert]; exact Or.inr TM2.stmts₁_self)
  | branch p q₁ q₂ =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    cases p v
    · exact sub_mem_Q tm hq (by
        simp only [TM2.stmts₁, Finset.mem_insert, Finset.mem_union, cond_false]
        exact Or.inr (Or.inr TM2.stmts₁_self))
    · exact sub_mem_Q tm hq (by
        simp only [TM2.stmts₁, Finset.mem_insert, Finset.mem_union, cond_true]
        exact Or.inr (Or.inl TM2.stmts₁_self))
  | goto l =>
    simp only [mstep, Option.some.injEq] at hq'; subst hq'
    exact m_mem_Q tm _
  | halt => simp [mstep] at hq'

/-- **The invariant is preserved.** -/
theorem Inv.step {c : MCfg tm} (hc : Inv tm c) : Inv tm (μ tm c) := by
  obtain ⟨hq, hS⟩ := hc
  obtain ⟨q, v, S⟩ := c
  cases q with
  | none =>
    exact ⟨fun q' h => by simp [TMSim.μ, mstep] at h, fun k => by
      simpa [TMSim.μ, mstep, Act.apply] using hS k⟩
  | some q =>
    have hqQ : q ∈ Q tm := hq q rfl
    refine ⟨fun q' h => mstep_q_mem tm hqQ v _ q' h, fun k => ?_⟩
    exact mem_apply_of (hS k) fun x hx => mstep_push_mem tm hqQ v _ k x hx

theorem Inv.iterate {c : MCfg tm} (hc : Inv tm c) (n : ℕ) : Inv tm ((μ tm)^[n] c) := by
  induction n with
  | zero => exact hc
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.step

/-- An operation lengthens each stack by at most one symbol. -/
theorem length_μ_le (c : MCfg tm) (k : tm.K) : ((μ tm c).S k).length ≤ (c.S k).length + 1 := by
  simp only [TMSim.μ]
  cases (mstep tm c.q c.v fun k => (c.S k).head?).2.2 k with
  | keep => simp [Act.apply]
  | pop => simp [Act.apply]; omega
  | push x => simp [Act.apply]

theorem length_iterate_μ_le (c : MCfg tm) (k : tm.K) (n : ℕ) :
    (((μ tm)^[n] c).S k).length ≤ (c.S k).length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have := length_μ_le tm ((μ tm)^[n] c) k
    omega

end TMSim

end HTN.PTime.CobhamTM
