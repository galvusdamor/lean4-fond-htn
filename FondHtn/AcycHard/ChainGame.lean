import FondHtn.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
/-!
# The chain game and windows

A primitive task network that is a **disjoint union of chains** — one *control* chain and a
multiset of *pool* chains, pairwise unordered — is played as follows (strong OD / belief
solvability, `FOND.Problem.BeliefSolvable`): the player executes the head of some chain whose
action is applicable, nature picks an outcome; the player wins when all chains are empty.
This is `FOND.AcycHard.CWin`.  It is the game underlying the EXPSPACE lower bound for acyclic,
partially ordered problems (`doc/notes_acyc_expspace.md`): after the (unique) decomposition of
the hierarchy, the network is exactly such a union of chains.

**Windows.**  Pool actions are *gated*: a pool action `a` with gate `g` needs the token fact
`op g`, deletes it and adds `dn g`.  The control opens a window by `opn g` (adds `op g`) and
closes it by `cls g` (needs and deletes `dn g`).  Between the two, the player must execute
**exactly one** pool action with gate `g` (and nothing else); outside windows no pool action is
applicable.  Further control actions (`plain`) act on the data facts only, possibly
nondeterministically (nature), and the control ends with `refill` actions (add every fact)
that let the player empty the remaining pool ("trash").

* `FOND.AcycHard.WWin` — the **window game**: a program of windows and plain actions played on
  a multiset of pool chains and a set of data facts;
* **`FOND.AcycHard.cwin_iff_wwin`** — the chain game with the token encoding is the window game,
  provided the control ends with at least as many refills as the pool has tasks.
-/

namespace FOND

namespace AcycHard

set_option linter.unusedSectionVars false

open HTN

/-! ## The chain game -/

section ChainGame

variable {F CA PA : Type} [DecidableEq PA]

/-- **The chain game.**  `CWin δC δP ctl M s`: from the control chain `ctl`, the multiset `M` of
pool chains and the state `s`, the player can empty all chains whatever nature does. -/
inductive CWin (δC : CA → Action F) (δP : PA → Action F) :
    List CA → Multiset (List PA) → Set F → Prop
  /-- Everything is executed. -/
  | done {M : Multiset (List PA)} {s : Set F} (h : ∀ c ∈ M, c = []) : CWin δC δP [] M s
  /-- Execute the head of the control chain. -/
  | ctl {a : CA} {ctl : List CA} {M : Multiset (List PA)} {s : Set F}
      (happ : (δC a).Applicable s)
      (hall : ∀ s' ∈ (δC a).outcomes s, CWin δC δP ctl M s') : CWin δC δP (a :: ctl) M s
  /-- Execute the head of a pool chain. -/
  | pool {ctl : List CA} {M : Multiset (List PA)} {s : Set F} {a : PA} {c : List PA}
      (hc : a :: c ∈ M) (happ : (δP a).Applicable s)
      (hall : ∀ s' ∈ (δP a).outcomes s, CWin δC δP ctl (c ::ₘ M.erase (a :: c)) s') :
      CWin δC δP ctl M s

end ChainGame

/-! ## Tokens and windows -/

/-- Facts of the window encoding: window tokens `op g` (window `g` open), `dn g` (a task of
window `g` has been executed) and data facts. -/
inductive Tok (G D : Type)
  | op (g : G)
  | dn (g : G)
  | dat (d : D)
  deriving DecidableEq

/-- Instructions of the control chain. -/
inductive CI (G P : Type)
  | opn (g : G)
  | cls (g : G)
  | plain (p : P)
  | refill
  deriving DecidableEq

/-- Instructions of a window program: a window, or a plain data action. -/
inductive WI (G P : Type)
  | win (g : G)
  | plain (p : P)
  deriving DecidableEq

/-- A window system: gates, data preconditions and effects of the (deterministic) pool actions,
and data preconditions and (nondeterministic) effects of the plain control actions. -/
structure WSys (G D PA P : Type) where
  /-- The gate of a pool action. -/
  gate : PA → G
  /-- Data precondition of a pool action. -/
  pre : PA → Set D
  /-- Data add list of a pool action. -/
  add : PA → Set D
  /-- Data delete list of a pool action. -/
  del : PA → Set D
  /-- Data precondition of a plain action. -/
  ppre : P → Set D
  /-- Data effects of a plain action (nature chooses one). -/
  peffs : P → Set (Set D × Set D)

namespace WSys

variable {G D PA P : Type} (W : WSys G D PA P)

/-- The data facts as facts. -/
def idle (d : Set D) : Set (Tok G D) := Tok.dat '' d

/-- The FOND action of a pool action. -/
def δP (a : PA) : Action (Tok G D) where
  pre := insert (Tok.op (W.gate a)) (Tok.dat '' W.pre a)
  preNeg := ∅
  effs := {(insert (Tok.dn (W.gate a)) (Tok.dat '' W.add a),
    insert (Tok.op (W.gate a)) (Tok.dat '' W.del a))}

/-- The FOND action of a control instruction. -/
def δC : CI G P → Action (Tok G D)
  | .opn g => ⟨∅, ∅, {({Tok.op g}, ∅)}⟩
  | .cls g => ⟨{Tok.dn g}, ∅, {(∅, {Tok.dn g})}⟩
  | .plain p => ⟨Tok.dat '' W.ppre p, ∅,
      (fun e : Set D × Set D => ((Tok.dat '' e.1 : Set (Tok G D)), (Tok.dat '' e.2 : Set (Tok G D)))) ''
        W.peffs p⟩
  | .refill => ⟨∅, ∅, {(Set.univ, ∅)}⟩

/-- The control chain of a window program. -/
def expand : List (WI G P) → List (CI G P)
  | [] => []
  | .win g :: ws => .opn g :: .cls g :: expand ws
  | .plain p :: ws => .plain p :: expand ws

/-- The data state after a data effect `(add, del)`. -/
def upd (d : Set D) (add del : Set D) : Set D := (d \ del) ∪ add

variable [DecidableEq PA]

/-- **The window game.**  A window `g`: the player executes one pool action with gate `g`
whose data precondition holds.  A plain action: its precondition must hold and every outcome
must be won.  The empty program is won (the trash phase follows). -/
def WWin : List (WI G P) → Multiset (List PA) → Set D → Prop
  | [], _, _ => True
  | .win g :: ws, M, d => ∃ a c, a :: c ∈ M ∧ W.gate a = g ∧ W.pre a ⊆ d ∧
      WWin ws (c ::ₘ M.erase (a :: c)) (upd d (W.add a) (W.del a))
  | .plain p :: ws, M, d => W.ppre p ⊆ d ∧ ∀ e ∈ W.peffs p, WWin ws M (upd d e.1 e.2)

/-! ### Computations with the token facts -/

lemma dat_mem_idle {d : Set D} {x : D} : (Tok.dat x : Tok G D) ∈ idle d ↔ x ∈ d := by
  simp [idle]

lemma op_not_mem_idle {d : Set D} {g : G} : (Tok.op g : Tok G D) ∉ idle d := by
  simp [idle]

lemma dn_not_mem_idle {d : Set D} {g : G} : (Tok.dn g : Tok G D) ∉ idle d := by
  simp [idle]

lemma image_dat_subset_iff {d e : Set D} :
    (Tok.dat '' e : Set (Tok G D)) ⊆ idle d ↔ e ⊆ d := by
  constructor
  · intro h x hx
    exact dat_mem_idle.1 (h ⟨x, hx, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩
    exact ⟨x, h hx, rfl⟩

lemma image_dat_subset_insert_iff {d e : Set D} {f : Tok G D} (hf : ∀ x, f ≠ Tok.dat x) :
    (Tok.dat '' e : Set (Tok G D)) ⊆ insert f (idle d) ↔ e ⊆ d := by
  constructor
  · intro h x hx
    rcases h ⟨x, hx, rfl⟩ with h' | h'
    · exact absurd h'.symm (hf x)
    · exact dat_mem_idle.1 h'
  · rintro h _ ⟨x, hx, rfl⟩
    exact Or.inr ⟨x, h hx, rfl⟩

lemma applyEff_dat (d e₁ e₂ : Set D) :
    Action.applyEff ((Tok.dat '' e₁ : Set (Tok G D)), (Tok.dat '' e₂ : Set (Tok G D))) (idle d) =
      idle (upd d e₁ e₂) := by
  ext f
  cases f with
  | op g => simp [Action.applyEff, idle, upd]
  | dn g => simp [Action.applyEff, idle, upd]
  | dat x => simp [Action.applyEff, idle, upd]

/-- No pool action is applicable outside windows. -/
lemma not_applicable_idle (a : PA) (d : Set D) : ¬ (W.δP a).Applicable (idle d) := by
  intro h
  exact op_not_mem_idle (h.1 (Set.mem_insert _ _))

/-- No pool action is applicable after the window task has been executed. -/
lemma not_applicable_dn (a : PA) (d : Set D) (g : G) :
    ¬ (W.δP a).Applicable (insert (Tok.dn g) (idle d)) := by
  intro h
  rcases h.1 (Set.mem_insert _ _) with h' | h'
  · cases h'
  · exact op_not_mem_idle h'

lemma applicable_op_iff (a : PA) (d : Set D) (g : G) :
    (W.δP a).Applicable (insert (Tok.op g) (idle d)) ↔ W.gate a = g ∧ W.pre a ⊆ d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h.1 (Set.mem_insert _ _) with h' | h'
      · exact Tok.op.inj h'
      · exact absurd h' op_not_mem_idle
    · exact (image_dat_subset_insert_iff (fun x h => by cases h)).1
        (fun f hf => h.1 (Set.mem_insert_of_mem _ hf))
  · rintro ⟨rfl, h⟩
    refine ⟨?_, Set.empty_disjoint _⟩
    intro f hf
    rcases hf with rfl | hf
    · exact Set.mem_insert _ _
    · exact (image_dat_subset_insert_iff (fun x h => by cases h)).2 h hf

lemma outcomes_δP_op (a : PA) (d : Set D) :
    (W.δP a).outcomes (insert (Tok.op (W.gate a)) (idle d)) =
      {insert (Tok.dn (W.gate a)) (idle (upd d (W.add a) (W.del a)))} := by
  ext s'
  simp only [Action.outcomes, δP, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    ext f
    cases f with
    | op g => simp [Action.applyEff, idle]
    | dn g =>
      simp only [Action.applyEff, idle, Set.mem_union, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_image, reduceCtorEq, and_false, exists_false, or_false, Tok.dn.injEq]
      tauto
    | dat x => simp [Action.applyEff, idle, upd]
  · rintro rfl
    ext f
    cases f with
    | op g => simp [Action.applyEff, idle]
    | dn g =>
      simp only [Action.applyEff, idle, Set.mem_union, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_image, reduceCtorEq, and_false, exists_false, or_false, Tok.dn.injEq]
      tauto
    | dat x => simp [Action.applyEff, idle, upd]

lemma outcomes_opn (g : G) (d : Set D) :
    (W.δC (.opn g)).outcomes (idle d) = {insert (Tok.op g) (idle d)} := by
  ext s'
  simp only [Action.outcomes, δC, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  constructor
  · rintro rfl
    ext f; simp [Action.applyEff]
  · rintro rfl
    ext f; simp [Action.applyEff]

lemma applicable_opn (g : G) (s : Set (Tok G D)) : (W.δC (.opn g)).Applicable s :=
  ⟨Set.empty_subset _, Set.empty_disjoint _⟩

lemma not_applicable_cls_op (g g' : G) (d : Set D) :
    ¬ (W.δC (.cls g)).Applicable (insert (Tok.op g') (idle d)) := by
  intro h
  rcases h.1 (Set.mem_singleton _) with h' | h'
  · cases h'
  · exact dn_not_mem_idle h'

lemma applicable_cls_dn (g : G) (d : Set D) :
    (W.δC (.cls g)).Applicable (insert (Tok.dn g) (idle d)) :=
  ⟨by simp [δC], Set.empty_disjoint _⟩

lemma outcomes_cls_dn (g : G) (d : Set D) :
    (W.δC (.cls g)).outcomes (insert (Tok.dn g) (idle d)) = {idle d} := by
  ext s'
  simp only [Action.outcomes, δC, Set.mem_singleton_iff, exists_eq_left, Set.mem_setOf_eq]
  have : Action.applyEff ((∅ : Set (Tok G D)), ({Tok.dn g} : Set (Tok G D)))
      (insert (Tok.dn g) (idle d)) = idle d := by
    ext f
    cases f with
    | op g' => simp [Action.applyEff, idle]
    | dn g' =>
      simp only [Action.applyEff, Set.mem_union, Set.mem_diff, Set.mem_insert_iff,
        Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact absurd h1 dn_not_mem_idle
      · intro h; exact absurd h dn_not_mem_idle
    | dat x => simp [Action.applyEff, idle]
  rw [this]

lemma applicable_plain_iff (p : P) (d : Set D) :
    (W.δC (.plain p)).Applicable (idle d) ↔ W.ppre p ⊆ d := by
  constructor
  · intro h
    exact image_dat_subset_iff.1 h.1
  · intro h
    exact ⟨image_dat_subset_iff.2 h, Set.empty_disjoint _⟩

lemma mem_outcomes_plain (p : P) (d : Set D) (s' : Set (Tok G D)) :
    s' ∈ (W.δC (.plain p)).outcomes (idle d) ↔ ∃ e ∈ W.peffs p, s' = idle (upd d e.1 e.2) := by
  simp only [Action.outcomes, δC, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, applyEff_dat d e.1 e.2⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, (applyEff_dat d e.1 e.2).symm⟩

/-! ### The trash phase -/

/-- Total number of tasks of a pool. -/
def size (M : Multiset (List PA)) : ℕ := (M.map List.length).sum

omit [DecidableEq PA] in
lemma size_eq_zero {M : Multiset (List PA)} (h : size M = 0) : ∀ c ∈ M, c = [] := by
  intro c hc
  have := Multiset.sum_eq_zero_iff.1 h (c.length) (Multiset.mem_map_of_mem _ hc)
  exact List.length_eq_zero_iff.1 this

lemma size_step {M : Multiset (List PA)} {a : PA} {c : List PA} (h : a :: c ∈ M) :
    size (c ::ₘ M.erase (a :: c)) + 1 = size M := by
  conv_rhs => rw [← Multiset.cons_erase h]
  simp only [size, Multiset.map_cons, Multiset.sum_cons, List.length_cons]
  ring

lemma applicable_univ (a : PA) : (W.δP a).Applicable Set.univ :=
  ⟨Set.subset_univ _, Set.empty_disjoint _⟩

/-- **The trash phase**: with at least as many refills as remaining pool tasks, the player
empties the network. -/
theorem cwin_refill : ∀ (R : ℕ) (M : Multiset (List PA)) (s : Set (Tok G D)), size M ≤ R →
    CWin W.δC W.δP (List.replicate R .refill) M s := by
  intro R
  induction R with
  | zero =>
    intro M s h
    exact CWin.done (size_eq_zero (Nat.le_zero.1 h))
  | succ R ih =>
    intro M s h
    refine CWin.ctl ⟨Set.empty_subset _, Set.empty_disjoint _⟩ ?_
    intro s' _
    -- empty the pool chains one task at a time, before the next refill
    by_cases h0 : size M = 0
    · exact ih M s' (by omega)
    · have : ∃ c ∈ M, c ≠ [] := by
        by_contra hc
        push_neg at hc
        apply h0
        simp only [size]
        rw [Multiset.sum_eq_zero_iff]
        intro n hn
        obtain ⟨c, hc', rfl⟩ := Multiset.mem_map.1 hn
        simp [hc c hc']
      obtain ⟨c, hc, hne⟩ := this
      obtain ⟨a, c', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hs := size_step hc
      -- the state after the refill is `univ`
      have hs' : s' = Set.univ := by
        simp only [Action.outcomes, δC, Set.mem_singleton_iff, exists_eq_left,
          Set.mem_setOf_eq] at *
        rename_i hs''
        rw [hs'']
        ext f; simp [Action.applyEff]
      subst hs'
      exact CWin.pool hc (W.applicable_univ a) (fun s'' _ => ih _ s'' (by omega))

/-! ### The chain game is the window game -/

/-- **The chain game with the token encoding is the window game.** -/
theorem cwin_iff_wwin (R : ℕ) : ∀ (ws : List (WI G P)) (M : Multiset (List PA)) (d : Set D),
    size M ≤ R →
    (CWin W.δC W.δP (expand ws ++ List.replicate R .refill) M (idle d) ↔ W.WWin ws M d) := by
  intro ws
  induction ws with
  | nil =>
    intro M d h
    simp only [expand, List.nil_append, WWin, iff_true]
    exact W.cwin_refill R M _ h
  | cons w ws ih =>
    intro M d hM
    cases w with
    | plain p =>
      simp only [expand, List.cons_append, WWin]
      constructor
      · intro h
        cases h with
        | ctl happ hall =>
          refine ⟨(W.applicable_plain_iff p d).1 happ, fun e he => ?_⟩
          exact (ih M _ hM).1 (hall _ ((W.mem_outcomes_plain p d _).2 ⟨e, he, rfl⟩))
        | pool hc happ _ => exact absurd happ (W.not_applicable_idle _ d)
      · rintro ⟨hpre, hall⟩
        refine CWin.ctl ((W.applicable_plain_iff p d).2 hpre) ?_
        intro s' hs'
        obtain ⟨e, he, rfl⟩ := (W.mem_outcomes_plain p d _).1 hs'
        exact (ih M _ hM).2 (hall e he)
    | win g =>
      simp only [expand, List.cons_append, WWin]
      constructor
      · intro h
        cases h with
        | pool hc happ _ => exact absurd happ (W.not_applicable_idle _ d)
        | ctl _ hall =>
          have h1 := hall _ (by rw [W.outcomes_opn]; exact Set.mem_singleton _)
          cases h1 with
          | ctl happ _ => exact absurd happ (W.not_applicable_cls_op g g d)
          | @pool _ _ _ a c hc happ hall' =>
            obtain ⟨hg, hpre⟩ := (W.applicable_op_iff a d g).1 happ
            subst hg
            have h2 := hall' _ (by rw [W.outcomes_δP_op]; exact Set.mem_singleton _)
            refine ⟨a, c, hc, rfl, hpre, ?_⟩
            have hs := size_step hc
            cases h2 with
            | pool _ happ' _ => exact absurd happ' (W.not_applicable_dn _ _ _)
            | ctl _ hall'' =>
              have h3 := hall'' _ (by rw [W.outcomes_cls_dn]; exact Set.mem_singleton _)
              exact (ih _ _ (by omega)).1 h3
      · rintro ⟨a, c, hc, rfl, hpre, hw⟩
        have hs := size_step hc
        refine CWin.ctl (W.applicable_opn _ _) ?_
        intro s' hs'
        rw [W.outcomes_opn, Set.mem_singleton_iff] at hs'
        subst hs'
        refine CWin.pool hc ((W.applicable_op_iff a d _).2 ⟨rfl, hpre⟩) ?_
        intro s'' hs''
        rw [W.outcomes_δP_op, Set.mem_singleton_iff] at hs''
        subst hs''
        refine CWin.ctl (W.applicable_cls_dn _ _) ?_
        intro s''' hs'''
        rw [W.outcomes_cls_dn, Set.mem_singleton_iff] at hs'''
        subst hs'''
        exact (ih _ _ (by omega)).2 hw

end WSys

end AcycHard

end FOND
