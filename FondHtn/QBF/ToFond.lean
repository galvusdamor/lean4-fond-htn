import FondHtn.QBF.Basic
import FondHtn.QBF.Game
import FondHtn.Prim.WeakHard
/-!
# TQBF reduces to strong OD plan existence of primitive problems

The reduction behind the repaired hardness proof of [CB21, Thm. 5.1].  **Deviation from
[CB21]:** the paper reduces from `(m, n, k)`-games (k-in-a-row), and that construction is
incorrect (catalogue G9); we reduce from TQBF instead.  No negative preconditions are used, so the
target problems are in the fragment of [CB21] (positive preconditions only).

For a QBF `φ` with prefix `(q₀, v₀), …, (q_{m-1}, v_{m-1})` and clauses `c₀, …, c_{k-1}`, let
`L = [(c, ℓ) | c < k, ℓ ∈ c_c]` (`FOND.QBF.ToFond.lits`).  Facts:

* `lf v b = 4v + [b]`: "variable `v` has value `b`" (two facts per variable);
* `satF c = 4c + 2`: "clause `c` is satisfied"; `winF = 3`.

Tasks (each task `i` is labelled by its own action `i`; `N = 2m + 2 + |L|`):

* block `p < m` consists of the tasks `2p` and `2p+1`.  For `∃ v_p`, task `2p + b` sets `v_p` to
  `b` (adds `lf v_p b`, deletes `lf v_p ¬b`): the policy chooses the order and the task executed
  last fixes the value.  For `∀ v_p`, both tasks have the two outcomes "set `v_p` to `true`" and
  "set `v_p` to `false`": nature fixes the value;
* `2m` (**fin**): precondition `{satF c | c < k}`, adds `winF`;
* `2m + 1` (**clear**): precondition `{winF}`, adds every literal fact `lf ℓ` (`ℓ` in `L`), so every
  remaining check task becomes executable;
* `2m + 2 + i` (**check** of `(c, ℓ) = L[i]`): precondition `{lf ℓ}`, adds `satF c`.

Order: every task of block `p` precedes every task of every block `p' > p` and every non-block
task (`FOND.QBF.ToFond.Ord`); the listed pairs are transitively closed.  `s_I = {lf v false |
v occurs in a clause}` (free variables read as `false`).

**Correctness** (`FOND.QBF.ToFond.strongOD_iff`): strong OD solvable iff `φ` is true.  While a
block is open only its two tasks are executable; afterwards the state encodes the current
assignment.  After the last block, `fin` must be executed before `clear` (only `fin` adds `winF`),
so every clause must have been marked by a check task whose literal is true; conversely, if the
assignment satisfies the matrix, mark every clause, run `fin`, `clear`, and the remaining checks.
-/

namespace FOND

namespace QBF

namespace ToFond

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

/-! ## The encoding -/

/-- The fact "`v` has value `b`". -/
def lf (v : ℕ) (b : Bool) : ℕ := 4 * v + b.toNat

/-- The fact "clause `c` is satisfied". -/
def satF (c : ℕ) : ℕ := 4 * c + 2

/-- The fact "all clauses are satisfied". -/
def winF : ℕ := 3

/-- The literal occurrences `(clause index, literal)`. -/
def lits (φ : Formula) : List (ℕ × Lit) :=
  (List.range φ.2.length).flatMap fun c => (φ.2.getI c).map fun l => (c, l)

/-- The number of tasks. -/
def nT (φ : Formula) : ℕ := 2 * φ.1.length + 2 + (lits φ).length

/-- The effect "set `v` to `b`". -/
def setEff (v : ℕ) (b : Bool) : List ℕ × List ℕ := ([lf v b], [lf v (!b)])

/-- The action of task `i`. -/
def act (φ : Formula) (i : ℕ) : FActDesc :=
  if i < 2 * φ.1.length then
    (i, [], [], if (φ.1.getI (i / 2)).1 then
      [setEff (φ.1.getI (i / 2)).2 true, setEff (φ.1.getI (i / 2)).2 false]
      else [setEff (φ.1.getI (i / 2)).2 (decide (i % 2 = 1))])
  else if i = 2 * φ.1.length then
    (i, (List.range φ.2.length).map satF, [], [([winF], [])])
  else if i = 2 * φ.1.length + 1 then
    (i, [winF], [], [((lits φ).map fun p => lf p.2.1 p.2.2, [])])
  else
    (i, [lf ((lits φ).getI (i - (2 * φ.1.length + 2))).2.1
      ((lits φ).getI (i - (2 * φ.1.length + 2))).2.2], [],
      [([satF ((lits φ).getI (i - (2 * φ.1.length + 2))).1], [])])

/-- The order: block tasks precede the tasks of later blocks and all non-block tasks. -/
def Ord (m a b : ℕ) : Prop := a < 2 * m ∧ (2 * m ≤ b ∨ a / 2 < b / 2)

instance (m a b : ℕ) : Decidable (Ord m a b) := by unfold Ord; infer_instance

/-- The listed ordering pairs. -/
def ordL (φ : Formula) : List (ℕ × ℕ) :=
  (List.range (nT φ)).flatMap fun b =>
    ((List.range (nT φ)).filter fun a => decide (Ord φ.1.length a b)).map fun a => (a, b)

/-- The initial task network. -/
def tn (φ : Formula) : TnDesc :=
  (List.range (nT φ), ordL φ, (List.range (nT φ)).map fun i => (i, false, i))

/-- **The encoding.** -/
def desc (φ : Formula) : FProbDesc :=
  (((List.range (nT φ)).map (act φ), []), ((lits φ).map (fun p => lf p.2.1 false), tn φ))

/-! ## Facts -/

theorem lf_inj {v w : ℕ} {b c : Bool} : lf v b = lf w c ↔ v = w ∧ b = c := by
  unfold lf
  constructor
  · intro h; cases b <;> cases c <;> simp at h ⊢ <;> omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem lf_ne_satF (v : ℕ) (b : Bool) (c : ℕ) : lf v b ≠ satF c := by
  unfold lf satF; cases b <;> simp <;> omega

theorem lf_ne_winF (v : ℕ) (b : Bool) : lf v b ≠ winF := by
  unfold lf winF; cases b <;> simp <;> omega

theorem satF_ne_winF (c : ℕ) : satF c ≠ winF := by unfold satF winF; omega

theorem satF_inj {c c' : ℕ} : satF c = satF c' ↔ c = c' := by unfold satF; omega

variable {φ : Formula}

theorem mem_lits {p : ℕ × Lit} : p ∈ lits φ ↔ p.1 < φ.2.length ∧ p.2 ∈ φ.2.getI p.1 := by
  obtain ⟨c, l⟩ := p
  simp only [lits, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨c', hc', l', hl', rfl, rfl⟩; exact ⟨hc', hl'⟩
  · rintro ⟨hc, hl⟩; exact ⟨c, hc, l, hl, rfl, rfl⟩

theorem getI_mem_lits {i : ℕ} (hi : i < (lits φ).length) : (lits φ).getI i ∈ lits φ := by
  rw [List.getI_eq_getElem _ hi]; exact List.getElem_mem hi

theorem exists_idx_lits {p : ℕ × Lit} (hp : p ∈ lits φ) :
    ∃ i, i < (lits φ).length ∧ (lits φ).getI i = p := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  exact ⟨i, hi, List.getI_eq_getElem _ hi⟩

/-! ## Well-formedness -/

theorem act_name (i : ℕ) : (act φ i).1 = i := by
  unfold act; split_ifs <;> rfl

theorem names_desc : (desc φ).actions.map FActDesc.name = List.range (nT φ) := by
  simp only [desc, FProbDesc.actions, List.map_map]
  conv_rhs => rw [← List.map_id (List.range (nT φ))]
  exact List.map_congr_left fun i _ => act_name i

theorem mem_ordL {a b : ℕ} : (a, b) ∈ ordL φ ↔ a < nT φ ∧ b < nT φ ∧ Ord φ.1.length a b := by
  simp only [ordL, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨b', hb', a', ⟨ha', ho⟩, rfl, rfl⟩; exact ⟨ha', hb', ho⟩
  · rintro ⟨ha, hb, ho⟩; exact ⟨b, hb, a, ⟨ha, ho⟩, rfl, rfl⟩

theorem tnValid_tn : TnValid (desc φ).Declared (tn φ) where
  nodup := List.nodup_range
  ord_mem := by
    rintro ⟨a, b⟩ hq
    have := mem_ordL.1 hq
    show a ∈ List.range (nT φ) ∧ b ∈ List.range (nT φ)
    simp only [List.mem_range]; omega
  irrefl := fun a h => by
    have := (mem_ordL.1 h).2.2
    unfold Ord at this; omega
  trans := fun a b c h1 h2 => by
    have h1' := mem_ordL.1 h1; have h2' := mem_ordL.1 h2
    refine mem_ordL.2 ⟨h1'.1, h2'.2.1, ?_⟩
    obtain ⟨-, -, ha, hab⟩ := h1'
    obtain ⟨-, -, hb, hbc⟩ := h2'
    unfold Ord at *
    omega
  lbl_perm := by simp [tn, TnDesc.lbl, TnDesc.ids, List.map_map, Function.comp_def]
  prim_ok := by
    intro q hq _
    simp only [tn, TnDesc.lbl, List.mem_map, List.mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    unfold FProbDesc.Declared
    rw [names_desc]; exact List.mem_range.2 hi

theorem effs_act_ne (i : ℕ) : (act φ i).2.2.2 ≠ [] := by
  unfold act; split_ifs <;> simp

theorem valid_desc : (desc φ).Valid where
  names_nodup := by rw [names_desc]; exact List.nodup_range
  effs_ne := by
    intro a ha
    simp only [desc, FProbDesc.actions, List.mem_map] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact effs_act_ne i
  tnI := tnValid_tn
  methods := by simp [desc, FProbDesc.methods]

theorem tnI_desc : (desc φ).toProblem.tnI = (tn φ).toTaskNetwork := rfl

theorem label_tn {i : ℕ} (hi : i < nT φ) : (tn φ).label i = Sum.inl i := by
  unfold TnDesc.label
  rw [show (tn φ).lbl = (List.range (nT φ)).map fun i => (i, (false, i)) from rfl,
    Undec.lookup_map_self _ _ (List.mem_range.2 hi)]

theorem mem_T_tn {i : ℕ} : i ∈ (tn φ).toTaskNetwork.T ↔ i < nT φ := by
  simp [TnDesc.toTaskNetwork, tn, TnDesc.ids]

theorem ord_tn {a b : ℕ} :
    (tn φ).toTaskNetwork.ord a b ↔ a < nT φ ∧ b < nT φ ∧ Ord φ.1.length a b := by
  show (tn φ).ordOf a b ↔ _
  rw [tnValid_tn.ordOf_iff]; exact mem_ordL

theorem prim_desc : FClass.PRIM (desc φ).toProblem := by
  intro t ht
  exact ⟨t, label_tn (mem_T_tn.1 ht)⟩

theorem tnI_isPrimitive : (desc φ).toProblem.tnI.IsPrimitive := by
  intro t ht
  exact ⟨t, label_tn (mem_T_tn.1 ht)⟩

theorem δ_desc {a : ℕ} (ha : a < nT φ) : (desc φ).toProblem.δ a = (act φ a).toAction := by
  have hm : act φ a ∈ (desc φ).actions := by
    simp only [desc, FProbDesc.actions, List.mem_map, List.mem_range]
    exact ⟨a, ha, rfl⟩
  have := FProbDesc.δ_of_mem valid_desc hm
  rw [show (act φ a).name = a from act_name a] at this
  exact this

/-! ## The game -/

/-- The game on the encoding. -/
abbrev W (φ : Formula) : Finset ℕ → Set ℕ → Prop :=
  (desc φ).toProblem.Win (desc φ).toProblem.tnI

theorem w_step {D : Finset ℕ} {s : Set ℕ} {t : ℕ} (ht : t < nT φ) (htD : t ∉ D)
    (hpred : ∀ t' < nT φ, Ord φ.1.length t' t → t' ∈ D) (happ : (act φ t).toAction.Applicable s)
    (hall : ∀ s' ∈ (act φ t).toAction.outcomes s, W φ (insert t D) s') : W φ D s := by
  refine Problem.Win.step (t := t) (a := t) (mem_T_tn.2 ht) htD (fun t' ht' ho => ?_)
    (label_tn ht) ?_ ?_
  · rw [tnI_desc, ord_tn] at ho
    exact hpred t' ho.1 ho.2.2
  · rw [δ_desc ht]; exact happ
  · rw [δ_desc ht]; exact hall

theorem w_cases {D : Finset ℕ} {s : Set ℕ} (h : W φ D s) :
    (∀ i < nT φ, i ∈ D) ∨ ∃ t < nT φ, t ∉ D ∧ (∀ t' < nT φ, Ord φ.1.length t' t → t' ∈ D) ∧
      (act φ t).toAction.Applicable s ∧
      ∀ s' ∈ (act φ t).toAction.outcomes s, W φ (insert t D) s' := by
  cases h with
  | done h => exact Or.inl fun i hi => h (mem_T_tn.2 hi)
  | @step _ _ t a ht htD hpred hα happ hall =>
    have ht' := mem_T_tn.1 ht
    have hat : a = t := by
      change (tn φ).label t = _ at hα
      rw [label_tn ht'] at hα; exact (Sum.inl_injective hα).symm
    subst hat
    rw [δ_desc ht'] at happ hall
    refine Or.inr ⟨a, ht', htD, fun t' ht'' ho => hpred t' (mem_T_tn.2 ht'') ?_, happ, hall⟩
    rw [tnI_desc, ord_tn]; exact ⟨ht'', ht', ho⟩

/-! ### The actions -/

theorem applicable_iff (i : ℕ) (s : Set ℕ) :
    (act φ i).toAction.Applicable s ↔ ∀ f ∈ (act φ i).2.1, f ∈ s := by
  have : (act φ i).2.2.1 = [] := by unfold act; split_ifs <;> rfl
  simp only [Action.Applicable, FActDesc.toAction, this, List.not_mem_nil, Set.setOf_false,
    Set.empty_disjoint, and_true]
  exact ⟨fun h f hf => h hf, fun h f hf => h f hf⟩

theorem outcomes_iff (i : ℕ) (s s' : Set ℕ) :
    s' ∈ (act φ i).toAction.outcomes s ↔
      ∃ x ∈ (act φ i).2.2.2, s' = (s \ {f | f ∈ x.2}) ∪ {f | f ∈ x.1} := by
  simp only [Action.outcomes, FActDesc.toAction, FActDesc.effs, Set.mem_setOf_eq, Action.applyEff]
  constructor
  · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- The state after setting `v` to `b`. -/
def setS (s : Set ℕ) (v : ℕ) (b : Bool) : Set ℕ := insert (lf v b) (s \ {lf v (!b)})

theorem applyEff_setEff (s : Set ℕ) (v : ℕ) (b : Bool) :
    (s \ {f | f ∈ (setEff v b).2}) ∪ {f | f ∈ (setEff v b).1} = setS s v b := by
  ext f; simp only [setEff, setS, List.mem_singleton, Set.mem_union, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

theorem pre_block {i : ℕ} (hi : i < 2 * φ.1.length) : (act φ i).2.1 = [] := by
  unfold act; rw [if_pos hi]

theorem applicable_block {i : ℕ} (hi : i < 2 * φ.1.length) (s : Set ℕ) :
    (act φ i).toAction.Applicable s := by
  rw [applicable_iff, pre_block hi]; simp

theorem outcomes_block {p j : ℕ} (hp : p < φ.1.length) (hj : j < 2) (s s' : Set ℕ) :
    s' ∈ (act φ (2 * p + j)).toAction.outcomes s ↔
      ∃ b, ((φ.1.getI p).1 = true ∨ b = decide (j = 1)) ∧ s' = setS s (φ.1.getI p).2 b := by
  rw [outcomes_iff]
  have h2 : (2 * p + j) / 2 = p := by omega
  have h3 : (2 * p + j) % 2 = j := by omega
  unfold act
  rw [if_pos (by omega), h2, h3]
  simp only
  cases (φ.1.getI p).1
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton, exists_eq_left, false_or,
      applyEff_setEff]
  · simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false, true_or, true_and]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact ⟨true, applyEff_setEff _ _ _⟩
      · exact ⟨false, applyEff_setEff _ _ _⟩
    · rintro ⟨b, rfl⟩
      cases b
      · exact ⟨_, Or.inr rfl, (applyEff_setEff _ _ _).symm⟩
      · exact ⟨_, Or.inl rfl, (applyEff_setEff _ _ _).symm⟩

theorem applicable_fin (s : Set ℕ) :
    (act φ (2 * φ.1.length)).toAction.Applicable s ↔ ∀ c < φ.2.length, satF c ∈ s := by
  rw [applicable_iff]
  unfold act
  rw [if_neg (by omega), if_pos rfl]
  simp

theorem outcomes_fin (s s' : Set ℕ) :
    s' ∈ (act φ (2 * φ.1.length)).toAction.outcomes s ↔ s' = insert winF s := by
  rw [outcomes_iff]
  unfold act
  rw [if_neg (by omega), if_pos rfl]
  simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, Set.setOf_false,
    Set.diff_empty]
  constructor <;> rintro rfl <;> ext f <;> simp

theorem applicable_clear (s : Set ℕ) :
    (act φ (2 * φ.1.length + 1)).toAction.Applicable s ↔ winF ∈ s := by
  rw [applicable_iff]
  unfold act
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  simp

theorem outcomes_clear (s s' : Set ℕ) :
    s' ∈ (act φ (2 * φ.1.length + 1)).toAction.outcomes s ↔
      s' = s ∪ {f | ∃ p ∈ lits φ, f = lf p.2.1 p.2.2} := by
  rw [outcomes_iff]
  unfold act
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, Set.setOf_false,
    Set.diff_empty, List.mem_map]
  constructor <;> rintro rfl <;> ext f <;> simp [eq_comm]

theorem applicable_chk {i : ℕ} (hi : 2 * φ.1.length + 2 ≤ i) (s : Set ℕ) :
    (act φ i).toAction.Applicable s ↔
      lf ((lits φ).getI (i - (2 * φ.1.length + 2))).2.1
        ((lits φ).getI (i - (2 * φ.1.length + 2))).2.2 ∈ s := by
  rw [applicable_iff]
  unfold act
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

theorem outcomes_chk {i : ℕ} (hi : 2 * φ.1.length + 2 ≤ i) (s s' : Set ℕ) :
    s' ∈ (act φ i).toAction.outcomes s ↔
      s' = insert (satF ((lits φ).getI (i - (2 * φ.1.length + 2))).1) s := by
  rw [outcomes_iff]
  unfold act
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [List.mem_singleton, exists_eq_left, List.not_mem_nil, Set.setOf_false,
    Set.diff_empty]
  constructor <;> rintro rfl <;> ext f <;> simp [or_comm]

/-! ### Encoded assignments -/

/-- The state encodes the assignment `σ` on the literals of the matrix. -/
def Enc (φ : Formula) (σ : ℕ → Bool) (s : Set ℕ) : Prop :=
  ∀ p ∈ lits φ, (lf p.2.1 p.2.2 ∈ s ↔ σ p.2.1 = p.2.2)

/-- No clause is marked and `winF` is false. -/
def Clean (s : Set ℕ) : Prop := winF ∉ s ∧ ∀ c, satF c ∉ s

theorem enc_setS {σ : ℕ → Bool} {s : Set ℕ} (h : Enc φ σ s) (v : ℕ) (b : Bool) :
    Enc φ (Function.update σ v b) (setS s v b) := by
  intro p hp
  have := h p hp
  simp only [setS, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff, lf_inj]
  by_cases hv : p.2.1 = v
  · rw [hv, Function.update_self] at *
    cases b <;> cases p.2.2 <;> simp
  · rw [Function.update_of_ne hv]
    simp [hv, this]

theorem clean_setS {s : Set ℕ} (h : Clean s) (v : ℕ) (b : Bool) : Clean (setS s v b) := by
  refine ⟨?_, fun c => ?_⟩
  · simp only [setS, Set.mem_insert_iff, Set.mem_diff, not_or]
    exact ⟨(lf_ne_winF v b).symm, fun h' => h.1 h'.1⟩
  · simp only [setS, Set.mem_insert_iff, Set.mem_diff, not_or]
    exact ⟨(lf_ne_satF v b c).symm, fun h' => h.2 c h'.1⟩

theorem enc_insert_satF {σ : ℕ → Bool} {s : Set ℕ} (h : Enc φ σ s) (c : ℕ) :
    Enc φ σ (insert (satF c) s) := by
  intro p hp
  rw [← h p hp, Set.mem_insert_iff, or_iff_right (lf_ne_satF _ _ _)]

/-! ### Induction on the game -/

theorem w_induction {M : Finset ℕ → Set ℕ → Prop}
    (hdone : ∀ D s, (∀ i < nT φ, i ∈ D) → M D s)
    (hstep : ∀ D s t, t < nT φ → t ∉ D → (∀ t' < nT φ, Ord φ.1.length t' t → t' ∈ D) →
      (act φ t).toAction.Applicable s →
      (∀ s' ∈ (act φ t).toAction.outcomes s, M (insert t D) s') → M D s) :
    ∀ {D s}, W φ D s → M D s := by
  intro D s h
  induction h with
  | done h => exact hdone _ _ fun i hi => h (mem_T_tn.2 hi)
  | @step D s t a ht htD hpred hα happ _ ih =>
    have ht' := mem_T_tn.1 ht
    have hat : a = t := by
      change (tn φ).label t = _ at hα
      rw [label_tn ht'] at hα; exact (Sum.inl_injective hα).symm
    subst hat
    rw [δ_desc ht'] at happ ih
    refine hstep D s a ht' htD (fun t' ht'' ho => hpred t' (mem_T_tn.2 ht'') ?_) happ ih
    rw [tnI_desc, ord_tn]; exact ⟨ht'', ht', ho⟩

theorem card_sdiff_insert_lt {D : Finset ℕ} {t : ℕ} (ht : t < nT φ) (htD : t ∉ D) :
    (Finset.range (nT φ) \ insert t D).card < (Finset.range (nT φ) \ D).card := by
  rw [Finset.sdiff_insert]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 ⟨Finset.mem_range.2 ht, htD⟩)

/-! ### The quantifier blocks -/

theorem w_block0 {p : ℕ} (hp : p < φ.1.length) (s : Set ℕ) :
    W φ (Finset.range (2 * p)) s ↔ ∃ j < 2, ∀ s' ∈ (act φ (2 * p + j)).toAction.outcomes s,
      W φ (insert (2 * p + j) (Finset.range (2 * p))) s' := by
  constructor
  · intro h
    rcases w_cases h with hall | ⟨t, ht, htD, hpred, -, hout⟩
    · exact absurd (hall (2 * p) (by unfold nT; omega)) (by simp)
    · have : t = 2 * p ∨ t = 2 * p + 1 := by
        simp only [Finset.mem_range] at htD hpred
        by_contra hne
        have := hpred (2 * p) (by unfold nT; omega) (by unfold Ord; omega)
        omega
      rcases this with rfl | rfl
      · exact ⟨0, by omega, hout⟩
      · exact ⟨1, by omega, hout⟩
  · rintro ⟨j, hj, h⟩
    refine w_step (t := 2 * p + j) (by unfold nT; omega) (by simp) (fun t' _ ho => ?_)
      (applicable_block (by omega) s) h
    unfold Ord at ho; simp only [Finset.mem_range]; omega

theorem w_block1 {p j : ℕ} (hp : p < φ.1.length) (hj : j < 2) (s : Set ℕ) :
    W φ (insert (2 * p + j) (Finset.range (2 * p))) s ↔
      ∀ s' ∈ (act φ (2 * p + (1 - j))).toAction.outcomes s, W φ (Finset.range (2 * (p + 1))) s' := by
  have hD : insert (2 * p + (1 - j)) (insert (2 * p + j) (Finset.range (2 * p))) =
      Finset.range (2 * (p + 1)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_range]; omega
  constructor
  · intro h
    rcases w_cases h with hall | ⟨t, ht, htD, hpred, -, hout⟩
    · exact absurd (hall (2 * p + (1 - j)) (by unfold nT; omega)) (by simp; omega)
    · have : t = 2 * p + (1 - j) := by
        simp only [Finset.mem_insert, Finset.mem_range, not_or] at htD hpred
        by_contra hne
        have := hpred (2 * p + (1 - j)) (by unfold nT; omega) (by unfold Ord; omega)
        omega
      subst this
      intro s' hs'; rw [← hD]; exact hout s' hs'
  · intro h
    refine w_step (t := 2 * p + (1 - j)) (by unfold nT; omega) (by simp; omega) (fun t' _ ho => ?_)
      (applicable_block (by omega) s) (fun s' hs' => ?_)
    · unfold Ord at ho; simp only [Finset.mem_insert, Finset.mem_range]; omega
    · rw [hD]; exact h s' hs'

theorem w_block {p : ℕ} (hp : p < φ.1.length) (s : Set ℕ) :
    W φ (Finset.range (2 * p)) s ↔ ∃ j < 2, ∀ b₁, ((φ.1.getI p).1 = true ∨ b₁ = decide (j = 1)) →
      ∀ b₂, ((φ.1.getI p).1 = true ∨ b₂ = decide (1 - j = 1)) →
        W φ (Finset.range (2 * (p + 1))) (setS (setS s (φ.1.getI p).2 b₁) (φ.1.getI p).2 b₂) := by
  rw [w_block0 hp]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  simp only [outcomes_block hp hj, w_block1 hp hj, outcomes_block hp (by omega : 1 - j < 2)]
  constructor
  · intro h b₁ h₁ b₂ h₂; exact h _ ⟨b₁, h₁, rfl⟩ _ ⟨b₂, h₂, rfl⟩
  · rintro h _ ⟨b₁, h₁, rfl⟩ _ ⟨b₂, h₂, rfl⟩; exact h b₁ h₁ b₂ h₂

/-! ### After the last block -/

theorem phase2_sound {σ : ℕ → Bool} : ∀ {D : Finset ℕ} {s : Set ℕ}, W φ D s →
    (∀ i < 2 * φ.1.length, i ∈ D) → 2 * φ.1.length ∉ D → winF ∉ s →
    (∀ c < φ.2.length, satF c ∈ s → ∃ l ∈ φ.2.getI c, σ l.1 = l.2) → Enc φ σ s → Sat φ.2 σ := by
  intro D s h
  refine w_induction (M := fun D s => (∀ i < 2 * φ.1.length, i ∈ D) → 2 * φ.1.length ∉ D →
    winF ∉ s → (∀ c < φ.2.length, satF c ∈ s → ∃ l ∈ φ.2.getI c, σ l.1 = l.2) → Enc φ σ s →
    Sat φ.2 σ) (fun D s hall _ hfin => absurd (hall _ (by unfold nT; omega)) hfin) ?_ h
  intro D s t ht htD hpred happ ih hpre hfin hwin hsat henc
  have ht2 : 2 * φ.1.length ≤ t := by
    by_contra h; exact htD (hpre t (by omega))
  rcases Nat.lt_trichotomy t (2 * φ.1.length) with h | rfl | h
  · omega
  · have := (applicable_fin s).1 happ
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    have := hsat i hi (this i hi)
    rwa [List.getI_eq_getElem _ hi] at this
  rcases Nat.lt_or_ge t (2 * φ.1.length + 2) with h' | h'
  · have : t = 2 * φ.1.length + 1 := by omega
    subst this
    exact absurd ((applicable_clear s).1 happ) hwin
  · have hi : t - (2 * φ.1.length + 2) < (lits φ).length := by unfold nT at ht; omega
    have hp := getI_mem_lits hi
    have hσ := (henc _ hp).1 ((applicable_chk h' s).1 happ)
    refine ih _ ((outcomes_chk h' s _).2 rfl) (fun i hi' => Finset.mem_insert_of_mem (hpre i hi'))
      (by simp only [Finset.mem_insert, not_or]; exact ⟨by omega, hfin⟩)
      (by simp only [Set.mem_insert_iff, not_or]; exact ⟨(satF_ne_winF _).symm, hwin⟩)
      (fun c hc hcs => ?_) (enc_insert_satF henc _)
    rcases (Set.mem_insert_iff.1 hcs) with hc' | hc'
    · rw [satF_inj] at hc'
      subst hc'
      exact ⟨_, (mem_lits.1 hp).2, hσ⟩
    · exact hsat c hc hc'

theorem finish : ∀ n (D : Finset ℕ) (s : Set ℕ), (Finset.range (nT φ) \ D).card = n →
    (∀ i < 2 * φ.1.length + 1, i ∈ D) → winF ∈ s →
    (2 * φ.1.length + 1 ∈ D → ∀ p ∈ lits φ, lf p.2.1 p.2.2 ∈ s) → W φ D s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D s hn hpre hwin hlit
  by_cases hall : ∀ i < nT φ, i ∈ D
  · exact Problem.Win.done fun x hx => hall x (mem_T_tn.1 hx)
  push_neg at hall
  obtain ⟨i, hi, hiD⟩ := hall
  have hpred : ∀ t, ∀ t' < nT φ, 2 * φ.1.length ≤ t → Ord φ.1.length t' t → t' ∈ D :=
    fun t t' _ ht ho => hpre t' (by unfold Ord at ho; omega)
  by_cases hc : 2 * φ.1.length + 1 ∈ D
  · have hi2 : 2 * φ.1.length + 2 ≤ i := by
      by_contra h
      rcases Nat.lt_or_ge i (2 * φ.1.length + 1) with h' | h'
      · exact hiD (hpre i h')
      · exact hiD (by rwa [show i = 2 * φ.1.length + 1 by omega])
    refine w_step hi hiD (hpred i · · (by omega)) ((applicable_chk hi2 s).2 ?_) fun s' hs' => ?_
    · exact hlit hc _ (getI_mem_lits (by unfold nT at hi; omega))
    · rw [(outcomes_chk hi2 s s').1 hs']
      exact ih _ (hn ▸ card_sdiff_insert_lt hi hiD) _ _ rfl
        (fun j hj => Finset.mem_insert_of_mem (hpre j hj)) (Set.mem_insert_of_mem _ hwin)
        fun _ p hp => Set.mem_insert_of_mem _ (hlit hc p hp)
  · have hlt : 2 * φ.1.length + 1 < nT φ := by unfold nT; omega
    refine w_step hlt hc (hpred _ · · (by omega)) ((applicable_clear s).2 hwin) fun s' hs' => ?_
    rw [(outcomes_clear s s').1 hs']
    exact ih _ (hn ▸ card_sdiff_insert_lt hlt hc) _ _ rfl
      (fun j hj => Finset.mem_insert_of_mem (hpre j hj)) (Or.inl hwin)
      fun _ p hp => Or.inr ⟨p, hp, rfl⟩

theorem collect {σ : ℕ → Bool} (hσ : Sat φ.2 σ) : ∀ n (D : Finset ℕ) (s : Set ℕ),
    (Finset.range (nT φ) \ D).card = n →
    (∀ i < 2 * φ.1.length, i ∈ D) → 2 * φ.1.length ∉ D → 2 * φ.1.length + 1 ∉ D → Enc φ σ s →
    (∀ i < (lits φ).length, 2 * φ.1.length + 2 + i ∈ D → satF ((lits φ).getI i).1 ∈ s) →
    W φ D s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D s hn hpre hfin hclr henc hinv
  have hpred : ∀ t, ∀ t' < nT φ, 2 * φ.1.length ≤ t → Ord φ.1.length t' t → t' ∈ D :=
    fun t t' _ ht ho => hpre t' (by unfold Ord at ho; omega)
  by_cases hall : ∀ c < φ.2.length, satF c ∈ s
  · have hlt : 2 * φ.1.length < nT φ := by unfold nT; omega
    refine w_step hlt hfin (hpred _ · · le_rfl) ((applicable_fin s).2 hall) fun s' hs' => ?_
    rw [(outcomes_fin s s').1 hs']
    refine finish _ _ _ rfl (fun i hi => ?_) (Set.mem_insert _ _) fun h => ?_
    · rcases Nat.lt_or_ge i (2 * φ.1.length) with h | h
      · exact Finset.mem_insert_of_mem (hpre i h)
      · rw [show i = 2 * φ.1.length by omega]; exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.1 h with h | h
      · omega
      · exact absurd h hclr
  push_neg at hall
  obtain ⟨c, hc, hcs⟩ := hall
  obtain ⟨l, hl, hσl⟩ := hσ _ (List.getI_eq_getElem φ.2 hc ▸ List.getElem_mem hc)
  have hcl : (c, l) ∈ lits φ := mem_lits.2 ⟨hc, hl⟩
  obtain ⟨i, hi, hgi⟩ := exists_idx_lits hcl
  have htD : 2 * φ.1.length + 2 + i ∉ D := fun h => hcs (by simpa [hgi] using hinv i hi h)
  have hlt : 2 * φ.1.length + 2 + i < nT φ := by unfold nT; omega
  have hsub : 2 * φ.1.length + 2 + i - (2 * φ.1.length + 2) = i := by omega
  refine w_step hlt htD (hpred _ · · (by omega)) ((applicable_chk (by omega) s).2 ?_)
    fun s' hs' => ?_
  · rw [hsub, hgi]; exact (henc _ hcl).2 hσl
  · rw [(outcomes_chk (by omega) s s').1 hs', hsub, hgi]
    refine ih _ (hn ▸ card_sdiff_insert_lt hlt htD) _ _ rfl
      (fun j hj => Finset.mem_insert_of_mem (hpre j hj))
      (by simp only [Finset.mem_insert, not_or]; exact ⟨by omega, hfin⟩)
      (by simp only [Finset.mem_insert, not_or]; exact ⟨by omega, hclr⟩)
      (enc_insert_satF henc _) fun j hj hjD => ?_
    rcases Finset.mem_insert.1 hjD with h | h
    · have : j = i := by omega
      subst this
      rw [hgi]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hinv j hj h)

theorem phase2_iff {σ : ℕ → Bool} {s : Set ℕ} (hE : Enc φ σ s) (hC : Clean s) :
    W φ (Finset.range (2 * φ.1.length)) s ↔ Sat φ.2 σ := by
  constructor
  · intro h
    exact phase2_sound h (fun i hi => Finset.mem_range.2 hi) (by simp) hC.1
      (fun c _ hc => absurd hc (hC.2 c)) hE
  · intro h
    exact collect h _ _ _ rfl (fun i hi => Finset.mem_range.2 hi) (by simp) (by simp) hE
      (fun i _ hi => by simp at hi; omega)

/-! ### Correctness -/

theorem prefix_iff : ∀ j p, p + j = φ.1.length → ∀ (σ : ℕ → Bool) (s : Set ℕ), Enc φ σ s →
    Clean s → (W φ (Finset.range (2 * p)) s ↔ Eval (φ.1.drop p) φ.2 σ) := by
  intro j
  induction j with
  | zero =>
    intro p hp σ s hE hC
    rw [add_zero] at hp
    subst hp
    rw [List.drop_length, eval_nil]
    exact phase2_iff hE hC
  | succ j ih =>
    intro p hp σ s hE hC
    have hpm : p < φ.1.length := by omega
    rw [w_block hpm, List.drop_eq_getElem_cons hpm, ← List.getI_eq_getElem _ hpm]
    have ih' := ih (p + 1) (by omega)
    generalize φ.1.getI p = x at *
    obtain ⟨q, v⟩ := x
    have key : ∀ b₁ b₂, W φ (Finset.range (2 * (p + 1))) (setS (setS s v b₁) v b₂) ↔
        Eval (φ.1.drop (p + 1)) φ.2 (Function.update σ v b₂) := fun b₁ b₂ => by
      rw [ih' _ _ (enc_setS (enc_setS hE v b₁) v b₂) (clean_setS (clean_setS hC v b₁) v b₂),
        Function.update_idem]
    simp only [key]
    cases q
    · simp only [Bool.false_eq_true, false_or, forall_eq, eval_exists]
      constructor
      · rintro ⟨j, -, h⟩; exact ⟨_, h⟩
      · rintro ⟨b, h⟩
        cases b
        · exact ⟨1, by omega, by simpa using h⟩
        · exact ⟨0, by omega, by simpa using h⟩
    · simp only [true_or, forall_const, eval_forall]
      constructor
      · rintro ⟨j, -, h⟩ b; exact h b
      · intro h; exact ⟨0, by omega, fun b => h b⟩

theorem enc_init : Enc φ (fun _ => false) {f | f ∈ (desc φ).init} := by
  intro p hp
  simp only [desc, FProbDesc.init, Set.mem_setOf_eq, List.mem_map, lf_inj]
  constructor
  · rintro ⟨p', -, -, h⟩; exact h
  · intro h; exact ⟨p, hp, rfl, h⟩

theorem clean_init : Clean {f | f ∈ (desc φ).init} := by
  simp only [Clean, desc, FProbDesc.init, Set.mem_setOf_eq, List.mem_map, not_exists, not_and]
  exact ⟨fun p _ h => lf_ne_winF _ _ h, fun c p _ h => lf_ne_satF _ _ _ h⟩

/-- **Correctness of the reduction**: the encoding is strong OD solvable iff `φ` is true. -/
theorem strongOD_iff : (desc φ).toProblem.StrongODSolvable ↔ Holds φ := by
  rw [Problem.strongODSolvable_iff_win tnI_isPrimitive]
  have := prefix_iff φ.1.length 0 (zero_add _) (fun _ => false) _ (enc_init (φ := φ)) clean_init
  rw [mul_zero, Finset.range_zero, List.drop_zero] at this
  exact this

end ToFond

end QBF

end FOND
