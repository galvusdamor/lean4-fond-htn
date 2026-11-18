import HtnComplexity.Computable.AcFreeRow
import HtnComplexity.Computable.AddRoot
import HtnPlanning.Computable.Bodies
import HtnComplexity.Computable.TrStripsCell
import HtnPlanning.Core.ToStateReach
import HtnComplexity.Space.ToAlt
/-!
# The sequencing gadget: rooting a totally ordered instance with the help of the length

This is step A1 of `TABLE4-PLAN.md`.  A totally ordered instance whose initial task network is
the task sequence `xs` (of length at most `N`) is turned into a **rooted** instance over a
domain that depends on the domain description and on `N` only:

* `HTN.Syn.SeqG.seqDom κ d N` — the domain description `d`, its facts renamed by `κ.ρ`, together
  with a fresh compound task `κ.S` whose methods walk through the positions `0, 1, …` of a task
  sequence: `S → [pick p x, x, S]` for every position `p < N` and every task `x` the domain
  mentions, `S → [skip p, S]` for a primitive task the domain does not mention, and
  `S → [stop p]`;
* `HTN.Syn.SeqG.seqInst κ d q xs` — the facts of `q` renamed by `κ.ρ`, the *static* facts
  `lab p x` "the task at position `p` is `x`" (and `nop p` when that task is a primitive task the
  domain does not mention), the facts `cur 0` and `len |xs|`, the goal of `q` extended by `fin`,
  and the single compound task `κ.S`.

The action `pick p x` needs `cur p` and `lab p x`, and moves `cur p` to `cur (p+1)`; `skip p`
needs `cur p` and `nop p` and does the same; `stop p` needs `cur p` and `len p` and adds `fin`.
So the only way to refine `κ.S` is to execute the tasks of `xs` in order, and
`HTN.Syn.SeqG.solvable_seq_iff` states that the rooted problem is solvable exactly when the
original one is.

The gadget keeps a domain totally ordered and tail recursive (`κ.S` is a fresh task of maximal
rank, its recursive call is last): `methodsTO_seqDom`, `isTailRec_seqDom`.

The encodings of the gadget's facts and names are parameters (`HTN.Syn.SeqG.Code`), so that the
machine of step A3 can choose numerals that are convenient inside Cobham's class.
-/

namespace HTN

namespace Syn

namespace SeqG

open AcFree Ac

/-! ### The encodings -/

/-- The facts of the gadget. -/
inductive GF
  /-- The next task to be executed is the one at position `p`. -/
  | cur (p : ℕ)
  /-- The sequence has length `p`. -/
  | len (p : ℕ)
  /-- The task at position `p` is `x`. -/
  | lab (p : ℕ) (x : ℕ ⊕ ℕ)
  /-- The task at position `p` is a primitive task the domain does not mention. -/
  | nop (p : ℕ)
  /-- The whole sequence has been executed. -/
  | fin
  /-- A witness fact, mentioned by no action: identifier `i` has rank `p`. -/
  | wit (p i : ℕ)
  deriving DecidableEq

/-- The actions of the gadget. -/
inductive GA
  /-- Execute the known task `x` at position `p`. -/
  | pick (p : ℕ) (x : ℕ ⊕ ℕ)
  /-- Skip the unknown primitive task at position `p`. -/
  | skip (p : ℕ)
  /-- Stop at position `p`. -/
  | stop (p : ℕ)
  deriving DecidableEq

/-- **The encodings of the gadget**: a renaming of the original facts, injective encodings of the
gadget's facts and actions, and the name of the fresh compound task.  The gadget's facts are
kept apart from the renamed original ones. -/
structure Code where
  /-- The renaming of the facts of the domain and of the instance. -/
  ρ : ℕ → ℕ
  /-- The numerals of the gadget's facts. -/
  gf : GF → ℕ
  /-- The names of the gadget's actions. -/
  ga : GA → ℕ
  /-- The fresh compound task. -/
  S : ℕ
  ρ_inj : Function.Injective ρ
  gf_inj : Function.Injective gf
  ga_inj : Function.Injective ga
  gf_ne_ρ : ∀ g v, gf g ≠ ρ v

/-! ### The vocabulary of a domain description -/

/-- The primitive task names a domain description mentions: its listed actions and the actions
of its method bodies. -/
def vocA (d : DomDesc) : List ℕ :=
  d.actions.map Prod.fst ++ d.methods.flatMap fun e => e.2.actionNames

/-- The compound task names a domain description mentions: its method heads and the compound
tasks of its method bodies. -/
def vocC (d : DomDesc) : List ℕ :=
  d.methods.map Prod.fst ++ d.methods.flatMap fun e => e.2.compoundNames

/-- Is the task mentioned by the domain description? -/
def knownB (d : DomDesc) : ℕ ⊕ ℕ → Bool
  | Sum.inl a => decide (a ∈ vocA d)
  | Sum.inr c => decide (c ∈ vocC d)

/-- The tasks the domain description mentions. -/
def knownList (d : DomDesc) : List (ℕ ⊕ ℕ) := (vocA d).map Sum.inl ++ (vocC d).map Sum.inr

/-- Is the task a primitive task the domain description does not mention? -/
def unknownPrimB (d : DomDesc) : ℕ ⊕ ℕ → Bool
  | Sum.inl a => !decide (a ∈ vocA d)
  | Sum.inr _ => false

/-- **The encodings are fresh for the domain description**: the gadget's actions are not
mentioned by `d`, and neither is its compound task. -/
structure Code.Fresh (κ : Code) (d : DomDesc) : Prop where
  ga_nmem : ∀ g, κ.ga g ∉ vocA d
  S_nmem : κ.S ∉ vocC d

/-! ### The gadget -/

/-- A task as a cell of a described row. -/
def toRow : ℕ ⊕ ℕ → Bool × ℕ
  | Sum.inl a => (false, a)
  | Sum.inr c => (true, c)

/-- An action description with its facts renamed. -/
def renAct (ρ : ℕ → ℕ) (a : ActionDesc) : ActionDesc :=
  (a.1, a.2.1.map ρ, a.2.2.1.map ρ, a.2.2.2.map ρ)

/-- The gadget actions offered for sequences of length at most `N`. -/
def gadList (d : DomDesc) (N : ℕ) : List GA :=
  (List.range N).flatMap (fun p => (knownList d).map (GA.pick p) ++ [GA.skip p]) ++
    (List.range (N + 1)).map GA.stop

/-- The precondition, add and delete list of a gadget action. -/
def gadVal (κ : Code) : GA → List ℕ × List ℕ × List ℕ
  | .pick p x => ([κ.gf (.cur p), κ.gf (.lab p x)], [κ.gf (.cur (p + 1))], [κ.gf (.cur p)])
  | .skip p => ([κ.gf (.cur p), κ.gf (.nop p)], [κ.gf (.cur (p + 1))], [κ.gf (.cur p)])
  | .stop p => ([κ.gf (.cur p), κ.gf (.len p)], [κ.gf .fin], [κ.gf (.cur p)])

/-- The actions of the gadget, for sequences of length at most `N`. -/
def gadActs (κ : Code) (d : DomDesc) (N : ℕ) : List ActionDesc :=
  (gadList d N).map fun g => (κ.ga g, gadVal κ g)

theorem pick_mem_gadList {d : DomDesc} {N p : ℕ} {x : ℕ ⊕ ℕ} :
    GA.pick p x ∈ gadList d N ↔ p < N ∧ x ∈ knownList d := by
  simp [gadList]

theorem skip_mem_gadList {d : DomDesc} {N p : ℕ} : GA.skip p ∈ gadList d N ↔ p < N := by
  simp [gadList]

theorem stop_mem_gadList {d : DomDesc} {N p : ℕ} : GA.stop p ∈ gadList d N ↔ p ≤ N := by
  simp [gadList]

/-- The body of the gadget method that uses the gadget action `g`. -/
def gadRow (κ : Code) : GA → List (Bool × ℕ)
  | .pick p x => [pAct (κ.ga (.pick p x)), toRow x, pTsk κ.S]
  | .skip p => [pAct (κ.ga (.skip p)), pTsk κ.S]
  | .stop p => [pAct (κ.ga (.stop p))]

/-- The methods of the gadget, for sequences of length at most `N`. -/
def gadMethods (κ : Code) (d : DomDesc) (N : ℕ) : List MethodDesc :=
  (gadList d N).map fun g => (κ.S, gridDesc [gadRow κ g])

/-- **The gadget domain**: `d` with renamed facts, and the gadget. -/
def seqDom (κ : Code) (d : DomDesc) (N : ℕ) : DomDesc :=
  (d.actions.map (renAct κ.ρ) ++ gadActs κ d N, d.methods ++ gadMethods κ d N)

/-- The static facts describing the task sequence `xs`: its length, the task at each position,
and the positions of the primitive tasks the domain does not mention. -/
def gadStatic (κ : Code) (d : DomDesc) (xs : List (ℕ ⊕ ℕ)) (ws : List (ℕ × ℕ)) : List ℕ :=
  ws.map (fun w => κ.gf (.wit w.1 w.2)) ++ κ.gf (.len xs.length) ::
    ((List.range xs.length).map (fun p => κ.gf (.lab p (xs.getD p (Sum.inl 0)))) ++
      ((List.range xs.length).filter (fun p => unknownPrimB d (xs.getD p (Sum.inl 0)))).map
        fun p => κ.gf (.nop p))

/-- The gadget's part of the initial state: the static facts and `cur 0`. -/
def gadInit (κ : Code) (d : DomDesc) (xs : List (ℕ ⊕ ℕ)) (ws : List (ℕ × ℕ)) : List ℕ :=
  κ.gf (.cur 0) :: gadStatic κ d xs ws

/-- **The rooted instance** for the task sequence `xs`. -/
def seqInst (κ : Code) (d : DomDesc) (q : InstDesc) (xs : List (ℕ ⊕ ℕ))
    (ws : List (ℕ × ℕ)) : InstDesc :=
  (q.initList.map κ.ρ ++ gadInit κ d xs ws, q.goalList.map κ.ρ ++ [κ.gf .fin], singleTn κ.S)

/-! ### Classes -/

/-- Every method the gadget adds has a one-row body. -/
theorem exists_row_of_mem_gadMethods {κ : Code} {d : DomDesc} {N : ℕ} {e : MethodDesc}
    (he : e ∈ gadMethods κ d N) : e.1 = κ.S ∧ ∃ row, e.2 = gridDesc [row] := by
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 he
  exact ⟨rfl, _, rfl⟩

theorem methodsTO_seqDom {κ : Code} {d : DomDesc} {N : ℕ} (hTO : d.MethodsTO) :
    (seqDom κ d N).MethodsTO := by
  intro e he
  rcases List.mem_append.1 he with he | he
  · exact hTO e he
  · obtain ⟨-, row, hrow⟩ := exists_row_of_mem_gadMethods he
    rw [hrow]
    exact oneRow_isTotallyOrdered

/-- A compound task of a one-row body is a compound cell of the row, and it is last exactly
when the cell is. -/
theorem oneRow_label_inr {row : List (Bool × ℕ)} {t c : ℕ}
    (ht : t ∈ (gridDesc [row]).toTaskNetwork.T)
    (hl : (gridDesc [row]).toTaskNetwork.α t = Sum.inr c) :
    ∃ j, ∃ hj : j < row.length, row[j] = (true, c) ∧
      ((gridDesc [row]).toTaskNetwork.IsLastId t ↔ j + 1 = row.length) := by
  have h := oneRow_isSeqNet (row := row)
  set l := (List.range row.length).map (Nat.pair 0) with hl_def
  have htl : t ∈ l := (h.memT t).1 ht
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem htl
  have hjr : j < row.length := by simpa [hl_def] using hj
  refine ⟨j, hjr, ?_, ?_⟩
  · have hlab : (l.map (gridDesc [row]).toTaskNetwork.α)[j]'(by simpa using hj) =
        (rowLabels row)[j]'(by simpa [rowLabels] using hjr) := by
      simp only [h.labels]
    rw [List.getElem_map, hl] at hlab
    simp only [rowLabels, List.getElem_map] at hlab
    generalize row[j] = r at hlab ⊢
    obtain ⟨b, n⟩ := r
    cases b <;> simp_all
  · rw [DomDesc.isLastId_getElem_iff h hj]
    simp [hl_def]

/-- The largest rank of a compound name the domain description mentions. -/
def vocRkMax (d : DomDesc) (rk : ℕ → ℕ) : ℕ := ((vocC d).map rk).foldr max 0

theorem le_foldr_max_map {rk : ℕ → ℕ} : ∀ {l : List ℕ} {c : ℕ}, c ∈ l →
    rk c ≤ (l.map rk).foldr max 0
  | [], _, hc => by simp at hc
  | y :: ys, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left _ _
    · exact (le_foldr_max_map hc).trans (le_max_right _ _)

theorem le_vocRkMax {d : DomDesc} {rk : ℕ → ℕ} {c : ℕ} (hc : c ∈ vocC d) :
    rk c ≤ vocRkMax d rk :=
  le_foldr_max_map hc

/-- The rank of the tail-recursion witness of the gadget domain. -/
def seqRk (κ : Code) (d : DomDesc) (rk : ℕ → ℕ) (c : ℕ) : ℕ :=
  if c = κ.S then vocRkMax d rk + 1 else rk c

/-- The tail-recursion condition for a gadget method with a one-row body: the compound cells
other than a final `κ.S` are known names. -/
theorem tailRec_row {κ : Code} {d : DomDesc} {rk : ℕ → ℕ} {row : List (Bool × ℕ)}
    (hrow : ∀ j (hj : j < row.length) c, row[j] = (true, c) →
      (c = κ.S ∧ j + 1 = row.length) ∨ (c ≠ κ.S ∧ c ∈ vocC d))
    {t c : ℕ} (ht : t ∈ (gridDesc [row]).toTaskNetwork.T)
    (hlab : (gridDesc [row]).toTaskNetwork.α t = Sum.inr c) :
    ((gridDesc [row]).toTaskNetwork.IsLastId t → seqRk κ d rk c ≤ seqRk κ d rk κ.S) ∧
      (¬ (gridDesc [row]).toTaskNetwork.IsLastId t → seqRk κ d rk c < seqRk κ d rk κ.S) := by
  obtain ⟨j, hj, hrowj, hiff⟩ := oneRow_label_inr ht hlab
  rw [hiff]
  unfold seqRk
  rw [if_pos rfl]
  rcases hrow j hj c hrowj with ⟨rfl, hlast⟩ | ⟨hne, hc⟩
  · exact ⟨fun _ => by simp, fun h => absurd hlast h⟩
  · rw [if_neg hne]
    have := le_vocRkMax (rk := rk) hc
    exact ⟨fun _ => by omega, fun _ => by omega⟩

theorem isTailRec_seqDom {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d)
    (hTR : d.IsTailRec) : (seqDom κ d N).IsTailRec := by
  obtain ⟨rk, hrk⟩ := hTR
  refine ⟨seqRk κ d rk, ?_⟩
  intro e he t ht c hlab
  rcases List.mem_append.1 he with he | he
  · have hhead : e.1 ∈ vocC d := List.mem_append_left _ (List.mem_map_of_mem he)
    have hc : c ∈ vocC d := by
      refine List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, ?_⟩)
      exact TnDesc.mem_compoundNames.2 ⟨t, by simpa using ht, hlab⟩
    have hne1 : e.1 ≠ κ.S := fun h => hκ.S_nmem (h ▸ hhead)
    have hne2 : c ≠ κ.S := fun h => hκ.S_nmem (h ▸ hc)
    unfold seqRk
    simp only [if_neg hne1, if_neg hne2]
    exact hrk e he t ht c hlab
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
    cases g with
    | pick p x =>
      have hx : x ∈ knownList d := (pick_mem_gadList.1 hg).2
      refine tailRec_row (fun j hj c' hc' => ?_) ht hlab
      have hj3 : j < 3 := by simpa [gadRow] using hj
      interval_cases j
      · simp [gadRow, pAct] at hc'
      · right
        cases x with
        | inl a => simp [gadRow, toRow] at hc'
        | inr c'' =>
          simp only [gadRow, toRow, List.getElem_cons_succ, List.getElem_cons_zero,
            Prod.mk.injEq, true_and] at hc'
          subst hc'
          have hmem : c'' ∈ vocC d := by simpa [knownList] using hx
          exact ⟨fun h => hκ.S_nmem (h ▸ hmem), hmem⟩
      · left
        simp only [gadRow, pTsk, List.getElem_cons_succ, List.getElem_cons_zero, Prod.mk.injEq,
          true_and] at hc'
        exact ⟨hc'.symm, rfl⟩
    | skip p =>
      refine tailRec_row (fun j hj c' hc' => ?_) ht hlab
      have hj2 : j < 2 := by simpa [gadRow] using hj
      interval_cases j
      · simp [gadRow, pAct] at hc'
      · left
        simp only [gadRow, pTsk, List.getElem_cons_succ, List.getElem_cons_zero, Prod.mk.injEq,
          true_and] at hc'
        exact ⟨hc'.symm, rfl⟩
    | stop p =>
      refine tailRec_row (fun j hj c' hc' => ?_) ht hlab
      have hj1 : j = 0 := by simpa [gadRow] using hj
      subst hj1
      simp [gadRow, pAct] at hc'

theorem isRooted_seqInst (κ : Code) (d : DomDesc) (q : InstDesc) (xs : List (ℕ ⊕ ℕ))
    (ws : List (ℕ × ℕ)) : (seqInst κ d q xs ws).IsRooted :=
  ⟨0, κ.S, singleTn_toTaskNetwork_T, singleTn_toTaskNetwork_α⟩

/-! ### Correctness -/

/-! #### The actions of the gadget domain -/

theorem lookup_eq_some_of_unique {β : Type} {l : List (ℕ × β)} {k : ℕ} {v : β}
    (hmem : (k, v) ∈ l) (huniq : ∀ w, (k, w) ∈ l → w = v) : l.lookup k = some v := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    obtain ⟨k', w⟩ := y
    by_cases hk : k = k'
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true]
      exact congrArg some (huniq w (List.mem_cons_self ..))
    · have hb : (k == k') = false := by simp [hk]
      rw [List.lookup_cons, hb]
      simp only
      refine ih ?_ fun w hw => huniq w (List.mem_cons_of_mem _ hw)
      rcases List.mem_cons.1 hmem with h | h
      · exact absurd (Prod.mk.inj h).1 hk
      · exact h

theorem lookup_eq_none_of_nmem {β : Type} {l : List (ℕ × β)} {k : ℕ}
    (h : k ∉ l.map Prod.fst) : l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨k', w⟩ := y
    have hk : k ≠ k' := fun hc => h (by simp [hc])
    have hb : (k == k') = false := by simp [hk]
    rw [List.lookup_cons, hb]
    exact ih fun hc => h (List.mem_cons_of_mem _ hc)

theorem lookup_append_of_nmem {β : Type} {l l' : List (ℕ × β)} {k : ℕ}
    (h : k ∉ l'.map Prod.fst) : (l ++ l').lookup k = l.lookup k := by
  induction l with
  | nil => exact lookup_eq_none_of_nmem h
  | cons y ys ih =>
    obtain ⟨k', w⟩ := y
    simp only [List.cons_append, List.lookup_cons]
    split <;> simp_all

theorem lookup_map_renAct (ρ : ℕ → ℕ) (l : List ActionDesc) (a : ℕ) :
    (l.map (renAct ρ)).lookup a =
      (l.lookup a).map fun x => (x.1.map ρ, x.2.1.map ρ, x.2.2.map ρ) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨k, v⟩ := y
    simp only [List.map_cons, renAct, List.lookup_cons]
    split <;> simp_all

/-- Every action name of the gadget is an encoded gadget action. -/
theorem mem_gadActs_names {κ : Code} {d : DomDesc} {N : ℕ} {a : ℕ}
    (h : a ∈ (gadActs κ d N).map Prod.fst) : ∃ g, κ.ga g = a := by
  simp only [gadActs, List.map_map, List.mem_map, Function.comp_def] at h
  obtain ⟨g, -, rfl⟩ := h
  exact ⟨g, rfl⟩

theorem names_actions_subset_vocA (d : DomDesc) : d.actions.map Prod.fst ⊆ vocA d :=
  fun _ h => List.mem_append_left _ h

/-- **An action the gadget does not add keeps its description, renamed.** -/
theorem lookup_seqDom_of_ne {κ : Code} {d : DomDesc} {N : ℕ} {a : ℕ} (ha : ∀ g, κ.ga g ≠ a) :
    (seqDom κ d N).actions.lookup a =
      (d.actions.lookup a).map fun x => (x.1.map κ.ρ, x.2.1.map κ.ρ, x.2.2.map κ.ρ) := by
  rw [show (seqDom κ d N).actions = d.actions.map (renAct κ.ρ) ++ gadActs κ d N from rfl,
    lookup_append_of_nmem, lookup_map_renAct]
  intro h
  obtain ⟨g, hg⟩ := mem_gadActs_names h
  exact ha g hg

theorem prec_seqDom_of_ne {κ : Code} {d : DomDesc} {N : ℕ} {a : ℕ} (ha : ∀ g, κ.ga g ≠ a) :
    (seqDom κ d N).prec a = κ.ρ '' d.prec a := by
  ext f
  simp only [DomDesc.prec, lookup_seqDom_of_ne ha, Set.mem_setOf_eq, Set.mem_image]
  rcases d.actions.lookup a with _ | ⟨P, A, E⟩ <;> simp

theorem add_seqDom_of_ne {κ : Code} {d : DomDesc} {N : ℕ} {a : ℕ} (ha : ∀ g, κ.ga g ≠ a) :
    (seqDom κ d N).add a = κ.ρ '' d.add a := by
  ext f
  simp only [DomDesc.add, lookup_seqDom_of_ne ha, Set.mem_setOf_eq, Set.mem_image]
  rcases d.actions.lookup a with _ | ⟨P, A, E⟩ <;> simp

theorem del_seqDom_of_ne {κ : Code} {d : DomDesc} {N : ℕ} {a : ℕ} (ha : ∀ g, κ.ga g ≠ a) :
    (seqDom κ d N).del a = κ.ρ '' d.del a := by
  ext f
  simp only [DomDesc.del, lookup_seqDom_of_ne ha, Set.mem_setOf_eq, Set.mem_image]
  rcases d.actions.lookup a with _ | ⟨P, A, E⟩ <;> simp

/-- An action not listed by `d` has an empty description. -/
theorem prec_eq_empty_of_nmem {d : DomDesc} {a : ℕ} (ha : a ∉ d.actions.map Prod.fst) :
    d.prec a = ∅ ∧ d.add a = ∅ ∧ d.del a = ∅ := by
  simp [DomDesc.prec, DomDesc.add, DomDesc.del, lookup_eq_none_of_nmem ha]

/-- The description of a gadget action. -/
theorem lookup_seqDom_ga {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d) {g : GA}
    (hg : g ∈ gadList d N) : (seqDom κ d N).actions.lookup (κ.ga g) = some (gadVal κ g) := by
  refine lookup_eq_some_of_unique (List.mem_append_right _ (List.mem_map_of_mem hg))
    fun w hw => ?_
  rcases List.mem_append.1 hw with hw | hw
  · exfalso
    obtain ⟨y, hy, hyw⟩ := List.mem_map.1 hw
    have : κ.ga g ∈ d.actions.map Prod.fst :=
      List.mem_map.2 ⟨y, hy, by simpa [renAct] using congrArg Prod.fst hyw⟩
    exact hκ.ga_nmem g (names_actions_subset_vocA d this)
  · obtain ⟨g', -, hg'⟩ := List.mem_map.1 hw
    obtain ⟨h1, h2⟩ := Prod.mk.inj hg'
    rw [κ.ga_inj h1] at h2
    exact h2.symm

theorem prec_seqDom_ga {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d) {g : GA}
    (hg : g ∈ gadList d N) :
    (seqDom κ d N).prec (κ.ga g) = {f | f ∈ (gadVal κ g).1} ∧
      (seqDom κ d N).add (κ.ga g) = {f | f ∈ (gadVal κ g).2.1} ∧
      (seqDom κ d N).del (κ.ga g) = {f | f ∈ (gadVal κ g).2.2} := by
  simp [DomDesc.prec, DomDesc.add, DomDesc.del, lookup_seqDom_ga hκ hg]

/-! #### The methods of the gadget domain -/

/-- The task sequence of the gadget method that uses the gadget action `g`. -/
def gadBody (κ : Code) : GA → List (ℕ ⊕ ℕ)
  | .pick p x => [Sum.inl (κ.ga (.pick p x)), x, Sum.inr κ.S]
  | .skip p => [Sum.inl (κ.ga (.skip p)), Sum.inr κ.S]
  | .stop p => [Sum.inl (κ.ga (.stop p))]

theorem rowLabels_gadRow (κ : Code) (g : GA) : rowLabels (gadRow κ g) = gadBody κ g := by
  cases g with
  | pick p x => cases x <;> rfl
  | skip p => rfl
  | stop p => rfl

theorem head_ne_S_of_mem {κ : Code} {d : DomDesc} (hκ : κ.Fresh d) {e : MethodDesc}
    (he : e ∈ d.methods) : e.1 ≠ κ.S := fun h =>
  hκ.S_nmem (h ▸ List.mem_append_left _ (List.mem_map_of_mem he))

/-- **A compound task other than `κ.S` has the bodies it has in `d`.** -/
theorem seqBody_seqDom_of_ne {κ : Code} {d : DomDesc} {N c : ℕ} (hc : c ≠ κ.S)
    {bs : List (ℕ ⊕ ℕ)} :
    (seqDom κ d N).toDomain.SeqBody c bs ↔ d.toDomain.SeqBody c bs := by
  rw [seqBody_desc_iff, seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, rfl, hb⟩
    rcases List.mem_append.1 he with he | he
    · exact ⟨e, he, rfl, hb⟩
    · exact absurd (exists_row_of_mem_gadMethods he).1 hc
  · rintro ⟨e, he, rfl, hb⟩
    exact ⟨e, List.mem_append_left _ he, rfl, hb⟩

/-- **The bodies of `κ.S` are the gadget bodies.** -/
theorem seqBody_seqDom_S {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d)
    {bs : List (ℕ ⊕ ℕ)} :
    (seqDom κ d N).toDomain.SeqBody κ.S bs ↔ ∃ g ∈ gadList d N, bs = gadBody κ g := by
  rw [seqBody_desc_iff]
  constructor
  · rintro ⟨e, he, hS, hb⟩
    rcases List.mem_append.1 he with he | he
    · exact absurd hS (head_ne_S_of_mem hκ he)
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
      exact ⟨g, hg, by rw [← rowLabels_gadRow]; exact hasSeqBody_oneRow.1 hb⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(κ.S, gridDesc [gadRow κ g]), List.mem_append_right _ (List.mem_map_of_mem hg),
      rfl, ?_⟩
    rw [← rowLabels_gadRow]
    exact hasSeqBody_oneRow.2 rfl

/-! #### The frame lemma: the original tasks do not see the gadget -/

theorem mem_knownList_inl {d : DomDesc} {a : ℕ} : Sum.inl a ∈ knownList d ↔ a ∈ vocA d := by
  simp [knownList]

theorem mem_knownList_inr {d : DomDesc} {c : ℕ} : Sum.inr c ∈ knownList d ↔ c ∈ vocC d := by
  simp [knownList]

/-- The bodies of the methods of `d` consist of tasks `d` mentions. -/
theorem known_of_seqBody {d : DomDesc} {c : ℕ} {bs : List (ℕ ⊕ ℕ)}
    (h : d.toDomain.SeqBody c bs) : ∀ x ∈ bs, x ∈ knownList d := by
  obtain ⟨e, he, -, l, hlin, hlab, -⟩ := seqBody_desc_iff.1 h
  intro x hx
  rw [← hlab] at hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  have htT : t ∈ e.2.ids := by simpa using (hlin.2.1 t).1 ht
  change e.2.label t ∈ knownList d
  rcases hl : e.2.label t with a | c'
  · refine mem_knownList_inl.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, ?_⟩))
    exact TnDesc.mem_actionNames.2 ⟨t, htT, hl⟩
  · refine mem_knownList_inr.2 (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, ?_⟩))
    exact TnDesc.mem_compoundNames.2 ⟨t, htT, hl⟩

theorem image_subset_union_iff {κ : Code} {G : Set ℕ} (hG : ∀ f ∈ G, ∀ v, f ≠ κ.ρ v)
    {P s : Set ℕ} : κ.ρ '' P ⊆ κ.ρ '' s ∪ G ↔ P ⊆ s := by
  constructor
  · intro h f hf
    rcases h ⟨f, hf, rfl⟩ with h' | h'
    · obtain ⟨f', hf', he⟩ := h'
      rwa [← κ.ρ_inj he]
    · exact absurd rfl (hG _ h' f)
  · intro h
    exact (Set.image_mono h).trans Set.subset_union_left

theorem transition_image {κ : Code} {G : Set ℕ} (hG : ∀ f ∈ G, ∀ v, f ≠ κ.ρ v)
    (s E A : Set ℕ) : (κ.ρ '' s ∪ G) \ κ.ρ '' E ∪ κ.ρ '' A = κ.ρ '' ((s \ E) ∪ A) ∪ G := by
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_image]
  constructor
  · rintro (⟨(⟨v, hv, rfl⟩ | hf), hE⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inl ⟨v, Or.inl ⟨hv, fun hvE => hE ⟨v, hvE, rfl⟩⟩, rfl⟩
    · exact Or.inr hf
    · exact Or.inl ⟨v, Or.inr hv, rfl⟩
  · rintro (⟨v, (⟨hv, hvE⟩ | hv), rfl⟩ | hf)
    · refine Or.inl ⟨Or.inl ⟨v, hv, rfl⟩, ?_⟩
      rintro ⟨w, hw, he⟩
      exact hvE (κ.ρ_inj he ▸ hw)
    · exact Or.inr ⟨v, hv, rfl⟩
    · refine Or.inl ⟨Or.inr hf, ?_⟩
      rintro ⟨w, -, rfl⟩
      exact hG _ hf w rfl

theorem ga_ne_of_mem_vocA {κ : Code} {d : DomDesc} (hκ : κ.Fresh d) {a : ℕ} (ha : a ∈ vocA d) :
    ∀ g, κ.ga g ≠ a := fun g h => hκ.ga_nmem g (h ▸ ha)

theorem seqReach_frame_mp {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d) {G : Set ℕ}
    (hG : ∀ f ∈ G, ∀ v, f ≠ κ.ρ v) {xs : List (ℕ ⊕ ℕ)} {s' u' : Set ℕ}
    (h : (seqDom κ d N).toDomain.SeqReach xs s' u') : ∀ s, s' = κ.ρ '' s ∪ G →
      (∀ x ∈ xs, x ∈ knownList d) → ∃ u, d.toDomain.SeqReach xs s u ∧ u' = κ.ρ '' u ∪ G := by
  induction h with
  | nil => intro s hs _; exact ⟨s, .nil, hs⟩
  | @prim a xs s' u' happ hrest ih =>
    intro s hs hk
    have ha : a ∈ vocA d := mem_knownList_inl.1 (hk _ (List.mem_cons_self ..))
    have hne := ga_ne_of_mem_vocA hκ ha
    have happ' : d.toDomain.toActionModel.Applicable a s := by
      have := happ
      simp only [ActionModel.Applicable, DomDesc.toDomain_prec] at this ⊢
      rw [prec_seqDom_of_ne hne, hs] at this
      exact (image_subset_union_iff hG).1 this
    have htr : (seqDom κ d N).toDomain.toActionModel.transition a s' =
        κ.ρ '' d.toDomain.toActionModel.transition a s ∪ G := by
      simp only [ActionModel.transition, DomDesc.toDomain_add, DomDesc.toDomain_del]
      rw [add_seqDom_of_ne hne, del_seqDom_of_ne hne, hs, transition_image hG]
    obtain ⟨u, hu, rfl⟩ := ih _ htr fun x hx => hk x (List.mem_cons_of_mem _ hx)
    exact ⟨u, .prim happ' hu, rfl⟩
  | @comp c bs xs s' t u' hm hb hrest ihb ihs =>
    intro s hs hk
    have hc : c ∈ vocC d := mem_knownList_inr.1 (hk _ (List.mem_cons_self ..))
    have hcS : c ≠ κ.S := fun h => hκ.S_nmem (h ▸ hc)
    have hm' := (seqBody_seqDom_of_ne hcS).1 hm
    obtain ⟨t₀, ht₀, rfl⟩ := ihb s hs (known_of_seqBody hm')
    obtain ⟨u, hu, rfl⟩ := ihs t₀ rfl fun x hx => hk x (List.mem_cons_of_mem _ hx)
    exact ⟨u, .comp hm' ht₀ hu, rfl⟩

/-- **The frame lemma**: a sequence of tasks `d` mentions behaves in the gadget domain as in `d`,
on the renamed facts, and leaves the gadget's facts alone. -/
theorem seqReach_frame {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d) {G : Set ℕ}
    (hG : ∀ f ∈ G, ∀ v, f ≠ κ.ρ v) {xs : List (ℕ ⊕ ℕ)} (hxs : ∀ x ∈ xs, x ∈ knownList d)
    {s u' : Set ℕ} :
    (seqDom κ d N).toDomain.SeqReach xs (κ.ρ '' s ∪ G) u' ↔
      ∃ u, d.toDomain.SeqReach xs s u ∧ u' = κ.ρ '' u ∪ G := by
  constructor
  · exact fun h => seqReach_frame_mp hκ hG h s rfl hxs
  · rintro ⟨u, h, rfl⟩
    induction h with
    | nil => exact .nil
    | @prim a xs s u happ hrest ih =>
      have ha : a ∈ vocA d := mem_knownList_inl.1 (hxs _ (List.mem_cons_self ..))
      have hne := ga_ne_of_mem_vocA hκ ha
      refine .prim ?_ ?_
      · simp only [ActionModel.Applicable, DomDesc.toDomain_prec] at happ ⊢
        rw [prec_seqDom_of_ne hne]
        exact (image_subset_union_iff hG).2 happ
      · have htr : (seqDom κ d N).toDomain.toActionModel.transition a (κ.ρ '' s ∪ G) =
            κ.ρ '' d.toDomain.toActionModel.transition a s ∪ G := by
          simp only [ActionModel.transition, DomDesc.toDomain_add, DomDesc.toDomain_del]
          rw [add_seqDom_of_ne hne, del_seqDom_of_ne hne, transition_image hG]
        rw [htr]
        exact ih fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    | @comp c bs xs s t u hm hb hrest ihb ihs =>
      have hc : c ∈ vocC d := mem_knownList_inr.1 (hxs _ (List.mem_cons_self ..))
      have hcS : c ≠ κ.S := fun h => hκ.S_nmem (h ▸ hc)
      exact .comp ((seqBody_seqDom_of_ne hcS).2 hm) (ihb (known_of_seqBody hm))
        (ihs fun x hx => hxs x (List.mem_cons_of_mem _ hx))

/-! #### Inversion of the reachability relation -/

section Inversion

variable {F A C I : Type} {D : Domain F A C I}

theorem seqReach_nil_iff {s u : Set F} : D.SeqReach [] s u ↔ u = s := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem seqReach_inl_iff {a : A} {xs : List (A ⊕ C)} {s u : Set F} :
    D.SeqReach (Sum.inl a :: xs) s u ↔
      D.toActionModel.Applicable a s ∧ D.SeqReach xs (D.toActionModel.transition a s) u := by
  constructor
  · intro h; cases h with | prim h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact .prim h1 h2

theorem seqReach_inr_iff {c : C} {xs : List (A ⊕ C)} {s u : Set F} :
    D.SeqReach (Sum.inr c :: xs) s u ↔
      ∃ bs t, D.SeqBody c bs ∧ D.SeqReach bs s t ∧ D.SeqReach xs t u := by
  constructor
  · intro h; cases h with | comp hm hb hs => exact ⟨_, _, hm, hb, hs⟩
  · rintro ⟨bs, t, hm, hb, hs⟩; exact .comp hm hb hs

end Inversion

/-! #### The static facts -/

/-- The static facts, as a set. -/
def stat (κ : Code) (d : DomDesc) (xs : List (ℕ ⊕ ℕ)) (ws : List (ℕ × ℕ)) : Set ℕ :=
  {f | f ∈ gadStatic κ d xs ws}

theorem mem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} {g : GF} :
    κ.gf g ∈ stat κ d xs ws ↔ (∃ w ∈ ws, g = .wit w.1 w.2) ∨ g = .len xs.length ∨
      (∃ p < xs.length, g = .lab p (xs.getD p (Sum.inl 0))) ∨
      (∃ p < xs.length, unknownPrimB d (xs.getD p (Sum.inl 0)) = true ∧ g = .nop p) := by
  simp only [stat, gadStatic, Set.mem_setOf_eq, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range, List.mem_filter, κ.gf_inj.eq_iff]
  constructor
  · rintro (⟨w, hw, h⟩ | h | ⟨p, hp, h⟩ | ⟨p, ⟨hp, hu⟩, h⟩)
    · exact Or.inl ⟨w, hw, h.symm⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, h.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hu, h.symm⟩))
  · rintro (⟨w, hw, h⟩ | h | ⟨p, hp, h⟩ | ⟨p, hp, hu, h⟩)
    · exact Or.inl ⟨w, hw, h.symm⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨p, hp, h.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, ⟨hp, hu⟩, h.symm⟩))

theorem cur_nmem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} (p : ℕ) :
    κ.gf (.cur p) ∉ stat κ d xs ws := by
  rw [mem_stat]; simp

theorem fin_nmem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} :
    κ.gf .fin ∉ stat κ d xs ws := by
  rw [mem_stat]; simp

theorem lab_mem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)}
    {ws : List (ℕ × ℕ)} {p : ℕ} {x : ℕ ⊕ ℕ} :
    κ.gf (.lab p x) ∈ stat κ d xs ws ↔ ∃ h : p < xs.length, xs[p] = x := by
  rw [mem_stat]
  simp only [reduceCtorEq, false_or, GF.lab.injEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨p', hp', rfl, rfl⟩
    exact ⟨hp', (List.getD_eq_getElem _ _ hp').symm⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨p, hp, rfl, (List.getD_eq_getElem _ _ hp).symm⟩

theorem nop_mem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} {p : ℕ} :
    κ.gf (.nop p) ∈ stat κ d xs ws ↔ ∃ h : p < xs.length, unknownPrimB d xs[p] = true := by
  rw [mem_stat]
  simp only [reduceCtorEq, false_or, GF.nop.injEq, and_false, exists_false, false_or]
  constructor
  · rintro ⟨p', hp', hu, rfl⟩
    exact ⟨hp', by rwa [List.getD_eq_getElem _ _ hp'] at hu⟩
  · rintro ⟨hp, hu⟩
    exact ⟨p, hp, by rwa [List.getD_eq_getElem _ _ hp], rfl⟩

theorem len_mem_stat {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} {p : ℕ} :
    κ.gf (.len p) ∈ stat κ d xs ws ↔ p = xs.length := by
  rw [mem_stat]
  simp

theorem stat_ne_ρ {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} :
    ∀ f ∈ stat κ d xs ws, ∀ v, f ≠ κ.ρ v := by
  intro f hf v
  simp only [stat, gadStatic, Set.mem_setOf_eq, List.mem_cons, List.mem_append,
    List.mem_map] at hf
  rcases hf with ⟨w, -, rfl⟩ | rfl | ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩ <;> exact κ.gf_ne_ρ _ _

/-! #### Walking through the sequence -/

theorem gf_mem_image_union {κ : Code} {s G : Set ℕ} {g : GF} :
    κ.gf g ∈ κ.ρ '' s ∪ G ↔ κ.gf g ∈ G := by
  constructor
  · rintro (⟨v, -, hv⟩ | h)
    · exact absurd hv.symm (κ.gf_ne_ρ _ _)
    · exact h
  · exact Or.inr

/-- Executing a gadget action. -/
theorem seqReach_ga_iff {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d) {g : GA}
    (hg : g ∈ gadList d N) {ys : List (ℕ ⊕ ℕ)} {w u' : Set ℕ} :
    (seqDom κ d N).toDomain.SeqReach (Sum.inl (κ.ga g) :: ys) w u' ↔
      {f | f ∈ (gadVal κ g).1} ⊆ w ∧ (seqDom κ d N).toDomain.SeqReach ys
        ((w \ {f | f ∈ (gadVal κ g).2.2}) ∪ {f | f ∈ (gadVal κ g).2.1}) u' := by
  rw [seqReach_inl_iff]
  simp only [ActionModel.Applicable, ActionModel.transition, DomDesc.toDomain_prec,
    DomDesc.toDomain_add, DomDesc.toDomain_del]
  obtain ⟨h1, h2, h3⟩ := prec_seqDom_ga hκ hg
  rw [h1, h2, h3]

/-- Moving the cursor. -/
theorem move_cur {κ : Code} {s T : Set ℕ} {p : ℕ} (hT : κ.gf (.cur p) ∉ T) {X : ℕ}
    (hX : ∀ v, X ≠ κ.ρ v) :
    (κ.ρ '' s ∪ (T ∪ {κ.gf (.cur p)})) \ {f | f ∈ [κ.gf (.cur p)]} ∪ {f | f ∈ [X]} =
      κ.ρ '' s ∪ (T ∪ {X}) := by
  ext f
  simp only [Set.mem_union, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, List.mem_singleton,
    Set.mem_singleton_iff]
  constructor
  · rintro (⟨(⟨v, hv, rfl⟩ | hf | hf), hne⟩ | rfl)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr (Or.inl hf)
    · exact absurd hf hne
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨v, hv, rfl⟩ | hf | rfl)
    · exact Or.inl ⟨Or.inl ⟨v, hv, rfl⟩, fun h => κ.gf_ne_ρ _ _ h.symm⟩
    · exact Or.inl ⟨Or.inr (Or.inl hf), fun h => hT (h ▸ hf)⟩
    · exact Or.inr rfl

theorem cur_mem_state {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)}
    {ws : List (ℕ × ℕ)} {s : Set ℕ} {p p' : ℕ} :
    κ.gf (.cur p') ∈ κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur p)}) ↔ p' = p := by
  rw [gf_mem_image_union, Set.mem_union, Set.mem_singleton_iff, κ.gf_inj.eq_iff]
  simp [cur_nmem_stat]

theorem stat_mem_state {κ : Code} {d : DomDesc} {xs : List (ℕ ⊕ ℕ)}
    {ws : List (ℕ × ℕ)} {s : Set ℕ} {p : ℕ} {g : GF}
    (hg : ∀ p', g ≠ .cur p') :
    κ.gf g ∈ κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur p)}) ↔ κ.gf g ∈ stat κ d xs ws := by
  rw [gf_mem_image_union, Set.mem_union, Set.mem_singleton_iff, κ.gf_inj.eq_iff]
  simp [hg p]

/-- **One step of the gadget** from the state with cursor `p`. -/
theorem seqReach_S_step {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d)
    {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} (hN : xs.length ≤ N) {s u' : Set ℕ} {p : ℕ} :
    (seqDom κ d N).toDomain.SeqReach [Sum.inr κ.S]
        (κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur p)})) u' ↔
      (p = xs.length ∧ u' = κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf .fin})) ∨
      (∃ h : p < xs.length, xs[p] ∈ knownList d ∧ (seqDom κ d N).toDomain.SeqReach
        [xs[p], Sum.inr κ.S] (κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur (p + 1))})) u') ∨
      (∃ h : p < xs.length, unknownPrimB d xs[p] = true ∧ (seqDom κ d N).toDomain.SeqReach
        [Sum.inr κ.S] (κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur (p + 1))})) u') := by
  have hT := cur_nmem_stat (κ := κ) (d := d) (xs := xs) (ws := ws) p
  have hcur : ∀ q, ∀ v, κ.gf (.cur q) ≠ κ.ρ v := fun q v => κ.gf_ne_ρ _ _
  rw [seqReach_inr_iff]
  simp only [seqReach_nil_iff, seqBody_seqDom_S hκ]
  constructor
  · rintro ⟨bs, t, ⟨g, hg, rfl⟩, hb, rfl⟩
    cases g with
    | pick p' x' =>
      rw [gadBody, seqReach_ga_iff hκ hg] at hb
      obtain ⟨hpre, hb⟩ := hb
      simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hpre
      obtain ⟨h1, h2⟩ := hpre
      obtain rfl := cur_mem_state.1 h1
      rw [stat_mem_state (by simp), lab_mem_stat] at h2
      obtain ⟨hp, rfl⟩ := h2
      simp only [gadVal] at hb
      rw [move_cur hT (hcur _)] at hb
      exact Or.inr (Or.inl ⟨hp, (pick_mem_gadList.1 hg).2, hb⟩)
    | skip p' =>
      rw [gadBody, seqReach_ga_iff hκ hg] at hb
      obtain ⟨hpre, hb⟩ := hb
      simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hpre
      obtain ⟨h1, h2⟩ := hpre
      obtain rfl := cur_mem_state.1 h1
      rw [stat_mem_state (by simp), nop_mem_stat] at h2
      obtain ⟨hp, hu⟩ := h2
      simp only [gadVal] at hb
      rw [move_cur hT (hcur _)] at hb
      exact Or.inr (Or.inr ⟨hp, hu, hb⟩)
    | stop p' =>
      rw [gadBody, seqReach_ga_iff hκ hg] at hb
      obtain ⟨hpre, hb⟩ := hb
      simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hpre
      obtain ⟨h1, h2⟩ := hpre
      obtain rfl := cur_mem_state.1 h1
      rw [stat_mem_state (by simp), len_mem_stat] at h2
      simp only [gadVal] at hb
      rw [move_cur hT (fun v => κ.gf_ne_ρ _ v), seqReach_nil_iff] at hb
      exact Or.inl ⟨h2, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hp, hk, hb⟩ | ⟨hp, hu, hb⟩)
    · have hg : GA.stop xs.length ∈ gadList d N := stop_mem_gadList.2 hN
      refine ⟨_, _, ⟨_, hg, rfl⟩, ?_, rfl⟩
      rw [gadBody, seqReach_ga_iff hκ hg]
      refine ⟨?_, ?_⟩
      · simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨cur_mem_state.2 rfl, (stat_mem_state (by simp)).2 (len_mem_stat.2 rfl)⟩
      · simp only [gadVal]
        rw [move_cur hT (fun v => κ.gf_ne_ρ _ v)]
        exact .nil
    · have hg : GA.pick p xs[p] ∈ gadList d N := pick_mem_gadList.2 ⟨by omega, hk⟩
      refine ⟨_, _, ⟨_, hg, rfl⟩, ?_, rfl⟩
      rw [gadBody, seqReach_ga_iff hκ hg]
      refine ⟨?_, ?_⟩
      · simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨cur_mem_state.2 rfl, (stat_mem_state (by simp)).2 (lab_mem_stat.2 ⟨hp, rfl⟩)⟩
      · simp only [gadVal]
        rw [move_cur hT (hcur _)]
        exact hb
    · have hg : GA.skip p ∈ gadList d N := skip_mem_gadList.2 (by omega)
      refine ⟨_, _, ⟨_, hg, rfl⟩, ?_, rfl⟩
      rw [gadBody, seqReach_ga_iff hκ hg]
      refine ⟨?_, ?_⟩
      · simp only [gadVal, Set.setOf_subset, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        exact ⟨cur_mem_state.2 rfl, (stat_mem_state (by simp)).2 (nop_mem_stat.2 ⟨hp, hu⟩)⟩
      · simp only [gadVal]
        rw [move_cur hT (hcur _)]
        exact hb

theorem mem_vocC_of_seqBody {d : DomDesc} {c : ℕ} {bs : List (ℕ ⊕ ℕ)}
    (h : d.toDomain.SeqBody c bs) : c ∈ vocC d := by
  obtain ⟨e, he, rfl, -⟩ := seqBody_desc_iff.1 h
  exact List.mem_append_left _ (List.mem_map_of_mem he)

/-- **The walk through the sequence**: from the state with cursor `p`, the gadget task `κ.S`
executes the suffix of the sequence from position `p` on, and sets `fin`. -/
theorem seqReach_walk {κ : Code} {d : DomDesc} {N : ℕ} (hκ : κ.Fresh d)
    {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)} (hN : xs.length ≤ N) :
    ∀ k p, xs.length - p = k → p ≤ xs.length → ∀ {s u' : Set ℕ},
      (seqDom κ d N).toDomain.SeqReach [Sum.inr κ.S]
          (κ.ρ '' s ∪ (stat κ d xs ws ∪ {κ.gf (.cur p)})) u' ↔
        ∃ u, d.toDomain.SeqReach (xs.drop p) s u ∧
          u' = κ.ρ '' u ∪ (stat κ d xs ws ∪ {κ.gf .fin}) := by
  intro k
  induction k with
  | zero =>
    intro p hk hp s u'
    obtain rfl : p = xs.length := by omega
    rw [seqReach_S_step hκ hN, List.drop_length]
    simp only [seqReach_nil_iff, lt_irrefl, true_and]
    constructor
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact ⟨s, rfl, h⟩
      · exact h.elim
      · exact h.elim
    · rintro ⟨u, rfl, rfl⟩
      exact Or.inl rfl
  | succ k ih =>
    intro p hk hp' s u'
    have hp : p < xs.length := by omega
    have ih' := fun {s u'} => ih (p + 1) (by omega) (by omega) (s := s) (u' := u')
    rw [seqReach_S_step hκ hN, List.drop_eq_getElem_cons hp]
    have hG : ∀ f ∈ stat κ d xs ws ∪ {κ.gf (.cur (p + 1))}, ∀ v, f ≠ κ.ρ v := by
      rintro f (hf | rfl) v
      · exact stat_ne_ρ f hf v
      · exact κ.gf_ne_ρ _ _
    by_cases hkn : xs[p] ∈ knownList d
    · have hnu : unknownPrimB d xs[p] = false := by
        rcases hx : xs[p] with a | c
        · rw [hx, mem_knownList_inl] at hkn
          simp [unknownPrimB, hkn]
        · rfl
      simp only [hp, hkn, hnu, exists_true_left, true_and, Bool.false_eq_true, false_and,
        or_false, show p ≠ xs.length by omega, false_and, false_or]
      rw [show [xs[p], Sum.inr κ.S] = [xs[p]] ++ [Sum.inr κ.S] from rfl,
        Domain.seqReach_append_iff]
      constructor
      · rintro ⟨t, h1, h2⟩
        obtain ⟨s₁, hs₁, rfl⟩ := (seqReach_frame hκ hG (by simpa using hkn)).1 h1
        obtain ⟨u, hu, rfl⟩ := ih'.1 h2
        exact ⟨u, (Domain.seqReach_append_iff (xs := [xs[p]])).2 ⟨s₁, hs₁, hu⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨s₁, hs₁, hu⟩ := (Domain.seqReach_append_iff (xs := [xs[p]])).1 hu
        exact ⟨_, (seqReach_frame hκ hG (by simpa using hkn)).2 ⟨s₁, hs₁, rfl⟩,
          ih'.2 ⟨u, hu, rfl⟩⟩
    · simp only [hp, hkn, exists_true_left, false_and, show p ≠ xs.length by omega,
        false_or]
      rcases hx : xs[p] with a | c
      · have ha : a ∉ vocA d := fun h => hkn (hx ▸ mem_knownList_inl.2 h)
        have hna : a ∉ d.actions.map Prod.fst := fun h => ha (names_actions_subset_vocA d h)
        obtain ⟨h1, h2, h3⟩ := prec_eq_empty_of_nmem hna
        simp only [unknownPrimB, ha, decide_false, Bool.not_false, true_and]
        rw [ih']
        simp only [seqReach_inl_iff, ActionModel.Applicable, ActionModel.transition,
          DomDesc.toDomain_prec, DomDesc.toDomain_add, DomDesc.toDomain_del, h1, h2, h3,
          Set.empty_subset, true_and, Set.diff_empty, Set.union_empty]
      · simp only [unknownPrimB, Bool.false_eq_true, false_and, false_iff, not_exists, not_and]
        intro u hu
        obtain ⟨bs, t, hb, -, -⟩ := seqReach_inr_iff.1 hu
        exact absurd (hx ▸ mem_knownList_inr.2 (mem_vocC_of_seqBody hb)) hkn

/-- **The sequencing gadget is correct**: an instance whose initial task network is the sequence
network of a task sequence `xs` of length at most `N` is solvable exactly when the rooted gadget
instance for `xs` is — whatever witness facts `ws` the gadget instance carries. -/
theorem solvable_seq_iff {κ : Code} {d : DomDesc} {q : InstDesc} {N : ℕ} (hκ : κ.Fresh d)
    (hTO : d.MethodsTO) {l : List ℕ} {xs : List (ℕ ⊕ ℕ)}
    (hseq : q.tnI.toTaskNetwork.IsSeqNet l xs) (hN : xs.length ≤ N) (ws : List (ℕ × ℕ)) :
    Solvable d q ↔ Solvable (seqDom κ d N) (seqInst κ d q xs ws) := by
  have hroot : rootName (seqInst κ d q xs ws) = κ.S := rfl
  have hinit : {f | f ∈ (seqInst κ d q xs ws).initList} =
      κ.ρ '' {f | f ∈ q.initList} ∪ (stat κ d xs ws ∪ {κ.gf (.cur 0)}) := by
    ext f
    simp only [seqInst, gadInit, InstDesc.initList, stat, Set.mem_setOf_eq, List.mem_append,
      List.mem_map, List.mem_cons, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
    constructor <;> rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hgoal : ∀ u, {f | f ∈ (seqInst κ d q xs ws).goalList} ⊆
      κ.ρ '' u ∪ (stat κ d xs ws ∪ {κ.gf .fin}) ↔ {f | f ∈ q.goalList} ⊆ u := by
    intro u
    simp only [seqInst, InstDesc.goalList, Set.setOf_subset, List.mem_append, List.mem_map,
      List.mem_singleton]
    constructor
    · intro h v hv
      rcases h _ (Or.inl ⟨v, hv, rfl⟩) with ⟨w, hw, hwv⟩ | h' | h'
      · rwa [← κ.ρ_inj hwv]
      · exact absurd h' (stat_ne_ρ _ · v rfl)
      · exact absurd h' (κ.gf_ne_ρ _ v).symm
    · rintro h f (⟨v, hv, rfl⟩ | rfl)
      · exact Or.inl ⟨v, h v hv, rfl⟩
      · exact Or.inr (Or.inr rfl)
  have hM : (problem d q).IsTO_M := fun m hm => by
    obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
    exact hTO e he
  rw [Solvable, Problem.solvable_iff_seqReach (problem_wf d q) hM hseq,
    Space.solvable_iff_seqReach_root (methodsTO_seqDom hTO) (isRooted_seqInst κ d q xs ws), hroot,
    hinit]
  simp only [seqReach_walk hκ hN xs.length 0 (by simp) (by simp), List.drop_zero]
  constructor
  · rintro ⟨u, hu, hg⟩
    exact ⟨_, ⟨u, hu, rfl⟩, (hgoal u).2 hg⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, hg⟩
    exact ⟨u, hu, (hgoal u).1 hg⟩

/-- The sequencing gadget for the linearisation of a totally ordered initial task network. -/
theorem solvable_seq_iff_lin {κ : Code} {d : DomDesc} {q : InstDesc} {N : ℕ} (hκ : κ.Fresh d)
    (hTO : d.MethodsTO) (hq : q.IsTO) (hN : (TnDesc.seqBody q.tnI).length ≤ N)
    (ws : List (ℕ × ℕ)) :
    Solvable d q ↔ Solvable (seqDom κ d N) (seqInst κ d q (TnDesc.seqBody q.tnI) ws) :=
  solvable_seq_iff hκ hTO (TnDesc.isSeqNet_lin hq) hN ws

end SeqG

end Syn

end HTN
