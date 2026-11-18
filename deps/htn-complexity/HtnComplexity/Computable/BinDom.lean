import HtnComplexity.Computable.AcSmall
import HtnComplexity.Computable.AcEnc
import HtnComplexity.ToHtnAc.ToHtnAcBodies
/-!
# Binarisation of a described totally ordered domain

The compilation of totally ordered problems into acyclic ones
(`HtnComplexity/Computable/AcSmall.lean`, `…/AcCell.lean`) assumes, following the source,
that every method has **exactly two subtasks** (`HTN.Syn.DomDesc.IsBin2`) and that no operator
adds and deletes the same fact (`HTN.Syn.DomDesc.NoAddDel`).  This file removes both
assumptions by a **compilation of descriptions** — the description-level counterpart of
`HtnPlanning/Binarisation/Binarisation.lean`.

A method `c ↦ x₁ … xₙ` of the source description is replaced by the chain

```
c        ↦ x₁ H(m,1)
H(m,1)   ↦ x₂ H(m,2)
  ⋮
H(m,n-1) ↦ xₙ nop
```

of methods with exactly two subtasks, where `H(m,k)` are fresh compound task names attached to
the *position* `m` of the method in the description, and `nop` is a fresh action with empty
precondition, add and delete list.  A method with an empty body becomes `c ↦ nop nop`.  So that
`nop` and the helper names are fresh, the names of the source are **doubled**:

    an action `a`      of the source becomes the action `2a`
    a compound name `c` of the source becomes the compound name `2c`
    the fresh action is `nop = 1`, the fresh compound names are `H(m,k) = 2⟨m,k⟩+1`

Finally the delete list of every action is intersected away from its add list, which changes no
transition (`(s \ (del \ add)) ∪ add = (s \ del) ∪ add`) and gives `NoAddDel`.

This file contains the construction and its *static* properties; the correctness proof is in
`HtnComplexity/Computable/BinCorrect.lean`.
-/

namespace HTN

namespace Syn

namespace Binarise

/-! ### Names -/

/-- The fresh no-op action of the compiled description. -/
def nopA : ℕ := 1

/-- The no-op task. -/
def nopTask : ℕ ⊕ ℕ := Sum.inl nopA

/-- The encoding of a task of the source description: names are doubled. -/
def encTask : ℕ ⊕ ℕ → ℕ ⊕ ℕ
  | Sum.inl a => Sum.inl (2 * a)
  | Sum.inr c => Sum.inr (2 * c)

/-- The fresh compound task name for the suffix of the body of the method at position `m`
starting at position `k` (used only for `k ≥ 1`). -/
def hName (m k : ℕ) : ℕ := 2 * Nat.pair m k + 1

lemma hName_odd (m k : ℕ) : hName m k % 2 = 1 := by
  unfold hName
  omega

lemma hName_ne_double (m k c : ℕ) : hName m k ≠ 2 * c := by
  intro h
  have := hName_odd m k
  omega

lemma hName_inj {m k m' k' : ℕ} (h : hName m k = hName m' k') : m = m' ∧ k = k' := by
  have hp : Nat.pair m k = Nat.pair m' k' := by
    simp only [hName] at h
    omega
  simpa using Nat.pair_eq_pair.1 hp

/-! ### Two-task bodies -/

/-- The label entry of a task. -/
def lblOf : ℕ ⊕ ℕ → Bool × ℕ
  | Sum.inl a => (false, a)
  | Sum.inr c => (true, c)

/-- The description of the totally ordered network with the two tasks `x` and `y`, in this
order. -/
def pairBody (x y : ℕ ⊕ ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, lblOf x), (1, lblOf y)])

@[simp] lemma pairBody_ids (x y : ℕ ⊕ ℕ) : (pairBody x y).ids = [0, 1] := rfl

@[simp] lemma pairBody_ordList (x y : ℕ ⊕ ℕ) : (pairBody x y).ordList = [(0, 1)] := rfl

@[simp] lemma pairBody_lbl (x y : ℕ ⊕ ℕ) :
    (pairBody x y).lbl = [(0, lblOf x), (1, lblOf y)] := rfl

@[simp] lemma pairBody_label_zero (x y : ℕ ⊕ ℕ) : (pairBody x y).label 0 = x := by
  cases x <;> rfl

@[simp] lemma pairBody_label_one (x y : ℕ ⊕ ℕ) : (pairBody x y).label 1 = y := by
  cases y <;> rfl

/-- The described two-task network is a sequence network. -/
theorem pairBody_isSeqNet (x y : ℕ ⊕ ℕ) :
    (pairBody x y).toTaskNetwork.IsSeqNet [0, 1] [x, y] := by
  have hno : ¬ (pairBody x y).preOrd 1 0 := by
    intro h
    rcases Relation.TransGen.head'_iff.1 h with ⟨c, hc, -⟩
    simp [TnDesc.listRel, pairBody, TnDesc.ordList] at hc
  have h01 : (pairBody x y).preOrd 0 1 :=
    Relation.TransGen.single (by simp [TnDesc.listRel, pairBody, TnDesc.ordList])
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro s
    simp [TnDesc.toTaskNetwork]
  · intro s u
    simp only [TnDesc.toTaskNetwork_ord, pairBody_ids, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨hs, hu, hpre, hnp⟩
      refine ⟨hs, hu, ?_⟩
      rcases hs with rfl | rfl <;> rcases hu with rfl | rfl <;>
        first
          | exact absurd hpre hno
          | simp_all
    · rintro ⟨hs, hu, hidx⟩
      rcases hs with rfl | rfl <;> rcases hu with rfl | rfl
      · simp at hidx
      · exact ⟨by simp, by simp, h01, hno⟩
      · simp at hidx
      · simp at hidx

theorem pairBody_isTO (x y : ℕ ⊕ ℕ) : (pairBody x y).toTaskNetwork.IsTotallyOrdered :=
  (pairBody_isSeqNet x y).isTotallyOrdered

/-- **The body of a two-task method description** is the pair of its tasks. -/
theorem seqBody_pairBody (x y : ℕ ⊕ ℕ) : TnDesc.seqBody (pairBody x y) = [x, y] := by
  have h₁ : (MethodDesc.toMethod (0, pairBody x y)).HasSeqBody (TnDesc.seqBody (pairBody x y)) :=
    Method.hasSeqBody_of_isSeqNet (TnDesc.isSeqNet_lin (pairBody_isTO x y))
  exact (Method.hasSeqBody_iff_of_isSeqNet
    (m := MethodDesc.toMethod (0, pairBody x y)) (pairBody_isSeqNet x y)).1 h₁

@[simp] lemma pairBody_size (x y : ℕ ⊕ ℕ) : (pairBody x y).size = 5 := by
  simp [TnDesc.size, pairBody, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

/-! ### The compiled description -/

variable (d : DomDesc)

/-- The head of the `k`-th method of the chain replacing the method at position `m`. -/
def headName (d : DomDesc) (m k : ℕ) : ℕ := if k = 0 then 2 * d.hd m else hName m k

/-- The second subtask of the `k`-th method of the chain replacing the method at position
`m`. -/
def tailTask (d : DomDesc) (m k : ℕ) : ℕ ⊕ ℕ :=
  if k + 1 = (d.bd m).length then nopTask else Sum.inr (hName m (k + 1))

/-- The chain of binary methods replacing the method at position `m`. -/
def chainMethods (d : DomDesc) (m : ℕ) : List MethodDesc :=
  if (d.bd m).length = 0 then [(2 * d.hd m, pairBody nopTask nopTask)]
  else (List.range (d.bd m).length).map fun k =>
    (headName d m k, pairBody (encTask ((d.bd m).getI k)) (tailTask d m k))

/-- An action of the source description, with its name doubled and its delete list made
disjoint from its add list. -/
def fixAct (p : ActionDesc) : ActionDesc :=
  (2 * p.1, p.2.1, p.2.2.1, p.2.2.2.filter fun f => !memB p.2.2.1 f)

/-- The action list of the compiled description: the fresh no-op, and every source action with
its name doubled and its delete list made disjoint from its add list. -/
def binActions (d : DomDesc) : List ActionDesc :=
  (nopA, [], [], []) :: d.actions.map fixAct

/-- **The binarised domain description.** -/
def binDom (d : DomDesc) : DomDesc :=
  (binActions d, (List.range d.methods.length).flatMap (chainMethods d))

/-- **The translated instance description**: the same state and goal, and the initial task
network with every name doubled. -/
def binInst (q : InstDesc) : InstDesc :=
  (q.initList, q.goalList,
    (q.tnI.ids, q.tnI.ordList, q.tnI.lbl.map fun p => (p.1, p.2.1, 2 * p.2.2)))

/-! ### Every listed method is a two-task method -/

theorem chainMethods_shape {d : DomDesc} {m : ℕ} {e : MethodDesc} (he : e ∈ chainMethods d m) :
    ∃ x y, e.2 = pairBody x y := by
  unfold chainMethods at he
  split at he
  · simp only [List.mem_singleton] at he
    exact ⟨nopTask, nopTask, by rw [he]⟩
  · simp only [List.mem_map, List.mem_range] at he
    obtain ⟨k, -, rfl⟩ := he
    exact ⟨_, _, rfl⟩

theorem binDom_methods_shape {d : DomDesc} {e : MethodDesc} (he : e ∈ (binDom d).methods) :
    ∃ x y, e.2 = pairBody x y := by
  simp only [binDom, DomDesc.methods, List.mem_flatMap] at he
  obtain ⟨m, -, hm⟩ := he
  exact chainMethods_shape hm

/-- The compiled description is totally ordered. -/
theorem binDom_methodsTO (d : DomDesc) : DomDesc.MethodsTO (binDom d) := by
  intro e he
  obtain ⟨x, y, hxy⟩ := binDom_methods_shape he
  rw [hxy]
  exact pairBody_isTO x y

/-- Every method of the compiled description has exactly two subtasks. -/
theorem binDom_isBin2 (d : DomDesc) : DomDesc.IsBin2 (binDom d) := by
  intro m hm
  have he : (binDom d).methods.getI m ∈ (binDom d).methods := getI_mem_methods hm
  obtain ⟨x, y, hxy⟩ := binDom_methods_shape he
  rw [DomDesc.bd, hxy, seqBody_pairBody]
  rfl

/-! ### The action model of the compiled description -/

lemma memB_eq_false_iff {l : List ℕ} {n : ℕ} : memB l n = false ↔ n ∉ l := by
  rw [← memB_iff]
  cases memB l n <;> simp

/-- The lookup of a doubled action name in the compiled action list. -/
theorem lookup_map_fixAct (l : List ActionDesc) (a : ℕ) :
    (l.map fixAct).lookup (2 * a) =
      (l.lookup a).map fun t => (t.1, t.2.1, t.2.2.filter fun f => !memB t.2.1 f) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, show fixAct p = (2 * p.1, p.2.1, p.2.2.1, _) from rfl,
      List.lookup_cons, show p = (p.1, p.2) from rfl, List.lookup_cons]
    by_cases hp : a = p.1
    · subst hp
      simp
    · have h1 : (2 * a == 2 * p.1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      have h2 : (a == p.1) = false := by simp [hp]
      rw [h1, h2]
      exact ih

/-- An odd name is not the name of a translated source action. -/
theorem lookup_map_fixAct_odd (l : List ActionDesc) {n : ℕ} (hodd : n % 2 = 1) :
    (l.map fixAct).lookup n = none := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, show fixAct p = (2 * p.1, p.2.1, p.2.2.1, _) from rfl, List.lookup_cons]
    have h1 : (n == 2 * p.1) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    rw [h1]
    exact ih

variable {d : DomDesc}

@[simp] theorem binDom_actions (d : DomDesc) : (binDom d).actions = binActions d := rfl

theorem binDom_prec_double (d : DomDesc) (a : ℕ) :
    DomDesc.prec (binDom d) (2 * a) = d.prec a := by
  have hne : ((2 * a) == nopA) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, nopA]
    omega
  simp only [DomDesc.prec, binDom_actions, binActions, List.lookup_cons, hne,
    lookup_map_fixAct]
  rcases h : d.actions.lookup a with _ | t <;> simp

theorem binDom_add_double (d : DomDesc) (a : ℕ) :
    DomDesc.add (binDom d) (2 * a) = d.add a := by
  have hne : ((2 * a) == nopA) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, nopA]
    omega
  simp only [DomDesc.add, binDom_actions, binActions, List.lookup_cons, hne,
    lookup_map_fixAct]
  rcases h : d.actions.lookup a with _ | t <;> simp

theorem binDom_del_double (d : DomDesc) (a : ℕ) :
    DomDesc.del (binDom d) (2 * a) = d.del a \ d.add a := by
  have hne : ((2 * a) == nopA) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, nopA]
    omega
  simp only [DomDesc.del, DomDesc.add, binDom_actions, binActions, List.lookup_cons, hne,
    lookup_map_fixAct]
  rcases h : d.actions.lookup a with _ | t
  · simp
  · ext f
    simp [Set.mem_diff, memB_eq_false_iff]

/-- An odd action name of the compiled description has empty precondition, add and delete
list. -/
theorem binDom_lists_odd (d : DomDesc) {n : ℕ} (hodd : n % 2 = 1) :
    DomDesc.prec (binDom d) n = ∅ ∧ DomDesc.add (binDom d) n = ∅ ∧
      DomDesc.del (binDom d) n = ∅ := by
  have hl : ∀ g : List ℕ × List ℕ × List ℕ → List ℕ, g ([], [], []) = [] →
      ((binDom d).actions.lookup n).elim [] g = [] := by
    intro g hg
    by_cases h1 : n = nopA
    · subst h1
      simp [binDom, DomDesc.actions, binActions, hg]
    · have hne : (n == nopA) = false := by simp [h1]
      simp only [binDom, DomDesc.actions, binActions, List.lookup_cons, hne,
        lookup_map_fixAct_odd _ hodd]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · show {f | f ∈ ((binDom d).actions.lookup n).elim [] fun x => x.1} = ∅
    rw [hl _ rfl]
    simp
  · show {f | f ∈ ((binDom d).actions.lookup n).elim [] fun x => x.2.1} = ∅
    rw [hl _ rfl]
    simp
  · show {f | f ∈ ((binDom d).actions.lookup n).elim [] fun x => x.2.2} = ∅
    rw [hl _ rfl]
    simp

/-- **No action of the compiled description adds and deletes the same fact.** -/
theorem binDom_noAddDel (d : DomDesc) : DomDesc.NoAddDel (binDom d) := by
  intro b f hf
  rcases Nat.even_or_odd b with ⟨a, ha⟩ | hodd
  · have hb : b = 2 * a := by omega
    subst hb
    rw [binDom_del_double]
    rw [binDom_add_double] at hf
    exact fun hcon => hcon.2 hf
  · have hodd' : b % 2 = 1 := Nat.odd_iff.1 hodd
    rw [(binDom_lists_odd d hodd').2.1] at hf
    exact hf.elim

/-! ### Plans of the compiled description -/

/-- The source plan of a plan of the compiled description: the no-ops are dropped and the
remaining, doubled, action names are halved. -/
def dec (as : List ℕ) : List ℕ := as.filterMap fun a => if a % 2 = 0 then some (a / 2) else none

@[simp] lemma dec_nil : dec [] = [] := rfl

@[simp] lemma dec_cons_double (a : ℕ) (l : List ℕ) : dec (2 * a :: l) = a :: dec l := by
  have h : (2 * a) % 2 = 0 := by omega
  simp only [dec, List.filterMap_cons, h, if_pos]
  congr 1
  omega

lemma dec_cons_odd {n : ℕ} (hodd : n % 2 = 1) (l : List ℕ) : dec (n :: l) = dec l := by
  simp [dec, hodd]

@[simp] lemma dec_cons_nop (l : List ℕ) : dec (nopA :: l) = dec l :=
  dec_cons_odd (by simp [nopA]) l

@[simp] lemma dec_append (l₁ l₂ : List ℕ) : dec (l₁ ++ l₂) = dec l₁ ++ dec l₂ := by
  simp [dec, List.filterMap_append]

lemma set_diff_diff_union (s D A : Set ℕ) : (s \ (D \ A)) ∪ A = (s \ D) ∪ A := by
  ext f
  by_cases hA : f ∈ A <;> simp [hA]

/-- **The compiled description executes a plan exactly as the source description executes its
decoding.** -/
theorem transitionSeq_bin (d : DomDesc) (as : List ℕ) (s : Set ℕ) :
    (binDom d).toDomain.transitionSeq as s = d.toDomain.transitionSeq (dec as) s := by
  induction as generalizing s with
  | nil => rfl
  | cons b as ih =>
    rcases Nat.even_or_odd b with ⟨a, ha⟩ | hodd
    · have hb : b = 2 * a := by omega
      subst hb
      have hstep : (binDom d).toDomain.transition (2 * a) s = d.toDomain.transition a s := by
        show ((s \ DomDesc.del (binDom d) (2 * a)) ∪ DomDesc.add (binDom d) (2 * a)) =
          ((s \ d.del a) ∪ d.add a)
        rw [binDom_del_double, binDom_add_double, set_diff_diff_union]
      rw [ActionModel.transitionSeq_cons, hstep, dec_cons_double, ActionModel.transitionSeq_cons, ih]
    · have hodd' : b % 2 = 1 := Nat.odd_iff.1 hodd
      obtain ⟨-, hadd, hdel⟩ := binDom_lists_odd d hodd'
      have hstep : (binDom d).toDomain.transition b s = s := by
        show ((s \ DomDesc.del (binDom d) b) ∪ DomDesc.add (binDom d) b) = s
        rw [hadd, hdel]
        simp
      rw [ActionModel.transitionSeq_cons, hstep, dec_cons_odd hodd', ih]

/-- **A plan of the compiled description is executable exactly when its decoding is.** -/
theorem seqApplicable_bin (d : DomDesc) (as : List ℕ) (s : Set ℕ) :
    (binDom d).toDomain.SeqApplicable as s ↔ d.toDomain.SeqApplicable (dec as) s := by
  induction as generalizing s with
  | nil => simp
  | cons b as ih =>
    rcases Nat.even_or_odd b with ⟨a, ha⟩ | hodd
    · have hb : b = 2 * a := by omega
      subst hb
      have hstep : (binDom d).toDomain.transition (2 * a) s = d.toDomain.transition a s := by
        show ((s \ DomDesc.del (binDom d) (2 * a)) ∪ DomDesc.add (binDom d) (2 * a)) =
          ((s \ d.del a) ∪ d.add a)
        rw [binDom_del_double, binDom_add_double, set_diff_diff_union]
      have happ : (binDom d).toDomain.Applicable (2 * a) s ↔ d.toDomain.Applicable a s := by
        show DomDesc.prec (binDom d) (2 * a) ⊆ s ↔ d.prec a ⊆ s
        rw [binDom_prec_double]
      show ((binDom d).toDomain.Applicable (2 * a) s ∧ _) ↔ _
      rw [happ, hstep, dec_cons_double]
      exact and_congr_right fun _ => ih _
    · have hodd' : b % 2 = 1 := Nat.odd_iff.1 hodd
      obtain ⟨hprec, hadd, hdel⟩ := binDom_lists_odd d hodd'
      have hstep : (binDom d).toDomain.transition b s = s := by
        show ((s \ DomDesc.del (binDom d) b) ∪ DomDesc.add (binDom d) b) = s
        rw [hadd, hdel]
        simp
      have happ : (binDom d).toDomain.Applicable b s := by
        show DomDesc.prec (binDom d) b ⊆ s
        rw [hprec]
        exact Set.empty_subset s
      show ((binDom d).toDomain.Applicable b s ∧ _) ↔ _
      rw [hstep, dec_cons_odd hodd']
      exact ⟨fun h => (ih s).1 h.2, fun h => ⟨happ, (ih s).2 h⟩⟩

/-! ### The translated instance -/

lemma lookup_map_double (l : List (ℕ × Bool × ℕ)) (i : ℕ) :
    (l.map fun p => (p.1, p.2.1, 2 * p.2.2)).lookup i =
      (l.lookup i).map fun t => (t.1, 2 * t.2) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    rw [List.map_cons, show ((p.1, p.2.1, 2 * p.2.2) : ℕ × Bool × ℕ) =
      (p.1, (p.2.1, 2 * p.2.2)) from rfl, List.lookup_cons,
      show p = (p.1, p.2) from rfl, List.lookup_cons]
    by_cases hp : i = p.1
    · subst hp
      simp
    · have h2 : (i == p.1) = false := by simp [hp]
      rw [h2]
      exact ih

@[simp] lemma binInst_initList (q : InstDesc) : (binInst q).initList = q.initList := rfl

@[simp] lemma binInst_goalList (q : InstDesc) : (binInst q).goalList = q.goalList := rfl

@[simp] lemma binInst_ids (q : InstDesc) : (binInst q).tnI.ids = q.tnI.ids := rfl

/-- The labels of the translated initial task network are the encoded labels. -/
theorem binInst_label (q : InstDesc) (i : ℕ) :
    (binInst q).tnI.label i = encTask (q.tnI.label i) := by
  show (match ((q.tnI.lbl.map fun p => (p.1, p.2.1, 2 * p.2.2)).lookup i) with
      | some (true, n) => Sum.inr n
      | some (false, n) => Sum.inl n
      | none => Sum.inl 0) = encTask (q.tnI.label i)
  rw [lookup_map_double]
  rcases h : q.tnI.lbl.lookup i with _ | ⟨b, n⟩
  · simp [TnDesc.label, h, encTask]
  · cases b <;> simp [TnDesc.label, h, encTask]

@[simp] lemma binInst_T (q : InstDesc) :
    (binInst q).tnI.toTaskNetwork.T = q.tnI.toTaskNetwork.T := rfl

/-- The root of a rooted instance description is doubled by the translation. -/
theorem binInst_root {q : InstDesc} {t c : ℕ} (hT : q.tnI.toTaskNetwork.T = {t})
    (hα : q.tnI.toTaskNetwork.α t = Sum.inr c) :
    (binInst q).tnI.toTaskNetwork.T = {t} ∧
      (binInst q).tnI.toTaskNetwork.α t = Sum.inr (2 * c) := by
  refine ⟨hT, ?_⟩
  show (binInst q).tnI.label t = Sum.inr (2 * c)
  rw [binInst_label]
  show encTask (q.tnI.label t) = Sum.inr (2 * c)
  rw [show q.tnI.label t = Sum.inr c from hα]
  rfl

/-- The translated instance description is rooted. -/
theorem binInst_isRooted {q : InstDesc} (h : InstDesc.IsRooted q) :
    InstDesc.IsRooted (binInst q) := by
  obtain ⟨t, c, hT, hα⟩ := h
  obtain ⟨hT', hα'⟩ := binInst_root hT hα
  exact ⟨t, 2 * c, hT', hα'⟩

/-! ### The productions of the compiled description -/

/-- The bodies of a totally ordered domain description, indexed by the *listed* methods. -/
theorem seqBody_iff_mem {d : DomDesc} (hTO : DomDesc.MethodsTO d) {c : ℕ}
    {bs : List (ℕ ⊕ ℕ)} :
    d.toDomain.SeqBody c bs ↔ ∃ e ∈ d.methods, e.1 = c ∧ TnDesc.seqBody e.2 = bs := by
  rw [DomDesc.seqBody_iff hTO]
  constructor
  · rintro ⟨m, hm, hc, hb⟩
    exact ⟨d.methods.getI m, getI_mem_methods hm, hc, hb⟩
  · rintro ⟨e, he, hc, hb⟩
    obtain ⟨m, hm, hgm⟩ := List.mem_iff_getElem.1 he
    refine ⟨m, hm, ?_, ?_⟩
    · rw [DomDesc.hd, List.getI_eq_getElem (l := d.methods) hm, hgm]
      exact hc
    · rw [DomDesc.bd, List.getI_eq_getElem (l := d.methods) hm, hgm]
      exact hb

/-- **The productions of the compiled description.** -/
theorem seqBody_binDom_iff (d : DomDesc) {c' : ℕ} {bs' : List (ℕ ⊕ ℕ)} :
    (binDom d).toDomain.SeqBody c' bs' ↔
      (∃ m, m < d.methods.length ∧ (d.bd m).length = 0 ∧ c' = 2 * d.hd m ∧
          bs' = [nopTask, nopTask]) ∨
      (∃ m k, m < d.methods.length ∧ k < (d.bd m).length ∧ c' = headName d m k ∧
          bs' = [encTask ((d.bd m).getI k), tailTask d m k]) := by
  rw [seqBody_iff_mem (binDom_methodsTO d)]
  constructor
  · rintro ⟨e, he, hc, hb⟩
    simp only [binDom, DomDesc.methods, List.mem_flatMap, List.mem_range] at he
    obtain ⟨m, hm, hme⟩ := he
    unfold chainMethods at hme
    split at hme
    · rename_i hlen
      simp only [List.mem_singleton] at hme
      subst hme
      refine Or.inl ⟨m, hm, hlen, hc.symm, ?_⟩
      rw [← hb, seqBody_pairBody]
    · simp only [List.mem_map, List.mem_range] at hme
      obtain ⟨k, hk, rfl⟩ := hme
      refine Or.inr ⟨m, k, hm, hk, hc.symm, ?_⟩
      rw [← hb, seqBody_pairBody]
  · rintro (⟨m, hm, hlen, rfl, rfl⟩ | ⟨m, k, hm, hk, rfl, rfl⟩)
    · refine ⟨(2 * d.hd m, pairBody nopTask nopTask), ?_, rfl, seqBody_pairBody _ _⟩
      simp only [binDom, DomDesc.methods, List.mem_flatMap, List.mem_range]
      exact ⟨m, hm, by unfold chainMethods; rw [if_pos hlen]; simp⟩
    · refine ⟨(headName d m k, pairBody (encTask ((d.bd m).getI k)) (tailTask d m k)), ?_, rfl,
        seqBody_pairBody _ _⟩
      simp only [binDom, DomDesc.methods, List.mem_flatMap, List.mem_range]
      refine ⟨m, hm, ?_⟩
      have hlen : ¬ ((d.bd m).length = 0) := by omega
      unfold chainMethods
      rw [if_neg hlen]
      simp only [List.mem_map, List.mem_range]
      exact ⟨k, hk, rfl⟩

end Binarise

end Syn

end HTN
