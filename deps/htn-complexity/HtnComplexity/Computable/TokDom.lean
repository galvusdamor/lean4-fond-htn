import HtnComplexity.Computable.RegStrips
import HtnComplexity.Computable.Rooted
import HtnComplexity.Regular.RegularWeakNormalForm
/-!
# The token gadget: the compiled description

The cell (`HTN-REG`, `TO-HTN-REG`) of the compilability table asks for a compilation of a
*regular* domain — whose methods may order their primitive subtasks arbitrarily — into a
**totally ordered** regular one.  The obstacle is that a regular method

    c ↦ {o₁ … oₙ} c'      (the `oⱼ` partially ordered, `c'` after all of them)

offers *every linearization* of its primitive part, and there may be exponentially many of
them, so they cannot be enumerated.

**The construction** replaces the block by a totally ordered chain of `n` fresh compound tasks
`Q(i,0) … Q(i,n)`, each of which may pick *any* of the `n` subtasks, and uses bookkeeping facts
to force the picks to be a linearization:

* `tok(i,x)` — the subtask `x` of the method `i` has not been executed yet.  It is produced by
  `strt i` and consumed by the action `doA(i,x)`, so no subtask can be picked twice;
* `don(i,x)` — the subtask `x` has been executed.  `doA(i,x)` requires `don(i,y)` for every `y`
  ordered before `x`, so the picks respect the ordering, and `fin i` requires — and deletes —
  all of them, so exactly `n` distinct subtasks have been picked and the bookkeeping is clean
  again.

This file defines the compiled description and proves that it belongs to the target class; the
correctness proof is in `HtnComplexity/Computable/TokCorrect.lean`.
-/

namespace HTN

namespace Syn

/-! ### The encodings

Facts, compound task names and action names of the compiled description are numbers; the
following injections keep the three kinds of fact, the two kinds of compound task and the three
kinds of action apart. -/

/-- The compiled fact of a fact of the source problem. -/
def stateF (v : ℕ) : ℕ := 3 * v

/-- The token of the subtask `x` of the method number `i`. -/
def tokF (i x : ℕ) : ℕ := 3 * Nat.pair i x + 1

/-- The fact recording that the subtask `x` of the method number `i` has been executed. -/
def donF (i x : ℕ) : ℕ := 3 * Nat.pair i x + 2

/-- The compiled compound task \"the source compound task `c` is still to be decomposed\". -/
def ctName (c : ℕ) : ℕ := 2 * c

/-- The compiled compound task \"`k` subtasks of the method number `i` have been executed\". -/
def qName (i k : ℕ) : ℕ := 2 * Nat.pair i k + 1

/-- The compiled action starting the block of the method number `i`. -/
def strtA (i : ℕ) : ℕ := 3 * i

/-- The compiled action executing the subtask `x` of the method number `i`. -/
def doA (i x : ℕ) : ℕ := 3 * Nat.pair i x + 1

/-- The compiled action closing the block of the method number `i`. -/
def finA (i : ℕ) : ℕ := 3 * i + 2

@[simp] theorem stateF_inj {v w : ℕ} : stateF v = stateF w ↔ v = w := by
  simp [stateF]

@[simp] theorem tokF_inj {i x j y : ℕ} : tokF i x = tokF j y ↔ i = j ∧ x = y := by
  simp only [tokF, add_left_inj, Nat.mul_left_cancel_iff (by norm_num : 0 < 3)]
  exact ⟨fun h => Nat.pair_eq_pair.1 h, fun h => by rw [h.1, h.2]⟩

@[simp] theorem donF_inj {i x j y : ℕ} : donF i x = donF j y ↔ i = j ∧ x = y := by
  simp only [donF, add_left_inj, Nat.mul_left_cancel_iff (by norm_num : 0 < 3)]
  exact ⟨fun h => Nat.pair_eq_pair.1 h, fun h => by rw [h.1, h.2]⟩

@[simp] theorem stateF_ne_tokF {v i x : ℕ} : stateF v ≠ tokF i x := by
  simp only [stateF, tokF]; omega

@[simp] theorem stateF_ne_donF {v i x : ℕ} : stateF v ≠ donF i x := by
  simp only [stateF, donF]; omega

@[simp] theorem tokF_ne_donF {i x j y : ℕ} : tokF i x ≠ donF j y := by
  simp only [tokF, donF]; omega

@[simp] theorem tokF_ne_stateF {v i x : ℕ} : tokF i x ≠ stateF v :=
  fun h => stateF_ne_tokF h.symm

@[simp] theorem donF_ne_stateF {v i x : ℕ} : donF i x ≠ stateF v :=
  fun h => stateF_ne_donF h.symm

@[simp] theorem donF_ne_tokF {i x j y : ℕ} : donF i x ≠ tokF j y :=
  fun h => tokF_ne_donF h.symm

/-- Every number is a state fact, a token or a done-mark. -/
theorem fact_cases (f : ℕ) :
    (∃ v, f = stateF v) ∨ (∃ j x, f = tokF j x) ∨ (∃ j x, f = donF j x) := by
  rcases hm : f % 3 with _ | _ | _ | m
  · exact Or.inl ⟨f / 3, by simp only [stateF]; omega⟩
  · refine Or.inr (Or.inl ⟨(f / 3).unpair.1, (f / 3).unpair.2, ?_⟩)
    simp only [tokF, Nat.pair_unpair]
    omega
  · refine Or.inr (Or.inr ⟨(f / 3).unpair.1, (f / 3).unpair.2, ?_⟩)
    simp only [donF, Nat.pair_unpair]
    omega
  · omega

@[simp] theorem ctName_inj {c c' : ℕ} : ctName c = ctName c' ↔ c = c' := by simp [ctName]

@[simp] theorem qName_inj {i k j l : ℕ} : qName i k = qName j l ↔ i = j ∧ k = l := by
  simp only [qName, add_left_inj, Nat.mul_left_cancel_iff (by norm_num : 0 < 2)]
  exact ⟨fun h => Nat.pair_eq_pair.1 h, fun h => by rw [h.1, h.2]⟩

@[simp] theorem ctName_ne_qName {c i k : ℕ} : ctName c ≠ qName i k := by
  simp only [ctName, qName]; omega

@[simp] theorem strtA_inj {i j : ℕ} : strtA i = strtA j ↔ i = j := by simp [strtA]

@[simp] theorem finA_inj {i j : ℕ} : finA i = finA j ↔ i = j := by simp [finA]

@[simp] theorem doA_inj {i x j y : ℕ} : doA i x = doA j y ↔ i = j ∧ x = y := by
  simp only [doA, add_left_inj, Nat.mul_left_cancel_iff (by norm_num : 0 < 3)]
  exact ⟨fun h => Nat.pair_eq_pair.1 h, fun h => by rw [h.1, h.2]⟩

@[simp] theorem strtA_ne_doA {i j x : ℕ} : strtA i ≠ doA j x := by
  simp only [strtA, doA]; omega

@[simp] theorem strtA_ne_finA {i j : ℕ} : strtA i ≠ finA j := by
  simp only [strtA, finA]; omega

@[simp] theorem doA_ne_finA {i x j : ℕ} : doA i x ≠ finA j := by
  simp only [doA, finA]; omega

/-! ### Reading a described task network -/

namespace TnDesc

/-- The primitive identifiers of a described task network, without repetitions. -/
def primIds (t : TnDesc) : List ℕ := t.ids.dedup.filter (fun x => !labelIsCompound t x)

/-- Does the described network contain a compound task? -/
def hasNextB (t : TnDesc) : Bool := !t.compoundNames.isEmpty

/-- The compound task name of the described network, if any. -/
def nextName (t : TnDesc) : ℕ := t.compoundNames.headI

/-- The compound task the described network leaves open, as an `Option`. -/
def tailName (t : TnDesc) : Option ℕ := if hasNextB t then some (nextName t) else none

/-- The primitive identifiers ordered before `x`. -/
def predsOf (t : TnDesc) (x : ℕ) : List ℕ := (primIds t).filter (fun y => ordB t y x)

theorem mem_primIds {t : TnDesc} {x : ℕ} :
    x ∈ primIds t ↔ x ∈ t.ids ∧ ∃ a, t.label x = Sum.inl a := by
  rw [primIds, List.mem_filter, List.mem_dedup]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, ?_⟩
    rcases hcase : t.label x with a | c
    · exact ⟨a, rfl⟩
    · exact absurd (labelIsCompound_iff.2 ⟨c, hcase⟩) (by simpa using hc)
  · rintro ⟨hx, a, ha⟩
    refine ⟨hx, ?_⟩
    have : labelIsCompound t x ≠ true := by
      intro hcon
      obtain ⟨c, hc⟩ := labelIsCompound_iff.1 hcon
      rw [ha] at hc
      exact absurd hc (by simp)
    simpa using this

theorem primIds_nodup (t : TnDesc) : (primIds t).Nodup :=
  (t.ids.nodup_dedup).filter _

theorem label_actOf {t : TnDesc} {x : ℕ} (h : x ∈ primIds t) :
    t.label x = Sum.inl (actOf t x) := by
  obtain ⟨-, a, ha⟩ := mem_primIds.1 h
  rw [ha, actOf_eq ha]

theorem mem_predsOf {t : TnDesc} {x y : ℕ} :
    y ∈ predsOf t x ↔ y ∈ primIds t ∧ t.toTaskNetwork.ord y x := by
  rw [predsOf, List.mem_filter, ordB_iff]

theorem exists_compound {t : TnDesc} (h : hasNextB t = true) :
    ∃ x ∈ t.ids, t.label x = Sum.inr (nextName t) := by
  have hne : t.compoundNames ≠ [] := by
    simpa [hasNextB, List.isEmpty_iff] using h
  have hmem : nextName t ∈ t.compoundNames := by
    rcases hc : t.compoundNames with _ | ⟨a, l⟩
    · exact absurd hc hne
    · simp [nextName, hc]
  exact mem_compoundNames.1 hmem

theorem not_compound {t : TnDesc} (h : hasNextB t = false) {x : ℕ} (hx : x ∈ t.ids) {c : ℕ} :
    t.label x ≠ Sum.inr c := by
  intro hcon
  have hne : t.compoundNames = [] := by
    simpa [hasNextB, List.isEmpty_iff] using h
  have : c ∈ t.compoundNames := mem_compoundNames.2 ⟨x, hx, hcon⟩
  rw [hne] at this
  simp at this

end TnDesc

/-! ### The compiled task networks

Every method of the compiled description has one or two subtasks, in a chain. -/

/-- The described task network `a ≺ c` — an action followed by a compound task. -/
def body2 (a c : ℕ) : TnDesc := ([0, 1], [(0, 1)], [(0, false, a), (1, true, c)])

/-- The described task network consisting of the single action `a`. -/
def body1 (a : ℕ) : TnDesc := ([0], [], [(0, false, a)])

theorem transGen_single {p : ℕ × ℕ} {a b : ℕ}
    (h : Relation.TransGen (fun x y => (x, y) ∈ [p]) a b) : a = p.1 ∧ b = p.2 := by
  induction h with
  | @single b hab =>
      have hc : (a, b) = p := by simpa using hab
      exact ⟨congrArg Prod.fst hc, congrArg Prod.snd hc⟩
  | @tail b c _ hbc ih =>
      have hc : (b, c) = p := by simpa using hbc
      exact ⟨ih.1, congrArg Prod.snd hc⟩

@[simp] theorem body2_T (a c : ℕ) : (body2 a c).toTaskNetwork.T = {0, 1} := by
  simp [body2, TnDesc.toTaskNetwork, TnDesc.ids]

@[simp] theorem body2_label0 (a c : ℕ) : (body2 a c).toTaskNetwork.α 0 = Sum.inl a := rfl

@[simp] theorem body2_label1 (a c : ℕ) : (body2 a c).toTaskNetwork.α 1 = Sum.inr c := rfl

theorem body2_ord (a c : ℕ) (x y : ℕ) :
    (body2 a c).toTaskNetwork.ord x y ↔ (x = 0 ∧ y = 1) := by
  constructor
  · rintro ⟨-, -, hxy, -⟩
    have := transGen_single (p := (0, 1)) (a := x) (b := y) hxy
    exact ⟨this.1, this.2⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨by simp [body2, TnDesc.ids], by simp [body2, TnDesc.ids], ?_, ?_⟩
    · exact Relation.TransGen.single (by simp [body2, TnDesc.ordList, TnDesc.listRel])
    · intro hcon
      have := transGen_single (p := (0, 1)) hcon
      simp at this

@[simp] theorem body1_T (a : ℕ) : (body1 a).toTaskNetwork.T = {0} := by
  simp [body1, TnDesc.toTaskNetwork, TnDesc.ids]

@[simp] theorem body1_label0 (a : ℕ) : (body1 a).toTaskNetwork.α 0 = Sum.inl a := rfl

theorem body1_ord (a : ℕ) (x y : ℕ) : ¬ (body1 a).toTaskNetwork.ord x y := by
  rintro ⟨-, -, hxy, -⟩
  have : ∀ u v : ℕ, ¬ Relation.TransGen (TnDesc.listRel (body1 a)) u v := by
    intro u v hcon
    induction hcon with
    | single h => simp [TnDesc.listRel, body1, TnDesc.ordList] at h
    | tail _ h _ => simp [TnDesc.listRel, body1, TnDesc.ordList] at h
  exact this _ _ hxy

theorem body2_isTotallyOrdered (a c : ℕ) : (body2 a c).toTaskNetwork.IsTotallyOrdered := by
  intro x hx y hy hxy
  rw [body2_T] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact Or.inl ((body2_ord _ _ _ _).2 ⟨rfl, rfl⟩)
  · exact Or.inr ((body2_ord _ _ _ _).2 ⟨rfl, rfl⟩)
  · exact absurd rfl hxy

theorem body2_isRegular (a c : ℕ) : (body2 a c).toTaskNetwork.IsRegular := by
  constructor
  · intro x hx y hy hax hay
    rw [body2_T] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have h0 : ¬ (body2 a c).toTaskNetwork.IsAbstractId 0 := by
      rintro ⟨c', hc'⟩
      rw [body2_label0] at hc'
      exact absurd hc' (by simp)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd hax h0
    · exact absurd hay h0
    · rfl
  · intro x hx hax y hy hyx
    rw [body2_T] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    have h0 : ¬ (body2 a c).toTaskNetwork.IsAbstractId 0 := by
      rintro ⟨c', hc'⟩
      rw [body2_label0] at hc'
      exact absurd hc' (by simp)
    rcases hx with rfl | rfl
    · exact absurd hax h0
    · rcases hy with rfl | rfl
      · exact (body2_ord _ _ _ _).2 ⟨rfl, rfl⟩
      · exact absurd rfl hyx

theorem body1_isTotallyOrdered (a : ℕ) : (body1 a).toTaskNetwork.IsTotallyOrdered := by
  intro x hx y hy hxy
  rw [body1_T] at hx hy
  simp only [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

theorem body1_isRegular (a : ℕ) : (body1 a).toTaskNetwork.IsRegular := by
  have h0 : ¬ (body1 a).toTaskNetwork.IsAbstractId 0 := by
    rintro ⟨c', hc'⟩
    rw [body1_label0] at hc'
    exact absurd hc' (by simp)
  constructor
  · intro x hx y hy hax _
    rw [body1_T] at hx hy
    simp only [Finset.mem_singleton] at hx hy
    subst hx
    exact absurd hax h0
  · intro x hx hax y _ _
    rw [body1_T] at hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    exact absurd hax h0

/-! ### The compiled description -/


/-- The compound task name decomposed by the method number `i` of the source description. -/
def cOf (d : DomDesc) (i : ℕ) : ℕ := (d.methods.getI i).1

/-- The subtask network of the method number `i` of the source description. -/
def tOf (d : DomDesc) (i : ℕ) : TnDesc := (d.methods.getI i).2

/-- The primitive subtask identifiers of the method number `i` of the source description. -/
def pOf (d : DomDesc) (i : ℕ) : List ℕ := TnDesc.primIds (tOf d i)

/-- The subtask network of the compiled method closing the block of the method number `i`. -/
def finBody (d : DomDesc) (i : ℕ) : TnDesc :=
  if TnDesc.hasNextB (tOf d i) then body2 (finA i) (ctName (TnDesc.nextName (tOf d i)))
    else body1 (finA i)

/-- The precondition of the compiled action executing the subtask `x` of the method `i`: its
token, the done-marks of the subtasks ordered before it, and the precondition of the source
action. -/
def doPre (d : DomDesc) (i x : ℕ) : List ℕ :=
  ((TnDesc.predsOf (tOf d i) x).map (donF i)) ++
    tokF i x :: (d.precList (TnDesc.actOf (tOf d i) x)).map stateF

/-- The add list of the compiled action executing the subtask `x` of the method `i`. -/
def doAdd (d : DomDesc) (i x : ℕ) : List ℕ :=
  donF i x :: (d.addList (TnDesc.actOf (tOf d i) x)).map stateF

/-- The delete list of the compiled action executing the subtask `x` of the method `i`. -/
def doDel (d : DomDesc) (i x : ℕ) : List ℕ :=
  tokF i x :: (d.delList (TnDesc.actOf (tOf d i) x)).map stateF

/-- The compiled actions belonging to the method number `i`: `strt i`, one `doA (i,x)` per
primitive subtask `x`, and `fin i`. -/
def tokActionsOf (d : DomDesc) (i : ℕ) : List ActionDesc :=
  (strtA i, [], (pOf d i).map (tokF i), []) ::
    ((pOf d i).map fun x => (doA i x, doPre d i x, doAdd d i x, doDel d i x)) ++
    [(finA i, (pOf d i).map (donF i), [], (pOf d i).map (donF i))]

/-- The compiled methods belonging to the method number `i`: the entry method, one step method
per position and per primitive subtask, and the closing method. -/
def tokMethodsOf (d : DomDesc) (i : ℕ) : List MethodDesc :=
  (ctName (cOf d i), body2 (strtA i) (qName i 0)) ::
    ((List.range (pOf d i).length).flatMap fun k =>
      (pOf d i).map fun x => (qName i k, body2 (doA i x) (qName i (k + 1)))) ++
    [(qName i (pOf d i).length, finBody d i)]

/-- **The compiled domain description.** -/
def tokDom (d : DomDesc) : DomDesc :=
  ((List.range d.methods.length).flatMap (tokActionsOf d),
    (List.range d.methods.length).flatMap (tokMethodsOf d))

/-- **The compiled instance description**: the state facts of the source instance, and the
single compound task `ctName c₀`. -/
def tokInst (q : InstDesc) : InstDesc :=
  (q.initList.map stateF, q.goalList.map stateF,
    ([0], [], [(0, true, ctName (rootName q))]))

/-! ### The compiled description belongs to the target class -/

theorem mem_tokMethods_iff {d : DomDesc} {e : MethodDesc} :
    e ∈ (tokDom d).methods ↔ ∃ i < d.methods.length, e ∈ tokMethodsOf d i := by
  simp only [tokDom, DomDesc.methods, List.mem_flatMap, List.mem_range]

theorem tokMethodsOf_shape {d : DomDesc} {i : ℕ} {e : MethodDesc} (he : e ∈ tokMethodsOf d i) :
    (∃ a c, e.2 = body2 a c) ∨ (∃ a, e.2 = body1 a) := by
  simp only [tokMethodsOf, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_range] at he
  rcases he with (rfl | ⟨k, -, x, -, rfl⟩) | (rfl | he)
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · by_cases h : TnDesc.hasNextB (tOf d i)
    · exact Or.inl ⟨finA i, ctName (TnDesc.nextName (tOf d i)), by simp [finBody, h]⟩
    · exact Or.inr ⟨finA i, by simp [finBody, h]⟩
  · simp at he

theorem tokDom_methodsTO (d : DomDesc) : (tokDom d).MethodsTO := by
  intro e he
  obtain ⟨i, -, hi⟩ := mem_tokMethods_iff.1 he
  rcases tokMethodsOf_shape hi with ⟨a, c, hb⟩ | ⟨a, hb⟩
  · rw [hb]; exact body2_isTotallyOrdered a c
  · rw [hb]; exact body1_isTotallyOrdered a

theorem tokDom_methodsReg (d : DomDesc) : (tokDom d).MethodsReg := by
  intro e he
  obtain ⟨i, -, hi⟩ := mem_tokMethods_iff.1 he
  rcases tokMethodsOf_shape hi with ⟨a, c, hb⟩ | ⟨a, hb⟩
  · rw [hb]; exact body2_isRegular a c
  · rw [hb]; exact body1_isRegular a

theorem tokInst_tnI_T (q : InstDesc) : (tokInst q).tnI.toTaskNetwork.T = {0} := by
  simp [tokInst, InstDesc.tnI, TnDesc.toTaskNetwork, TnDesc.ids]

theorem tokInst_tnI_α (q : InstDesc) :
    (tokInst q).tnI.toTaskNetwork.α 0 = Sum.inr (ctName (rootName q)) := rfl

theorem tokInst_isRooted (q : InstDesc) : (tokInst q).IsRooted :=
  ⟨0, ctName (rootName q), tokInst_tnI_T q, tokInst_tnI_α q⟩

end Syn

end HTN
