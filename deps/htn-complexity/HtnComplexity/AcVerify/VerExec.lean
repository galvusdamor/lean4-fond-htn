import HtnComplexity.AcVerify.VerPair
/-!
# Semantics of the verifier, part 5: the execution test is `ExecOK`
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan PolyInst Compress Space Classical

variable {d : DomDesc} {q : InstDesc}

/-! ### Runs over entries -/

/-- The set of facts written in a list of strings. -/
def setOf (L : List (List Bool)) : Set ℕ := {f | bitsOfNat f ∈ L}

/-- **A run over the entries**: each entry carries its flag, its action and the state after it;
an empty leaf keeps the state, an action leaf applies its action; the last state is a goal
state. -/
def Run (d : DomDesc) (q : InstDesc) : Set ℕ → List (Bool × ℕ × Set ℕ) → Prop
  | s, [] => (problem d q).GoalState s
  | s, (f, a, T) :: r =>
    (if f then T = s else (problem d q).Applicable a s ∧ T = (problem d q).transition a s) ∧
      Run d q T r

/-- The actions of the action leaves of a run. -/
def runActs (L : List (Bool × ℕ × Set ℕ)) : List ℕ := (L.filter fun x => !x.1).map (·.2.1)

theorem exec_of_run : ∀ {s : Set ℕ} {L : List (Bool × ℕ × Set ℕ)}, Run d q s L →
    (problem d q).SeqApplicable (runActs L) s ∧
      (problem d q).GoalState ((problem d q).transitionSeq (runActs L) s)
  | s, [], h => ⟨trivial, h⟩
  | s, (f, a, T) :: r, ⟨h1, h2⟩ => by
    have ih := exec_of_run h2
    cases f
    · simp only [Bool.false_eq_true, if_false] at h1
      obtain ⟨ha, rfl⟩ := h1
      simp only [runActs, List.filter_cons, Bool.not_false, if_true, List.map_cons] at ih ⊢
      exact ⟨⟨ha, ih.1⟩, ih.2⟩
    · simp only [if_true] at h1
      subst h1
      simpa [runActs] using ih

/-- The states of the run of a list of flagged actions. -/
def runStates (d : DomDesc) (q : InstDesc) : Set ℕ → List (Bool × ℕ) → List (Bool × ℕ × Set ℕ)
  | _, [] => []
  | s, (f, a) :: r =>
    (f, a, if f then s else (problem d q).transition a s) ::
      runStates d q (if f then s else (problem d q).transition a s) r

/-- The actions of the action leaves of a list of flagged actions. -/
def flActs (L : List (Bool × ℕ)) : List ℕ := (L.filter fun x => !x.1).map (·.2)

theorem run_of_exec : ∀ {s : Set ℕ} {L : List (Bool × ℕ)},
    (problem d q).SeqApplicable (flActs L) s →
      (problem d q).GoalState ((problem d q).transitionSeq (flActs L) s) →
        Run d q s (runStates d q s L)
  | s, [], _, h => h
  | s, (f, a) :: r, h1, h2 => by
    cases f
    · simp only [flActs, List.filter_cons, Bool.not_false, if_true, List.map_cons] at h1 h2
      exact ⟨⟨h1.1, rfl⟩, run_of_exec h1.2 h2⟩
    · simp only [flActs, List.filter_cons, Bool.not_true, Bool.false_eq_true, if_false] at h1 h2
      exact ⟨rfl, run_of_exec h1 h2⟩

theorem runActs_runStates : ∀ (s : Set ℕ) (L : List (Bool × ℕ)),
    runActs (runStates d q s L) = flActs L
  | _, [] => rfl
  | s, (f, a) :: r => by
    cases f <;> simp [runStates, runActs, flActs] <;>
      simpa [runActs, flActs] using runActs_runStates _ r

/-! ### Actions -/

theorem lookup_eq_none {l : List ActionDesc} {a : ℕ} (h : a ∉ l.map (·.1)) :
    l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [List.lookup, show (a == p.1) = false from by simpa using h.1, ih h.2]

theorem actSer_of_not_mem {a : ℕ} (h : a ∉ d.actions.map (·.1)) :
    actSer d a = [false, false, false] := by
  simp [actSer, actLists, lookup_eq_none h]

/-- **The action test**: the three lists are those of the action. -/
theorem actB_iff (a : ℕ) (P : List Bool) :
    actB (advOf d) (key a) P = true ↔ P = actSer d a := by
  unfold actB
  rw [tA_advOf]
  have hb : true :: (key a ++ (dbl P ++ [false])) = true :: bstr (serNat a ++ P) := by
    rw [bstr_serNat_append, bstr_eq_dbl]
  rw [hb, show blist (actT d) = blist (actT d) ++ [] by simp]
  have hany : entAny (blist (actT d) ++ []) (fun _ E _ => decide (kat 0 E = key a)) = true ↔
      a ∈ d.actions.map (·.1) := by
    rw [entAny_iff]
    constructor
    · rintro ⟨l₁, w, l₂, hl, hw⟩
      have hm : w ∈ actT d := by rw [hl]; simp
      unfold actT at hm
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hm
      rw [bstr_serNat_append] at hw
      simp only [kat_zero, decide_eq_true_eq] at hw
      rwa [key_injective hw] at ha'
    · intro ha
      have hm : serNat a ++ actSer d a ∈ actT d := mem_actT.2 ⟨ha, rfl⟩
      obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hm
      exact ⟨l₁, _, l₂, hl, by rw [bstr_serNat_append]; simp⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  rw [occB_iff, mem_actT, ← Bool.not_eq_true, hany]
  constructor
  · rintro (⟨-, h⟩ | ⟨h1, h2⟩)
    · exact h
    · rw [h2, actSer_of_not_mem h1]
  · intro h
    by_cases ha : a ∈ d.actions.map (·.1)
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr ⟨ha, by rw [h, actSer_of_not_mem ha]⟩

/-- The three lists of an action, as lists of strings. -/
def preS (d : DomDesc) (a : ℕ) : List (List Bool) := (actLists d a).1.map bitsOfNat
/-- The add list of an action, as strings. -/
def addS (d : DomDesc) (a : ℕ) : List (List Bool) := (actLists d a).2.1.map bitsOfNat
/-- The delete list of an action, as strings. -/
def delS (d : DomDesc) (a : ℕ) : List (List Bool) := (actLists d a).2.2.map bitsOfNat

/-- **The row of an entry**: empty lists for an empty leaf, the lists of the action `a` for an
action leaf. -/
def RowOK (d : DomDesc) (e : CE) (a : ℕ) : Prop :=
  if e.f then e.pr = [] ∧ e.ad = [] ∧ e.de = [] else
    e.pr = preS d a ∧ e.ad = addS d a ∧ e.de = delS d a

theorem p3Of_enc (e : CE) : p3Of e.enc = blist e.pr ++ blist e.ad ++ blist e.de :=
  p3Of_encEnt _ _ _ _ _ _

theorem blist3_iff {a b c a' b' c' : List (List Bool)} :
    blist a ++ blist b ++ blist c = blist a' ++ blist b' ++ blist c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨h1, h⟩ := blist_parse h
    obtain ⟨h2, h⟩ := blist_parse h
    exact ⟨h1, h2, (blist_parse (r := []) (s := []) (by simpa using h)).1⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- **The row test.** -/
theorem rowB_iff (e : CE) (p : List PStep) (x : PStep) (a : ℕ)
    (hp : e.recs = p.map (recOf d q)) (hx : p.getLast? = some x)
    (ha : e.f = false → stepLabel d q x = Sum.inl a) :
    rowB (advOf d) e.enc = true ↔ RowOK d e a := by
  unfold rowB RowOK
  rw [CE.flagOf_enc, p3Of_enc]
  cases hf : e.f
  · simp only [Bool.false_and, Bool.false_or, Bool.not_false, Bool.true_and, if_false,
      Bool.false_eq_true]
    rw [enc_eq_recs e, hp, entAll_iff, forall_split_map (recOf d q) p (fun l₁ w l₂ => _ = true)]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' ++ [x] := by
      obtain ⟨p', y, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left (by rintro rfl; simp at hx)
      simp at hx; subst hx; exact ⟨p', by simp⟩
    have hlab := ha hf
    constructor
    · intro h
      have := h p' x [] (by simp)
      simp only [List.map_nil, isLast_blist_map.2 rfl, Bool.not_true, Bool.false_or] at this
      rw [kat3_recOf, hlab] at this
      have h2 := (actB_iff a _).1 this
      rw [actSer] at h2
      exact blist3_iff.1 h2
    · rintro ⟨h1, h2, h3⟩ l₁ y l₂ hsplit
      rcases l₂ with _ | ⟨z, l₂'⟩
      · have := List.append_inj' hsplit rfl
        simp only [List.cons.injEq, and_true] at this
        obtain ⟨rfl, rfl⟩ := this
        simp only [List.map_nil, isLast_blist_map.2 rfl, Bool.not_true, Bool.false_or]
        rw [kat3_recOf, hlab, actB_iff, actSer, h1, h2, h3]; rfl
      · have : isLast (blist ((z :: l₂').map (recOf d q)) ++ stOf e.enc) = false := by
          simp [isLast, blist_cons]
        rw [this]; rfl
  · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false, if_true,
      decide_eq_true_eq]
    rw [show [false, false, false] = blist [] ++ blist [] ++ blist [] from rfl, blist3_iff]

/-! ### The transition test -/

theorem enc_eq_st (e : CE) : stOf e.enc = blist e.st ++ prOf e.enc := by
  simp [CE.enc, prOf_encEnt]

theorem prOf_enc (e : CE) : prOf e.enc = blist e.pr ++ adOf e.enc := by
  simp [CE.enc]

theorem adOf_enc (e : CE) : adOf e.enc = blist e.ad ++ deOf e.enc := by
  simp [CE.enc]

theorem deOf_enc (e : CE) : deOf e.enc = blist e.de ++ [e.f] := by
  simp [CE.enc]

/-- The list conditions of a transition from the state list `L` to the state of `e`. -/
def TransL (e : CE) (L : List (List Bool)) : Prop :=
  (∀ w ∈ e.pr, w ∈ L) ∧ (∀ w ∈ e.ad, w ∈ e.st) ∧ (∀ w ∈ L, w ∈ e.de ∨ w ∈ e.st) ∧
    (∀ w ∈ e.st, w ∈ e.ad ∨ (w ∈ L ∧ w ∉ e.de))

/-- **The transition test.** -/
theorem transB_iff (e : CE) (L : List (List Bool)) (z : List Bool) :
    transB (advOf d) (blist L ++ z) e.enc = true ↔ TransL e L ∧ rowB (advOf d) e.enc = true := by
  unfold transB TransL
  simp only [Bool.and_eq_true]
  rw [prOf_enc, enc_eq_st, adOf_enc, deOf_enc, subEntB_iff, subEntB_iff, keepB_iff, postB_iff]
  simp only [and_assoc]

theorem mem_preS {a f : ℕ} : bitsOfNat f ∈ preS d a ↔ f ∈ (problem d q).prec a := by
  rw [preS, mem_map_bitsOfNat_iff]
  simp only [problem, DomDesc.toDomain, Domain.mkProblem, DomDesc.prec, actLists]
  cases d.actions.lookup a <;> rfl

theorem mem_addS {a f : ℕ} : bitsOfNat f ∈ addS d a ↔ f ∈ (problem d q).add a := by
  rw [addS, mem_map_bitsOfNat_iff]
  simp only [problem, DomDesc.toDomain, Domain.mkProblem, DomDesc.add, actLists]
  cases d.actions.lookup a <;> rfl

theorem mem_delS {a f : ℕ} : bitsOfNat f ∈ delS d a ↔ f ∈ (problem d q).del a := by
  rw [delS, mem_map_bitsOfNat_iff]
  simp only [problem, DomDesc.toDomain, Domain.mkProblem, DomDesc.del, actLists]
  cases d.actions.lookup a <;> rfl

/-- **The semantics of an accepted transition.** -/
theorem trans_sem {e : CE} {L : List (List Bool)} {a : ℕ} (ht : TransL e L) (hr : RowOK d e a) :
    if e.f then setOf e.st = setOf L else
      (problem d q).Applicable a (setOf L) ∧
        setOf e.st = (problem d q).transition a (setOf L) := by
  obtain ⟨h1, h2, h3, h4⟩ := ht
  unfold RowOK at hr
  cases hf : e.f
  · rw [hf] at hr
    simp only [Bool.false_eq_true, if_false] at hr ⊢
    obtain ⟨hp, ha, hd⟩ := hr
    refine ⟨fun f hfp => h1 _ (hp ▸ (mem_preS (q := q)).2 hfp), ?_⟩
    ext f
    simp only [setOf, Set.mem_setOf_eq, ActionModel.transition, Set.mem_union, Set.mem_diff]
    constructor
    · intro hfs
      rcases h4 _ hfs with h | ⟨h, h'⟩
      · exact Or.inr ((mem_addS (q := q)).1 (ha ▸ h))
      · exact Or.inl ⟨h, fun hd' => h' (hd ▸ (mem_delS (q := q)).2 hd')⟩
    · rintro (⟨h, h'⟩ | h)
      · rcases h3 _ h with h'' | h''
        · exact absurd ((mem_delS (q := q)).1 (hd ▸ h'')) h'
        · exact h''
      · exact h2 _ (ha ▸ (mem_addS (q := q)).2 h)
  · rw [hf] at hr
    simp only [if_true] at hr ⊢
    obtain ⟨-, ha, hd⟩ := hr
    ext f
    simp only [setOf, Set.mem_setOf_eq]
    constructor
    · intro hfs
      rcases h4 _ hfs with h | ⟨h, -⟩
      · rw [ha] at h; simp at h
      · exact h
    · intro h
      rcases h3 _ h with h' | h'
      · rw [hd] at h'; simp at h'
      · exact h'

end AcVer

end Syn

end HTN
