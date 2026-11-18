import HtnPlanning.Core.Productive
import HtnComplexity.Computable.StripsTarget
import HtnComplexity.Complexity.Serial
/-!
# The marking domain of a described hierarchy

Solvability of a **no-op** problem is the existence of a refinement of its initial task network
into a primitive one (plus `g ⊆ s₀`), and by `HTN.exists_primitive_iff_productive` that is the
productivity of every compound task the initial network mentions.  Productivity is the
least-fixed-point computation that the emptiness test for a context-free grammar performs — and
a least fixed point of monotone rules is exactly what a **delete-free STRIPS problem** computes.

This file builds that STRIPS problem out of a domain description:

* `HTN.Syn.mark c = 2 * c + 1` — the fact "the compound name `c` is productive"; the even facts
  `HTN.Syn.orig f = 2 * f` are left for the facts of the source problem, and no action of the
  marking domain touches them (`HTN.Syn.orig_mem_transitionSeq_iff`);
* `HTN.Syn.markAction e` — the action `⋀_{c ∈ body} mark c ⟶ mark (abstract task)` of the
  method description `e`;
* `HTN.Syn.noopStripsDom d` — the canonical STRIPS domain description
  (`HtnComplexity/Computable/StripsTarget.lean`) over these actions;
* `HTN.Syn.productive_iff_reachable_mark` — **a compound name is productive for `d` exactly
  when its mark can be reached in the marking domain**, which is the correctness of the
  construction.

`HtnCompilability/Computable/NoopStrips.lean` assembles this into the cell
(`HTN-NOOP`, `STRIPS`) of the computable table.

The compound names of a described task network are computed by `HTN.Syn.labelList`, a `foldr`
over the label list; that shape is what makes them primitive recursive
(`HTN.Syn.primrec_compoundNames`), which the compilation needs.
-/

namespace HTN

namespace Syn

/-! ### The two families of facts -/

/-- The fact "the compound name `c` is productive". -/
def mark (c : ℕ) : ℕ := 2 * c + 1

/-- The fact of the marking domain standing for the fact `f` of the source problem.  No action
of the marking domain adds or deletes it. -/
def orig (f : ℕ) : ℕ := 2 * f

theorem mark_injective : Function.Injective mark := fun _ _ h => by
  simp only [mark] at h; omega

theorem orig_injective : Function.Injective orig := fun _ _ h => by
  simp only [orig] at h; omega

theorem mark_ne_orig (c f : ℕ) : mark c ≠ orig f := by
  simp only [mark, orig]; omega

/-- The same, in terms of the described task network. -/
theorem TnDesc.mem_compoundNames_iff_mem_T {t : TnDesc} {c : ℕ} :
    c ∈ t.compoundNames ↔ ∃ i ∈ t.toTaskNetwork.T, t.toTaskNetwork.α i = Sum.inr c := by
  rw [TnDesc.mem_compoundNames]
  simp

/-! ### The marking domain -/

open PTime in
/-- A binary numeral ending in `1` is read back unchanged. -/
theorem bitsOfNat_natOfBits_append_true : ∀ w : List Bool,
    bitsOfNat (natOfBits (w ++ [true])) = w ++ [true]
  | [] => by simp [natOfBits_cons, bitsOfNat_succ]
  | b :: w => by
    have ih := bitsOfNat_natOfBits_append_true w
    have hpos : 0 < natOfBits (w ++ [true]) := by
      rcases h : natOfBits (w ++ [true]) with _ | n
      · rw [h] at ih; simp at ih
      · omega
    obtain ⟨n, hn⟩ : ∃ n, (if b then 1 else 0) + 2 * natOfBits (w ++ [true]) = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [List.cons_append, natOfBits_cons, hn, bitsOfNat_succ, ← hn]
    cases b <;> simp [ih, Nat.add_mul_div_left]

open PTime in
/-- The name of the marking action of a method description: the number whose binary digits are
the serialisation of the method followed by a `1`.  Its binary length is linear in the size of
the method (unlike its Gödel number), and different methods get different names. -/
def markName (e : MethodDesc) : ℕ := natOfBits (serNat e.1 ++ tnSer e.2 ++ [true])

open PTime in
theorem markName_injective : Function.Injective markName := by
  rintro ⟨n, t⟩ ⟨n', t'⟩ h
  have h' := congrArg bitsOfNat h
  simp only [markName] at h'
  rw [bitsOfNat_natOfBits_append_true, bitsOfNat_natOfBits_append_true] at h'
  simp only [List.append_assoc] at h'
  obtain ⟨h1, h⟩ := serNat_parse h'
  obtain ⟨h2, -⟩ := tnSer_parse h
  simp [h1, h2]

/-- The marking action of a method description: it marks the decomposed task once all compound
tasks of its body are marked.  The name of the action is `markName e`, so that different methods
get different actions. -/
def markAction (e : MethodDesc) : ActionDesc :=
  (markName e, e.2.compoundNames.map mark, [mark e.1], [])

/-- The marking actions of a domain description. -/
def markActions (d : DomDesc) : List ActionDesc := d.methods.map markAction

/-- **The marking domain** of a domain description: the canonical STRIPS domain over its
marking actions. -/
def noopStripsDom (d : DomDesc) : DomDesc := stripsDom (markActions d)

@[simp] theorem noopStripsDom_actions (d : DomDesc) :
    (noopStripsDom d).actions = markActions d := rfl

/-- Looking up a marking action yields a marking action. -/
theorem lookup_markActions {d : DomDesc} {a : ℕ} {x : List ℕ × List ℕ × List ℕ}
    (h : (markActions d).lookup a = some x) : ∃ e ∈ d.methods, markAction e = (a, x) := by
  have hmem : (a, x) ∈ markActions d := mem_of_lookup_eq_some h
  obtain ⟨e, he, hex⟩ := List.mem_map.1 hmem
  exact ⟨e, he, hex⟩

/-- The marking action of a listed method is found by its name. -/
theorem lookup_markAction_list {l : List MethodDesc} {e : MethodDesc} (he : e ∈ l) :
    (l.map markAction).lookup (markName e) = some (markAction e).2 := by
  induction l with
  | nil => exact absurd he (by simp)
  | cons f fs ih =>
    rw [List.map_cons, show markAction f = ((markAction f).1, (markAction f).2) from rfl,
      List.lookup_cons]
    by_cases hfe : markName f = markName e
    · have hf : f = e := markName_injective hfe
      subst hf
      simp [markAction]
    · have hne : (markName e == (markAction f).1) = false := by
        simp only [markAction, beq_eq_false_iff_ne, ne_eq]
        exact fun h => hfe h.symm
      rw [hne]
      refine ih ?_
      rcases List.mem_cons.1 he with rfl | he'
      · exact absurd rfl hfe
      · exact he'

theorem lookup_markAction {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    (markActions d).lookup (markName e) = some (markAction e).2 :=
  lookup_markAction_list he

section Domain

variable (d : DomDesc)

/-- The marking domain deletes nothing. -/
theorem noopStripsDom_del (a : ℕ) : (noopStripsDom d).del a = ∅ := by
  rcases h : (markActions d).lookup a with _ | x
  · simp [DomDesc.del, noopStripsDom, stripsDom, DomDesc.actions, h]
  · obtain ⟨e, -, hex⟩ := lookup_markActions h
    have : x.2.2 = [] := by
      have := congrArg Prod.snd hex
      simp only [markAction] at this
      rw [← this]
    simp [DomDesc.del, noopStripsDom, stripsDom, DomDesc.actions, h, this]

/-- Every fact a marking action adds is the mark of the task some listed method decomposes, and
the action's precondition then contains the marks of all compound tasks of that method's
body. -/
theorem noopStripsDom_add_prec {a f : ℕ} (hf : f ∈ (noopStripsDom d).add a) :
    ∃ e ∈ d.methods, f = mark e.1 ∧
      ∀ c ∈ e.2.compoundNames, mark c ∈ (noopStripsDom d).prec a := by
  rcases h : (markActions d).lookup a with _ | x
  · rw [show (noopStripsDom d).add a = {g | g ∈ ((markActions d).lookup a).elim [] fun y => y.2.1}
      from rfl, h] at hf
    exact absurd hf (by simp)
  · obtain ⟨e, he, hex⟩ := lookup_markActions h
    have hx : (markAction e).2 = x := congrArg Prod.snd hex
    rw [← hx] at h
    rw [show (noopStripsDom d).add a = {g | g ∈ ((markActions d).lookup a).elim [] fun y => y.2.1}
      from rfl, h] at hf
    simp only [markAction, Option.elim, Set.mem_setOf_eq, List.mem_singleton] at hf
    refine ⟨e, he, hf, fun c hc => ?_⟩
    rw [show (noopStripsDom d).prec a = {g | g ∈ ((markActions d).lookup a).elim [] fun y => y.1}
      from rfl, h]
    simp only [markAction, Option.elim, Set.mem_setOf_eq]
    exact List.mem_map_of_mem hc

/-- The precondition of the marking action of a listed method is the set of marks of the
compound tasks of its body. -/
theorem noopStripsDom_prec_markAction {e : MethodDesc} (he : e ∈ d.methods) :
    (noopStripsDom d).prec (markName e) =
      {f | ∃ c ∈ e.2.compoundNames, f = mark c} := by
  rw [show (noopStripsDom d).prec (markName e) =
    {g | g ∈ ((markActions d).lookup (markName e)).elim [] fun y => y.1} from rfl,
    lookup_markAction he]
  ext f
  simp [markAction, eq_comm]

/-- The marking action of a listed method adds the mark of the task it decomposes. -/
theorem noopStripsDom_add_markAction {e : MethodDesc} (he : e ∈ d.methods) :
    mark e.1 ∈ (noopStripsDom d).add (markName e) := by
  rw [show (noopStripsDom d).add (markName e) =
    {g | g ∈ ((markActions d).lookup (markName e)).elim [] fun y => y.2.1} from rfl,
    lookup_markAction he]
  simp [markAction]

end Domain

/-! ### Delete-free domains are monotone -/

section Monotone

variable {D : Domain ℕ ℕ ℕ ℕ} (hdel : ∀ a, D.del a = ∅)
include hdel

theorem transition_eq_union (a : ℕ) (s : Set ℕ) : D.transition a s = s ∪ D.add a := by
  simp [ActionModel.transition, hdel a]

theorem subset_transitionSeq (as : List ℕ) (s : Set ℕ) : s ⊆ D.transitionSeq as s := by
  induction as generalizing s with
  | nil => exact le_rfl
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons]
    refine subset_trans ?_ (ih (D.transition a s))
    rw [transition_eq_union hdel]
    exact Set.subset_union_left

theorem transitionSeq_mono {s s' : Set ℕ} (hs : s ⊆ s') (as : List ℕ) :
    D.transitionSeq as s ⊆ D.transitionSeq as s' := by
  induction as generalizing s s' with
  | nil => exact hs
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_cons]
    refine ih ?_
    rw [transition_eq_union hdel, transition_eq_union hdel]
    exact Set.union_subset_union_left _ hs

theorem seqApplicable_mono {s s' : Set ℕ} (hs : s ⊆ s') {as : List ℕ}
    (happ : D.SeqApplicable as s) : D.SeqApplicable as s' := by
  induction as generalizing s s' with
  | nil => trivial
  | cons a as ih =>
    obtain ⟨h₁, h₂⟩ := happ
    refine ⟨subset_trans h₁ hs, ih ?_ h₂⟩
    rw [transition_eq_union hdel, transition_eq_union hdel]
    exact Set.union_subset_union_left _ hs

end Monotone

/-! ### Marking is productivity -/

section Correct

variable {d : DomDesc}

/-- Every method of a described domain is described by a listed method description. -/
theorem exists_methodDesc {m : Method ℕ ℕ ℕ} (h : m ∈ d.toDomain.methods) :
    ∃ e ∈ d.methods, e.toMethod = m := h

/-- **Completeness of the marking**: the mark of a productive compound name is reachable. -/
theorem exists_plan_mark_of_productive {c : ℕ} (h : Productive d.toDomain.methods c) :
    ∃ as : List ℕ, (noopStripsDom d).toDomain.SeqApplicable as ∅ ∧
      mark c ∈ (noopStripsDom d).toDomain.transitionSeq as ∅ := by
  have hdel : ∀ a, (noopStripsDom d).toDomain.del a = ∅ := noopStripsDom_del d
  induction h with
  | intro m hm hbody ih =>
    obtain ⟨e, he, rfl⟩ := exists_methodDesc hm
    -- a plan marking all compound names of the body
    have hall : ∀ L : List ℕ, (∀ c ∈ L, c ∈ e.2.compoundNames) →
        ∃ as : List ℕ, (noopStripsDom d).toDomain.SeqApplicable as ∅ ∧
          ∀ c ∈ L, mark c ∈ (noopStripsDom d).toDomain.transitionSeq as ∅ := by
      intro L
      induction L with
      | nil => exact fun _ => ⟨[], trivial, by simp⟩
      | cons c L ihL =>
        intro hL
        obtain ⟨as, has, hasL⟩ := ihL fun x hx => hL x (by simp [hx])
        obtain ⟨i, hi, hlab⟩ := TnDesc.mem_compoundNames.1 (hL c (by simp))
        obtain ⟨bs, hbs, hbc⟩ := ih i (by simpa using hi) c (by simpa using hlab)
        refine ⟨as ++ bs, ?_, ?_⟩
        · rw [ActionModel.seqApplicable_append]
          exact ⟨has, seqApplicable_mono hdel (Set.empty_subset _) hbs⟩
        · intro x hx
          rw [ActionModel.transitionSeq_append]
          rcases List.mem_cons.1 hx with rfl | hx
          · exact transitionSeq_mono hdel (Set.empty_subset _) bs hbc
          · exact subset_transitionSeq hdel bs _ (hasL x hx)
    obtain ⟨as, has, hasL⟩ := hall e.2.compoundNames fun _ h => h
    refine ⟨as ++ [markName e], ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      refine ⟨has, ?_, trivial⟩
      have hsub : (noopStripsDom d).prec (markName e) ⊆
          (noopStripsDom d).toDomain.transitionSeq as ∅ := by
        rw [noopStripsDom_prec_markAction d he]
        rintro f ⟨c', hc', rfl⟩
        exact hasL c' hc'
      exact hsub
    · rw [ActionModel.transitionSeq_append, ActionModel.transitionSeq_cons,
        ActionModel.transitionSeq_nil, transition_eq_union hdel]
      exact Or.inr (noopStripsDom_add_markAction d he)

/-- **Completeness of the marking, for a list of names**: one plan marks all the productive
names of a list at once. -/
theorem exists_plan_marks (L : List ℕ) (h : ∀ c ∈ L, Productive d.toDomain.methods c) :
    ∃ as : List ℕ, (noopStripsDom d).toDomain.SeqApplicable as ∅ ∧
      ∀ c ∈ L, mark c ∈ (noopStripsDom d).toDomain.transitionSeq as ∅ := by
  have hdel : ∀ a, (noopStripsDom d).toDomain.del a = ∅ := noopStripsDom_del d
  induction L with
  | nil => exact ⟨[], trivial, by simp⟩
  | cons c L ih =>
    obtain ⟨as, has, hasL⟩ := ih fun x hx => h x (by simp [hx])
    obtain ⟨bs, hbs, hbc⟩ := exists_plan_mark_of_productive (h c (by simp))
    refine ⟨as ++ bs, ?_, ?_⟩
    · rw [ActionModel.seqApplicable_append]
      exact ⟨has, seqApplicable_mono hdel (Set.empty_subset _) hbs⟩
    · intro x hx
      rw [ActionModel.transitionSeq_append]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact transitionSeq_mono hdel (Set.empty_subset _) bs hbc
      · exact subset_transitionSeq hdel bs _ (hasL x hx)

/-- **Soundness of the marking**: only marks of productive compound names are reachable. -/
theorem productive_of_mem_transitionSeq {as : List ℕ} {s : Set ℕ}
    (hs : ∀ c, mark c ∈ s → Productive d.toDomain.methods c)
    (happ : (noopStripsDom d).toDomain.SeqApplicable as s) :
    ∀ c, mark c ∈ (noopStripsDom d).toDomain.transitionSeq as s →
      Productive d.toDomain.methods c := by
  have hdel : ∀ a, (noopStripsDom d).toDomain.del a = ∅ := noopStripsDom_del d
  induction as generalizing s with
  | nil => simpa using hs
  | cons a as ih =>
    obtain ⟨happ₁, happ₂⟩ := happ
    rw [ActionModel.transitionSeq_cons]
    refine ih ?_ happ₂
    intro c hc
    rw [transition_eq_union hdel] at hc
    rcases hc with hc | hc
    · exact hs c hc
    · obtain ⟨e, he, hce, hprec⟩ := noopStripsDom_add_prec d hc
      have hce' : c = e.1 := mark_injective hce
      subst hce'
      have hpre : ∀ c' ∈ e.2.compoundNames, Productive d.toDomain.methods c' :=
        fun c' hc' => hs c' (happ₁ (hprec c' hc'))
      have hmem : e.toMethod ∈ d.toDomain.methods := ⟨e, he, rfl⟩
      exact Productive.intro e.toMethod hmem fun t ht c' hct =>
        hpre c' (TnDesc.mem_compoundNames_iff_mem_T.2 ⟨t, ht, hct⟩)

/-- **The marking domain computes productivity.** -/
theorem productive_iff_reachable_mark {c : ℕ} :
    Productive d.toDomain.methods c ↔
      ∃ as : List ℕ, (noopStripsDom d).toDomain.SeqApplicable as ∅ ∧
        mark c ∈ (noopStripsDom d).toDomain.transitionSeq as ∅ := by
  refine ⟨exists_plan_mark_of_productive, ?_⟩
  rintro ⟨as, happ, hmem⟩
  exact productive_of_mem_transitionSeq (by simp) happ c hmem

/-- **The marking domain does not touch the even facts**: a fact `orig f` is reachable exactly
when it holds initially.  This is what lets the compiled instance carry the goal of the source
problem next to the marks. -/
theorem orig_mem_transitionSeq_iff {as : List ℕ} (s : Set ℕ) (f : ℕ) :
    orig f ∈ (noopStripsDom d).toDomain.transitionSeq as s ↔ orig f ∈ s := by
  have hdel : ∀ a, (noopStripsDom d).toDomain.del a = ∅ := noopStripsDom_del d
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [ActionModel.transitionSeq_cons]
    refine (ih ((noopStripsDom d).toDomain.transition a s)).trans ?_
    rw [transition_eq_union hdel]
    refine ⟨fun h => ?_, fun h => Or.inl h⟩
    rcases h with h | h
    · exact h
    · obtain ⟨e, -, hfe, -⟩ := noopStripsDom_add_prec d h
      exact absurd hfe.symm (mark_ne_orig e.1 f)

end Correct

/-! ### Computability of the marking domain -/

open Primrec

theorem primrec_mark : Primrec mark :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)

theorem primrec_orig : Primrec orig := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

open PTime in
theorem primrec_markName : Primrec markName :=
  primrec_natOfBits.comp (Primrec.list_append.comp
    (Primrec.list_append.comp (primrec_serNat.comp Primrec.fst) (primrec_tnSer.comp Primrec.snd))
    (Primrec.const _))

theorem primrec_markAction : Primrec markAction :=
  Primrec.pair primrec_markName
    (Primrec.pair (Primrec.list_map (primrec_compoundNames.comp Primrec.snd)
        (primrec_mark.comp Primrec.snd))
      (Primrec.pair
        (Primrec.list_cons.comp (primrec_mark.comp Primrec.fst) (Primrec.const []))
        (Primrec.const [])))

theorem primrec_markActions : Primrec markActions :=
  Primrec.list_map primrec_methods (primrec_markAction.comp Primrec.snd)

theorem primrec_noopStripsDom : Primrec noopStripsDom :=
  primrec_stripsDom.comp primrec_markActions

theorem computable_noopStripsDom : Computable noopStripsDom := primrec_noopStripsDom.to_comp

end Syn

end HTN
