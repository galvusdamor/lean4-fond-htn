import HtnComplexity.Computable.ChainNet
import HtnComplexity.Computable.AcFreeMid
/-!
# Extending a described domain, and the frame property of a network

Three generic tools for the compilation of `(TO-HTN, HTN-AC)` with an unrestricted initial task
network:

* `HTN.Syn.Chain.extDom` — a domain description extended by further actions and methods, and
  **conservativity** (`HTN.Syn.Chain.netReach_ext_iff`): on a network whose labels satisfy a
  predicate `P` closed under the old methods and false on the new names, the extension has the
  same state transformer as the original description;
* `HTN.Syn.Chain.netReach_frame` — **the frame property** of a network: a domain mentioning only
  the facts of `R` acts on two states agreeing on `R` in the same way, and leaves the facts
  outside `R` alone;
* `HTN.Syn.Chain.netReach_single_prim`, `HTN.Syn.Chain.netReach_single_comp` — the state
  transformers of one-task networks.
-/

namespace HTN

namespace Syn

namespace Chain

open AcFree TaskNetwork

/-! ### Extensions -/

/-- **The description `d₀` extended by the actions `xa` and the methods `xm`.** -/
def extDom (d₀ : DomDesc) (xa : List ActionDesc) (xm : List MethodDesc) : DomDesc :=
  (d₀.actions ++ xa, d₀.methods ++ xm)

@[simp] lemma extDom_actions (d₀ : DomDesc) (xa : List ActionDesc) (xm : List MethodDesc) :
    (extDom d₀ xa xm).actions = d₀.actions ++ xa := rfl

@[simp] lemma extDom_methods (d₀ : DomDesc) (xa : List ActionDesc) (xm : List MethodDesc) :
    (extDom d₀ xa xm).methods = d₀.methods ++ xm := rfl

/-- **An extension is conservative on the labels satisfying `P`**: the new methods and actions
have names outside `P`, and the bodies of the old methods with a head in `P` have labels in
`P`. -/
structure ExtOk (P : ℕ ⊕ ℕ → Prop) (d₀ : DomDesc) (xa : List ActionDesc)
    (xm : List MethodDesc) : Prop where
  /-- The heads of the new methods are outside `P`. -/
  heads : ∀ e ∈ xm, ¬ P (Sum.inr e.1)
  /-- The old methods with a head in `P` have bodies labelled in `P`. -/
  bodies : ∀ e ∈ d₀.methods, P (Sum.inr e.1) → ∀ t ∈ e.2.ids, P (e.2.label t)
  /-- The new actions are outside `P`. -/
  acts : ∀ e ∈ xa, ¬ P (Sum.inl e.1)

variable {P : ℕ ⊕ ℕ → Prop} {d₀ : DomDesc} {xa : List ActionDesc} {xm : List MethodDesc}

/-- **Conservativity of an extension** at the level of decompositions. -/
theorem decomposesTo_ext (hok : ExtOk P d₀ xa xm) {tn tn' : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, P (tn.α t))
    (h : DecomposesTo (extDom d₀ xa xm).toDomain.methods tn tn') :
    DecomposesTo d₀.toDomain.methods tn tn' ∧ ∀ t ∈ tn'.T, P (tn'.α t) := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, h₀⟩
  | @tail u w _ hstep ih =>
      obtain ⟨hdec, hlab⟩ := ih
      obtain ⟨t, m, hm, htT, hαt, v, hvwf, ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩ := hstep
      obtain ⟨e, he, rfl⟩ := hm
      have hgood : P (Sum.inr e.1) := by
        have := hlab t htT
        rw [hαt] at this
        exact this
      have hebase : e ∈ d₀.methods := by
        rcases List.mem_append.1 (by simpa using he) with h' | h'
        · exact h'
        · exact absurd hgood (hok.heads e h')
      have hmbase : e.toMethod ∈ d₀.toDomain.methods := ⟨e, hebase, rfl⟩
      refine ⟨Relation.ReflTransGen.tail hdec
        ⟨t, e.toMethod, hmbase, htT, hαt, v, hvwf, ⟨σ, hbij, hord, hα⟩, hdisj, rfl⟩, ?_⟩
      intro x hx
      rw [decomposeWith_α]
      by_cases hxv : x ∈ v.T
      · simp only [hxv, if_true]
        rw [hα x hxv]
        have hσ : σ x ∈ e.toMethod.subtasks.T := by
          simpa using hbij.mapsTo (by simpa using hxv)
        exact hok.bodies e hebase hgood _ (by simpa using hσ)
      · simp only [hxv, if_false]
        rcases mem_decomposeWith_T.1 hx with ⟨hxT, -⟩ | hxv'
        · exact hlab x hxT
        · exact absurd hxv' hxv

/-- **The extension refines a network labelled in `P` exactly as the original description.** -/
theorem netYield_ext_iff (hok : ExtOk P d₀ xa xm) {tn : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, P (tn.α t)) {bs : List ℕ} :
    (extDom d₀ xa xm).toDomain.NetYield tn bs ↔ d₀.toDomain.NetYield tn bs := by
  have hsub : d₀.toDomain.methods ⊆ (extDom d₀ xa xm).toDomain.methods := by
    rintro m ⟨e, he, rfl⟩
    exact ⟨e, by simp [he], rfl⟩
  rw [Domain.netYield_iff, Domain.netYield_iff]
  constructor
  · rintro ⟨tn', hd, hprim, l, hlin, has⟩
    exact ⟨tn', (decomposesTo_ext hok h₀ hd).1, hprim, l, hlin, has⟩
  · rintro ⟨tn', hd, hprim, l, hlin, has⟩
    exact ⟨tn', Problem.decomposesTo_mono hsub hd, hprim, l, hlin, has⟩

/-- **The actions of a refinement of a network labelled in `P` are in `P`.** -/
theorem acts_of_netYield_ext (hok : ExtOk P d₀ xa xm) {tn : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, P (tn.α t)) {bs : List ℕ}
    (h : (extDom d₀ xa xm).toDomain.NetYield tn bs) : ∀ a ∈ bs, P (Sum.inl a) := by
  obtain ⟨tn', hd, -, l, hlin, has⟩ := Domain.netYield_iff.1 h
  have hlab := (decomposesTo_ext hok h₀ hd).2
  intro a ha
  have hmem : (Sum.inl a : ℕ ⊕ ℕ) ∈ l.map tn'.α := by
    rw [has]
    exact List.mem_map_of_mem ha
  obtain ⟨t, htl, hαt⟩ := List.mem_map.1 hmem
  have htT : t ∈ tn'.T := (hlin.2.1 t).1 htl
  have := hlab t htT
  rw [hαt] at this
  exact this

/-- On an action in `P` the extension looks the action up in the original description. -/
lemma lookup_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) :
    (extDom d₀ xa xm).actions.lookup a = d₀.actions.lookup a := by
  have hnone : xa.lookup a = none := by
    have key : ∀ l : List ActionDesc, (∀ e ∈ l, ¬ P (Sum.inl e.1)) → l.lookup a = none := by
      intro l hl
      induction l with
      | nil => rfl
      | cons e l ih =>
        have hne : (a == e.1) = false :=
          beq_eq_false_iff_ne.2 fun h => hl e List.mem_cons_self (h ▸ ha)
        rw [show e = (e.1, e.2) from rfl, List.lookup_cons, hne]
        exact ih fun e' he' => hl e' (List.mem_cons_of_mem _ he')
    exact key xa hok.acts
  rw [extDom_actions, List.lookup_append, hnone]
  cases d₀.actions.lookup a <;> rfl

lemma prec_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) :
    (extDom d₀ xa xm).prec a = d₀.prec a := by
  simp only [DomDesc.prec, lookup_ext hok ha]

lemma add_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) :
    (extDom d₀ xa xm).add a = d₀.add a := by
  simp only [DomDesc.add, lookup_ext hok ha]

lemma del_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) :
    (extDom d₀ xa xm).del a = d₀.del a := by
  simp only [DomDesc.del, lookup_ext hok ha]

lemma transition_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) (s : Set ℕ) :
    (extDom d₀ xa xm).toDomain.transition a s = d₀.toDomain.transition a s := by
  show (s \ (extDom d₀ xa xm).del a) ∪ (extDom d₀ xa xm).add a = (s \ d₀.del a) ∪ d₀.add a
  rw [del_ext hok ha, add_ext hok ha]

lemma applicable_ext (hok : ExtOk P d₀ xa xm) {a : ℕ} (ha : P (Sum.inl a)) (s : Set ℕ) :
    (extDom d₀ xa xm).toDomain.Applicable a s ↔ d₀.toDomain.Applicable a s := by
  show (extDom d₀ xa xm).prec a ⊆ s ↔ d₀.prec a ⊆ s
  rw [prec_ext hok ha]

lemma transitionSeq_ext (hok : ExtOk P d₀ xa xm) {bs : List ℕ} (hb : ∀ a ∈ bs, P (Sum.inl a))
    (s : Set ℕ) :
    (extDom d₀ xa xm).toDomain.transitionSeq bs s = d₀.toDomain.transitionSeq bs s := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    rw [ActionModel.transitionSeq_cons, ActionModel.transitionSeq_cons,
      transition_ext hok (hb b List.mem_cons_self)]
    exact ih (fun a ha => hb a (List.mem_cons_of_mem _ ha)) _

lemma seqApplicable_ext (hok : ExtOk P d₀ xa xm) {bs : List ℕ} (hb : ∀ a ∈ bs, P (Sum.inl a))
    (s : Set ℕ) :
    (extDom d₀ xa xm).toDomain.SeqApplicable bs s ↔ d₀.toDomain.SeqApplicable bs s := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    rw [ActionModel.seqApplicable_cons, ActionModel.seqApplicable_cons,
      applicable_ext hok (hb b List.mem_cons_self), transition_ext hok (hb b List.mem_cons_self),
      ih (fun a ha => hb a (List.mem_cons_of_mem _ ha))]

/-- **Conservativity of an extension, for the state transformer of a network labelled in
`P`.** -/
theorem netReach_ext_iff (hok : ExtOk P d₀ xa xm) {tn : TaskNetwork ℕ ℕ ℕ}
    (h₀ : ∀ t ∈ tn.T, P (tn.α t)) {s s' : Set ℕ} :
    (extDom d₀ xa xm).toDomain.NetReach tn s s' ↔ d₀.toDomain.NetReach tn s s' := by
  constructor
  · rintro ⟨bs, hy, happ, hs⟩
    have hb := acts_of_netYield_ext hok h₀ hy
    exact ⟨bs, (netYield_ext_iff hok h₀).1 hy, (seqApplicable_ext hok hb s).1 happ,
      (transitionSeq_ext hok hb s) ▸ hs⟩
  · rintro ⟨bs, hy, happ, hs⟩
    have hy' := (netYield_ext_iff hok h₀).2 hy
    have hb := acts_of_netYield_ext hok h₀ hy'
    exact ⟨bs, hy', (seqApplicable_ext hok hb s).2 happ, (transitionSeq_ext hok hb s).symm ▸ hs⟩

/-! ### The frame property -/

/-- **Outside the facts it mentions, a network changes nothing.** -/
theorem netReach_sdiff {D : Domain ℕ ℕ ℕ ℕ} {R : Set ℕ}
    (hM : ActionModel.MentionsOnly D.toActionModel R) {tn : TaskNetwork ℕ ℕ ℕ} {s s' : Set ℕ}
    (h : D.NetReach tn s s') : s' \ R = s \ R := by
  obtain ⟨bs, -, -, rfl⟩ := h
  exact ActionModel.transitionSeq_sdiff hM bs s

/-- **The frame property of a network**: a run from `s` can be replayed from every state `u`
agreeing with `s` on the facts `R` the domain mentions; the result agrees with the original
result on `R` and with `u` outside `R`. -/
theorem netReach_frame {D : Domain ℕ ℕ ℕ ℕ} {R : Set ℕ}
    (hM : ActionModel.MentionsOnly D.toActionModel R) {tn : TaskNetwork ℕ ℕ ℕ} {s s' u : Set ℕ}
    (h : D.NetReach tn s s') (hsu : s ∩ R = u ∩ R) :
    ∃ u', D.NetReach tn u u' ∧ u' ∩ R = s' ∩ R ∧ u' \ R = u \ R := by
  obtain ⟨bs, hy, happ, rfl⟩ := h
  refine ⟨D.transitionSeq bs u, ⟨bs, hy, (ActionModel.seqApplicable_congr hM bs hsu).1 happ,
    rfl⟩, (ActionModel.transitionSeq_congr D.toActionModel R bs hsu).symm,
    ActionModel.transitionSeq_sdiff hM bs u⟩

/-! ### One-task networks -/

/-- The state transformer of a one-task network labelled with an action. -/
theorem netReach_single_prim {D : Domain ℕ ℕ ℕ ℕ} (i a : ℕ) {s s' : Set ℕ} :
    D.NetReach (netSingle i (Sum.inl a)) s s' ↔ D.Applicable a s ∧ s' = D.transition a s := by
  constructor
  · rintro ⟨bs, ⟨n, hy⟩, happ, rfl⟩
    obtain ⟨-, rfl⟩ := (Domain.netYieldN_single_prim isSingle_netSingle rfl).1 hy
    exact ⟨((ActionModel.seqApplicable_cons _).1 happ).1, rfl⟩
  · rintro ⟨happ, rfl⟩
    exact ⟨[a], ⟨0, (Domain.netYieldN_single_prim isSingle_netSingle rfl).2 ⟨rfl, rfl⟩⟩,
      (ActionModel.seqApplicable_cons _).2 ⟨happ, trivial⟩, rfl⟩

/-- The state transformer of a one-task network labelled with a compound task of a described
domain: the union over the methods of the task. -/
theorem netReach_single_comp (d : DomDesc) (i c : ℕ) {s s' : Set ℕ} :
    d.toDomain.NetReach (netSingle i (Sum.inr c)) s s' ↔
      ∃ e ∈ d.methods, e.1 = c ∧ d.toDomain.NetReach e.2.toTaskNetwork s s' := by
  constructor
  · rintro ⟨bs, ⟨n, hy⟩, happ, hs⟩
    obtain ⟨k, m, -, ⟨e, he, rfl⟩, hmt, hk⟩ :=
      (Domain.netYieldN_single_comp (D := d.toDomain) isSingle_netSingle rfl (methods_wf d)).1 hy
    exact ⟨e, he, hmt, bs, ⟨k, hk⟩, happ, hs⟩
  · rintro ⟨e, he, rfl, bs, ⟨k, hk⟩, happ, hs⟩
    exact ⟨bs, ⟨k + 1, (Domain.netYieldN_single_comp (D := d.toDomain) isSingle_netSingle rfl
      (methods_wf d)).2 ⟨k, e.toMethod, rfl, ⟨e, he, rfl⟩, rfl, hk⟩⟩, happ, hs⟩

/-- The state transformer of a one-cell described grid is that of the one-task network. -/
theorem netReach_gridSingle {D : Domain ℕ ℕ ℕ ℕ} (p : Bool × ℕ) {s s' : Set ℕ} :
    D.NetReach (gridDesc [[p]]).toTaskNetwork s s' ↔
      D.NetReach (netSingle 0 (if p.1 then Sum.inr p.2 else Sum.inl p.2)) s s' := by
  rw [netReach_oneRow]
  simp only [rowLabels_cons, rowLabels_nil]
  constructor
  · rintro ⟨s₁, h₁, rfl⟩
    exact h₁
  · intro h
    exact ⟨s', h, rfl⟩

end Chain

end Syn

end HTN
