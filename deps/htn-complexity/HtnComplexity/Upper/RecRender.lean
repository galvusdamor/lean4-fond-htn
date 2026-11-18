import HtnComplexity.Upper.Records
import HtnPlanning.Core.Transfer
import HtnPlanning.Core.MethodRestrict
import HtnPlanning.Core.SolutionIso
import HtnPlanning.Computable.Syntax
/-!
# Writing a finite problem down as records

For a finite planning problem over an arbitrary signature `(F, A, C, I)` with `I ≃ ℕ`, this file
writes the domain and the instance down as finite sets of records (`HTN.Upper.domRecs`,
`HTN.Upper.instRecs`, in the format of `HtnComplexity/Upper/Records.lean`) and proves

* `HTN.Upper.net_iso` — the task network read off the records of a network is the relabelled
  network, up to isomorphism (identifiers are renumbered `0, 1, …` inside each network);
* `HTN.Upper.solvable_records_iff` — **the described problem is solvable exactly when the
  semantic one is**.

The proof is the four-step argument of `HtnComplexity/Computable/Render.lean`, for arbitrary
task networks instead of grids: the described initial task network is the relabelled one up to
isomorphism, so is every described method body, and the change of signature preserves
solvability (`HTN.Problem.solvable_relabel_iff`).  All methods are written down, so no method
has to be shown unreachable.
-/

namespace HTN

namespace Upper

open Syn TaskNetwork

/-! ### Lookups -/

theorem lookup_eq_of_forall {β : Type} {l : List (ℕ × β)} {k : ℕ} {v : β}
    (hex : ∃ w, (k, w) ∈ l) (hall : ∀ w, (k, w) ∈ l → w = v) : l.lookup k = some v := by
  induction l with
  | nil => obtain ⟨w, hw⟩ := hex; simp at hw
  | cons p l ih =>
    obtain ⟨k', w'⟩ := p
    rw [List.lookup_cons]
    by_cases h : k = k'
    · subst h
      simp only [beq_self_eq_true, Option.some.injEq]
      exact hall w' (by simp)
    · rw [show (k == k') = false by simp [h]]
      refine ih ?_ fun w hw => hall w (List.mem_cons_of_mem _ hw)
      obtain ⟨w, hw⟩ := hex
      rcases List.mem_cons.1 hw with hw | hw
      · exact absurd (Prod.ext_iff.1 hw).1 h
      · exact ⟨w, hw⟩

theorem lookup_map_self {β : Type} {l : List ℕ} {g : ℕ → β} {a : ℕ} (ha : a ∈ l) :
    (l.map fun x => (x, g x)).lookup a = some (g a) :=
  lookup_eq_of_forall ⟨g a, List.mem_map.2 ⟨a, ha, rfl⟩⟩ fun w hw => by
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hw
    simp only [Prod.mk.injEq] at hx
    rw [← hx.2, hx.1]

/-! ### The records of a task network -/

variable {F A C I : Type}

open Classical in
/-- The renumbering of the identifiers of a network: position in an enumeration of `T`. -/
noncomputable def rn (tn : TaskNetwork I A C) (t : I) : ℕ :=
  if h : t ∈ tn.T then (tn.T.equivFin ⟨t, h⟩ : ℕ) else 0

theorem rn_inj {tn : TaskNetwork I A C} {t t' : I} (ht : t ∈ tn.T) (ht' : t' ∈ tn.T)
    (h : rn tn t = rn tn t') : t = t' := by
  simp only [rn, dif_pos ht, dif_pos ht'] at h
  have := tn.T.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

theorem rn_lt {tn : TaskNetwork I A C} {t : I} (ht : t ∈ tn.T) : rn tn t < tn.T.card := by
  simp only [rn, dif_pos ht]
  exact (tn.T.equivFin ⟨t, ht⟩).isLt

/-- The code of a task name: `(0, a)` for an action, `(1, c)` for a compound name. -/
def lab (eA : A → ℕ) (eC : C → ℕ) : A ⊕ C → ℕ × ℕ :=
  Sum.elim (fun a => (0, eA a)) (fun c => (1, eC c))

open Classical in
/-- **The records of a task network**, under the tag `j`. -/
noncomputable def netRecs (eA : A → ℕ) (eC : C → ℕ) (j : ℕ) (tn : TaskNetwork I A C) :
    Finset Rec :=
  tn.T.image (fun t => (5, j, rn tn t, 0, 0)) ∪
    ((tn.T ×ˢ tn.T).filter (fun p => tn.ord p.1 p.2)).image
      (fun p => (6, j, rn tn p.1, rn tn p.2, 0)) ∪
    tn.T.image (fun t => (7, j, rn tn t, (lab eA eC (tn.α t)).1, (lab eA eC (tn.α t)).2))

theorem mem_netRecs {eA : A → ℕ} {eC : C → ℕ} {j : ℕ} {tn : TaskNetwork I A C} {r : Rec} :
    r ∈ netRecs eA eC j tn ↔
      (∃ t ∈ tn.T, r = (5, j, rn tn t, 0, 0)) ∨
      (∃ t ∈ tn.T, ∃ t' ∈ tn.T, tn.ord t t' ∧ r = (6, j, rn tn t, rn tn t', 0)) ∨
      (∃ t ∈ tn.T, r = (7, j, rn tn t, (lab eA eC (tn.α t)).1, (lab eA eC (tn.α t)).2)) := by
  classical
  simp only [netRecs, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ((⟨t, ht, rfl⟩ | ⟨⟨t, t'⟩, ⟨⟨ht, ht'⟩, ho⟩, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr (Or.inl ⟨t, ht, t', ht', ho, rfl⟩)
    · exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, t', ht', ho, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl (Or.inl ⟨t, ht, rfl⟩)
    · exact Or.inl (Or.inr ⟨⟨t, t'⟩, ⟨⟨ht, ht'⟩, ho⟩, rfl⟩)
    · exact Or.inr ⟨t, ht, rfl⟩

/-- The records of kinds `5`, `6`, `7` and tag `j` in `L` are exactly those of the network. -/
def NetIn (L : List Rec) (eA : A → ℕ) (eC : C → ℕ) (j : ℕ) (tn : TaskNetwork I A C) : Prop :=
  ∀ r : Rec, (r.1 = 5 ∨ r.1 = 6 ∨ r.1 = 7) → r.2.1 = j → (r ∈ L ↔ r ∈ netRecs eA eC j tn)

section NetIso

variable {L : List Rec} {eA : A → ℕ} {eC : C → ℕ} {j : ℕ} {tn : TaskNetwork I A C}

theorem mem_ids_body (h : NetIn L eA eC j tn) {k : ℕ} :
    k ∈ (body L j).1 ↔ ∃ t ∈ tn.T, rn tn t = k := by
  show k ∈ xs L 5 j ↔ _
  rw [mem_xs]
  constructor
  · rintro ⟨r, hr, hk, hj, rfl⟩
    rcases mem_netRecs.1 ((h r (Or.inl hk) hj).1 hr) with ⟨t, ht, rfl⟩ | ⟨t, -, t', -, -, rfl⟩ |
      ⟨t, -, rfl⟩
    · exact ⟨t, ht, rfl⟩
    · simp at hk
    · simp at hk
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(5, j, rn tn t, 0, 0), (h _ (Or.inl rfl) rfl).2 (mem_netRecs.2 (Or.inl ⟨t, ht, rfl⟩)),
      rfl, rfl, rfl⟩

theorem mem_ord_body (h : NetIn L eA eC j tn) {a b : ℕ} :
    (a, b) ∈ (body L j).2.1 ↔
      ∃ t ∈ tn.T, ∃ t' ∈ tn.T, tn.ord t t' ∧ rn tn t = a ∧ rn tn t' = b := by
  show (a, b) ∈ (sel L 6 j).map (fun r => (r.2.2.1, r.2.2.2.1)) ↔ _
  simp only [List.mem_map, mem_sel, Prod.mk.injEq]
  constructor
  · rintro ⟨r, ⟨hr, hk, hj⟩, ha, hb⟩
    rcases mem_netRecs.1 ((h r (Or.inr (Or.inl hk)) hj).1 hr) with ⟨t, -, rfl⟩ |
      ⟨t, ht, t', ht', ho, rfl⟩ | ⟨t, -, rfl⟩
    · simp at hk
    · exact ⟨t, ht, t', ht', ho, ha, hb⟩
    · simp at hk
  · rintro ⟨t, ht, t', ht', ho, rfl, rfl⟩
    exact ⟨(6, j, rn tn t, rn tn t', 0), ⟨(h _ (Or.inr (Or.inl rfl)) rfl).2
      (mem_netRecs.2 (Or.inr (Or.inl ⟨t, ht, t', ht', ho, rfl⟩))), rfl, rfl⟩, rfl, rfl⟩

theorem mem_lbl_body (h : NetIn L eA eC j tn) {k : ℕ} {w : Bool × ℕ} :
    (k, w) ∈ (body L j).2.2 ↔
      ∃ t ∈ tn.T, rn tn t = k ∧ w = (decide ((lab eA eC (tn.α t)).1 = 1),
        (lab eA eC (tn.α t)).2) := by
  show (k, w) ∈ (sel L 7 j).map (fun r => (r.2.2.1, decide (r.2.2.2.1 = 1), r.2.2.2.2)) ↔ _
  simp only [List.mem_map, mem_sel]
  constructor
  · rintro ⟨r, ⟨hr, hk, hj⟩, hrw⟩
    rcases mem_netRecs.1 ((h r (Or.inr (Or.inr hk)) hj).1 hr) with ⟨t, -, rfl⟩ |
      ⟨t, -, t', -, -, rfl⟩ | ⟨t, ht, rfl⟩
    · simp at hk
    · simp at hk
    · simp only [Prod.mk.injEq] at hrw
      exact ⟨t, ht, hrw.1, by rw [← hrw.2]⟩
  · rintro ⟨t, ht, rfl, rfl⟩
    exact ⟨(7, j, rn tn t, (lab eA eC (tn.α t)).1, (lab eA eC (tn.α t)).2),
      ⟨(h _ (Or.inr (Or.inr rfl)) rfl).2 (mem_netRecs.2 (Or.inr (Or.inr ⟨t, ht, rfl⟩))), rfl,
        rfl⟩, rfl⟩

theorem label_body (h : NetIn L eA eC j tn) {t : I} (ht : t ∈ tn.T) :
    (body L j).label (rn tn t) = Sum.map eA eC (tn.α t) := by
  have hl : (body L j).lbl.lookup (rn tn t) =
      some (decide ((lab eA eC (tn.α t)).1 = 1), (lab eA eC (tn.α t)).2) := by
    refine lookup_eq_of_forall ⟨_, (mem_lbl_body h).2 ⟨t, ht, rfl, rfl⟩⟩ fun w hw => ?_
    obtain ⟨t', ht', hrn, rfl⟩ := (mem_lbl_body h).1 hw
    rw [rn_inj ht' ht hrn]
  unfold TnDesc.label
  rw [hl]
  rcases tn.α t with a | c <;> rfl

theorem preOrd_body_iff (h : NetIn L eA eC j tn) (hwf : tn.WF) {a b : ℕ} :
    (body L j).preOrd a b ↔
      ∃ t ∈ tn.T, ∃ t' ∈ tn.T, tn.ord t t' ∧ rn tn t = a ∧ rn tn t' = b := by
  constructor
  · intro hp
    induction hp with
    | single hab => exact (mem_ord_body h).1 hab
    | tail _ hbc ih =>
      obtain ⟨t, ht, t', ht', ho, rfl, rfl⟩ := ih
      obtain ⟨s, hs, s', hs', ho', hsr, rfl⟩ := (mem_ord_body h).1 hbc
      have hst : s = t' := rn_inj hs ht' hsr
      subst hst
      exact ⟨t, ht, s', hs', hwf.trans ho ho', rfl, rfl⟩
  · intro hx
    exact Relation.TransGen.single ((mem_ord_body h).2 hx)

theorem ord_body_iff (h : NetIn L eA eC j tn) (hwf : tn.WF) {t t' : I} (ht : t ∈ tn.T)
    (ht' : t' ∈ tn.T) :
    (body L j).toTaskNetwork.ord (rn tn t) (rn tn t') ↔ tn.ord t t' := by
  show (body L j).ordOf (rn tn t) (rn tn t') ↔ tn.ord t t'
  unfold TnDesc.ordOf
  rw [preOrd_body_iff h hwf, preOrd_body_iff h hwf]
  constructor
  · rintro ⟨-, -, ⟨s, hs, s', hs', ho, h1, h2⟩, -⟩
    rw [rn_inj hs ht h1, rn_inj hs' ht' h2] at ho
    exact ho
  · intro ho
    refine ⟨(mem_ids_body h).2 ⟨t, ht, rfl⟩, (mem_ids_body h).2 ⟨t', ht', rfl⟩,
      ⟨t, ht, t', ht', ho, rfl, rfl⟩, ?_⟩
    rintro ⟨s, hs, s', hs', ho', h1, h2⟩
    rw [rn_inj hs ht' h1, rn_inj hs' ht h2] at ho'
    exact hwf.irrefl _ (hwf.trans ho ho')

theorem mem_T_body (h : NetIn L eA eC j tn) {k : ℕ} :
    k ∈ (body L j).toTaskNetwork.T ↔ ∃ t ∈ tn.T, rn tn t = k := by
  rw [TnDesc.toTaskNetwork_T, List.mem_toFinset]
  exact mem_ids_body h

theorem isLastId_body_iff (h : NetIn L eA eC j tn) (hwf : tn.WF) {s : I} (hs : s ∈ tn.T) :
    (body L j).toTaskNetwork.IsLastId (rn tn s) ↔ tn.IsLastId s := by
  constructor
  · rintro ⟨-, hall⟩
    refine ⟨hs, fun s' hs' hne => ?_⟩
    have hk := hall (rn tn s') ((mem_T_body h).2 ⟨s', hs', rfl⟩)
      (fun he => hne (rn_inj hs' hs he))
    exact (ord_body_iff h hwf hs' hs).1 hk
  · rintro ⟨-, hall⟩
    refine ⟨(mem_T_body h).2 ⟨s, hs, rfl⟩, fun k hk hne => ?_⟩
    obtain ⟨s', hs', rfl⟩ := (mem_T_body h).1 hk
    exact (ord_body_iff h hwf hs' hs).2 (hall s' hs' (fun he => hne (by rw [he])))

/-- **The task network read off the records of a network is the relabelled network**, up to
isomorphism. -/
theorem net_iso (eI : I ≃ ℕ) [DecidableEq I] (h : NetIn L eA eC j tn) (hwf : tn.WF) :
    (body L j).toTaskNetwork.Iso (TaskNetwork.relabel eA eC eI tn) := by
  classical
  set σ : ℕ → ℕ := fun k =>
    if hk : k < tn.T.card then eI (tn.T.equivFin.symm ⟨k, hk⟩ : I) else 0 with hσ
  have hσrn : ∀ t ∈ tn.T, σ (rn tn t) = eI t := by
    intro t ht
    simp only [hσ, dif_pos (rn_lt ht)]
    congr 1
    have : (⟨rn tn t, rn_lt ht⟩ : Fin tn.T.card) = tn.T.equivFin ⟨t, ht⟩ := by
      ext; simp [rn, dif_pos ht]
    rw [this, Equiv.symm_apply_apply]
  have hT : ∀ k, k ∈ (body L j).toTaskNetwork.T ↔ ∃ t ∈ tn.T, rn tn t = k := by
    intro k
    show k ∈ (body L j).1.toFinset ↔ _
    rw [List.mem_toFinset]
    exact mem_ids_body h
  refine ⟨σ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro k hk
    obtain ⟨t, ht, rfl⟩ := (hT k).1 hk
    rw [hσrn t ht]
    exact mem_relabel_T_apply.2 ht
  · intro k hk k' hk' heq
    obtain ⟨t, ht, rfl⟩ := (hT k).1 hk
    obtain ⟨t', ht', rfl⟩ := (hT k').1 hk'
    rw [hσrn t ht, hσrn t' ht'] at heq
    rw [eI.injective heq]
  · intro y hy
    have hy' : eI.symm y ∈ tn.T := mem_relabel_T.1 hy
    refine ⟨rn tn (eI.symm y), (hT _).2 ⟨_, hy', rfl⟩, ?_⟩
    rw [hσrn _ hy', Equiv.apply_symm_apply]
  · intro k hk k' hk'
    obtain ⟨t, ht, rfl⟩ := (hT k).1 hk
    obtain ⟨t', ht', rfl⟩ := (hT k').1 hk'
    rw [hσrn t ht, hσrn t' ht', relabel_ord_apply]
    exact ord_body_iff h hwf ht ht'
  · intro k hk
    obtain ⟨t, ht, rfl⟩ := (hT k).1 hk
    rw [hσrn t ht]
    show (body L j).label (rn tn t) = _
    rw [label_body h ht, relabel_α, Equiv.symm_apply_apply]

end NetIso

/-! ### The records of a domain and of an instance -/

variable [Fintype F] [Fintype A] [Fintype C]

/-- The numbering of the elements of a finite type (facts, actions, compound task names). -/
noncomputable def eFn (F : Type) [Finite F] (x : F) : ℕ := (Finite.equivFin F x : ℕ)

theorem eFn_injective (F : Type) [Finite F] : Function.Injective (eFn F) := fun x y h =>
  (Finite.equivFin F).injective (Fin.ext h)

theorem eFn_lt {F : Type} [Finite F] (x : F) : eFn F x < Nat.card F :=
  (Finite.equivFin F x).isLt

open Classical in
/-- The numbering of the methods of a domain with finitely many methods. -/
noncomputable def ix {D : Domain F A C I} (hm : D.methods.Finite) (m : Method I A C) : ℕ :=
  if h : m ∈ hm.toFinset then (hm.toFinset.equivFin ⟨m, h⟩ : ℕ) else 0

theorem ix_inj {D : Domain F A C I} (hm : D.methods.Finite) {m m' : Method I A C}
    (h : m ∈ D.methods) (h' : m' ∈ D.methods) (he : ix hm m = ix hm m') : m = m' := by
  have h1 : m ∈ hm.toFinset := hm.mem_toFinset.2 h
  have h2 : m' ∈ hm.toFinset := hm.mem_toFinset.2 h'
  simp only [ix, dif_pos h1, dif_pos h2] at he
  exact congrArg Subtype.val (hm.toFinset.equivFin.injective (Fin.ext he))

open Classical in
/-- The records `(k, a, f, 0, 0)` of a relation between actions and facts. -/
noncomputable def factRecs (k : ℕ) (R : A → Set F) : Finset Rec :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : A × F => p.2 ∈ R p.1)).image
    (fun p => (k, eFn A p.1, eFn F p.2, 0, 0))

theorem mem_factRecs {k : ℕ} {R : A → Set F} {r : Rec} :
    r ∈ factRecs k R ↔ ∃ a f, f ∈ R a ∧ r = (k, eFn A a, eFn F f, 0, 0) := by
  classical
  constructor
  · intro h
    obtain ⟨⟨a, f⟩, hp, rfl⟩ := Finset.mem_image.1 h
    exact ⟨a, f, (Finset.mem_filter.1 hp).2, rfl⟩
  · rintro ⟨a, f, h, rfl⟩
    exact Finset.mem_image.2 ⟨(a, f), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩, rfl⟩

/-- The records `(3, 0, a, 0, 0)` listing the actions. -/
noncomputable def actRecs (A : Type) [Fintype A] : Finset Rec :=
  Finset.univ.image (fun a : A => ((3, 0, eFn A a, 0, 0) : Rec))

theorem mem_actRecs {r : Rec} : r ∈ actRecs A ↔ ∃ a : A, r = (3, 0, eFn A a, 0, 0) := by
  constructor
  · intro h
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩

/-- The records `(4, 0, j, c, 0)` listing the methods. -/
noncomputable def methRecs (D : Domain F A C I) (hm : D.methods.Finite) : Finset Rec :=
  hm.toFinset.image (fun m => ((4, 0, ix hm m, eFn C m.abstractTask, 0) : Rec))

theorem mem_methRecs {D : Domain F A C I} {hm : D.methods.Finite} {r : Rec} :
    r ∈ methRecs D hm ↔ ∃ m ∈ D.methods, r = (4, 0, ix hm m, eFn C m.abstractTask, 0) := by
  constructor
  · intro h
    obtain ⟨m, hmem, rfl⟩ := Finset.mem_image.1 h
    exact ⟨m, hm.mem_toFinset.1 hmem, rfl⟩
  · rintro ⟨m, hmem, rfl⟩
    exact Finset.mem_image.2 ⟨m, hm.mem_toFinset.2 hmem, rfl⟩

/-- The records of the method bodies, the body of method number `j` under the tag `j`. -/
noncomputable def bodyRecs (D : Domain F A C I) (hm : D.methods.Finite) : Finset Rec :=
  hm.toFinset.biUnion (fun m => netRecs (eFn A) (eFn C) (ix hm m) m.subtasks)

theorem mem_bodyRecs {D : Domain F A C I} {hm : D.methods.Finite} {r : Rec} :
    r ∈ bodyRecs D hm ↔ ∃ m ∈ D.methods, r ∈ netRecs (eFn A) (eFn C) (ix hm m) m.subtasks := by
  constructor
  · intro h
    obtain ⟨m, hmem, hr⟩ := Finset.mem_biUnion.1 h
    exact ⟨m, hm.mem_toFinset.1 hmem, hr⟩
  · rintro ⟨m, hmem, hr⟩
    exact Finset.mem_biUnion.2 ⟨m, hm.mem_toFinset.2 hmem, hr⟩

/-- **The records of a domain.** -/
noncomputable def domRecs (D : Domain F A C I) (hm : D.methods.Finite) : Finset Rec :=
  factRecs 0 D.prec ∪ factRecs 1 D.add ∪ factRecs 2 D.del ∪ actRecs A ∪ methRecs D hm ∪
    bodyRecs D hm

open Classical in
/-- **The records of an instance.** -/
noncomputable def instRecs (Q : Instance F A C I) : Finset Rec :=
  (Finset.univ.filter (· ∈ Q.init)).image (fun x => ((0, 0, eFn F x, 0, 0) : Rec)) ∪
    (Finset.univ.filter (· ∈ Q.goal)).image (fun x => ((1, 0, eFn F x, 0, 0) : Rec)) ∪
    netRecs (eFn A) (eFn C) 0 Q.tnI

theorem netRecs_kind {eA : A → ℕ} {eC : C → ℕ} {j : ℕ} {tn : TaskNetwork I A C} {r : Rec}
    (h : r ∈ netRecs eA eC j tn) : (r.1 = 5 ∨ r.1 = 6 ∨ r.1 = 7) ∧ r.2.1 = j := by
  rcases mem_netRecs.1 h with ⟨t, -, rfl⟩ | ⟨t, -, t', -, -, rfl⟩ | ⟨t, -, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨Or.inr (Or.inr rfl), rfl⟩

section DomRecs

variable {D : Domain F A C I} {hm : D.methods.Finite}

theorem mem_domRecs_cases {r : Rec} (h : r ∈ domRecs D hm) :
    (∃ a f, f ∈ D.prec a ∧ r = (0, eFn A a, eFn F f, 0, 0)) ∨
    (∃ a f, f ∈ D.add a ∧ r = (1, eFn A a, eFn F f, 0, 0)) ∨
    (∃ a f, f ∈ D.del a ∧ r = (2, eFn A a, eFn F f, 0, 0)) ∨
    (∃ a : A, r = (3, 0, eFn A a, 0, 0)) ∨
    (∃ m ∈ D.methods, r = (4, 0, ix hm m, eFn C m.abstractTask, 0)) ∨
    (∃ m ∈ D.methods, r ∈ netRecs (eFn A) (eFn C) (ix hm m) m.subtasks) := by
  simp only [domRecs, Finset.mem_union] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact Or.inl (mem_factRecs.1 h)
  · exact Or.inr (Or.inl (mem_factRecs.1 h))
  · exact Or.inr (Or.inr (Or.inl (mem_factRecs.1 h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_actRecs.1 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_methRecs.1 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_bodyRecs.1 h)))))

theorem mem_domRecs_of_factRecs {k : ℕ} {R : A → Set F} {r : Rec}
    (hR : factRecs k R ⊆ domRecs D hm) (h : r ∈ factRecs k R) : r ∈ domRecs D hm := hR h

theorem factRecs0_sub : factRecs 0 D.prec ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))

theorem factRecs1_sub : factRecs 1 D.add ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))

theorem factRecs2_sub : factRecs 2 D.del ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem actRecs_sub : actRecs A ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inl (Or.inl (Or.inr h))

theorem methRecs_sub : methRecs D hm ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inl (Or.inr h)

theorem bodyRecs_sub : bodyRecs D hm ⊆ domRecs D hm := fun _ h => by
  simp only [domRecs, Finset.mem_union]; exact Or.inr h

theorem domRecs_kind_fact {r : Rec} (h : r ∈ domRecs D hm) :
    (r.1 = 0 → ∃ a f, f ∈ D.prec a ∧ r = (0, eFn A a, eFn F f, 0, 0)) ∧
    (r.1 = 1 → ∃ a f, f ∈ D.add a ∧ r = (1, eFn A a, eFn F f, 0, 0)) ∧
    (r.1 = 2 → ∃ a f, f ∈ D.del a ∧ r = (2, eFn A a, eFn F f, 0, 0)) := by
  rcases mem_domRecs_cases h with h' | h' | h' | ⟨a, rfl⟩ | ⟨m, -, rfl⟩ | ⟨m, -, hr⟩
  · refine ⟨fun _ => h', fun hk => ?_, fun hk => ?_⟩ <;>
      obtain ⟨a, f, -, rfl⟩ := h' <;> simp at hk
  · refine ⟨fun hk => ?_, fun _ => h', fun hk => ?_⟩ <;>
      obtain ⟨a, f, -, rfl⟩ := h' <;> simp at hk
  · refine ⟨fun hk => ?_, fun hk => ?_, fun _ => h'⟩ <;>
      obtain ⟨a, f, -, rfl⟩ := h' <;> simp at hk
  · refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩ <;> simp at hk
  · refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩ <;> simp at hk
  · have h5 := (netRecs_kind hr).1
    refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩ <;> omega

theorem domRecs_kind3 {r : Rec} (h : r ∈ domRecs D hm) (hk : r.1 = 3) :
    ∃ a : A, r = (3, 0, eFn A a, 0, 0) := by
  rcases mem_domRecs_cases h with ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ | h' |
    ⟨m, -, rfl⟩ | ⟨m, -, hr⟩
  · simp at hk
  · simp at hk
  · simp at hk
  · exact h'
  · simp at hk
  · have h5 := (netRecs_kind hr).1
    omega

theorem domRecs_kind4 {r : Rec} (h : r ∈ domRecs D hm) (hk : r.1 = 4) :
    ∃ m ∈ D.methods, r = (4, 0, ix hm m, eFn C m.abstractTask, 0) := by
  rcases mem_domRecs_cases h with ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ | ⟨a, rfl⟩ |
    h' | ⟨m, -, hr⟩
  · simp at hk
  · simp at hk
  · simp at hk
  · simp at hk
  · exact h'
  · have h5 := (netRecs_kind hr).1
    omega

/-- The list of the records of a domain. -/
noncomputable def domList (D : Domain F A C I) (hm : D.methods.Finite) : List Rec :=
  recsOf (recCode (domRecs D hm))

theorem mem_domList {r : Rec} : r ∈ domList D hm ↔ r ∈ domRecs D hm := mem_recsOf_recCode

/-- **The domain description read off the records of a domain.** -/
noncomputable def domD (D : Domain F A C I) (hm : D.methods.Finite) : DomDesc :=
  toDom (domList D hm)

/-- The records of the body of a method of the domain are those of its subtask network. -/
theorem netIn_dom {m : Method I A C} (hmD : m ∈ D.methods) :
    NetIn (domList D hm) (eFn A) (eFn C) (ix hm m) m.subtasks := by
  intro r hk hj
  rw [mem_domList]
  constructor
  · intro h
    rcases mem_domRecs_cases h with ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ | ⟨a, f, -, rfl⟩ |
      ⟨a, rfl⟩ | ⟨m', -, rfl⟩ | ⟨m', hm', hr⟩
    · simp at hk
    · simp at hk
    · simp at hk
    · simp at hk
    · simp at hk
    · have h1 := (netRecs_kind hr).2
      have he : m = m' := ix_inj hm hmD hm' (hj.symm.trans h1)
      subst he
      exact hr
  · intro h
    exact bodyRecs_sub (mem_bodyRecs.2 ⟨m, hmD, h⟩)

theorem mem_xs_fact {L : List Rec} {k : ℕ} {R : A → Set F}
    (h1 : ∀ r ∈ L, r.1 = k → ∃ a f, f ∈ R a ∧ r = (k, eFn A a, eFn F f, 0, 0))
    (h2 : ∀ a f, f ∈ R a → ((k, eFn A a, eFn F f, 0, 0) : Rec) ∈ L) {a : A} {x : ℕ} :
    x ∈ xs L k (eFn A a) ↔ ∃ f ∈ R a, eFn F f = x := by
  rw [mem_xs]
  constructor
  · rintro ⟨r, hr, hk, hj, rfl⟩
    obtain ⟨a', f, hf, rfl⟩ := h1 r hr hk
    have ha : a' = a := eFn_injective A hj
    subst ha
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨_, h2 a f hf, rfl, rfl, rfl⟩

theorem mem_acts_domD (a : A) : eFn A a ∈ xs (domList D hm) 3 0 :=
  mem_xs.2 ⟨(3, 0, eFn A a, 0, 0), mem_domList.2 (actRecs_sub (mem_actRecs.2 ⟨a, rfl⟩)),
    rfl, rfl, rfl⟩

theorem lookup_domD (a : A) :
    (domD D hm).actions.lookup (eFn A a) =
      some (xs (domList D hm) 0 (eFn A a), xs (domList D hm) 1 (eFn A a),
        xs (domList D hm) 2 (eFn A a)) :=
  lookup_map_self (g := fun a => (xs (domList D hm) 0 a, xs (domList D hm) 1 a,
    xs (domList D hm) 2 a)) (mem_acts_domD a)

theorem prec_domD (a : A) : (domD D hm).prec (eFn A a) = eFn F '' D.prec a := by
  ext x
  show x ∈ ((domD D hm).actions.lookup (eFn A a)).elim [] (fun y => y.1) ↔ _
  rw [lookup_domD, Set.mem_image]
  exact mem_xs_fact (fun r hr hk => (domRecs_kind_fact (mem_domList.1 hr)).1 hk)
    (fun a f hf => mem_domList.2 (factRecs0_sub (mem_factRecs.2 ⟨a, f, hf, rfl⟩)))

theorem add_domD (a : A) : (domD D hm).add (eFn A a) = eFn F '' D.add a := by
  ext x
  show x ∈ ((domD D hm).actions.lookup (eFn A a)).elim [] (fun y => y.2.1) ↔ _
  rw [lookup_domD, Set.mem_image]
  exact mem_xs_fact (fun r hr hk => (domRecs_kind_fact (mem_domList.1 hr)).2.1 hk)
    (fun a f hf => mem_domList.2 (factRecs1_sub (mem_factRecs.2 ⟨a, f, hf, rfl⟩)))

theorem del_domD (a : A) : (domD D hm).del (eFn A a) = eFn F '' D.del a := by
  ext x
  show x ∈ ((domD D hm).actions.lookup (eFn A a)).elim [] (fun y => y.2.2) ↔ _
  rw [lookup_domD, Set.mem_image]
  exact mem_xs_fact (fun r hr hk => (domRecs_kind_fact (mem_domList.1 hr)).2.2 hk)
    (fun a f hf => mem_domList.2 (factRecs2_sub (mem_factRecs.2 ⟨a, f, hf, rfl⟩)))

/-- **The methods of the described domain** are the methods of the domain, with their bodies
read off the records. -/
theorem mem_methods_domD {e : MethodDesc} :
    e ∈ (domD D hm).methods ↔
      ∃ m ∈ D.methods, e = (eFn C m.abstractTask, body (domList D hm) (ix hm m)) := by
  show e ∈ (sel (domList D hm) 4 0).map (fun r => (r.2.2.2.1, body (domList D hm) r.2.2.1)) ↔ _
  simp only [List.mem_map, mem_sel]
  constructor
  · rintro ⟨r, ⟨hr, hk, -⟩, rfl⟩
    obtain ⟨m, hmD, rfl⟩ := domRecs_kind4 (mem_domList.1 hr) hk
    exact ⟨m, hmD, rfl⟩
  · rintro ⟨m, hmD, rfl⟩
    exact ⟨_, ⟨mem_domList.2 (methRecs_sub (mem_methRecs.2 ⟨m, hmD, rfl⟩)), rfl, rfl⟩, rfl⟩

end DomRecs

section InstRecs

variable {Q : Instance F A C I}

theorem mem_instRecs_cases {r : Rec} (h : r ∈ instRecs Q) :
    (∃ x ∈ Q.init, r = (0, 0, eFn F x, 0, 0)) ∨ (∃ x ∈ Q.goal, r = (1, 0, eFn F x, 0, 0)) ∨
      r ∈ netRecs (eFn A) (eFn C) 0 Q.tnI := by
  classical
  simp only [instRecs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  rcases h with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | h
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr (Or.inl ⟨x, hx, rfl⟩)
  · exact Or.inr (Or.inr h)

theorem init_mem_instRecs {x : F} (hx : x ∈ Q.init) : ((0, 0, eFn F x, 0, 0) : Rec) ∈ instRecs Q := by
  classical
  simp only [instRecs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨x, hx, rfl⟩)

theorem goal_mem_instRecs {x : F} (hx : x ∈ Q.goal) : ((1, 0, eFn F x, 0, 0) : Rec) ∈ instRecs Q := by
  classical
  simp only [instRecs, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨x, hx, rfl⟩)

/-- The list of the records of an instance. -/
noncomputable def instList (Q : Instance F A C I) : List Rec := recsOf (recCode (instRecs Q))

theorem mem_instList {r : Rec} : r ∈ instList Q ↔ r ∈ instRecs Q := mem_recsOf_recCode

/-- **The instance description read off the records of an instance.** -/
noncomputable def instD (Q : Instance F A C I) : InstDesc := toInst (instList Q)

theorem netIn_inst : NetIn (instList Q) (eFn A) (eFn C) 0 Q.tnI := by
  intro r hk hj
  rw [mem_instList]
  constructor
  · intro h
    rcases mem_instRecs_cases h with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | h'
    · simp at hk
    · simp at hk
    · exact h'
  · intro h
    classical
    simp only [instRecs, Finset.mem_union]
    exact Or.inr h

theorem init_instD : {x | x ∈ (instD Q).initList} = eFn F '' Q.init := by
  ext x
  show x ∈ xs (instList Q) 0 0 ↔ _
  rw [mem_xs, Set.mem_image]
  constructor
  · rintro ⟨r, hr, hk, -, rfl⟩
    rcases mem_instRecs_cases (mem_instList.1 hr) with ⟨y, hy, rfl⟩ | ⟨y, -, rfl⟩ | h'
    · exact ⟨y, hy, rfl⟩
    · simp at hk
    · have h5 := (netRecs_kind h').1
      omega
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, mem_instList.2 (init_mem_instRecs hy), rfl, rfl, rfl⟩

theorem goal_instD : {x | x ∈ (instD Q).goalList} = eFn F '' Q.goal := by
  ext x
  show x ∈ xs (instList Q) 1 0 ↔ _
  rw [mem_xs, Set.mem_image]
  constructor
  · rintro ⟨r, hr, hk, -, rfl⟩
    rcases mem_instRecs_cases (mem_instList.1 hr) with ⟨y, -, rfl⟩ | ⟨y, hy, rfl⟩ | h'
    · simp at hk
    · exact ⟨y, hy, rfl⟩
    · have h5 := (netRecs_kind h').1
      omega
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, mem_instList.2 (goal_mem_instRecs hy), rfl, rfl, rfl⟩

end InstRecs

/-! ### The described problem is the semantic one -/

/-- A problem without tasks is solvable exactly when the goal holds initially. -/
theorem solvable_iff_of_tnI_T_eq_empty {F' A' C' I' : Type} [DecidableEq I']
    {P : Problem F' A' C' I'} (h : P.tnI.T = ∅) : P.Solvable ↔ P.goal ⊆ P.init := by
  constructor
  · rintro ⟨tn, hreach, -, l, as, hlin, has, -, hgoal⟩
    have htn : tn = P.tnI := by
      rcases Relation.ReflTransGen.cases_head hreach with h' | ⟨tn', ⟨t, m, -, ht, -⟩, -⟩
      · exact h'.symm
      · rw [h] at ht
        simp at ht
    subst htn
    have hl : l = [] := List.eq_nil_iff_forall_not_mem.2 fun t ht => by
      have h' := (hlin.2.1 t).1 ht
      rw [h] at h'
      simp at h'
    subst hl
    have has' : as = [] := List.map_eq_nil_iff.1 has.symm
    subst has'
    exact hgoal
  · intro hg
    refine ⟨P.tnI, Relation.ReflTransGen.refl, fun t ht => by rw [h] at ht; simp at ht, [], [],
      ⟨List.nodup_nil, fun t => by rw [h]; simp, List.Pairwise.nil⟩, rfl, trivial, hg⟩

section Solvable

variable [DecidableEq I] {D : Domain F A C I} {hm : D.methods.Finite} {Q : Instance F A C I}

/-- **The described methods are the relabelled methods of the domain**, up to isomorphism of
the bodies. -/
theorem methodsIsoEquiv_domD (eI : I ≃ ℕ) (hwf : ∀ m ∈ D.methods, m.subtasks.WF) :
    Problem.MethodsIsoEquiv {m : Method ℕ ℕ ℕ | ∃ e ∈ (domD D hm).methods, e.toMethod = m}
      (Method.relabel (eFn A) (eFn C) eI '' D.methods) := by
  constructor
  · rintro n ⟨e, he, rfl⟩
    obtain ⟨m, hmD, rfl⟩ := mem_methods_domD.1 he
    exact ⟨Method.relabel (eFn A) (eFn C) eI m, ⟨m, hmD, rfl⟩, rfl,
      net_iso eI (netIn_dom hmD) (hwf m hmD)⟩
  · rintro n ⟨m, hmD, rfl⟩
    exact ⟨MethodDesc.toMethod (eFn C m.abstractTask, body (domList D hm) (ix hm m)),
      ⟨_, mem_methods_domD.2 ⟨m, hmD, rfl⟩, rfl⟩, rfl,
      (net_iso eI (netIn_dom hmD) (hwf m hmD)).symm⟩

/-- **The problem described by the records is solvable exactly when the semantic one is.** -/
theorem solvable_records_iff (eI : I ≃ ℕ) [Infinite I] (hwf : (D.mkProblem Q).WF) :
    Solvable (domD D hm) (instD Q) ↔ (D.mkProblem Q).Solvable := by
  classical
  set P := D.mkProblem Q with hP
  set PD := problem (domD D hm) (instD Q) with hPD
  by_cases hne : Nonempty (A ⊕ C)
  · set tn' := TaskNetwork.relabel (eFn A) (eFn C) eI P.tnI with htn'
    set N := Method.relabel (eFn A) (eFn C) eI '' D.methods with hN
    have hwfP : P.tnI.WF := hwf.tnI
    have htnIiso : PD.tnI.Iso tn' := net_iso eI netIn_inst hwfP
    have step1 : PD.Solvable ↔ (PD.withTnI tn').Solvable := by
      refine Iff.trans (Iff.of_eq (congrArg Problem.Solvable (rfl : PD = PD.withTnI PD.tnI))) ?_
      exact Problem.solvable_congr_tnI_iff PD (TnDesc.toTaskNetwork_wf _)
        (TaskNetwork.relabel_wf hwfP) htnIiso
    have step2 : (PD.withTnI tn').Solvable ↔ ((PD.withTnI tn').withMethods N).Solvable :=
      (Problem.solvable_congr_methods (methodsIsoEquiv_domD eI hwf.methods)).symm
    have step3 : ((PD.withTnI tn').withMethods N).Solvable ↔ P.Solvable :=
      Problem.solvable_relabel_iff (eF := eFn F) (eA := eFn A) (eC := eFn C) (eI := eI)
        (eFn_injective F) (eFn_injective A) (eFn_injective C)
        (fun o _ => prec_domD o) (fun o _ => add_domD o) (fun o _ => del_domD o)
        init_instD goal_instD hwfP rfl rfl
    exact step1.trans (step2.trans step3)
  · have hA : ∀ t ∈ Q.tnI.T, False := fun t _ => hne ⟨Q.tnI.α t⟩
    have hPT : P.tnI.T = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => hA t ht
    have hPDT : PD.tnI.T = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun k hk => ?_
      have hk' : k ∈ (body (instList Q) 0).1 := List.mem_toFinset.1 hk
      obtain ⟨t, ht, -⟩ := (mem_ids_body netIn_inst).1 hk'
      exact hA t ht
    show PD.Solvable ↔ P.Solvable
    rw [solvable_iff_of_tnI_T_eq_empty hPT, solvable_iff_of_tnI_T_eq_empty hPDT]
    show {x | x ∈ (instD Q).goalList} ⊆ {x | x ∈ (instD Q).initList} ↔ Q.goal ⊆ Q.init
    rw [goal_instD, init_instD]
    exact Set.image_subset_image_iff (eFn_injective F)

end Solvable

end Upper

end HTN
