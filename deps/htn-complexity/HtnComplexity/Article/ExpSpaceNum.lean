import HtnComplexity.SpaceEnc.RenderTR
import HtnComplexity.Article.NBody
import HtnComplexity.Article.StripsTM
/-!
# The tail-recursive encoding of space-bounded machines, with explicit numberings

The rendering `HTN.SpaceEnc.rend` of the tail-recursive encoding numbers facts, actions and
compound tasks through `Encodable.encode`, which says nothing about the cost of computing the
numbers.  `HTN.SpaceEnc.rendP` is the same rendering, for machines with states `Fin k` over
`(Option Bool)`, with explicit arithmetic numberings (`HTN.SpaceEnc.cFP`, `HTN.SpaceEnc.cAP`,
`HTN.SpaceEnc.eCP`) and without repeated actions.  It is solvable iff the machine accepts in
space `2 ^ m` (`HTN.SpaceEnc.solvable_rendP_iff`), tail recursive and rooted.
-/

namespace HTN

namespace SpaceEnc

open TM Syn Article

variable {k : ℕ}

/-! ### The numberings -/

/-- The numbering of the facts (before moving the input facts to their positions). -/
def cFP : Fct (Fin k) (Option Bool) → ℕ
  | .boot0 => Nat.pair 0 0
  | .inp i b => Nat.pair 1 (Nat.pair i b.toNat)
  | .pc s => Nat.pair 2 s
  | .cb j x => Nat.pair 3 (Nat.pair j x.toNat)
  | .hb j x => Nat.pair 4 (Nat.pair j x.toNat)
  | .st q => Nat.pair 5 q.val
  | .sym g => Nat.pair 6 (symCode g)
  | .mv μ => Nat.pair 7 (moveCode μ)
  | .par p => Nat.pair 8 p.toNat
  | .first => Nat.pair 9 0
  | .u j => Nat.pair 10 j
  | .eqf => Nat.pair 11 0
  | .neqf => Nat.pair 12 0
  | .drain => Nat.pair 13 0

theorem moveCode_eq_iff {a b : Move} : moveCode a = moveCode b ↔ a = b :=
  ⟨fun h => by cases a <;> cases b <;> simp_all [moveCode], fun h => h ▸ rfl⟩

theorem symCode_eq_iff {a b : Option Bool} : symCode a = symCode b ↔ a = b :=
  ⟨symCode_inj, fun h => h ▸ rfl⟩

theorem toNat_eq_iff {a b : Bool} : a.toNat = b.toNat ↔ a = b :=
  ⟨fun h => by cases a <;> cases b <;> simp_all, fun h => h ▸ rfl⟩

theorem cFP_injective : Function.Injective (cFP (k := k)) := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [cFP, Nat.pair_eq_pair, moveCode_eq_iff, symCode_eq_iff, toNat_eq_iff, Fin.val_inj]

/-- **The numbering of the actions.** -/
def cAP : Act (Fin k) (Option Bool) → ℕ
  | .boot => Nat.pair 0 0
  | .ws p => Nat.pair 1 p.toNat
  | .wb p j x e => Nat.pair 2 (Nat.pair (Nat.pair p.toNat j) (Nat.pair x.toNat e.toNat))
  | .rb p j x => Nat.pair 3 (Nat.pair (Nat.pair p.toNat j) x.toNat)
  | .rv p g => Nat.pair 4 (Nat.pair p.toNat (symCode g))
  | .ri i b => Nat.pair 5 (Nat.pair i b.toNat)
  | .rblank => Nat.pair 6 0
  | .cp p g => Nat.pair 7 (Nat.pair p.toNat (symCode g))
  | .tr p q0 g0 q1 g1 μ => Nat.pair 8 (Nat.pair (Nat.pair p.toNat q0.val)
      (Nat.pair (Nat.pair (symCode g0) q1.val) (Nat.pair (symCode g1) (moveCode μ))))
  | .inc p j => Nat.pair 9 (Nat.pair p.toNat j)
  | .wrap p => Nat.pair 10 p.toNat
  | .hinc p j => Nat.pair 11 (Nat.pair p.toNat j)
  | .hdec p j => Nat.pair 12 (Nat.pair p.toNat j)
  | .hdec0 p => Nat.pair 13 p.toNat
  | .hstay p => Nat.pair 14 p.toNat
  | .fin q => Nat.pair 15 q.val
  | .drn => Nat.pair 16 0

theorem cAP_injective : Function.Injective (cAP (k := k)) := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [cAP, Nat.pair_eq_pair, moveCode_eq_iff, symCode_eq_iff, toNat_eq_iff, Fin.val_inj]

/-- **The numbering of the compound tasks**: `root ↦ 0`. -/
def eCP : Cmp → ℕ
  | .root => 0
  | .main => Nat.pair 1 0 + 1
  | .loop p => Nat.pair 2 p.toNat + 1
  | .block p => Nat.pair 3 p.toNat + 1
  | .tree p j => Nat.pair 4 (Nat.pair p.toNat j) + 1
  | .bit p j => Nat.pair 5 (Nat.pair p.toNat j) + 1
  | .rd0 => Nat.pair 6 0 + 1
  | .core p => Nat.pair 7 p.toNat + 1
  | .incT p => Nat.pair 8 p.toNat + 1
  | .reT p => Nat.pair 9 p.toNat + 1
  | .finish => Nat.pair 10 0 + 1
  | .drainT => Nat.pair 11 0 + 1

theorem eCP_injective : Function.Injective eCP := by
  intro x y h
  cases x <;> cases y <;> simp_all [eCP, Nat.pair_eq_pair, toNat_eq_iff]

/-! ### The rendering -/

section Rend

variable (m n' : ℕ) (N : NTM (Fin k) (Option Bool))

/-- **The rendering with explicit numberings** and without repeated actions. -/
noncomputable def rendP (w : List Bool) : Rendering (prob m n' some N w) :=
  { rend m n' some N 0 w with
    eF := cFP
    eA := cAP
    eC := eCP
    eF_inj := cFP_injective
    eA_inj := cAP_injective
    eC_inj := eCP_injective
    acts := (actsL m n' N).dedup
    used_mem := fun o h => List.mem_dedup.2 ((rend m n' some N 0 w).used_mem o h)
    precL_eq := fun _ _ => rfl
    addL_eq := fun _ _ => rfl
    delL_eq := fun _ _ => rfl }

/-- **The described problem is solvable iff the machine accepts in space `2 ^ m`.** -/
theorem solvable_rendP_iff {w : List Bool} (hn' : n' = w.length) :
    Syn.Solvable (rendP m n' N w).domDesc (rendP m n' N w).instDesc ↔
      N.AcceptsInSpace (w.map some) (2 ^ m) :=
  (rendP m n' N w).solvable_iff.trans (solvable_iff_accepts hn')

theorem isTailRec_rendP (w : List Bool) : DomDesc.IsTailRec (rendP m n' N w).domDesc := by
  refine (rendP m n' N w).isTailRec_domDesc_of (rkC m) ?_
  intro p hp
  simp only [rendP, rend, List.mem_map] at hp
  obtain ⟨b, hb, rfl⟩ := hp
  exact rank_ok m n' N b hb

theorem isRooted_rendP (w : List Bool) : InstDesc.IsRooted (rendP m n' N w).instDesc :=
  (rendP m n' N w).isRooted_instDesc rfl

/-! ### The description with the actions written out -/

/-- The description of an action. -/
noncomputable def actDP (o : Act (Fin k) (Option Bool)) : ActionDesc :=
  (cAP o, (precL m n' o).map cFP, (addL m some N o).map cFP, (delL m o).map cFP)

/-- **The bodies with the actions written out.** -/
noncomputable def nbP : List NBody :=
  (bodies m n' N).map fun b => (eCP b.1, b.2.map (·.map (Sum.map (actDP m n' N) eCP)))

theorem map_dedup_of_injective {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) : ∀ l : List α, l.dedup.map f = (l.map f).dedup := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : a ∈ l
    · rw [List.dedup_cons_of_mem ha, List.map_cons, List.dedup_cons_of_mem (List.mem_map_of_mem ha), ih]
    · rw [List.dedup_cons_of_notMem ha, List.map_cons, List.map_cons,
        List.dedup_cons_of_notMem (fun h => ha (by
          obtain ⟨b, hb, e⟩ := List.mem_map.1 h; rw [← hf e]; exact hb)), ih]

theorem gridAfterDesc_zero (ls : List (List (Bool × ℕ))) : gridAfterDesc ls 0 = gridDesc ls := by
  simp [gridAfterDesc, gridDesc, tailOrd]

theorem encLabel_eq (x : Act (Fin k) (Option Bool) ⊕ Cmp) :
    encLabel cAP eCP x = nLab (Sum.map (actDP m n' N) eCP x) := by
  rcases x with o | c <;> rfl

/-- **The described domain is the domain of the written-out bodies.** -/
theorem domDesc_rendP (w : List Bool) : (rendP m n' N w).domDesc = nDom (nbP m n' N) := by
  have hinj : Function.Injective (actDP m n' N) := fun o o' h =>
    cAP_injective (congrArg Prod.fst h)
  unfold Rendering.domDesc nDom
  refine Prod.ext ?_ ?_
  · show (actsL m n' N).dedup.map (actDP m n' N) = _
    rw [map_dedup_of_injective hinj]
    congr 1
    simp only [actsL, nbP, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun b _ => ?_
    simp only [bodyActs, ← List.map_flatten]
    generalize b.2.flatten = l
    induction l with
    | nil => rfl
    | cons x l ih => rcases x with o | c <;> simp [ih]
  · simp only [rendP, rend, nbP, List.map_map]
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, Shape.desc, gridAfterDescOf, gridAfterDesc_zero, List.map_map]
    congr 2
    refine List.map_congr_left fun row _ => ?_
    simp only [Function.comp_apply, List.map_map]
    exact List.map_congr_left fun x _ => encLabel_eq m n' N x

end Rend

end SpaceEnc

end HTN
