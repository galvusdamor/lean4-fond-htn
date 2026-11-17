import FondHtn.QBF.ToFond
import HtnComplexity.PT.DivMod
/-!
# TQBF ≤ₚ strong OD plan existence of primitive problems

The encoding `FOND.QBF.ToFond.desc` is computed in polynomial time (`FOND.QBF.ToFond.pt_desc`),
so with its correctness (`FOND.QBF.ToFond.strongOD_iff`):

* **`FOND.QBF.tqbf_redP_strongOD_PRIM`** — `TQBF ≤ₚ PlanExFM strongOD PRIM`.
-/

namespace FOND

namespace QBF

namespace ToFond

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

theorem pt_lf {α : Type} [BEnc α] {v : α → ℕ} {b : α → Bool} (hv : PT v) (hb : PT b) :
    PT fun a => lf (v a) (b a) := by
  unfold lf
  refine PT.add (PT.affine 4 0 hv |>.of_eq fun _ => by ring) ?_
  exact (PT.cond hb (PT.const 1) (PT.const 0)).of_eq fun a => by cases b a <;> rfl

theorem pt_satF {α : Type} [BEnc α] {c : α → ℕ} (hc : PT c) : PT fun a => satF (c a) :=
  PT.affine 4 2 hc

theorem pt_setEff {α : Type} [BEnc α] {v : α → ℕ} {b : α → Bool} (hv : PT v) (hb : PT b) :
    PT fun a => setEff (v a) (b a) :=
  PT.pair (PT.single (pt_lf hv hb)) (PT.single (pt_lf hv (PT.not hb)))

theorem pt_lits : PT lits := by
  unfold lits
  exact PT.flatMap (PT.rangeLength PT.snd)
    (PT.map (PT.getI (PT.snd.comp PT.fst) PT.snd) (PT.pair (PT.snd.comp PT.fst) PT.snd))

/-- A list of length `nT φ`. -/
def padL (φ : Formula) : List Unit :=
  φ.1.map (fun _ => ()) ++ φ.1.map (fun _ => ()) ++ [(), ()] ++ (lits φ).map fun _ => ()

theorem length_padL (φ : Formula) : (padL φ).length = nT φ := by
  simp [padL, nT]; ring

theorem pt_range : PT fun φ : Formula => List.range (nT φ) := by
  have h : PT padL := by
    unfold padL
    exact PT.append (PT.append (PT.append (PT.map PT.fst (PT.const ())) (PT.map PT.fst (PT.const ())))
      (PT.const _)) (PT.map pt_lits (PT.const ()))
  exact (PT.rangeLength h).of_eq fun φ => by rw [length_padL]

theorem getI_pad {β : Type} [Inhabited β] (L : List β) : ∀ (pad : List β) (i : ℕ),
    pad.length ≤ i → (pad ++ L).getI i = L.getI (i - pad.length)
  | [], i, _ => by simp
  | b :: pad, i, h => by
    obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by simp at h; omega⟩
    simp only [List.cons_append, List.getI_cons_succ, List.length_cons]
    rw [getI_pad L pad i (by simp at h; omega)]
    congr 1; omega

/-- The padding in front of the literal list, of length `2m + 2`. -/
def padP (φ : Formula) : List (ℕ × Lit) := (φ.1 ++ φ.1).map (fun _ => default) ++ [default, default]

theorem length_padP (φ : Formula) : (padP φ).length = 2 * φ.1.length + 2 := by
  simp [padP]; ring

theorem pt_act : PT fun x : Formula × ℕ => act x.1 x.2 := by
  have hm : PT fun x : Formula × ℕ => 2 * x.1.1.length :=
    PT.affine 2 0 (PT.length (PT.fst.comp PT.fst)) |>.of_eq fun _ => by ring
  have hq : PT fun x : Formula × ℕ => x.1.1.getI (x.2 / 2) :=
    PT.getI (PT.fst.comp PT.fst) (PT.divC PT.snd (by norm_num))
  have hv : PT fun x : Formula × ℕ => (x.1.1.getI (x.2 / 2)).2 := PT.snd.comp hq
  have hL : PT fun x : Formula × ℕ => lits x.1 := pt_lits.comp PT.fst
  have hp : PT fun x : Formula × ℕ => (padP x.1 ++ lits x.1).getI x.2 := by
    refine PT.getI (PT.append ?_ hL) PT.snd
    unfold padP
    exact PT.append (PT.map (PT.append (PT.fst.comp PT.fst) (PT.fst.comp PT.fst))
      (PT.const default)) (PT.const _)
  refine PT.of_eq (f := fun x : Formula × ℕ => if x.2 < 2 * x.1.1.length then
    ((x.2, [], [], if (x.1.1.getI (x.2 / 2)).1 then
      [setEff (x.1.1.getI (x.2 / 2)).2 true, setEff (x.1.1.getI (x.2 / 2)).2 false]
      else [setEff (x.1.1.getI (x.2 / 2)).2 (decide (x.2 % 2 = 1))]) : FActDesc)
    else if x.2 = 2 * x.1.1.length then
      (x.2, (List.range x.1.2.length).map satF, [], [([winF], [])])
    else if x.2 = 2 * x.1.1.length + 1 then
      (x.2, [winF], [], [((lits x.1).map fun p => lf p.2.1 p.2.2, [])])
    else
      (x.2, [lf ((padP x.1 ++ lits x.1).getI x.2).2.1 ((padP x.1 ++ lits x.1).getI x.2).2.2], [],
        [([satF ((padP x.1 ++ lits x.1).getI x.2).1], [])])) ?_ ?_
  rotate_left
  · intro x
    dsimp only
    unfold act
    split_ifs with h1 h2 h3 <;> try rfl
    rw [getI_pad _ _ _ (by rw [length_padP]; omega), length_padP]
  refine PT.ite (PT.lt PT.snd hm) ?_ (PT.ite (PT.eq PT.snd hm) ?_ (PT.ite (PT.eq PT.snd (PT.succ hm)) ?_ ?_))
  · refine PT.pair PT.snd (PT.pair PT.nil (PT.pair PT.nil ?_))
    refine PT.ite (PT.eq (PT.fst.comp hq) (PT.const true)) ?_ ?_
    · exact PT.cons (pt_setEff hv (PT.const true)) (PT.single (pt_setEff hv (PT.const false)))
    · exact PT.single (pt_setEff hv (PT.eq (PT.modC PT.snd (by norm_num)) (PT.const 1)))
  · exact PT.pair PT.snd (PT.pair (PT.map (PT.rangeLength (PT.snd.comp PT.fst))
      (pt_satF PT.snd)) (PT.pair PT.nil (PT.const _)))
  · exact PT.pair PT.snd (PT.pair (PT.const [winF]) (PT.pair PT.nil (PT.single (PT.pair
      (PT.map hL (pt_lf (PT.fst.comp (PT.snd.comp PT.snd)) (PT.snd.comp (PT.snd.comp PT.snd))))
      PT.nil))))
  · exact PT.pair PT.snd (PT.pair (PT.single (pt_lf (PT.fst.comp (PT.snd.comp hp))
      (PT.snd.comp (PT.snd.comp hp)))) (PT.pair PT.nil (PT.single (PT.pair
      (PT.single (pt_satF (PT.fst.comp hp))) PT.nil))))

theorem pt_ordL : PT ordL := by
  unfold ordL
  have hm : PT fun x : (Formula × ℕ) × ℕ => 2 * x.1.1.1.length :=
    PT.affine 2 0 (PT.length (PT.fst.comp (PT.fst.comp PT.fst))) |>.of_eq fun _ => by ring
  have hOrd : PT fun x : (Formula × ℕ) × ℕ => decide (Ord x.1.1.1.length x.2 x.1.2) := by
    refine (PT.and (PT.lt PT.snd hm) (PT.or (PT.le hm (PT.snd.comp PT.fst))
      (PT.lt (PT.divC (c := 2) PT.snd (by norm_num)) (PT.divC (c := 2) (PT.snd.comp PT.fst) (by norm_num))))).of_eq
      fun x => ?_
    simp only [Ord, Bool.decide_and, Bool.decide_or]
  exact PT.flatMap pt_range (PT.map (PT.filter (pt_range.comp PT.fst) hOrd)
    (PT.pair PT.snd (PT.snd.comp PT.fst)))

theorem pt_tn : PT tn := by
  unfold tn
  exact PT.pair pt_range (PT.pair pt_ordL (PT.map pt_range
    (PT.pair PT.snd (PT.pair (PT.const false) PT.snd))))

/-- **The encoding is computed in polynomial time.** -/
theorem pt_desc : PT desc := by
  unfold desc
  exact PT.pair (PT.pair (PT.map pt_range pt_act) PT.nil)
    (PT.pair (PT.map pt_lits (pt_lf (PT.fst.comp (PT.snd.comp PT.snd)) (PT.const false))) pt_tn)

end ToFond

open ToFond

/-- **TQBF reduces to strong OD plan existence of primitive problems.** -/
theorem tqbf_redP_strongOD_PRIM : HTN.Cx.RedP TQBF (PlanExFM .strongOD FClass.PRIM) :=
  HTN.Syn.PolyDom.redP_codeLang (α := Formula) (β := FProbDesc)
    (R := fun p => p.Valid ∧ FClass.PRIM p.toProblem ∧ FMCrit.Solvable .strongOD p.toProblem)
    pt_desc
    (fun _ => ⟨fun h => ⟨valid_desc, prim_desc, strongOD_iff.2 h⟩, fun h => strongOD_iff.1 h.2.2⟩)
    badDesc (fun h => badDesc_not_valid h.1)

end QBF

end FOND
