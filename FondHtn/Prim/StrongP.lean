import FondHtn.Upper.StrongDesc
import HtnComplexity.Article.NoHTNTORank
import HtnComplexity.Article.AcycRegNP
/-!
# Strong plan existence of primitive totally ordered problems is in P ([CB21, Cor. 4.8])

Strong LD plan existence reduces to deterministic plan existence class by class
(`FOND.redP_strongLD`).  For deterministic problems that are primitive and totally ordered the
only linearisation of `tn_I` lists the tasks by their rank (the number of predecessors,
`HTN.Article.NoHTNTO.linOf`), so solvability is the execution check of that one plan
(`HTN.Article.NoHTNTO.solvable_iff_execB`).  The library proves this problem to be in `L`
(Thm. 4.2.10); here we show directly that it is in `P`, by checking the certificate
`linOf p.tnI` of the NP verifier `HTN.Article.NoHTN.certB` together with the total-order test
`HTN.Article.toB` — `linOf` is computed in polynomial time (`FOND.PrimP.pt_linOf`).

* `FOND.noHTN_TO_inP` — `PlanEx (noHTN ∩ TO) ∈ P` (deterministic problems);
* **`FOND.strongLD_PRIM_TO_mem`** — `PlanExFM strongLD (PRIM ∩ TO) ∈ P`;
* **`FOND.strongOD_PRIM_TO_mem`** — `PlanExFM strongOD (PRIM ∩ TO) ∈ P` (strong OD = strong LD
  for totally ordered problems, [CB21, Prop. 2.15]).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN HTN.Article.NoHTNTO HTN.Logspace
  PTime

namespace PrimP

/-! ## The plan by ranks in polynomial time -/

theorem find?_getD_eq (f : ℕ → Bool) (l : List ℕ) (d : ℕ) :
    (l.find? f).getD d = (l.filter f ++ [d]).headI := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : f a <;> simp [h, ih]

theorem pt_rank : PT fun z : TnDesc × ℕ => rank z.1 z.2 := by
  unfold rank NoHTNTO.cnt
  have hids : PT fun z : TnDesc × ℕ => z.1.ids := PT.fst.comp PT.fst
  exact PT.length (PT.filter (PT.rangeLength hids)
    ((PT.elem (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.fst)))
      (PT.pair (PT.getI (hids.comp PT.fst) PT.snd) (PT.snd.comp PT.fst))).of_eq
        fun _ => by congr))

theorem pt_stepIdx : PT fun z : TnDesc × ℕ => stepIdx z.1 z.2 := by
  have hids : PT fun z : TnDesc × ℕ => z.1.ids := PT.fst.comp PT.fst
  have h : PT fun z : TnDesc × ℕ =>
      ((List.range z.1.ids.length).filter (fun i => rank z.1 (z.1.ids.getI i) == z.2) ++
        [z.1.ids.length]).headI :=
    PT.headI (PT.append (PT.filter (PT.rangeLength hids)
      (PT.beq (pt_rank.comp (PT.pair (PT.fst.comp PT.fst) (PT.getI (hids.comp PT.fst) PT.snd)))
        (PT.snd.comp PT.fst))) (PT.single (PT.length hids)))
  refine h.of_eq fun z => ?_
  unfold stepIdx firstIdx
  rw [find?_getD_eq]
  rfl

theorem pt_linOf : PT linOf := by
  unfold linOf stepId
  exact PT.map (PT.rangeLength PT.fst)
    (PT.getI (PT.fst.comp PT.fst) (pt_stepIdx.comp (PT.pair PT.fst PT.snd)))

/-! ## The decider -/

/-- **The decision procedure** for plan existence of primitive totally ordered deterministic
descriptions. -/
def decB (p : ProbDesc) : Bool := NoHTN.certB (p, linOf p.tnI) && toB p.tnI

theorem pt_decB : PT decB := by
  have htn : PT fun p : ProbDesc => p.tnI := PT.fst.comp (PT.snd.comp PT.snd)
  exact PT.and (pt_certB.comp (PT.pair PT.id (pt_linOf.comp htn))) (pt_toB.comp htn)

theorem decB_iff (p : ProbDesc) :
    decB p = true ↔ p.Valid ∧ (p.toProblem.IsNoHTN ∧ p.toProblem.IsTO) ∧ p.toProblem.Solvable := by
  unfold decB
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hc, hto⟩
    obtain ⟨hv, hn, hs⟩ := (iff_exists_cert p).2 ⟨_, hc⟩
    have htn : p.toProblem.IsTO_tnI := (toB_iff hv.tnI).1 hto
    exact ⟨hv, ⟨hn, htn, isTO_M_of_noHTN hn⟩, hs⟩
  · rintro ⟨hv, ⟨hn, hto, -⟩, hs⟩
    have hto' : TOL p.tnI := (isTO_tnI_iff hv).1 hto
    refine ⟨?_, (toB_iff hv.tnI).2 hto⟩
    have hprim : p.tnI.toTaskNetwork.IsPrimitive := hn
    simp only [NoHTN.certB, Bool.and_eq_true, validB_iff, noHTNB_iff]
    exact ⟨⟨⟨hv, hprim⟩, linB_linOf hv.tnI hto'⟩, (solvable_iff_execB hv hn hto').1 hs⟩

end PrimP

open PrimP in
/-- Plan existence of primitive totally ordered (deterministic) problems is in `P`. -/
theorem noHTN_TO_inP : Cx.P (PlanEx fun P => P.IsNoHTN ∧ P.IsTO) :=
  inP_codeLang (α := ProbDesc)
    (Q := fun p => p.Valid ∧ (p.toProblem.IsNoHTN ∧ p.toProblem.IsTO) ∧ p.toProblem.Solvable)
    pt_decB decB_iff

/-- **[CB21, Cor. 4.8], strong LD**: strong LD plan existence of primitive totally ordered
problems is in `P`. -/
theorem strongLD_PRIM_TO_mem : Cx.P (PlanExFM .strongLD (FClass.inter FClass.PRIM FClass.TO)) :=
  Cx.P.of_redP (redP_strongLD (sMatches_PRIM.inter sMatches_TO)) noHTN_TO_inP

/-- **[CB21, Cor. 4.8], strong OD**: strong OD plan existence of primitive totally ordered
problems is in `P`. -/
theorem strongOD_PRIM_TO_mem : Cx.P (PlanExFM .strongOD (FClass.inter FClass.PRIM FClass.TO)) := by
  rw [planExFM_strongOD_TO fun _ h => h.2]
  exact strongLD_PRIM_TO_mem

end FOND
