import FondHtn.QBF.SavitchRun
import HtnComplexity.Article.StripsHard
import HtnComplexity.Article.Valid
/-!
# TQBF is PSPACE-hard

Savitch's construction (`FOND.QBF.Savitch.formula`) is computed in polynomial time
(`FOND.QBF.Savitch.pt_formula`), so

* **`FOND.QBF.strips_redP_tqbf`** — `PlanExSTRIPS ≤ₚ TQBF`;
* **`FOND.QBF.tqbf_pspaceHard`** — TQBF is PSPACE-hard (from Bylander's theorem
  `HTN.Article.strips_pspaceHard` of the library).

Ill-formed STRIPS descriptions (repeated action names) are mapped to the false QBF `([], [[]])`.
-/

namespace FOND

namespace QBF

namespace Savitch

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime

section PTLemmas

variable {α : Type} [BEnc α]

theorem pt_vv {w i : α → ℕ} (hw : PT w) (hi : PT i) : PT fun a => vv (w a) (i a) :=
  PT.natPair hw hi

theorem pt_exB {f : α → List ℕ} (hf : PT f) : PT fun a => exB (f a) :=
  PT.map hf (PT.pair (PT.const false) PT.snd)

theorem pt_guard {g : α → Lit} {cls : α → List Clause} (hg : PT g) (hc : PT cls) :
    PT fun a => guard (g a) (cls a) :=
  PT.map hc (PT.cons (hg.comp PT.fst) PT.snd)

theorem pt_eq2 {x y : α → ℕ} (hx : PT x) (hy : PT y) : PT fun a => eq2 (x a) (y a) := by
  unfold eq2
  exact PT.cons (PT.cons (PT.pair hx (PT.const false)) (PT.single (PT.pair hy (PT.const true))))
    (PT.single (PT.cons (PT.pair hx (PT.const true)) (PT.single (PT.pair hy (PT.const false)))))

theorem pt_allF : PT allF := by
  unfold allF
  have hA : PT fun d : StripsDesc => d.actions := PT.fst
  exact PT.dedup (PT.append (PT.append (PT.append (PT.fst.comp PT.snd)
    (PT.fst.comp (PT.snd.comp PT.snd))) (PT.snd.comp (PT.snd.comp PT.snd)))
    (PT.flatMap hA (PT.append (PT.append (PT.append (PT.fst.comp (PT.snd.comp PT.snd))
      (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd))))
      (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))
      (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd)))))))

theorem pt_rangeN {D : α → StripsDesc} (hD : PT D) : PT fun a => List.range (nF (D a)) :=
  PT.rangeLength (pt_allF.comp hD)

theorem pt_nF {D : α → StripsDesc} (hD : PT D) : PT fun a => nF (D a) :=
  PT.length (pt_allF.comp hD)

theorem pt_vars {D : α → StripsDesc} (hD : PT D) {w : α → ℕ} (hw : PT w) :
    PT fun a => vars (nF (D a)) (w a) :=
  PT.map (pt_rangeN hD) (pt_vv (hw.comp PT.fst) PT.snd)

theorem pt_eqs {D : α → StripsDesc} (hD : PT D) {U V : α → ℕ} (hU : PT U) (hV : PT V) :
    PT fun a => eqs (nF (D a)) (U a) (V a) :=
  PT.flatMap (pt_rangeN hD) (pt_eq2 (pt_vv (hU.comp PT.fst) PT.snd) (pt_vv (hV.comp PT.fst) PT.snd))

theorem pt_fI {D : α → StripsDesc} (hD : PT D) {i : α → ℕ} (hi : PT i) :
    PT fun a => fI (D a) (i a) :=
  PT.getI (pt_allF.comp hD) hi

end PTLemmas

/-! ## The parts -/

theorem steps_eq (d : StripsDesc) (K : ℕ) : ∀ c r,
    steps d K r c = (List.range c).flatMap fun t => stepPre d K (r + t) := by
  intro c
  induction c with
  | zero => intro r; rfl
  | succ c ih =>
    intro r
    rw [steps, ih, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [add_zero]
    congr 1
    exact List.flatMap_congr fun t _ => by rw [Nat.add_assoc, Nat.add_comm 1 t]

theorem stepsCl_eq (d : StripsDesc) (K : ℕ) : ∀ c r,
    stepsCl d K r c = (List.range c).flatMap fun t => stepCl d K (r + t) := by
  intro c
  induction c with
  | zero => intro r; rfl
  | succ c ih =>
    intro r
    rw [stepsCl, ih, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [add_zero]
    congr 1
    exact List.flatMap_congr fun t _ => by rw [Nat.add_assoc, Nat.add_comm 1 t]

/-- Triples `(d, K, r)`. -/
abbrev SvT3 : Type := StripsDesc × ℕ × ℕ

theorem pt_stepPre : PT fun x : SvT3 => stepPre x.1 x.2.1 x.2.2 := by
  have hD : PT fun x : SvT3 => x.1 := PT.fst
  have hK : PT fun x : SvT3 => x.2.1 := PT.fst.comp PT.snd
  have hr : PT fun x : SvT3 => x.2.2 := PT.snd.comp PT.snd
  unfold stepPre bV
  exact PT.append (pt_exB (pt_vars hD (PT.affine 3 2 hr))) (PT.cons
    (PT.pair (PT.const true) (pt_vv (PT.affine 3 2 hK) hr))
    (PT.append (pt_exB (pt_vars hD (PT.affine 3 3 hr))) (pt_exB (pt_vars hD (PT.affine 3 4 hr)))))

theorem pt_stepCl : PT fun x : SvT3 => stepCl x.1 x.2.1 x.2.2 := by
  have hD : PT fun x : SvT3 => x.1 := PT.fst
  have hK : PT fun x : SvT3 => x.2.1 := PT.fst.comp PT.snd
  have hr : PT fun x : SvT3 => x.2.2 := PT.snd.comp PT.snd
  have hb : PT fun x : SvT3 => bV x.2.1 x.2.2 := pt_vv (PT.affine 3 2 hK) hr
  have h0 : PT fun x : SvT3 => 3 * x.2.2 := (PT.affine 3 0 hr).of_eq fun _ => by ring
  unfold stepCl
  exact PT.append
    (pt_guard (PT.pair hb (PT.const true)) (PT.append (pt_eqs hD (PT.affine 3 3 hr) h0)
      (pt_eqs hD (PT.affine 3 4 hr) (PT.affine 3 2 hr))))
    (pt_guard (PT.pair hb (PT.const false)) (PT.append (pt_eqs hD (PT.affine 3 3 hr)
      (PT.affine 3 2 hr)) (pt_eqs hD (PT.affine 3 4 hr) (PT.affine 3 1 hr))))

theorem pt_rangeA1 : PT fun d : StripsDesc => List.range (nA d + 1) :=
  (PT.rangeLength (PT.cons (PT.const ((0, [], [], [], []) : ActDesc)) PT.fst)).of_eq
    fun d => by simp [nA, StripsDesc.actions]

theorem pt_basePre : PT fun d : StripsDesc => basePre d (nF d) := by
  unfold basePre cV
  exact pt_exB (PT.map pt_rangeA1 (pt_vv (PT.affine 3 3 (pt_nF PT.fst)) PT.snd))

/-- Quadruples `(d, a, X, Y)`. -/
abbrev SvT4 : Type := StripsDesc × ActDesc × ℕ × ℕ

theorem pt_actBody : PT fun x : SvT4 => actBody x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  unfold actBody
  -- on pairs `(x, i)`
  have hD : PT fun y : SvT4 × ℕ => y.1.1 := PT.fst.comp PT.fst
  have ha : PT fun y : SvT4 × ℕ => y.1.2.1 := PT.fst.comp (PT.snd.comp PT.fst)
  have hX : PT fun y : SvT4 × ℕ => vv y.1.2.2.1 y.2 :=
    pt_vv (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))) PT.snd
  have hY : PT fun y : SvT4 × ℕ => vv y.1.2.2.2 y.2 :=
    pt_vv (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))) PT.snd
  have hf : PT fun y : SvT4 × ℕ => (allF y.1.1).getI y.2 := pt_fI hD PT.snd
  have hpre : PT fun y : SvT4 × ℕ => y.1.2.1.2.1 := PT.fst.comp (PT.snd.comp ha)
  have hpreN : PT fun y : SvT4 × ℕ => y.1.2.1.2.2.1 := PT.fst.comp (PT.snd.comp (PT.snd.comp ha))
  have hadd : PT fun y : SvT4 × ℕ => y.1.2.1.2.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp ha)))
  have hdel : PT fun y : SvT4 × ℕ => y.1.2.1.2.2.2.2 :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp ha)))
  refine PT.flatMap (pt_rangeN PT.fst) (PT.append (PT.append ?_ ?_) ?_)
  · exact PT.ite (PT.elem hpre hf) (PT.single (PT.single (PT.pair hX (PT.const true)))) PT.nil
  · exact PT.ite (PT.elem hpreN hf) (PT.single (PT.single (PT.pair hX (PT.const false)))) PT.nil
  · exact PT.ite (PT.elem hadd hf) (PT.single (PT.single (PT.pair hY (PT.const true))))
      (PT.ite (PT.elem hdel hf) (PT.single (PT.single (PT.pair hY (PT.const false))))
        (pt_eq2 hX hY))

theorem pt_cV {α : Type} [BEnc α] {K j : α → ℕ} (hK : PT K) (hj : PT j) :
    PT fun a => cV (K a) (j a) :=
  pt_vv (PT.affine 3 3 hK) hj

theorem pt_baseCl : PT fun d : StripsDesc => baseCl d (nF d) := by
  have hK : PT fun d : StripsDesc => nF d := pt_nF PT.id
  have h0 : PT fun d : StripsDesc => 3 * nF d := (PT.affine 3 0 hK).of_eq fun _ => by ring
  have h1 : PT fun d : StripsDesc => 3 * nF d + 1 := PT.affine 3 1 hK
  have p1 : PT fun d : StripsDesc => [(List.range (nA d + 1)).map fun j => (cV (nF d) j, true)] :=
    PT.single (PT.map pt_rangeA1 (PT.pair (pt_cV (hK.comp PT.fst) PT.snd) (PT.const true)))
  have p2 : PT fun d : StripsDesc =>
      guard (cV (nF d) 0, false) (eqs (nF d) (3 * nF d) (3 * nF d + 1)) :=
    pt_guard (PT.pair (pt_cV hK (PT.const 0)) (PT.const false)) (pt_eqs PT.id h0 h1)
  have hA : PT fun d : StripsDesc => List.range (nA d) := PT.rangeLength PT.fst
  have ha : PT fun y : StripsDesc × ℕ => y.1.actions.getI y.2 :=
    PT.getI (PT.fst.comp PT.fst) PT.snd
  have h0' : PT fun y : StripsDesc × ℕ => 3 * nF y.1 := h0.comp PT.fst
  have h1' : PT fun y : StripsDesc × ℕ => 3 * nF y.1 + 1 := h1.comp PT.fst
  have hg : PT fun y : StripsDesc × ℕ =>
      ((y.1, y.1.actions.getI y.2, 3 * nF y.1, 3 * nF y.1 + 1) : SvT4) :=
    PT.pair PT.fst (PT.pair ha (PT.pair h0' h1'))
  have hbody : PT fun y : StripsDesc × ℕ =>
      actBody y.1 (y.1.actions.getI y.2) (3 * nF y.1) (3 * nF y.1 + 1) := by
    have := pt_actBody.comp hg
    exact this
  have hK' : PT fun y : StripsDesc × ℕ => nF y.1 := hK.comp PT.fst
  have hc : PT fun y : StripsDesc × ℕ => ((cV (nF y.1) (y.2 + 1), false) : Lit) :=
    PT.pair (pt_cV hK' (PT.succ PT.snd)) (PT.const false)
  have hgd : PT fun y : StripsDesc × ℕ => guard (cV (nF y.1) (y.2 + 1), false)
      (actBody y.1 (y.1.actions.getI y.2) (3 * nF y.1) (3 * nF y.1 + 1)) := pt_guard hc hbody
  have p3 : PT fun d : StripsDesc => (List.range (nA d)).flatMap fun j =>
      guard (cV (nF d) (j + 1), false) (actBody d (d.actions.getI j) (3 * nF d) (3 * nF d + 1)) :=
    PT.flatMap hA hgd
  have := PT.append (PT.append p1 p2) p3
  exact this

theorem pt_initCl : PT initCl := by
  unfold initCl
  have hf : PT fun y : StripsDesc × ℕ => (allF y.1).getI y.2 := pt_fI PT.fst PT.snd
  refine PT.flatMap (pt_rangeN PT.id) (PT.append (PT.append ?_ ?_) ?_)
  · exact PT.single (PT.single (PT.pair (pt_vv (PT.const 0) PT.snd)
      (PT.elem (PT.fst.comp (PT.snd.comp PT.fst)) hf)))
  · exact PT.ite (PT.elem (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))) hf)
      (PT.single (PT.single (PT.pair (pt_vv (PT.const 1) PT.snd) (PT.const true)))) PT.nil
  · exact PT.ite (PT.elem (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))) hf)
      (PT.single (PT.single (PT.pair (pt_vv (PT.const 1) PT.snd) (PT.const false)))) PT.nil

/-- **Savitch's construction is computed in polynomial time.** -/
theorem pt_formula : PT formula := by
  have hK : PT fun d : StripsDesc => nF d := pt_nF PT.id
  have hK' : PT fun y : StripsDesc × ℕ => nF y.1 := hK.comp PT.fst
  have ht : PT fun y : StripsDesc × ℕ => 0 + y.2 := PT.add (PT.const 0) PT.snd
  have hx : PT fun y : StripsDesc × ℕ => ((y.1, nF y.1, 0 + y.2) : SvT3) :=
    PT.pair PT.fst (PT.pair hK' ht)
  have hsp : PT fun y : StripsDesc × ℕ => stepPre y.1 (nF y.1) (0 + y.2) := by
    have := pt_stepPre.comp hx
    exact this
  have hsc : PT fun y : StripsDesc × ℕ => stepCl y.1 (nF y.1) (0 + y.2) := by
    have := pt_stepCl.comp hx
    exact this
  have hR : PT fun d : StripsDesc => List.range (nF d) := pt_rangeN PT.id
  have q1 : PT fun d : StripsDesc => (List.range (nF d)).flatMap fun t => stepPre d (nF d) (0 + t) :=
    PT.flatMap hR hsp
  have q2 : PT fun d : StripsDesc => (List.range (nF d)).flatMap fun t => stepCl d (nF d) (0 + t) :=
    PT.flatMap hR hsc
  have e0 : PT fun d : StripsDesc => exB (vars (nF d) 0) := pt_exB (pt_vars PT.id (PT.const 0))
  have e1 : PT fun d : StripsDesc => exB (vars (nF d) 1) := pt_exB (pt_vars PT.id (PT.const 1))
  refine (PT.pair (PT.append e0 (PT.append e1 (PT.append q1 pt_basePre)))
    (PT.append pt_initCl (PT.append q2 pt_baseCl))).of_eq fun d => ?_
  rw [formula, steps_eq, stepsCl_eq]

/-! ## The reduction -/

/-- The false QBF. -/
def falseQBF : Formula := ([], [[]])

theorem not_holds_falseQBF : ¬ Holds falseQBF := by
  simp [Holds, falseQBF, Sat]

/-- **The reduction**: Savitch's formula for well-formed descriptions. -/
def red (d : StripsDesc) : Formula :=
  if nodupB (d.actions.map ActDesc.name) = true then formula d else falseQBF

theorem pt_red : PT red := by
  unfold red
  exact PT.ite (PT.eq (pt_nodupB (PT.map PT.fst (PT.fst.comp PT.snd))) (PT.const true)) pt_formula
    (PT.const _)

theorem red_iff (d : StripsDesc) : d.Valid ∧ d.Solvable ↔ Holds (red d) := by
  unfold red
  split_ifs with h
  · have hv : d.Valid := (nodupB_iff _).1 h
    rw [holds_formula_iff_solvable d hv]
    exact ⟨fun h => h.2, fun h' => ⟨hv, h'⟩⟩
  · have hv : ¬ d.Valid := fun hv => h ((nodupB_iff _).2 hv)
    exact ⟨fun h' => absurd h'.1 hv, fun h' => absurd h' not_holds_falseQBF⟩

end Savitch

open Savitch

/-- **STRIPS plan existence reduces to TQBF** (Savitch's construction). -/
theorem strips_redP_tqbf : HTN.Cx.RedP HTN.Article.PlanExSTRIPS TQBF :=
  HTN.Syn.PolyDom.redP_codeLang (α := HTN.Article.StripsDesc) (β := Formula)
    (Q := fun d => d.Valid ∧ d.Solvable) (R := Holds) pt_red red_iff falseQBF not_holds_falseQBF

/-- **TQBF is PSPACE-hard.** -/
theorem tqbf_pspaceHard : HTN.Cx.Hard HTN.Cx.PSPACE TQBF :=
  HTN.Article.strips_pspaceHard.of_redP strips_redP_tqbf

end QBF

end FOND
