import FondHtn.MPStrong.Acyc
import FondHtn.MP.Fair
/-!
# Fair strong cyclic = strong for acyclic problems

For acyclic problems every execution is finite: each step of the execution structure (executing
a primitive task or decomposing *any* compound task) lowers the measure `FOND.MPS.mu` of
`FondHtn/MPStrong/Acyc.lean`.  Hence in a fair strong cyclic solution (Cimatti et al.: from every
reachable node a goal node is reachable, `FOND.Problem.IsMPStrongCyclicFairSolution`) the
reachable nodes win the strong AND/OR game `FOND.Problem.MPAndOr`
(`FOND.MPS.mpAndOr_of_fair_measure`), so fair strong cyclic solvability coincides with strong
solvability (`FOND.MPS.fair_iff_strong_ACYC`), and the languages agree for every class contained
in `ACYC` (`FOND.planExMPFair_eq_strong`).

* **`FOND.fairMP_ACYC_TO_mem`** — `PlanExMPFair (ACYC ∩ TO) ∈ EXPTIME` ([CB22, Thm. 1], strong
  cyclic in the fair reading);
* **`FOND.fairMP_ACYC_mem`** — `PlanExMPFair ACYC ∈ EXPSPACE` ([CB22, Thm. 2], fair reading);

with the inherited lower bounds (`FOND.fairMP_ACYC_TO_bounds`, `FOND.fairMP_ACYC_bounds`).
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article PTime MPS

namespace MPS

section Fair

variable {F F' : Type} {P : Problem F ℕ ℕ ℕ} {Q : HTN.Problem F' ℕ ℕ ℕ}

/-- In a fair strong cyclic solution, every reachable node with names reachable in `Q` wins the
strong AND/OR game, provided the measure `μ` of a stratification of `Q` is available. -/
theorem mpAndOr_of_fair_measure (hM : Q.methods = P.methods) {le : ℕ → ℕ → Prop}
    (hs : Q.IsStrat0 le) {f : ℕ → ℕ}
    (hf : ∀ c c', Q.ReachableName c → Q.ReachableName c' → (le c c' ↔ f c ≤ f c'))
    {mm : ℕ} (hmm : ∀ m, Q.ReachableMethod m → m.subtasks.T.card ≤ mm)
    {π : MPPolicy F ℕ ℕ ℕ} (hfair : P.IsMPStrongCyclicFairSolution π) :
    ∀ (N : ℕ) (x : MPNode F ℕ ℕ ℕ), mu mm f x.net ≤ N → P.MPReach π x →
      Q.NamesReachable x.net → P.MPAndOr x.net x.state := by
  intro N
  induction N with
  | zero =>
    intro x hN hx hn
    refine .empty ?_
    unfold mu at hN
    have : x.net.T.card = 0 := by omega
    exact Finset.card_eq_zero.1 this
  | succ N ih =>
    intro x hN hx hn
    obtain ⟨y, hxy, hy⟩ := hfair.2 x hx
    rcases Relation.ReflTransGen.cases_head hxy with rfl | ⟨x₁, hx₁, -⟩
    · exact .empty hy
    · cases hx₁ with
      | @prim t a s' hi hu hα happ hs' =>
        refine .prim hu hα happ fun s'' hs'' => ?_
        have hst := Problem.MPStep.prim hi hu hα happ hs''
        have hmu := mu_progress (mm := mm) (f := f) hu.1 hα
        exact ih _ (by simp only; omega) (hx.tail hst)
          fun z hz c hc => hn z (Finset.mem_of_mem_erase hz) c hc
      | @decomp t m tn' hi hd =>
        have hst := Problem.MPStep.decomp hi hd
        obtain ⟨hle, hn'⟩ := mu_decomp hM hs hf hmm hd hn
        exact .decomp hd (ih _ (by simp only; omega) (hx.tail hst) hn')

end Fair

/-- **For acyclic problems fair strong cyclic solvability is strong solvability.** -/
theorem fair_iff_strong_ACYC {p : FProbDesc} (hp : p.Valid) (hY : FClass.ACYC p.toProblem) :
    p.toProblem.MPStrongCyclicFairSolvable ↔ p.toProblem.MPStrongSolvable := by
  refine ⟨fun ⟨π, hπ⟩ => ?_, Problem.fair_of_mpStrongSolvable⟩
  set q := skDesc p with hqdef
  have hq := skDesc_valid hp
  have hac := (sameShape_skDesc p).isAcyclic.1 hY
  obtain ⟨R, rkL, hb, -, hRl, -, -, hnd, -, -, -⟩ := exists_acycCert hq hac
  have hh := ((acycB_iff q R rkL).1 hb).isACYC_h hnd hRl
  obtain ⟨le, hs, f, -, hf⟩ := hh
  have h := mpAndOr_of_fair_measure (Q := q.toProblem.toPos) (P := p.toProblem) rfl hs hf
    (meth_card_le q) hπ _ p.toProblem.mpInit le_rfl .refl
    (HTN.Problem.namesReachable_tnI q.toProblem.toPos)
  exact (Problem.mpStrongSolvable_iff_mpAndOr (FProbDesc.toProblem_wf hp)).2 h

end MPS

/-- For classes of acyclic problems the fair strong cyclic and the strong languages coincide. -/
theorem planExMPFair_eq_strong {Y : FClass} (hY : ∀ P, Y P → FClass.ACYC P) :
    PlanExMPFair Y = PlanExMP .strong Y := by
  funext w
  apply propext
  constructor
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy, (MPS.fair_iff_strong_ACYC hp (hY _ hy)).1 hs⟩
  · rintro ⟨p, rfl, hp, hy, hs⟩
    exact ⟨p, rfl, hp, hy, (MPS.fair_iff_strong_ACYC hp (hY _ hy)).2 hs⟩

/-- **[CB22, Thm. 1] for strong cyclic (fair reading), membership.** -/
theorem fairMP_ACYC_TO_mem : Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.ACYC FClass.TO)) := by
  rw [planExMPFair_eq_strong fun _ h => h.1]; exact strongMP_ACYC_TO_mem

/-- **[CB22, Thm. 2] for strong cyclic (fair reading), membership.** -/
theorem fairMP_ACYC_mem : Cx.EXPSPACE (PlanExMPFair FClass.ACYC) := by
  rw [planExMPFair_eq_strong fun _ h => h]; exact strongMP_ACYC_mem

theorem fairMP_ACYC_TO_bounds :
    Cx.EXPTIME (PlanExMPFair (FClass.inter FClass.ACYC FClass.TO)) ∧
      Cx.Hard Cx.PSPACE (PlanExMPFair (FClass.inter FClass.ACYC FClass.TO)) :=
  ⟨fairMP_ACYC_TO_mem, hardFair_ACYC_TO⟩

theorem fairMP_ACYC_bounds :
    Cx.EXPSPACE (PlanExMPFair FClass.ACYC) ∧ Cx.Hard Cx.NEXPTIME (PlanExMPFair FClass.ACYC) := by
  refine ⟨fairMP_ACYC_mem, ?_⟩
  rw [planExMPFair_eq_strong fun _ h => h]
  exact (strongMP_ACYC_bounds).2

end FOND
