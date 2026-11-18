import HtnComplexity.TrVerify.ReprN
import HtnComplexity.AcVerify.Complete
import HtnComplexity.Computable.TrDecideCell
/-!
# Short path witnesses for tail-recursive problems

The path witnesses of `HtnComplexity/AcVerify/` certify plan existence for **every**
described problem (`HTN.Syn.AcVer.PathOK`); acyclicity was only used to bound their size.  This
file bounds them for tail-recursive descriptions instead:

* `HTN.Syn.TrVer.exists_solution_RN_of_tailRec` — a solvable tail-recursive problem has a solution
  network reached by at most `R = (allCfgs d q (trBnd d q)).length` decomposition steps: the
  progression search has a short solving run (`HTN.Syn.exists_short_ppath`, with the invariant
  `HTN.Syn.TrInv` of tail recursion), and a run of `R` steps decomposes at most `R` times
  (`HTN.Problem.exists_solution_RN_of_stepN`);
* `HTN.Syn.TrVer.exists_pathOK_of_RN` — a solution network reached by at most `k` decomposition
  steps has a path witness whose paths have at most `k + 1` steps and which has at most
  `|ids| + k · |d| + k` entries.
-/

namespace HTN

namespace Syn

namespace TrVer

open AcVer Problem

variable {d : DomDesc} {q : InstDesc}

/-! ### From a run of the search of descriptions to a counted semantic run -/

theorem stepN_of_ppath : ∀ (cs : List PConfig) (c : PConfig) (j : ℕ) (π : List ℕ),
    PNet.Ok c.2 → PPath d c cs →
    (problem d q).StepN j (problem d q).initNode ⟨{f | f ∈ c.1}, PNet.toTN c.2, π⟩ →
    ∃ π', (problem d q).StepN (j + cs.length) (problem d q).initNode
      ⟨{f | f ∈ (endOf c cs).1}, PNet.toTN (endOf c cs).2, π'⟩
  | [], _, _, π, _, _, h => ⟨π, by simpa using h⟩
  | x :: xs, c, j, π, hok, hp, h => by
    obtain ⟨π', hs⟩ := step_of_pStep (q := q) hok hp.1 π
    obtain ⟨π'', h'⟩ := stepN_of_ppath xs x (j + 1) π' (ok_of_pStep hok hp.1) hp.2 ⟨_, h, hs⟩
    refine ⟨π'', ?_⟩
    have : j + (x :: xs).length = j + 1 + xs.length := by simp; omega
    rw [this]
    simpa using h'

theorem initNode_eq (d : DomDesc) (q : InstDesc) :
    (⟨{f | f ∈ (initConfig q).1}, PNet.toTN (initConfig q).2, []⟩ : SearchNode ℕ ℕ ℕ ℕ) =
      (problem d q).initNode := by
  rw [toTN_initConfig]
  rfl

theorem isGoalNode_of_isGoalB {c : PConfig} (π : List ℕ) (hg : isGoalB q c = true) :
    (problem d q).IsGoalNode ⟨{f | f ∈ c.1}, PNet.toTN c.2, π⟩ := by
  constructor
  · simp only [isGoalB, Bool.and_eq_true, List.isEmpty_iff] at hg
    show (PNet.toTN c.2).T = ∅
    rw [PNet.toTN_T, hg.1]
    rfl
  · simp only [isGoalB, Bool.and_eq_true, List.all_eq_true] at hg
    intro f hf
    have := hg.2 f (by simpa using hf)
    simpa using memB_iff.1 this

/-- The number of normal forms of configurations of the tail-recursive search. -/
noncomputable def trRounds (d : DomDesc) (q : InstDesc) : ℕ := (allCfgs d q (trBnd d q)).length

/-- **A solvable tail-recursive problem has a solution reached by few decompositions.** -/
theorem exists_solution_RN_of_tailRec (hd : d.IsTailRec) (h : Solvable d q) :
    ∃ tn₀, (problem d q).RN (trRounds d q) tn₀ ∧ tn₀.IsPrimitive ∧
      (problem d q).Executable tn₀ := by
  obtain ⟨c, hr, hg⟩ := exists_pReach_of_solvable h
  obtain ⟨cs, hcs, hend⟩ := exists_ppath_of_pReach hr
  obtain ⟨cs', hcs', hlen, hg'⟩ :=
    exists_short_ppath (P := TrInv d q) (fun h => h.toCfgInv) (fun hc hs => hc.step hd hs)
      cs.length cs _ le_rfl (trInv_initConfig d q) hcs (by rw [hend]; exact hg)
  have h0 : (problem d q).StepN 0 (problem d q).initNode
      ⟨{f | f ∈ (initConfig q).1}, PNet.toTN (initConfig q).2, []⟩ := (initNode_eq d q).symm
  obtain ⟨π', hrun⟩ := stepN_of_ppath (q := q) cs' (initConfig q) 0 [] (ok_initConfig q) hcs' h0
  obtain ⟨tn₀, hR, hprim, hex⟩ :=
    exists_solution_RN_of_stepN (problem_wf d q) hrun (isGoalNode_of_isGoalB π' hg')
  exact ⟨tn₀, hR.mono (by simpa using hlen), hprim, hex⟩

/-! ### The witness of a counted decomposition -/

theorem card_T_tnI_le : (problem d q).tnI.T.card ≤ q.tnI.ids.length := by
  show q.tnI.toTaskNetwork.T.card ≤ _
  simpa [TnDesc.toTaskNetwork] using List.toFinset_card_le q.tnI.ids

theorem card_T_decompStep_le {tn tn₂ : TaskNetwork ℕ ℕ ℕ} {t : ℕ} {m : Method ℕ ℕ ℕ}
    (hstep : DecompStep (problem d q).methods tn t m tn₂) :
    tn₂.T.card ≤ tn.T.card + d.size := by
  obtain ⟨⟨e, he, rfl⟩, ht, hαt, tn', hwf', ⟨σ, hbij, hσord, hσα⟩, hdisj, rfl⟩ := hstep
  have h1 : tn'.T.card ≤ e.2.ids.length := by
    have himg : tn'.T.image σ ⊆ e.2.ids.toFinset := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
      have := hbij.mapsTo (by simpa using hu)
      simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using this
    have hinj : Set.InjOn σ tn'.T := fun u hu u' hu' h => hbij.injOn hu hu' h
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card himg).trans (List.toFinset_card_le _)
  have h2 : e.2.ids.length ≤ d.size := by
    have h3 := List.le_sum_of_mem (List.mem_map_of_mem (f := MethodDesc.size) he)
    have h4 : e.2.ids.length ≤ e.size := by simp only [MethodDesc.size, TnDesc.size]; omega
    unfold DomDesc.size
    omega
  simp only [decomposeWith]
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_erase_le (s := tn.T) (a := t)
  omega

/-- **The counted invariant**: after `j` decomposition steps, the paths have at most `j + 1`
steps, there are at most `j` empty leaves and at most `|ids| + j · |d|` tasks. -/
theorem exists_inv_of_decompN : ∀ {j : ℕ} {tn : TaskNetwork ℕ ℕ ℕ},
    DecompN (problem d q).methods j (problem d q).tnI tn →
    ∃ f E, Inv d q tn f E ∧ (∀ u ∈ tn.T, (f u).length ≤ j + 1) ∧ (∀ e ∈ E, e.length ≤ j + 1) ∧
      E.length ≤ j ∧ tn.T.card ≤ q.tnI.ids.length + j * d.size
  | 0, tn, h => by
    subst h
    refine ⟨_, _, inv_init, by simp, by simp, by simp, by simpa using card_T_tnI_le (d := d) (q := q)⟩
  | j + 1, tn, ⟨b, hb, t, m, hs⟩ => by
    obtain ⟨f, E, hI, hf, hE, hEl, hc⟩ := exists_inv_of_decompN hb
    obtain ⟨f₂, E₂, hI₂, hf₂, hE₂, hE₂l⟩ := hI.stepB hs
    have hft : (f t).length ≤ j + 1 := hf t hs.2.1
    refine ⟨f₂, E₂, hI₂, fun u hu => ?_, fun e he => ?_, by omega, ?_⟩
    · rcases hf₂ u hu with ⟨hu', he⟩ | he
      · rw [he]; have := hf u hu'; omega
      · omega
    · rcases hE₂ e he with he' | he'
      · have := hE e he'; omega
      · omega
    · have := card_T_decompStep_le hs
      rw [Nat.add_mul, one_mul]
      omega

/-- **A solution reached by at most `k` decompositions has a small path witness.** -/
theorem exists_pathOK_of_RN {k : ℕ} {tn : TaskNetwork ℕ ℕ ℕ} (hR : (problem d q).RN k tn)
    (hprim : tn.IsPrimitive) (hex : (problem d q).Executable tn) :
    ∃ W, PathOK d q W ∧ (∀ u ∈ W, u.2 = true → ∃ p k, u.1 = p ++ [(k, 0)]) ∧
      (∀ u ∈ W, u.1.length ≤ k + 1) ∧ W.length ≤ q.tnI.ids.length + k * d.size + k := by
  obtain ⟨j, hj, hd⟩ := hR
  obtain ⟨f, E, hI, hf, hE, hEl, hc⟩ := exists_inv_of_decompN hd
  obtain ⟨l, as, hlin, has, happ, hgoal⟩ := hex
  obtain ⟨hW, h0⟩ := pathOK_witnessOf hI hprim hlin has happ hgoal
  refine ⟨_, hW, h0, fun u hu => ?_, ?_⟩
  · simp only [witnessOf, List.mem_append, List.mem_map] at hu
    rcases hu with ⟨t, ht, rfl⟩ | ⟨e, he, rfl⟩
    · have := hf t ((hlin.2.1 t).1 ht); simpa using this.trans (by omega)
    · have := hE e he; simpa using this.trans (by omega)
  · have hll : l.length = tn.T.card := by
      rw [← List.toFinset_card_of_nodup hlin.1]
      congr 1
      ext x
      simpa using hlin.2.1 x
    have hjk : j * d.size ≤ k * d.size := Nat.mul_le_mul_right _ hj
    simp only [witnessOf, List.length_append, List.length_map]
    omega

end TrVer

end Syn

end HTN
