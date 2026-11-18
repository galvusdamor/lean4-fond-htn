import HtnComplexity.NPHard.TabCob
import HtnComplexity.NPHard.Stage4
/-!
# 3-Partition is NP-hard (in the strong sense)

**Main theorem** `HTN.NPHard.threePartitionNPHard : HTN.Syn.ThreePartitionNPHard`: every language
of `NP` reduces in polynomial time to the equal-sum partition problem with the numbers written in
unary, in exactly the form the table cells use (`HTN.Syn.ReducesToPartition`).

The reduction is the composite of three polynomial-time stages:

1. `stage1` (Cook–Levin): the input `x` is mapped to the token code of the tableau formula of
   the verifier on `x` (`VerTab.lean`, `StackCNF.lean`), written in polynomial time
   (`TabCob.lean`);
2. `stage2` (Garey–Johnson): satisfiability → 3-dimensional matching → unary equal-sum partition
   (`GJ.lean`, `FourPart.lean`, `Nums.lean`, `Stage2*.lean`);
3. `stage4`: the serialisation of the partition instance `partInst as B m` (`Stage4.lean`).
-/

namespace HTN.NPHard

open HTN.PTime HTN.PTime.CobhamTM HTN.PTime.CobhamTM.Prog HTN.Syn Merge

section

variable {f : Fn} (R : Realizer f) (k : ℕ)

/-- **The Cook–Levin stage**: the number of variables and the tokens of the tableau formula. -/
noncomputable def stage1 (x : List Bool) : List Bool :=
  unl ((verTab R k x).nV :: toks (verTab R k x).cnf)

theorem verTab_eq_tabF (x : List Bool) :
    verTab R k x = tabF (codeStep (vC R) (vN R)) (lab (vC R).length 0) 0 [Fin.last _]
      (stk (vN R) 2) true (pairPre x) (vB k x) (vT R k x)
      ((pairPre x).length + vB k x + vT R k x + 1) := rfl

theorem cobN_pow {g : Args → ℕ} (hg : CobN g) (n : ℕ) : CobN fun a => g a ^ n := by
  induction n with
  | zero => exact (cobN_const 1).of_eq fun _ => by simp
  | succ n ih => exact (cobN_mul ih hg).of_eq fun _ => by ring

theorem cobN_poly (p : Polynomial ℕ) {g : Args → ℕ} (hg : CobN g) : CobN fun a => p.eval (g a) := by
  obtain ⟨cnt, hcnt, hlen⟩ := exists_cobham_poly p
  exact (cobN_len (CobhamTM.cobham_c1 hcnt hg)).of_eq fun a => by simp [hlen]

theorem polyTimeFun_stage1 : PolyTimeFun (stage1 R k) := by
  have hx : CobN fun a : Args => (a.getD 0 []).length := cobN_arg 0
  have hpre : Cobham fun a : Args => pairPre (a.getD 0 []) :=
    cobham_appendConst (cobham_flatMapBits (fun b => [b, b]) (Cobham.proj 0)) _
  have hB : CobN fun a : Args => vB k (a.getD 0 []) := cobN_pow (cobN_add hx (cobN_const 1)) k
  have hT : CobN fun a : Args => vT R k (a.getD 0 []) :=
    cobN_poly _ (cobN_add (cobN_len hpre) hB)
  have hW : CobN fun a : Args => (pairPre (a.getD 0 [])).length + vB k (a.getD 0 []) +
      vT R k (a.getD 0 []) + 1 := cobN_add (cobN_add (cobN_add (cobN_len hpre) hB) hT)
    (cobN_const 1)
  have htoks := cobList_toks_tabF (codeStep (vC R) (vN R)) (lab (vC R).length 0) 0
    [Fin.last _] (stk (vN R) 2) true hpre hB hT hW
  have hnV : CobN fun a : Args => (verTab R k (a.getD 0 [])).nV := by
    simp only [Tab.nV, Tab.Z, verTab]
    exact cobN_mul (cobN_add hT (cobN_const 1)) (cobN_add (cobN_const _)
      (cobN_mul (cobN_mul (cobN_const _) hW) (cobN_const _)))
  exact PolyTimeFun.of_cobham (cobList_cons hnV htoks) fun x => rfl

/-- **The tableau formula is a yes instance of satisfiability exactly when the verifier accepts
some certificate**, and it meets the side conditions of the Garey–Johnson stage. -/
theorem verTab_props (x : List Bool) :
    1 ≤ (verTab R k x).nV ∧ (∀ c ∈ (verTab R k x).cnf, ∀ l ∈ c, l.1 < (verTab R k x).nV) ∧
      (∀ c ∈ (verTab R k x).cnf, c ≠ []) := by
  refine ⟨?_, Tab.cnf_vars_lt _ (by simp [verTab]), Tab.cnf_ne_nil _ (by simp [verTab])⟩
  simp only [Tab.nV, Tab.Z]
  have : 1 ≤ Ix.card (Fin ((vC R).length + 1)) := by
    show 1 ≤ (vC R).length + 1
    omega
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))

end

/-- **3-Partition (in the unary form used by the table cells) is NP-hard**: every language of
`NP` reduces to it in polynomial time. -/
theorem threePartitionNPHard : ThreePartitionNPHard := by
  rintro L ⟨V, k, hV, hL⟩
  obtain ⟨f, hf, hVf⟩ := hV.cobhamFun
  obtain ⟨R⟩ := nonempty_realizer hf
  refine ⟨fun x => stage4 (stage2 (stage1 R k x)),
    polyTimeFun_stage4.comp (polyTimeFun_stage2.comp (polyTimeFun_stage1 R k)), fun x => ?_⟩
  set n := (verTab R k x).nV
  set φ := (verTab R k x).cnf
  obtain ⟨hn, hv, hne⟩ := verTab_props R k x
  refine ⟨numsOf n φ, bigB (gjq n φ), (gj n φ).length, numsOf_pos n φ, ?_, ?_⟩
  · show stage4 (stage2 (unl (n :: toks φ))) = _
    rw [stage2_code, stage4_code]
  · rw [esp_numsOf_iff hn hv hne, satisfiable_verTab_iff, hL x]
    simp only [hVf]

end HTN.NPHard
