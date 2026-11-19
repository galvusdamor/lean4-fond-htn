import FondHtn.TOHard2.FGame
import FondHtn.MPStrong.CyclicGame
import FondHtn.HardMP.Bridge
/-!
# From fair policies of a compiled grammar to its fair list game

**`FOND.TOHard2.fair_compile`**: if the compiled description of a grammar has a fair strong
cyclic solution, then the root lies in a fair set of the grammar's list game (target: all
configurations).  The fair set consists of the grammar positions whose sequence network lies in
the set of the progression fair game (`FOND.Problem.mpStrongCyclicFairSolvable_iff_prog`); the
attractor ranks of the network game bound those of the list game.
-/

namespace FOND

namespace TOHard2

open HTN HTN.TaskNetwork HTN.Article HTN.Syn HardMP Problem

section FBridge

variable {G : Gram} {init : List ℕ} {root : List (Bool × ℕ)} (hG : G.Good)
  (hv : (compile G init root).Valid)

/-- The grammar positions whose sequence network lies in the network fair set `X`. -/
def YB (X : NSet ℕ ℕ ℕ ℕ) : List (Bool × ℕ) → Cfg → Prop :=
  fun xs c => ∃ tn l, X tn c.enc ∧ tn.IsSeqNet l (xs.map (toLab ∘ symL))

include hG hv

theorem fa_of_fattr (X : NSet ℕ ℕ ℕ ℕ) : ∀ n (tn : TaskNetwork ℕ ℕ ℕ) (c : Cfg) (l : List ℕ)
    (xs : List (Bool × ℕ)), (compile G init root).toProblem.FAttrH true X n tn c.enc →
      tn.IsSeqNet l (xs.map (toLab ∘ symL)) → FA G Set.univ (YB X) n xs c := by
  have hP := FProbDesc.toProblem_wf hv
  have hM := methods_TO' (seqMeths_compile (G := G) init root)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro tn c l xs h hs
  generalize hsc : c.enc = s at h
  cases h with
  | goal he =>
    have hl : l = [] := List.eq_nil_iff_forall_not_mem.2 fun z hz => by
      have := hs.mem_of_mem hz; rw [he] at this; simp at this
    subst hl
    have := hs.labels
    simp only [List.map_nil] at this
    rw [List.map_eq_nil_iff.1 this.symm]
    exact .nil trivial
  | prim hu hα happ hall hs₀ h =>
    exfalso
    obtain ⟨l', rfl⟩ := eq_cons_of_unconstrained hs hu
    have hlab := hs.labels
    rcases xs with _ | ⟨q, xs⟩
    · simp at hlab
    simp only [List.map_cons, List.cons.injEq, Function.comp_apply, lab_symL] at hlab
    rw [hα] at hlab
    exact absurd hlab.1 (by simp)
  | @decomp n tn tn' s t m hu hd hX h' =>
    obtain ⟨l', rfl⟩ := eq_cons_of_unconstrained hs (hu rfl)
    have hlab := hs.labels
    rcases xs with _ | ⟨q, xs⟩
    · simp at hlab
    simp only [List.map_cons, List.cons.injEq, Function.comp_apply, lab_symL] at hlab
    obtain ⟨hm, htT, hαt, tn'', hw'', hiso, hdisj, rfl⟩ := hd
    obtain ⟨lm₀, bs, hbody⟩ := exists_isSeqNet (hP.methods m hm) (hM m hm)
    obtain ⟨lm, hlm⟩ := hbody.iso hw'' hiso.symm
    have hs' : tn.IsSeqNet ([] ++ t :: l') ([] ++ Sum.inr m.abstractTask :: xs.map (toLab ∘ symL)) := by
      have := hs
      rw [List.map_cons, Function.comp_apply, lab_symL, ← hlab.1, hαt] at this
      simpa using this
    have hnew := isSeqNet_decomposeWith hs' rfl hlm hdisj
    simp only [List.nil_append] at hnew
    have hb : (compile G init root).toProblem.SeqBodyF m.abstractTask bs :=
      ⟨m, hm, rfl, Method.hasSeqBody_of_isSeqNet hbody⟩
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff (seqMeths_compile init root)).1 hb
    have hab : m.abstractTask = 2 * q.2 + q.1.toNat := by
      rw [hαt] at hlab; simpa using hlab.1
    rw [hab] at hls
    obtain ⟨b, mq⟩ := q
    rcases meth_mem_compile.1 hls with ⟨p, hp, alt, halt, he, rfl⟩ | ⟨q', hq', he, rfl⟩
    · -- an instruction: the single action follows
      obtain rfl : b = false := by cases b <;> simp at he ⊢; omega
      obtain rfl : mq = p.1 := by simp at he; omega
      simp only [List.map_cons, List.map_nil, toLab, Bool.false_eq_true, if_false,
        List.singleton_append] at hnew
      subst hsc
      generalize hsc' : c.enc = s' at h'
      cases h' with
      | goal he' =>
        exfalso
        have hl := hnew.labels
        obtain ⟨x, hx⟩ : ∃ x, x ∈ lm ++ l' := by
          rcases hlm' : lm ++ l' with _ | ⟨x, r⟩
          · rw [hlm'] at hl; simp at hl
          · exact ⟨x, by simp⟩
        have := hnew.mem_of_mem hx
        rw [he'] at this; simp at this
      | @decomp n₂ _ tn₂ _ t₂ m₂ hu₂ hd₂ =>
        exfalso
        obtain ⟨l₂, hl₂⟩ := eq_cons_of_unconstrained hnew (hu₂ rfl)
        have hlab₂ := hnew.labels
        rw [hl₂] at hlab₂
        simp only [List.map_cons, List.cons.injEq] at hlab₂
        obtain ⟨-, -, hα₂, -⟩ := hd₂
        rw [hlab₂.1] at hα₂
        exact absurd hα₂ (by simp)
      | @prim n₂ _ _ t₂ a₂ hu₂ hα₂ happ₂ hall₂ s₀ hs₀ h₂ =>
        obtain ⟨l₂, hl₂⟩ := eq_cons_of_unconstrained hnew hu₂
        have hnew' := hnew
        rw [hl₂] at hnew'
        have hlab₂ := hnew'.labels
        simp only [List.map_cons, List.cons.injEq] at hlab₂
        rw [hα₂] at hlab₂
        obtain rfl : a₂ = Nat.pair p.1 alt := by simpa using hlab₂.1
        have hwf := (hG.spec p hp _ (getI_memS halt)).1
        rw [← hsc', δ_compile hv hp halt, applicable_enc] at happ₂
        have hout := outcomes_enc (Nat.pair p.1 alt) hwf happ₂
        rw [← hsc', δ_compile hv hp halt, hout] at hall₂ hs₀
        obtain ⟨c₀, hc₀, rfl⟩ := hs₀
        have hprog := isSeqNet_progress hnew'
        have ih' := ih n₂ (by omega) _ c₀ _ xs h₂ hprog
        refine (FA.ins hp (getI_memS halt) happ₂ (fun c' hc' => ?_) hc₀ ih').mono (by omega)
        exact ⟨_, _, hall₂ _ ⟨c', hc', rfl⟩, hprog⟩
    · -- a nonterminal
      obtain rfl : b = true := by cases b <;> simp at he ⊢; omega
      obtain rfl : mq = q'.1 := by simp at he; omega
      have hlab' : (q'.2.map symL).map toLab ++ xs.map (toLab ∘ symL) =
          (q'.2 ++ xs).map (toLab ∘ symL) := by simp [List.map_map]
      rw [hlab'] at hnew
      subst hsc
      exact .comp hq' ⟨_, _, hX, hnew⟩ (ih n (by omega) _ c _ _ h' hnew)

/-- **Fair solutions of a compiled grammar give its fair list game.** -/
theorem fair_compile {c₀ : Cfg} (hinit : {f | f ∈ init} = c₀.enc)
    (h : (compile G init root).toProblem.MPStrongCyclicFairSolvable) :
    ∃ Y, FSet G Set.univ Y ∧ Y root c₀ := by
  have hP := FProbDesc.toProblem_wf hv
  obtain ⟨X, -, hX0, hXa⟩ := (mpStrongCyclicFairSolvable_iff_prog hP.tnI).1 h
  refine ⟨YB X, fun xs c ⟨tn, l, hX, hs⟩ => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hXa tn c.enc hX
    exact ⟨n, fa_of_fattr hG hv X n tn c l xs hn hs⟩
  · have h1 : (compile G init root).toProblem.init = c₀.enc := hinit
    have h2 : (compile G init root).toProblem.tnI = (seqTn (root.map symL)).toTaskNetwork := rfl
    have h3 := isSeqNet_seqTn (root.map symL)
    rw [List.map_map] at h3
    exact ⟨_, _, h1 ▸ hX0, h2 ▸ h3⟩

end FBridge

end TOHard2

end FOND
