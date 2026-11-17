import FondHtn.HardMP.Bridge
import FondHtn.MPStrong.CyclicGame
/-!
# The fair progression game on sequences of task names

For problems whose methods are totally ordered, the nodes of a winning set `X` of the fair
progression game (`FOND.Problem.FairWin true`) are seen as label lists (`FOND.Problem.XL`).
A node of `X` with a non-empty list has a leftmost move all of whose successors are again in `X`
(`FOND.Problem.XL_step`), and a fair strong cyclic solution provides such a set containing the
initial list (`FOND.Problem.XL_init`).
-/

namespace FOND

open HTN HTN.TaskNetwork

namespace Problem

variable {F A C I : Type} [DecidableEq I] {P : Problem F A C I}

/-- Nodes of `X` seen as label lists. -/
def XL (X : NSet F A C I) (xs : List (A ⊕ C)) (s : Set F) : Prop :=
  ∃ (tn : TaskNetwork I A C) (l : List I), X tn s ∧ tn.IsSeqNet l xs

/-- **One leftmost move of the fair game on lists.** -/
theorem XL_step [Infinite I] (hP : P.WF) (hM : ∀ m ∈ P.methods, m.subtasks.IsTotallyOrdered)
    {X : NSet F A C I} (hX : NGood X) (hA : ∀ tn s, X tn s → ∃ n, P.FAttrH true X n tn s)
    {xs : List (A ⊕ C)} {s : Set F} (h : XL X xs s) (hne : xs ≠ []) :
    (∃ a xs', xs = Sum.inl a :: xs' ∧ (P.δ a).Applicable s ∧
        ∀ s' ∈ (P.δ a).outcomes s, XL X xs' s') ∨
    (∃ c bs xs', xs = Sum.inr c :: xs' ∧ P.SeqBodyF c bs ∧ XL X (bs ++ xs') s) := by
  obtain ⟨tn, l, hXt, hs⟩ := h
  obtain ⟨n, hn⟩ := hA tn s hXt
  cases hn with
  | goal he =>
    exfalso; apply hne
    have hl : l = [] := List.eq_nil_iff_forall_not_mem.2 fun z hz => by
      have := hs.mem_of_mem hz; rw [he] at this; simp at this
    have := hs.labels
    subst hl
    rw [← this]; rfl
  | @prim _ _ _ t a hu hα happ hall s₀ hs₀ _ =>
    left
    obtain ⟨l', rfl⟩ := eq_cons_of_unconstrained hs hu
    obtain rfl := hs.labels
    refine ⟨a, l'.map tn.α, by rw [List.map_cons, hα], happ, fun s' hs' => ?_⟩
    have hs2 : tn.IsSeqNet (t :: l') (tn.α t :: l'.map tn.α) := by simpa using hs
    exact ⟨_, l', hall s' hs', isSeqNet_progress hs2⟩
  | @decomp _ _ tn' _ t m hu hd hXt' _ =>
    right
    obtain ⟨l', rfl⟩ := eq_cons_of_unconstrained hs (hu rfl)
    obtain rfl := hs.labels
    obtain ⟨hm, htT, hα, tn'', hw'', hiso, hdisj, rfl⟩ := hd
    obtain ⟨lm₀, bs, hbody⟩ := exists_isSeqNet (hP.methods m hm) (hM m hm)
    obtain ⟨lm, hlm⟩ := hbody.iso hw'' hiso.symm
    have hs' : tn.IsSeqNet ([] ++ t :: l')
        ([] ++ Sum.inr m.abstractTask :: l'.map tn.α) := by
      have := hs; simpa [hα] using this
    have hnew := isSeqNet_decomposeWith hs' rfl hlm hdisj
    refine ⟨m.abstractTask, bs, l'.map tn.α, by rw [List.map_cons, hα],
      ⟨m, hm, rfl, Method.hasSeqBody_of_isSeqNet hbody⟩, _, lm ++ l', hXt', by simpa using hnew⟩

/-- **A fair strong cyclic solution gives a winning set containing the initial list.** -/
theorem XL_init [Infinite I] (hP : P.WF) {l : List I} {xs : List (A ⊕ C)}
    (h : P.tnI.IsSeqNet l xs) (hf : P.MPStrongCyclicFairSolvable) :
    ∃ X, NGood X ∧ (∀ tn s, X tn s → ∃ n, P.FAttrH true X n tn s) ∧ XL X xs P.init := by
  obtain ⟨X, hX, hXtn, hA⟩ := (mpStrongCyclicFairSolvable_iff_prog hP.tnI).1 hf
  exact ⟨X, hX, hA, P.tnI, l, hXtn, h⟩

end Problem

end FOND
