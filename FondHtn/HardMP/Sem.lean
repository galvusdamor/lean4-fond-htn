import FondHtn.HardMP.Desc
/-!
# The list game on the compiled programs

For a description `D` whose actions are `acts P` and whose methods are the chain methods of the
programs `P` (with exit `ex`) plus methods of other (non-program) tasks, the list game on a
program state `cN r pc` is the weakest precondition of the rest of program `r`, followed by the
exit (`FOND.HardMP.chain_sound`, `FOND.HardMP.chain_complete`).
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## Sequence networks of descriptions -/

theorem isSeqNet_seqTn (ls : List (Bool × ℕ)) :
    (seqTn ls).toTaskNetwork.IsSeqNet (List.range ls.length) (ls.map toLab) := by
  have h := TaskNetwork.isSeqNet_of_pairwise_ord (TnDesc.toTaskNetwork_wf (seqTn ls))
    (List.nodup_range) (fun t => by simp [TnDesc.toTaskNetwork, seqTn_ids])
    (List.pairwise_lt_range.imp_of_mem fun {a b} _ hb hab =>
      ord_seqTn_iff.2 ⟨hab, List.mem_range.1 hb⟩)
  have hl : (List.range ls.length).map (seqTn ls).toTaskNetwork.α = ls.map toLab :=
    map_label_range_seqTn ls
  rwa [hl] at h

theorem hasSeqBody_meth_iff {c : ℕ} {ls : List (Bool × ℕ)} {bs : List (ℕ ⊕ ℕ)} :
    (meth c ls).toMethod.HasSeqBody bs ↔ bs = ls.map toLab :=
  Method.hasSeqBody_iff_of_isSeqNet (isSeqNet_seqTn ls)

/-- The bodies of a description all of whose methods are sequence methods. -/
theorem seqBodyF_iff {D : FProbDesc} (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls) {c : ℕ}
    {bs : List (ℕ ⊕ ℕ)} :
    D.toProblem.SeqBodyF c bs ↔ ∃ ls, meth c ls ∈ D.methods ∧ bs = ls.map toLab := by
  constructor
  · rintro ⟨m, ⟨e, he, rfl⟩, hc, hb⟩
    obtain ⟨c', ls, rfl⟩ := hmeth e he
    obtain rfl : c' = c := hc
    exact ⟨ls, he, hasSeqBody_meth_iff.1 hb⟩
  · rintro ⟨ls, he, rfl⟩
    exact ⟨_, ⟨_, he, rfl⟩, rfl, hasSeqBody_meth_iff.2 rfl⟩

/-! ## Actions on encoded configurations -/

section Acts

variable {P : List (List (List ASpec))} {D : FProbDesc} (hv : D.Valid) (hA : D.actions = acts P)
include hv hA

theorem δ_aN {r pc alt : ℕ} (hr : r < P.length) (hpc : pc < (P.getI r).length)
    (halt : alt < ((P.getI r).getI pc).length) :
    D.toProblem.δ (aN r pc alt) = (toFAct (aN r pc alt) (((P.getI r).getI pc).getI alt)).toAction := by
  have hm : toFAct (aN r pc alt) (((P.getI r).getI pc).getI alt) ∈ D.actions := by
    rw [hA]
    refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨r, List.mem_range.2 hr,
      List.mem_flatMap.2 ⟨pc, List.mem_range.2 hpc, List.mem_map.2 ⟨alt, List.mem_range.2 halt,
        rfl⟩⟩⟩)
  exact FProbDesc.δ_of_mem hv hm

theorem δ_finN : D.toProblem.δ finN = (toFAct finN finSpec).toAction := by
  have hm : toFAct finN finSpec ∈ D.actions := by rw [hA]; exact List.mem_cons_self ..
  exact FProbDesc.δ_of_mem hv hm

/-- The game on a leading action of the programs. -/
theorem lrunH_aN {r pc alt : ℕ} (hr : r < P.length) (hpc : pc < (P.getI r).length)
    (halt : alt < ((P.getI r).getI pc).length) (hwf : (((P.getI r).getI pc).getI alt).WF)
    {n : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)} :
    D.toProblem.LRunH (n + 1) (Sum.inl (aN r pc alt) :: xs) c.enc Φ ↔
      (((P.getI r).getI pc).getI alt).App c ∧
        ∀ c' ∈ (((P.getI r).getI pc).getI alt).Out c, D.toProblem.LRunH n xs c'.enc Φ := by
  rw [Problem.lrunH_prim_iff, δ_aN hv hA hr hpc halt, applicable_enc]
  refine and_congr_right fun happ => ?_
  rw [outcomes_enc _ hwf happ]
  simp only [Set.mem_image, forall_exists_index, and_imp]
  exact ⟨fun h c' hc' => h _ c' hc' rfl, fun h _ c' hc' he => he ▸ h c' hc'⟩

theorem lrunH_finN {n : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)} :
    D.toProblem.LRunH (n + 1) (Sum.inl finN :: xs) c.enc Φ ↔
      c.val fDone = true ∧ D.toProblem.LRunH n xs c.enc Φ := by
  have hwf : finSpec.WF := by simp [finSpec, ASpec.WF, ASpec.cnew]
  rw [Problem.lrunH_prim_iff, δ_finN hv hA, applicable_enc]
  have happ : finSpec.App c ↔ c.val fDone = true := by
    simp [finSpec, ASpec.App, ASpec.pre, ASpec.neg, ASpec.cpre]
  rw [happ]
  refine and_congr_right fun hd => ?_
  rw [outcomes_enc _ hwf ((happ).2 hd)]
  have : finSpec.Out c = {c} := by
    ext c'
    simp [ASpec.Out, finSpec, ASpec.effs, noeff, eff_nil']
  rw [this, Set.image_singleton]
  simp

end Acts

/-! ## The methods of the program states -/

theorem getI_memS {α : Type} [Inhabited α] {l : List α} {i : ℕ} (h : i < l.length) :
    l.getI i ∈ l := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem exists_getI_of_mem {α : Type} [Inhabited α] {l : List α} {a : α} (h : a ∈ l) :
    ∃ i < l.length, l.getI i = a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hi]⟩

theorem seqTn_injective : Function.Injective seqTn := by
  intro l l' h
  have hl : ∀ ls : List (Bool × ℕ), (seqTn ls).lbl.map (fun q => q.2) = ls := by
    intro ls
    simp only [seqTn, TnDesc.lbl, List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getI_eq_getElem _ h2]
  rw [← hl l, ← hl l', h]

@[simp] theorem meth_injS {c c' : ℕ} {ls ls' : List (Bool × ℕ)} :
    meth c ls = meth c' ls' ↔ c = c' ∧ ls = ls' := by
  unfold meth
  rw [Prod.mk.injEq, seqTn_injective.eq_iff]

@[simp] theorem cN_inj {r pc r' pc' : ℕ} : cN r pc = cN r' pc' ↔ r = r' ∧ pc = pc' := by
  unfold cN
  constructor
  · intro h
    have : Nat.pair r pc = Nat.pair r' pc' := by omega
    exact Nat.pair_eq_pair.1 this
  · rintro ⟨rfl, rfl⟩; rfl

theorem mem_chainMethsS {P : List (List (List ASpec))} {ex : List (Bool × ℕ)} {c : ℕ}
    {ls : List (Bool × ℕ)} :
    meth c ls ∈ chainMeths P ex ↔ ∃ r < P.length,
      (∃ pc < (P.getI r).length, ∃ alt < ((P.getI r).getI pc).length,
        c = cN r pc ∧ ls = [(false, aN r pc alt), (true, cN r (pc + 1))]) ∨
      (c = cN r (P.getI r).length ∧ ls = ex) := by
  simp only [chainMeths, List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map,
    List.mem_singleton, meth_injS]
  constructor
  · rintro ⟨r, hr, ⟨pc, hpc, alt, halt, h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨r, hr, Or.inl ⟨pc, hpc, alt, halt, h1.symm, h2.symm⟩⟩
    · exact ⟨r, hr, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨r, hr, ⟨pc, hpc, alt, halt, h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨r, hr, Or.inl ⟨pc, hpc, alt, halt, h1.symm, h2.symm⟩⟩
    · exact ⟨r, hr, Or.inr ⟨h1, h2⟩⟩

section Chain

variable {P : List (List (List ASpec))} {ex : List (Bool × ℕ)} {D : FProbDesc} {O : List MethodDesc}
  (hv : D.Valid) (hA : D.actions = acts P) (hM : D.methods = chainMeths P ex ++ O)
  (hO : ∀ e ∈ O, ∀ r pc, e.1 ≠ cN r pc) (hmeth : ∀ e ∈ D.methods, ∃ c ls, e = meth c ls)
  (hspec : ∀ r < P.length, ∀ pc < (P.getI r).length, ∀ alt < ((P.getI r).getI pc).length,
    (((P.getI r).getI pc).getI alt).WF)
include hv hA hM hO hmeth hspec

omit hv hA hmeth hspec in
theorem meth_cN_mem {r pc : ℕ} {ls : List (Bool × ℕ)} :
    meth (cN r pc) ls ∈ D.methods ↔ meth (cN r pc) ls ∈ chainMeths P ex := by
  rw [hM, List.mem_append]
  exact ⟨fun h => h.resolve_right fun h' => hO _ h' r pc rfl, Or.inl⟩

/-- **The game on a program state**, soundness. -/
theorem chain_sound {r : ℕ} (hr : r < P.length) : ∀ (k pc : ℕ), (P.getI r).length = pc + k →
    ∀ {n : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)},
      D.toProblem.LRunH n (Sum.inr (cN r pc) :: xs) c.enc Φ →
      c ∈ wpP ((P.getI r).drop pc) {c' | D.toProblem.LRunH n (ex.map toLab ++ xs) c'.enc Φ} := by
  intro k
  induction k with
  | zero =>
    intro pc hpc n xs c Φ h
    rw [List.drop_eq_nil_of_le (by omega), wpP_nil]
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
    obtain ⟨r', hr', ⟨pc', hpc', alt, -, he, -⟩ | ⟨he, rfl⟩⟩ :=
      mem_chainMethsS.1 ((meth_cN_mem hM hO).1 hls)
    · obtain ⟨rfl, rfl⟩ := cN_inj.1 he; omega
    · exact h.mono (by omega) le_rfl
  | succ k ih =>
    intro pc hpc n xs c Φ h
    have hpcl : pc < (P.getI r).length := by omega
    rw [List.drop_eq_getElem_cons hpcl, wpP_cons]
    rcases n with _ | n
    · exact absurd h Problem.not_lrunH_zero_cons
    obtain ⟨bs, hb, h⟩ := Problem.lrunH_comp_iff.1 h
    obtain ⟨ls, hls, rfl⟩ := (seqBodyF_iff hmeth).1 hb
    obtain ⟨r', hr', ⟨pc', hpc', alt, halt, he, rfl⟩ | ⟨he, -⟩⟩ :=
      mem_chainMethsS.1 ((meth_cN_mem hM hO).1 hls)
    · obtain ⟨rfl, rfl⟩ := cN_inj.1 he
      rcases n with _ | n
      · exact absurd h Problem.not_lrunH_zero_cons
      simp only [List.map_cons, List.map_nil, toLab, if_false, if_true, List.cons_append,
        List.nil_append, Bool.false_eq_true] at h
      obtain ⟨happ, hall⟩ := (lrunH_aN hv hA hr hpcl halt (hspec _ hr _ hpcl _ halt)).1 h
      have hgi : (P.getI r)[pc] = (P.getI r).getI pc := (List.getI_eq_getElem _ hpcl).symm
      rw [hgi]
      refine ⟨_, getI_memS halt, happ, fun c' hc' => ?_⟩
      exact wpP_mono _ (fun c'' hc'' => Problem.LRunH.mono hc'' (by omega) le_rfl)
        (ih (pc + 1) (by omega) (hall c' hc'))
    · obtain ⟨rfl, rfl⟩ := cN_inj.1 he; omega

/-- **The game on a program state**, completeness. -/
theorem chain_complete {r : ℕ} (hr : r < P.length) : ∀ (k pc : ℕ), (P.getI r).length = pc + k →
    ∀ {m : ℕ} {xs : List (ℕ ⊕ ℕ)} {c : Cfg} {Φ : Set (Set ℕ)},
      c ∈ wpP ((P.getI r).drop pc) {c' | D.toProblem.LRunH m (ex.map toLab ++ xs) c'.enc Φ} →
      D.toProblem.LRunH (m + 2 * k + 1) (Sum.inr (cN r pc) :: xs) c.enc Φ := by
  intro k
  induction k with
  | zero =>
    intro pc hpc m xs c Φ h
    rw [List.drop_eq_nil_of_le (by omega), wpP_nil] at h
    refine .comp ((seqBodyF_iff hmeth).2 ⟨ex, (meth_cN_mem hM hO).2
      (mem_chainMethsS.2 ⟨r, hr, Or.inr ⟨by rw [hpc]; rfl, rfl⟩⟩), rfl⟩) ?_
    simpa using h
  | succ k ih =>
    intro pc hpc m xs c Φ h
    have hpcl : pc < (P.getI r).length := by omega
    have hgi : (P.getI r)[pc] = (P.getI r).getI pc := (List.getI_eq_getElem _ hpcl).symm
    rw [List.drop_eq_getElem_cons hpcl, wpP_cons, hgi] at h
    obtain ⟨a, ha, happ, hall⟩ := h
    obtain ⟨alt, halt, rfl⟩ := exists_getI_of_mem ha
    refine .comp ((seqBodyF_iff hmeth).2 ⟨_, (meth_cN_mem hM hO).2
      (mem_chainMethsS.2 ⟨r, hr, Or.inl ⟨pc, hpcl, alt, halt, rfl, rfl⟩⟩), rfl⟩) ?_
    rw [show m + 2 * (k + 1) = (m + 2 * k + 1) + 1 by omega]
    simp only [List.map_cons, List.map_nil, toLab, if_false, if_true, List.cons_append,
      List.nil_append, Bool.false_eq_true]
    exact (lrunH_aN hv hA hr hpcl halt (hspec _ hr _ hpcl _ halt)).2
      ⟨happ, fun c' hc' => ih (pc + 1) (by omega) (hall c' hc')⟩

end Chain

end HardMP

end FOND
