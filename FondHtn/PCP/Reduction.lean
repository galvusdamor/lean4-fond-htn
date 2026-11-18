import FondHtn.PCP.Correct
/-!
# Undecidability of strong OD plan existence for regular, tail-recursive problems

The reduction maps the input `n` of the halting problem to `desc undecTSM Xu [0] (redStack n)`
(`HTN.Undec.undecTSM_halts_iff`), where the fixed alphabet `Xu` contains all symbols of the
stacks `redStack n`. Then the description depends on `n` only through the first method of
chain `A` (`FOND.PCP.desc_eq_descR`), so it is computable (`FOND.PCP.primrec_descR`).

**`FOND.PCP.undecidable_strongOD_REG_TR`**: `PlanExFM .strongOD (REG ∩ TR)` is undecidable.
-/

namespace FOND

namespace PCP

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Undec HTN.Undec.Sim HTN.Undec.TMChain
  Turing.PartrecToTM2 AcycHard

/-! ## The alphabet does not depend on the stacks -/

theorem dedup_append_of_subset {l₁ l₂ : List ℕ} (h : ∀ a ∈ l₁, a ∈ l₂) :
    (l₁ ++ l₂).dedup = l₂.dedup := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    rw [List.cons_append, List.dedup_cons_of_mem
      (List.mem_append_right _ (h a (List.mem_cons_self ..)))]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

variable {M : TSM} {X s₁ s₂ : List ℕ}

theorem syms_of_subset (h : ∀ a ∈ s₁ ++ s₂, a ∈ X) : syms M X s₁ s₂ = syms M X [] [] := by
  unfold syms
  rw [show ∀ T : List ℕ, s₁ ++ s₂ ++ X ++ T = (s₁ ++ s₂) ++ (X ++ T) from fun T => by simp,
    dedup_append_of_subset (fun a ha => List.mem_append_left _ (h a ha))]
  simp

theorem chars_of_subset (h : ∀ a ∈ s₁ ++ s₂, a ∈ X) : chars M X s₁ s₂ = chars M X [] [] := by
  unfold chars; rw [syms_of_subset h]

theorem actions_of_subset (h : ∀ a ∈ s₁ ++ s₂, a ∈ X) :
    actions M X s₁ s₂ = actions M X [] [] := by
  unfold actions letters actCheat; rw [chars_of_subset h]

/-- The names of the first method of chain `A`. -/
def xs0 (M : TSM) (s₁ s₂ : List ℕ) : List ℕ :=
  nInit :: (only2 (encC (c₀ M s₁ s₂) ++ [Ch.sep])).map nA

/-- The description, with the part that does not depend on the stacks computed at `[]`. -/
def descR (M : TSM) (X s₁ s₂ : List ℕ) : FProbDesc :=
  ((actions M X [] [], (0, chainTn (xs0 M s₁ s₂) (some 1)) :: (methods M X [] []).tail),
    ([], tnI))

theorem desc_eq_descR (h : ∀ a ∈ s₁ ++ s₂, a ∈ X) : desc M X s₁ s₂ = descR M X s₁ s₂ := by
  have ht : triples M X s₁ s₂ = (0, xs0 M s₁ s₂, some 1) :: (triples M X [] []).tail := by
    unfold triples; rw [chars_of_subset h, syms_of_subset h]; rfl
  simp only [desc, descR, actions_of_subset h, methods, ht, List.map_cons, List.map_tail]

/-! ## Computability -/

/-- The name of the letter `(·, c)` of `A`, for a character code `k = codeC c`. -/
def gA (k : ℕ) : ℕ := Nat.pair 5 (Nat.pair 0 (k + 1))

theorem xs0_eq (M : TSM) (s₁ s₂ : List ℕ) : xs0 M s₁ s₂ =
    0 :: (s₁.reverse.map (fun a => gA (3 * a)) ++ [gA (3 * M.start + 1)] ++
      s₂.map (fun a => gA (3 * a)) ++ [gA 2]) := by
  simp [xs0, only2, encC, c₀, nA, codeL, codeO, codeC, gA, nInit, List.map_append,
    Function.comp_def]

theorem primrec_gA : Primrec gA :=
  Primrec₂.natPair.comp (Primrec.const 5)
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.succ)

theorem primrec_xs0 (M : TSM) (s₁ : List ℕ) : Primrec fun s₂ => xs0 M s₁ s₂ := by
  have hg : Primrec fun a : ℕ => gA (3 * a) :=
    primrec_gA.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
  refine (Primrec.list_cons.comp (Primrec.const 0) ?_).of_eq fun s₂ => (xs0_eq M s₁ s₂).symm
  refine Primrec.list_append.comp (Primrec.list_append.comp (Primrec.const _) ?_) (Primrec.const _)
  exact Primrec.list_map Primrec.id (hg.comp Primrec.snd).to₂

theorem primrec_ltPairs : Primrec ltPairs := by
  have hinner : Primrec₂ fun (p : ℕ × ℕ) (j : ℕ) =>
      (if p.2 < j then some (p.2, j) else none : Option (ℕ × ℕ)) :=
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))
      (Primrec.const none)).to₂
  have hmid : Primrec₂ fun (n i : ℕ) =>
      (List.range n).filterMap fun j => (if i < j then some (i, j) else none : Option (ℕ × ℕ)) :=
    (Primrec.listFilterMap (Primrec.list_range.comp Primrec.fst) hinner).to₂
  unfold ltPairs
  exact Primrec.list_flatMap Primrec.list_range hmid

theorem primrec_chainTn : Primrec fun xs : List ℕ => chainTn xs (some 1) := by
  have hn : Primrec fun xs : List ℕ => xs.length + 1 := Primrec.succ.comp Primrec.list_length
  have hlab : Primrec fun xs : List ℕ =>
      (List.range xs.length).map (fun i => (i, false, xs.getD i 0)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
      (Primrec.pair Primrec.snd (Primrec.pair (Primrec.const false)
        (Primrec.list_getD 0 |>.comp Primrec.fst Primrec.snd))).to₂
  refine (Primrec.pair (Primrec.list_range.comp hn) (Primrec.pair (primrec_ltPairs.comp hn)
    (Primrec.list_append.comp hlab (Primrec.list_cons.comp (Primrec.pair Primrec.list_length
      (Primrec.const (true, 1))) (Primrec.const []))))).of_eq fun xs => ?_
  simp [chainTn]

theorem primrec_descR (M : TSM) (X s₁ : List ℕ) : Primrec fun s₂ => descR M X s₁ s₂ := by
  unfold descR
  refine Primrec.pair (Primrec.pair (Primrec.const _) (Primrec.list_cons.comp
    (Primrec.pair (Primrec.const 0) (primrec_chainTn.comp (primrec_xs0 M s₁))) (Primrec.const _)))
    (Primrec.const _)

/-! ## The reduction -/

/-- All tape symbols of the stacks `redStack n`. -/
noncomputable def Xu : List ℕ :=
  symCode ((true, TMChain.cell Γ'.cons) : TMChain.Gam1) :: 0 ::
    [Γ'.consₗ, Γ'.cons, Γ'.bit0, Γ'.bit1].map gcode

theorem redStack_sub (n : ℕ) : ∀ a ∈ [0] ++ redStack n, a ∈ Xu := by
  intro a ha
  simp only [redStack, List.singleton_append, List.mem_cons, List.mem_append, List.mem_reverse,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | ha | rfl
  · simp [Xu]
  · simp [Xu]
  · simp only [TMChain.digs, List.mem_map] at ha
    obtain ⟨γ, -, rfl⟩ := ha
    cases γ <;> simp [Xu]
  · simp [Xu]

/-- **The reduction.** -/
noncomputable def red (n : ℕ) : FProbDesc := desc undecTSM Xu [0] (redStack n)

theorem red_iff (n : ℕ) :
    PlanExFM .strongOD (FClass.inter FClass.REG FClass.TR) (enc (red n)) ↔
      undecTSM.Halts [0] (redStack n) := by
  rw [planExFM_enc_iff]
  simp only [FMCrit.Solvable, red]
  rw [strongOD_iff]
  refine ⟨fun h => h.2.2.to_reflTransGen, fun h => ⟨desc_valid, ⟨isREG, isTailREC⟩, ?_⟩⟩
  rcases (Relation.reflTransGen_iff_eq_or_transGen).1 h with h | h
  · exact absurd (congrArg Cfg.s1 h) (by simp)
  · exact h

theorem primrec_red : Primrec fun n => enc (red n) := by
  refine (primrec_enc_fprobDesc.comp ((primrec_descR undecTSM Xu [0]).comp
    primrec_redStack)).of_eq fun n => ?_
  rw [red, desc_eq_descR (redStack_sub n)]

/-- **Strong OD plan existence is undecidable for regular, tail-recursive problems** (the
repaired [CB21, Thm. 3.3]; `doc/notes_pcp_check.md`). -/
theorem undecidable_strongOD_REG_TR :
    ¬ Cx.Decidable (PlanExFM .strongOD (FClass.inter FClass.REG FClass.TR)) := by
  intro hdec
  obtain ⟨f, hf, hfeq⟩ := ComputablePred.computable_iff.1 hdec
  refine ComputablePred.halting_problem 0 ?_
  refine ComputablePred.computable_iff.2
    ⟨fun c : Nat.Partrec.Code => f (enc (red (Encodable.encode c))), ?_, ?_⟩
  · exact hf.comp (primrec_red.comp Primrec.encode).to_comp
  · funext c
    have hu := undecTSM_halts_iff (Encodable.encode c)
    rw [univFun, Denumerable.ofNat_encode] at hu
    have h2 := congrFun hfeq (enc (red (Encodable.encode c)))
    simp only [eq_iff_iff] at h2 ⊢
    rw [← hu, ← red_iff, h2]

end PCP

end FOND
