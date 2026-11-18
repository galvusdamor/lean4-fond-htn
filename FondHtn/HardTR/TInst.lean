import FondHtn.HardTR.TPlay
import FondHtn.HardTR.TClass
import FondHtn.HardTR.SrcTab
/-!
# CB22 Thm 5: the instance for a source machine

The symbols are the tableau symbols `CSym (Fin k) (Option Bool)` of a machine `M`; `cSym` codes
them injectively, `allSym` lists them; `opsOf no L` lists the operations that can be applicable,
`ensOf` all round ends.  **`FOND.HardTR.TI.red_iff`**: for the transducer parameters
`srcSpec M q x e` of the padded input, `x ∈ L` iff the description is strongly solvable.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

namespace TI

open TL TT TE TD HardMP HTN HTN.Syn ATM TM PTime

variable {k : ℕ}

/-! ## The symbols -/

/-- The code of a tableau symbol. -/
def cSym : NTM.CSym (Fin k) (Option Bool) → ℕ
  | (q, γ) => Nat.pair (match q with | none => 0 | some q => q.val + 1)
      (match γ with | none => 0 | some b => b.toNat + 1)

theorem cSym_inj : Function.Injective (cSym (k := k)) := by
  rintro ⟨q, γ⟩ ⟨q', γ'⟩ h
  simp only [cSym, Nat.pair_eq_pair] at h
  obtain ⟨h1, h2⟩ := h
  have hq : q = q' := by
    cases q <;> cases q' <;> simp_all [Fin.ext_iff]
  have hγ : γ = γ' := by
    rcases γ with _ | ⟨_ | _⟩ <;> rcases γ' with _ | ⟨_ | _⟩ <;>
      first | rfl | exact absurd h2 (by decide)
  rw [hq, hγ]

/-- All tableau symbols. -/
def allSym : List (NTM.CSym (Fin k) (Option Bool)) :=
  (none :: (List.finRange k).map some).flatMap fun q => [none, some false, some true].map fun γ => (q, γ)

theorem mem_allSym (s : NTM.CSym (Fin k) (Option Bool)) : s ∈ allSym (k := k) := by
  obtain ⟨q, γ⟩ := s
  simp only [allSym, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_finRange, true_and,
    List.not_mem_nil, or_false]
  refine ⟨q, by cases q <;> simp, ?_⟩
  rcases γ with _ | ⟨_ | _⟩ <;> simp

/-! ## The operations and the round ends -/

/-- The operations that can be applicable (`no` intervals, `L` special positions). -/
def opsOf (no L : ℕ) : List Op :=
  (none :: (List.range no).map some).flatMap (fun gs =>
      [false, true].flatMap fun b => [false, true].map fun w => Op.t gs b w) ++
    (none :: (List.range no).flatMap fun ℓ => (List.range L).map fun s => some (ℓ, s)).flatMap
      (fun sp => [false, true].flatMap fun dec => [false, true].flatMap fun b =>
        [false, true].map fun w => Op.i dec b w sp) ++
    [Op.bt false, Op.bt true, Op.bi false, Op.bi true]

/-- All round ends. -/
def ensOf {S : Type} (allS : List S) : List (En S) :=
  allS.map En.boot ++ [false, true].flatMap fun z => allS.flatMap fun l => allS.flatMap fun c =>
    allS.map fun r => En.norm z l c r

theorem mem_ensOf {S : Type} {allS : List S} (hall : ∀ s, s ∈ allS) (e : En S) :
    e ∈ ensOf allS := by
  cases e with
  | boot σ => simp [ensOf, hall]
  | norm z l c r =>
    simp only [ensOf, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false]
    exact Or.inr ⟨z, by cases z <;> simp, l, hall l, c, hall c, r, hall r, rfl⟩

theorem mem_opsOf {S : Type} {X : Spec S} {o : Op} {g : Ctl S} {b : Bool} {c : ℕ}
    (h : X.opOK o g b c) (hg : ∀ ℓ, g.gs = some ℓ → ℓ < X.no) : o ∈ opsOf X.no X.P.length := by
  have hb : ∀ x : Bool, x = false ∨ x = true := fun x => by cases x <;> simp
  cases o with
  | t gs b w =>
    simp only [opsOf, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false]
    refine Or.inl (Or.inl ⟨gs, ?_, b, hb b, w, hb w, rfl⟩)
    cases gs with
    | none => exact Or.inl rfl
    | some ℓ => exact Or.inr ⟨ℓ, (h.2.2.2.2 ℓ rfl).2.1, rfl⟩
  | i dec b w sp =>
    simp only [opsOf, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false]
    refine Or.inl (Or.inr ⟨sp, ?_, dec, hb dec, b, hb b, w, hb w, rfl⟩)
    rcases sp with _ | ⟨ℓ, s⟩
    · exact Or.inl rfl
    · obtain ⟨hgs, -, hs, -⟩ := h.2.2.2.2.2 ℓ s rfl
      exact Or.inr ⟨ℓ, hg ℓ hgs, s, hs, rfl⟩
  | bt w => cases w <;> simp [opsOf]
  | bi w => cases w <;> simp [opsOf]

/-! ## The intervals cover the indices -/

theorem cover_rowSpec {S : Type} {F : Option S → S → S → S} {row0 : ℕ → S} {acc : Set S}
    {e n p : ℕ} :
    ∀ i < 2 ^ ((rowSpec F row0 acc e n p).B + 1), ∃ ℓ < (rowSpec F row0 acc e n p).no,
      (rowSpec F row0 acc e n p).lo ℓ ≤ i ∧ i < (rowSpec F row0 acc e n p).hi ℓ := by
  intro i hi
  simp only [Spec.B, rowSpec] at hi ⊢
  have hA : 2 * n + 1 < rA n p := by unfold rA; have := Nat.one_le_two_pow (n := p); omega
  by_cases h1 : i ≤ 2 * n
  · exact ⟨i, by omega, by simp [rlo, show i ≤ 2 * n + 1 by omega],
      by simp [rhi, h1]⟩
  by_cases h2 : i < rA n p
  · exact ⟨2 * n + 1, by omega, by simp [rlo]; omega, by simp [rhi, h2]⟩
  · exact ⟨2 * n + 2, by omega, by simp [rlo]; omega, by simp [rhi]; omega⟩

/-! ## The reduction -/

variable (M : NTM (Fin k) (Option Bool)) (q e : Polynomial ℕ)

/-- The initial claim (any symbol). -/
def σI : NTM.CSym (Fin k) (Option Bool) := (none, none)

/-- **The reduction.** -/
noncomputable def red (x : List Bool) : FProbDesc :=
  desc cSym (srcSpec M q x e) allSym (opsOf (srcSpec M q x e).no (srcSpec M q x e).P.length)
    (ensOf allSym) σI

variable {M q e}

/-- **Correctness of the reduction.** -/
theorem red_iff {L : Cx.Language} (hb : M.blank = none)
    (hB : ∀ n, 2 ^ q.eval n + n + 3 ≤ 2 ^ e.eval n)
    (hL : ∀ x, L x ↔ ∃ i < 2 ^ 2 ^ e.eval x.length, ∃ qa ∈ M.accept, ∃ γ,
      TabWin M.F (row0 M q x) (2 ^ 2 ^ e.eval x.length - 1) i (some qa, γ)) (x : List Bool) :
    L x ↔ (red M q e x).toProblem.MPStrongSolvable := by
  have hX := srcSpec_valid (M := M) (q := q) (x := x) hb hB
  constructor
  · intro hx
    obtain ⟨i, hi, qa, hqa, γ, htab⟩ := (hL x).1 hx
    exact complete cSym_inj mem_allSym hX (cover_rowSpec)
      (fun o g b c h hg => mem_opsOf h hg) (fun e' _ _ => mem_ensOf mem_allSym e')
      (σ := (some qa, γ)) ⟨qa, hqa, γ, rfl⟩ hi htab
  · intro h
    exact src_sound hb hB (hL x) (sound cSym_inj mem_allSym hX h)

/-- **The reduction is tail-recursive.** -/
theorem red_TR (x : List Bool) : FClass.TR (red M q e x).toProblem := desc_TR

end TI

end HardTR

end FOND
