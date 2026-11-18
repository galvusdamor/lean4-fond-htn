import HtnComplexity.Hypotheses.ExpSpace
import HtnComplexity.Computable.TMRenderGen
import HtnComplexity.Complexity.PosFamily
import HtnComplexity.Computable.Guard
import ComplexityTheory.Complexity.CobhamTable
import ComplexityTheory.Complexity.CobhamExamples
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# The source side of cells 3 and 5: `NEXPTIME`-hardness of `HTN-AC-1` and `HTN-TR-1`

This file proves `HTN.Space.NExpHardSourceNU codingSer S` for the acyclic and the tail-recursive
rooted classes: for every language of `NEXPTIME` (`HTN.Space.InNExp`, clocked nondeterministic
machines with an exponential time bound) there is a hardness family whose instance map is
polynomial time and whose domain descriptions, one per input length, are of polynomial size.

The family is the re-split construction of Theorem 4.3.7 of Bercher et al., as written down in
`HtnComplexity/Computable/TMRenderGen.lean`, applied to the normalised machine
`HTN.TMEnc.homingMachine N` with the time bound `2 · 2 ^ (p(n) + n) + 1`.  Two choices make the
instance map polynomial time:

* the input facts are numbered as in the positional encoding of
  `HtnComplexity/Complexity/PosFamily.lean` (`HTN.Space.posNum`), and the initial state fact
  of the machine gets the number `0`; so the instance description of a word `w` is
  `guardInst (0 :: posFacts w)` (`HTN.Space.famInstDescG_posNum`), whose serialisation is a
  constant followed by the serialisation of the positional encoding;
* the compound task `sI` gets the number `0` (`HTN.Space.eCs`), so that the initial task network is
  the one of `guardInst`.

The empty word is handled separately, by a guard domain that is solvable exactly when the empty
word is in the language.

## Main results

* `HTN.Space.nexpFamily` — the family, in `HTN-AC-1`;
* `HTN.Space.nexpHardSourceNU_HTN_AC_root`, `HTN.Space.nexpHardSourceNU_HTN_TR_root` — the source
  side of cells 5 and 3;
* `HTN.Space.cellEff_HTN_AC_to_TO_HTN_of_scale`, `HTN.Space.cellEff_HTN_TR_to_TO_HTN_of_scale`
  — cells 5 and 3 for any scale whose `Σ₁` level is inside `NEXPTIME`, with the source side
  discharged.
-/

namespace HTN

namespace Space

open scoped Classical

open Syn Syn.Coded Hier Table TM TMEnc TMEnc.Fam PTime

/-! ### Polynomial time: prepending a constant -/

theorem polyTimeFun_prependConst (C : List Bool) {F : List Bool → List Bool}
    (hF : PolyTimeFun F) : PolyTimeFun (fun w => C ++ F w) := by
  have h := polyTimeFun_reverse.comp ((polyTimeFun_appendConst C.reverse).comp
    (polyTimeFun_reverse.comp hF))
  refine (show (fun w => ((F w).reverse ++ C.reverse).reverse) = (fun w => C ++ F w) from ?_) ▸ h
  funext w
  simp

/-! ### The numberings -/

variable {k : ℕ}

/-- The numbering of the states of the normalised machine. -/
def hq : Fin k ⊕ Bool → ℕ := Encodable.encode

/-- The numbering of the symbols of the normalised machine. -/
def hg : TapeSym × Bool → ℕ := Encodable.encode

theorem hq_injective : Function.Injective (hq (k := k)) := Encodable.encode_injective

theorem hg_injective : Function.Injective hg := Encodable.encode_injective

/-- **The positional numbering of the facts** for the inputs of length `n`: the input fact of the
`i`-th bit of a word, correctly marked, is the fact `posFact (n - 1 - i) b` of the positional
encoding; the initial state fact of the normalised machine is `0`; every other fact is shifted
above all of these. -/
def posNum (N : NTM (Fin k) TapeSym) (n : ℕ) : GFact (Fin k ⊕ Bool) (TapeSym × Bool) → ℕ
  | Sum.inl (i, (some b, m)) =>
      if i < n ∧ m = decide (i = 0) then posFact (n - 1 - i) b
      else 2 * n + 2 + encGFact (hq (k := k)) hg (Sum.inl (i, (some b, m)))
  | Sum.inl (i, (none, m)) => 2 * n + 2 + encGFact (hq (k := k)) hg (Sum.inl (i, (none, m)))
  | Sum.inr f =>
      if f = TMFact.st (Sum.inl N.init) then 0 else 2 * n + 2 + encGFact (hq (k := k)) hg (Sum.inr f)

theorem posNum_injective (N : NTM (Fin k) TapeSym) (n : ℕ) :
    Function.Injective (posNum N n) := by
  have henc := encGFact_injective (hq_injective (k := k)) hg_injective
  intro x y h
  rcases x with ⟨i, ⟨_ | b, m⟩⟩ | f <;> rcases y with ⟨j, ⟨_ | c, m'⟩⟩ | f' <;>
    simp only [posNum] at h
  all_goals (try split_ifs at h with h1 h2) <;> (try simp only [posFact] at h)
  all_goals first
    | exact henc (by omega)
    | (exfalso; split_ifs at h <;> omega)
    | rw [h1, h2]
    | (obtain ⟨hi, rfl⟩ := h1
       obtain ⟨hj, rfl⟩ := h2
       have hij : i = j := by split_ifs at h <;> omega
       subst hij
       cases b <;> cases c <;> simp at h ⊢)

/-- The numbering of the compound tasks: `encTMTask`, with `sI` and `0` exchanged. -/
def eCs (t : TMTask (Fin k ⊕ Bool) (TapeSym × Bool)) : ℕ := Equiv.swap 0 19 (encTMTask hg t)

theorem eCs_injective : Function.Injective (eCs (k := k)) :=
  (Equiv.swap 0 19).injective.comp (encTMTask_injective hg_injective)

/-! ### The instance map -/

/-- **The instance description of a word**: the positional facts of the word, the fact `0`, and
the single compound task `0`. -/
def hardInst (w : List Bool) : InstDesc := guardInst (0 :: posFacts w)

theorem posFacts_eq_range (w : List Bool) :
    posFacts w = (List.range w.length).map fun i => posFact (w.length - 1 - i) (w.getD i false) := by
  induction w with
  | nil => rfl
  | cons b x ih =>
    rw [posFacts_cons, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply, List.getD_cons_succ]
    congr 1
    omega

theorem famInstDescG_posNum (N : NTM (Fin k) TapeSym) (w : List Bool) :
    famInstDescG (homingMachine N) hq hg (posNum N w.length) eCs (markInput N (w.map some)) =
      hardInst w := by
  unfold famInstDescG hardInst guardInst
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · simp only [famInitL, List.map_cons, List.map_map]
    rw [posFacts_eq_range]
    congr 1
    · simp [posNum, homingMachine]
    · simp only [markInput_length, List.length_map]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      have hget : (markInput N (w.map some)).getD i (homingMachine N).blank =
          (some (w.getD i false), decide (i = 0)) := by
        have hi' : i < (markInput N (w.map some)).length := by simpa using hi
        rw [List.getD_eq_getElem _ _ hi']
        simp [markInput, List.getD_eq_getElem?_getD, hi]
      simp only [Function.comp_apply, hget, posNum, hi, true_and, if_true]
  · rfl

theorem hardInst_injective : Function.Injective hardInst := by
  intro w w' h
  have := congrArg InstDesc.initList h
  simp only [hardInst, guardInst_initList, List.cons.injEq, true_and] at this
  exact posFacts_injective this

theorem size_hardInst (w : List Bool) : (hardInst w).size = w.length + 3 := by
  simp [hardInst, guardInst, InstDesc.size, InstDesc.initList, InstDesc.goalList, InstDesc.tnI,
    TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

/-- **The instance map is polynomial time**: its serialisation is a constant followed by the
serialisation of the positional encoding. -/
theorem polyTimeCode_hardInst : PolyTimeCode codingSer hardInst := by
  refine ⟨fun w => (true :: bstr (bitsOfNat 0)) ++ posSer w,
    polyTimeFun_prependConst _ polyTimeFun_posSer, fun w => ?_⟩
  beta_reduce
  rw [codingSer_code, hardInst, instSer_guardInst, ← instSer_posEnc, posEnc, instSer_guardInst]
  simp

/-! ### The domain map -/

/-- The time bound of the construction for the inputs of length `n`. -/
def kBound (p : Polynomial ℕ) (n : ℕ) : ℕ := 2 ^ (p.eval n + n)

/-- **The domain description for the inputs of length `n`.**  For `n = 0` a guard domain that is
solvable exactly when the empty word is in the language; otherwise the re-split construction for
the normalised machine with the time bound `2 · kBound p n + 1`. -/
noncomputable def hardDom (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (n : ℕ) : DomDesc :=
  if n = 0 then guardDom (if NTMLang N p [] then [[]] else [])
  else famDomDescG (homingMachine N) hq hg (posNum N n) eCs n (2 * kBound p n + 1)

/-- **Correctness of the family.** -/
theorem solvable_hardDom_iff (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (hN : ClockedExp N p)
    (w : List Bool) : Solvable (hardDom N p w.length) (hardInst w) ↔ NTMLang N p w := by
  by_cases hw : w = []
  · subst hw
    have hI : hardInst [] = guardInst [0] := rfl
    rw [hI]
    simp only [List.length_nil, hardDom, if_true]
    rw [solvable_guard_iff']
    by_cases hL : NTMLang N p []
    · simp [hL]
    · simp [hL]
  · have hn : w.length ≠ 0 := by simpa using hw
    have hw1 : 1 ≤ (w.map some).length := by simp; omega
    rw [hardDom, if_neg hn, ← famInstDescG_posNum N w]
    have h := solvable_famDescG_iff (homingMachine N) hq_injective hg_injective
      (posNum_injective N w.length) eCs_injective (markInput N (w.map some))
      (2 * kBound p w.length + 1)
    rw [markInput_length, List.length_map] at h
    rw [h]
    have hle : 2 ^ p.eval w.length ≤ kBound p w.length :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hK : (w.map some).length ≤ kBound p w.length := by
      rw [List.length_map]
      exact le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hclock : ClockedAt N (w.map some) (kBound p w.length) :=
      fun m hm => N.acceptsWithin_mono hle (hN w m hm)
    rw [solvable_problemFix_homingMachine_iff N hw1 hK le_rfl hclock]
    unfold NTMLang NTM.AcceptsExp
    rw [List.length_map]
    exact ⟨fun h => hN w _ h, fun h => N.acceptsWithin_mono hle h⟩

/-! ### Size -/

/-- The bound `famDomBound`, with polynomials as arguments. -/
noncomputable def famDomBoundP (nq ng : ℕ) (n L l : Polynomial ℕ) : Polynomial ℕ :=
  (1 + n * Polynomial.C ng + ((Polynomial.C ng + 1) + (Polynomial.C ng + Polynomial.C nq + 9) +
      12 + 2 + Polynomial.C nq * ((Polynomial.C ng + 1) * (Polynomial.C nq *
        (Polynomial.C ng + 1))))) * (Polynomial.C ng + 8) +
    34 * ((25 + 2 * n + 13 * L + L * L + l + Polynomial.C ng) *
      (((Polynomial.C ng + 1) + Polynomial.C nq * (Polynomial.C ng * (Polynomial.C nq *
        (Polynomial.C ng * 3))) + Polynomial.C nq + 2) + Polynomial.C ng) + 1)

theorem eval_famDomBoundP (nq ng : ℕ) (n L l : Polynomial ℕ) (x : ℕ) :
    (famDomBoundP nq ng n L l).eval x = famDomBound nq ng (n.eval x) (L.eval x) (l.eval x) := by
  simp [famDomBoundP, famDomBound]

theorem famDomBound_mono {nq ng n L L' l l' : ℕ} (hL : L ≤ L') (hl : l ≤ l') :
    famDomBound nq ng n L l ≤ famDomBound nq ng n L' l' := by
  unfold famDomBound
  gcongr

theorem log_two_le_of_le {e x : ℕ} (hx : x ≤ 2 * 2 ^ e + 3) : Nat.log 2 x ≤ e + 2 := by
  rcases Nat.eq_zero_or_pos x with rfl | hpos
  · simp
  · have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have hlt : x < 2 ^ (e + 3) := by
      rw [pow_add]
      omega
    exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hpos.ne' hlt)

theorem size_hardDom_le (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ n, (hardDom N p n).size ≤ P.eval n := by
  refine ⟨famDomBoundP (k + 2) 6 Polynomial.X (8 * (p + Polynomial.X) + 24)
    (2 * (p + Polynomial.X) + 6) + 4, fun n => ?_⟩
  unfold hardDom
  by_cases hn : n = 0
  · rw [if_pos hn]
    have hsz : (guardDom (if NTMLang N p [] then [[]] else [])).size ≤ 4 := by
      split_ifs <;> decide
    rw [Polynomial.eval_add]
    simp only [Polynomial.eval_ofNat]
    omega
  · rw [if_neg hn]
    refine le_trans (size_famDomDescG_le _ _ _ _ _ _ _) ?_
    rw [Polynomial.eval_add, eval_famDomBoundP]
    have hcardQ : Fintype.card (Fin k ⊕ Bool) = k + 2 := by simp
    have hcardG : Fintype.card (TapeSym × Bool) = 6 := by simp
    rw [hcardQ, hcardG]
    set e := p.eval n + n with he
    have hK : 2 * kBound p n + 1 = 2 * 2 ^ e + 1 := rfl
    rw [hK]
    have l1 := log_two_le_of_le (e := e) (x := 2 * 2 ^ e + 1) (by omega)
    have l2 := log_two_le_of_le (e := e) (x := 2 * 2 ^ e + 1 + 1) (by omega)
    have l3 := log_two_le_of_le (e := e) (x := 2 * 2 ^ e + 1 + 2) (by omega)
    have l4 := log_two_le_of_le (e := e) (x := 2 * 2 ^ e + 1 - n) (by omega)
    have l5 := log_two_le_of_le (e := e) (x := 2 * 2 ^ e + 1 - 1) (by omega)
    have hmono := famDomBound_mono (nq := k + 2) (ng := 6) (n := n)
      (L := (2 * Nat.log 2 (2 * 2 ^ e + 1) + 2) + (2 * Nat.log 2 (2 * 2 ^ e + 1 + 1) + 2) +
        (2 * Nat.log 2 (2 * 2 ^ e + 1 + 2) + 2) + (2 * Nat.log 2 (2 * 2 ^ e + 1 - n) + 2))
      (L' := 8 * e + 24) (l := 2 * Nat.log 2 (2 * 2 ^ e + 1 - 1) + 2) (l' := 2 * e + 6)
      (by omega) (by omega)
    have hev : (famDomBound (k + 2) 6 (Polynomial.X.eval n)
        ((8 * (p + Polynomial.X) + 24 : Polynomial ℕ).eval n)
        ((2 * (p + Polynomial.X) + 6 : Polynomial ℕ).eval n)) =
        famDomBound (k + 2) 6 n (8 * e + 24) (2 * e + 6) := by
      simp [he]
    rw [hev]
    omega

/-! ### The family -/

/-- **The `NEXPTIME` hardness family**, in `HTN-AC-1`, for the language of a clocked
exponential-time machine. -/
noncomputable def nexpFamily (N : NTM (Fin k) TapeSym) (p : Polynomial ℕ) (hN : ClockedExp N p) :
    HardFamilyNU codingSer SynClass.HTN_AC_root (NTMLang N p) where
  dom := hardDom N p
  inst := hardInst
  bound := (size_hardDom_le N p).choose + Polynomial.X + 3
  dom_size := fun n => by
    have := (size_hardDom_le N p).choose_spec n
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  inst_size := fun w => by
    rw [size_hardInst]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    omega
  dom_ok := fun n => by
    show DomDesc.IsAcyclic (hardDom N p n)
    unfold hardDom
    by_cases hn : n = 0
    · rw [if_pos hn]; exact guardDom_isAcyclic
    · rw [if_neg hn]
      exact isAcyclic_famDomDescG _ hq_injective hg_injective (posNum_injective N n)
        eCs_injective _ _
  inst_ok := fun w => guardInst_isRooted
  inst_injective := hardInst_injective
  correct := solvable_hardDom_iff N p hN
  inst_polyTime := polyTimeCode_hardInst

/-- **`HTN-AC-1` is `NEXPTIME`-hard in the family sense**, with non-uniform domains. -/
theorem nexpHardSourceNU_HTN_AC_root : NExpHardSourceNU codingSer SynClass.HTN_AC_root := by
  rintro L ⟨k, N, p, hN, hL⟩
  exact ⟨(nexpFamily N p hN).congrLang fun w => (hL w).symm⟩

/-- **`HTN-TR-1` is `NEXPTIME`-hard in the family sense**, with non-uniform domains. -/
theorem nexpHardSourceNU_HTN_TR_root : NExpHardSourceNU codingSer SynClass.HTN_TR_root :=
  nexpHardSourceNU_HTN_AC_root.mono ⟨fun _ h => SynClass.isAcyclic_isTailRec h, fun _ h => h⟩

end Space

end HTN
