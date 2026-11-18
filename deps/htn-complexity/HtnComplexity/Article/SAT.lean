import HtnComplexity.NPHard.ThreePartition
import HtnComplexity.PT.Lang
import HtnComplexity.PT.DivMod
/-!
# Satisfiability is NP-hard (Cook–Levin), as a language of codes

The article's NP-hardness proofs (Thms. 4.3.8 and 4.3.12) reduce from satisfiability of formulas
in conjunctive normal form, whose NP-hardness (Cook) they cite.  Here:

* `HTN.Article.SAT` — the language of the codes `enc φ` of the satisfiable formulas
  `φ : HTN.NPHard.CNF` (a clause is a list of literals `(variable, polarity)`);
* **`HTN.Article.sat_npHard`** — every language of `NP` reduces to `SAT` in polynomial time.

The Cook–Levin construction is the one of `HtnComplexity/NPHard/` (the tableau formula of a
polynomial-time verifier, written in polynomial time as a list of numbers in unary,
`HTN.NPHard.stage1`); this file adds the polynomial-time conversion of that unary token list into
the code of the formula.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime NPHard PTime.CobhamTM PTime.CobhamTM.Prog

/-- **SAT**: the codes of the satisfiable formulas in conjunctive normal form. -/
def SAT : Cx.Language := codeLang CNF Satisfiable

/-! ### Reading a list of numbers in unary -/

/-- One step of the unary reader (numbers collected in reverse order). -/
def unlStep (acc : List ℕ) (b : Bool) : List ℕ := bif b then (acc.headI + 1) :: acc.tail else 0 :: acc

/-- **The numbers of a unary list.** -/
def parseUnl (z : List Bool) : List ℕ := (z.foldl unlStep []).reverse

theorem foldl_unlStep_un (k n : ℕ) (acc : List ℕ) :
    (un n).foldl unlStep (k :: acc) = (k + n) :: acc := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [un, List.replicate_succ, List.foldl_cons] at ih ⊢
    rw [show unlStep (k :: acc) true = (k + 1) :: acc from rfl, ih]
    congr 1; omega

theorem foldl_unlStep_unl (l acc : List ℕ) : (unl l).foldl unlStep acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons n l ih =>
    rw [unl_cons, List.foldl_cons, List.foldl_append,
      show unlStep acc false = 0 :: acc from rfl, foldl_unlStep_un, ih]
    simp

theorem parseUnl_unl (l : List ℕ) : parseUnl (unl l) = l := by
  simp [parseUnl, foldl_unlStep_unl]

/-! ### Reading the tokens of a formula -/

/-- One step of the token reader (clauses and literals collected in reverse order). -/
def tokStep (acc : CNF) (t : ℕ) : CNF :=
  bif t == 0 then [] :: acc else (decLit t :: acc.headI) :: acc.tail

/-- **The formula of a token list.** -/
def toksToCNF (T : List ℕ) : CNF := ((T.foldl tokStep []).map List.reverse).reverse

theorem foldl_tokStep_lits (c : List (ℕ × Bool)) (d : List (ℕ × Bool)) (acc : CNF) :
    (c.map litTok).foldl tokStep (d :: acc) = (c.reverse ++ d) :: acc := by
  induction c generalizing d with
  | nil => rfl
  | cons l c ih =>
    rw [List.map_cons, List.foldl_cons]
    have : tokStep (d :: acc) (litTok l) = (l :: d) :: acc := by
      have h0 : (litTok l == 0) = false := by simpa using litTok_ne_zero l
      simp [tokStep, h0, decLit_litTok]
    rw [this, ih]
    simp

theorem foldl_tokStep_toks (φ acc : CNF) :
    (toks φ).foldl tokStep acc = (φ.map List.reverse).reverse ++ acc := by
  induction φ generalizing acc with
  | nil => rfl
  | cons c φ ih =>
    rw [toks_cons, List.foldl_append, List.foldl_cons,
      show tokStep acc 0 = [] :: acc from rfl, foldl_tokStep_lits, ih]
    simp

theorem toksToCNF_toks (φ : CNF) : toksToCNF (toks φ) = φ := by
  simp [toksToCNF, foldl_tokStep_toks, List.map_reverse, Function.comp_def]

/-- **The conversion** of the output of the Cook–Levin stage into the formula. -/
def cnfOfUnl (z : List Bool) : CNF := toksToCNF (parseUnl z).tail

theorem cnfOfUnl_stage1 (n : ℕ) (φ : CNF) : cnfOfUnl (unl (n :: toks φ)) = φ := by
  rw [cnfOfUnl, parseUnl_unl, List.tail_cons, toksToCNF_toks]

/-! ### Polynomial time -/

theorem length_bitsOfNat_pos {n : ℕ} (hn : 0 < n) :
    (bitsOfNat n).length = (bitsOfNat (n / 2)).length + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [show 0 + m + 1 = m + 1 by omega, bitsOfNat_succ, List.length_cons]

theorem length_bitsOfNat_mono : ∀ {n m : ℕ}, n ≤ m → (bitsOfNat n).length ≤ (bitsOfNat m).length := by
  intro n m
  induction m using Nat.strong_induction_on generalizing n with
  | _ m ih =>
    intro hnm
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hm : 0 < m := lt_of_lt_of_le hn hnm
      rw [length_bitsOfNat_pos hn, length_bitsOfNat_pos hm]
      exact Nat.succ_le_succ (ih _ (Nat.div_lt_self hm (by norm_num)) (Nat.div_le_div_right hnm))

theorem sz_nat_mono {n m : ℕ} (h : n ≤ m) : sz n ≤ sz m := by
  rw [sz_nat, sz_nat]; have := length_bitsOfNat_mono h; omega

theorem sz_nat_succ_le (h : ℕ) : sz (h + 1) ≤ sz h + 2 := by
  have h1 : sz (h + 1) ≤ sz (2 * h + 1) := sz_nat_mono (by omega)
  have h2 : sz (2 * h + 1) = sz h + 2 := by
    rw [sz_nat, sz_nat, length_bitsOfNat_pos (by omega)]
    rw [show (2 * h + 1) / 2 = h by omega]; ring
  omega

theorem sz_unlStep (acc : List ℕ) (b : Bool) : sz (unlStep acc b) ≤ sz acc + 8 := by
  unfold unlStep
  cases b
  · simp only [cond_false, sz_cons]
    have : sz (0 : ℕ) = 1 := by simp [sz_nat]
    omega
  · simp only [cond_true]
    cases acc with
    | nil =>
      have : sz (1 : ℕ) = 3 := by simp [sz_nat]
      have hd : (default : ℕ) = 0 := rfl
      simp only [List.headI_nil, List.tail_nil, sz_cons, sz_nil, hd, Nat.zero_add]
      omega
    | cons h t =>
      simp only [List.headI_cons, List.tail_cons, sz_cons]
      have := sz_nat_succ_le h
      omega

theorem pt_unlStep : PT fun q : List Bool × List ℕ × Bool => unlStep q.2.1 q.2.2 := by
  unfold unlStep
  have hacc : PT fun q : List Bool × List ℕ × Bool => q.2.1 := PT.fst.comp PT.snd
  exact PT.cond (PT.snd.comp PT.snd) (PT.cons (PT.succ (PT.headI hacc)) (PT.tail hacc))
    (PT.cons (PT.const (0 : ℕ)) hacc)

theorem pt_parseUnl : PT parseUnl := by
  have h : PT fun z : List Bool => z.foldl unlStep [] :=
    PT.foldl (α := List Bool) (β := Bool) (σ := List ℕ) (g := fun _ s b => unlStep s b) PT.id
      (PT.const _) pt_unlStep (c := 0) (d := 8) fun _ s _ _ => by simpa using sz_unlStep s _
  exact PT.reverse h

theorem sz_decLit_le (t : ℕ) : sz (decLit t) ≤ sz t + 1 := by
  simp only [decLit, sz_prod, sz_bool]
  have := sz_nat_mono (show (t - 1) / 2 ≤ t by omega)
  omega

theorem sz_tokStep (acc : CNF) (t : ℕ) : sz (tokStep acc t) ≤ sz acc + 4 * sz t + 14 := by
  unfold tokStep
  cases h : t == 0
  · simp only [cond_false]
    have hd := sz_decLit_le t
    cases acc with
    | nil =>
      have hd : (default : List (ℕ × Bool)) = [] := rfl
      simp only [List.headI_nil, List.tail_nil, sz_cons, sz_nil, hd]
      omega
    | cons c rest => simp only [List.headI_cons, List.tail_cons, sz_cons]; omega
  · simp only [cond_true, sz_cons, sz_nil]; omega

theorem pt_tokStep : PT fun q : List ℕ × CNF × ℕ => tokStep q.2.1 q.2.2 := by
  unfold tokStep
  have hacc : PT fun q : List ℕ × CNF × ℕ => q.2.1 := PT.fst.comp PT.snd
  have ht : PT fun q : List ℕ × CNF × ℕ => q.2.2 := PT.snd.comp PT.snd
  have hdec : PT fun q : List ℕ × CNF × ℕ => decLit q.2.2 := by
    unfold decLit
    exact PT.pair (PT.divC (PT.subC ht 1) (by norm_num : 0 < 2))
      (PT.beq (PT.modC (PT.subC ht 1) (by norm_num : 0 < 2)) (PT.const 1))
  exact PT.cond (PT.beq ht (PT.const (0 : ℕ))) (PT.cons PT.nil hacc)
    (PT.cons (PT.cons hdec (PT.headI hacc)) (PT.tail hacc))

theorem pt_toksToCNF : PT toksToCNF := by
  have h : PT fun T : List ℕ => T.foldl tokStep [] :=
    PT.foldl (α := List ℕ) (β := ℕ) (σ := CNF) (g := fun _ s t => tokStep s t) PT.id
      (PT.const _) pt_tokStep (c := 1) (d := 20) fun T s t ht => by
        have h1 := sz_tokStep s t
        have h2 : sz t ≤ sz T := sz_le_of_mem ht
        simp only at h1 ⊢
        nlinarith
  exact PT.reverse (PT.map h (PT.reverse PT.snd))

theorem pt_cnfOfUnl : PT cnfOfUnl := pt_toksToCNF.comp (PT.tail pt_parseUnl)

/-! ### NP-hardness -/

/-- **Satisfiability is NP-hard**: every language of `NP` reduces to `SAT` in polynomial time
(the Cook–Levin theorem, `HtnComplexity/NPHard/`). -/
theorem sat_npHard : Cx.Hard Cx.NP SAT := by
  rintro L ⟨V, k, hV, hL⟩
  obtain ⟨f, hf, hVf⟩ := hV.cobhamFun
  obtain ⟨R⟩ := nonempty_realizer hf
  have hconv : UC fun z => (enc (cnfOfUnl z) : List Bool) :=
    uc_of_pt_list (BDec.pt_encL.comp pt_cnfOfUnl)
  refine ⟨fun x => enc (cnfOfUnl (stage1 R k x)),
    (polyTimeFun_of_uc hconv).comp (polyTimeFun_stage1 R k), fun x => ?_⟩
  show L x ↔ codeLang CNF Satisfiable (enc (cnfOfUnl (unl ((verTab R k x).nV :: toks (verTab R k x).cnf))))
  rw [cnfOfUnl_stage1, codeLang_enc, satisfiable_verTab_iff, hL x]
  simp only [hVf]

end Article

end HTN
