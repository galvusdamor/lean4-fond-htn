import HtnComplexity.Article.TOHardComplete
import HtnComplexity.Article.TOHardPT
import HtnComplexity.Article.StripsHard
import HtnComplexity.PT.ExpTime
import ComplexityTheory.Machine.PTime
import ComplexityTheory.TM.Tableau
/-!
# Totally ordered HTN planning is EXPTIME-hard (Thm. 4.3.6)

**`HTN.Article.thm_4_3_6`** — `PlanEx^{UNRES ∩ TO}_htn` is EXPTIME-hard.

The article reduces the game `G6` of Stockmeyer and Chandra, whose EXPTIME-hardness it cites.
Here the reduction is from the definition of `EXPTIME` itself (a padding of the language is in
`P`), with the article's technique — compound tasks that check a condition with *inverse* actions,
so that the tasks of a sequence are checked one after the other from the same state, which
encodes universal branching, while the choice of methods encodes existential branching:

* a language `L` of `EXPTIME` has a padding `padLang q L` in `P`, decided by a *deterministic*
  single-tape machine `M` in polynomial time (`HTN.Mach.exists_dtm_of_inP`); on the padded word
  `padExp q x` of length `c₂(x) = 2|x| + 2 + 2 ^ q(|x|)` it runs in time exponential in `|x|`;
* the tableau of the run (`TM.NTM.tab`) is checked by the problem `HTN.Article.TabData.desc`
  (`HTN.Article.TabData.solvable_iff`), with counters of `B(x)` bits, `B` a polynomial with
  `2 ^ B > c₂ + r(c₂)`; the input of the machine enters only through the first row: the cells of
  the explicit prefix `x.flatMap (b ↦ [b, b]) ++ [false]` of the padded word, the cells holding
  `1`, and the blank cells.

This reduction encodes an alternating polynomial-space computation (the tableau check of
Chandra, Kozen and Stockmeyer) instead of the game `G6`; the encoding technique is the article's.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime TM

variable {k : ℕ}

/-! ### Codes of tableau entries -/

/-- The code of a tableau entry. -/
def symC (a : Option (Fin k) × Option Bool) : ℕ := (a.1.elim 0 fun q => q.val + 1) * 3 + symCode a.2

theorem symC_inj : Function.Injective (symC (k := k)) := by
  rintro ⟨o, a⟩ ⟨o', a'⟩ h
  unfold symC at h
  simp only at h
  have ha := symCode_lt a
  have ha' := symCode_lt a'
  have h1 : o.elim 0 (fun q => q.val + 1) = o'.elim 0 (fun q => q.val + 1) := by omega
  have h2 : symCode a = symCode a' := by omega
  rw [symCode_inj h2]
  congr 1
  rcases o with _ | q <;> rcases o' with _ | q' <;> simp at h1
  · rfl
  · exact congrArg some (Fin.ext h1)

/-- All entries. -/
noncomputable def allSyms : List (Option (Fin k) × Option Bool) := Finset.univ.toList

theorem mem_allSyms (a : Option (Fin k) × Option Bool) : a ∈ allSyms := by simp [allSyms]

variable (M : NTM (Fin k) (Option Bool))

/-- The local rule in the middle. -/
noncomputable def midL : List (ℕ × ℕ × ℕ × ℕ) :=
  allSyms.flatMap fun l => allSyms.flatMap fun c => allSyms.map fun r =>
    (symC (M.F (some l) c r), symC l, symC c, symC r)

/-- The local rule at cell `0`. -/
noncomputable def lftL : List (ℕ × ℕ × ℕ) :=
  allSyms.flatMap fun c => allSyms.map fun r => (symC (M.F none c r), symC c, symC r)

/-- The local rule at the last cell (blank right neighbour). -/
noncomputable def rgtL : List (ℕ × ℕ × ℕ) :=
  allSyms.flatMap fun l => allSyms.map fun c => (symC (M.F (some l) c (none, none)), symC l, symC c)

open Classical in
/-- The accepting entries. -/
noncomputable def accL : List ℕ :=
  (allSyms.filter fun a => decide (∃ q ∈ M.accept, a.1 = some q)).map symC

/-- The explicit prefix of the padded word. -/
def prefW (x : List Bool) : List Bool := x.flatMap (fun b => [b, b]) ++ [false]

/-- The code of the first-row entry of a cell of the prefix. -/
def baseCode (q₀ : ℕ) (x : List Bool) (c : ℕ) : ℕ :=
  (if c = 0 then (q₀ + 1) * 3 else 0) + if (prefW x).getI c = true then 2 else 1

/-- **The data of the reduction**, for `B` bits and the padding `N`. -/
noncomputable def dOf (Bl : List Unit) (x : List Bool) (N : ℕ) : TabData :=
  ⟨Bl.length, (prefW x).length, (prefW x).length + 1 + N,
    (List.range (prefW x).length).map (baseCode M.init.val x), symC ((none, some true) :
      Option (Fin k) × Option Bool), symC ((none, none) : Option (Fin k) × Option Bool),
    midL M, lftL M, rgtL M, accL M, 2 ^ Bl.length - 1⟩

/-! ### The tableau is described -/

theorem padExp_eq (q : Polynomial ℕ) (x : List Bool) :
    Cx.padExp q x = prefW x ++ true :: List.replicate (2 ^ q.eval x.length) true := by
  simp [Cx.padExp, pairStr, prefW]

theorem length_prefW (x : List Bool) : (prefW x).length = 2 * x.length + 1 := by
  simp [prefW]; ring

theorem getD_w {q : Polynomial ℕ} {x : List Bool} {i : ℕ} :
    ((Cx.padExp q x).map some).getD i none =
      if i < (prefW x).length then some ((prefW x).getI i)
      else if i < (prefW x).length + 1 + 2 ^ q.eval x.length then some true else none := by
  rw [getD_map_some, padExp_eq]
  generalize 2 ^ q.eval x.length = N
  have hl : (prefW x ++ true :: List.replicate N true).length =
      (prefW x).length + 1 + N := by simp; omega
  rw [hl]
  by_cases h1 : i < (prefW x).length
  · rw [if_pos (by omega), if_pos h1, List.getI_append _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i < (prefW x).length + 1 + N
    · rw [if_pos h2, if_pos h2, List.getI_append_right _ _ _ (by omega)]
      rcases hi : i - (prefW x).length with _ | j
      · rfl
      · simp only [List.getI_cons_succ]
        rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ (by simp; omega)]
        simp
    · rw [if_neg h2, if_neg h2]

theorem good_dOf (hdet : ∀ q γ, (M.step q γ).Subsingleton) (hblank : M.blank = none)
    {q : Polynomial ℕ} {Bl : List Unit} {x : List Bool} (hB : 1 ≤ Bl.length)
    (hc₂ : (prefW x).length + 1 + 2 ^ q.eval x.length < 2 ^ Bl.length) :
    (dOf M Bl x (2 ^ q.eval x.length)).Good
      (fun t i => symC (M.tab ((Cx.padExp q x).map some) t i)) := by
  set w := (Cx.padExp q x).map some
  have hpl := length_prefW x
  have hN0 := Nat.two_pow_pos (q.eval x.length)
  have h2B : 2 ≤ 2 ^ Bl.length := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Bl.length := Nat.pow_le_pow_right (by norm_num) hB
  have tab0 : ∀ i, M.tab w 0 i = (if i = 0 then some M.init else none, w.getD i none) := by
    intro i; rw [NTM.tab_zero, hblank]
  have hsucc : ∀ t i, M.tab w (t + 1) i =
      M.F (if i = 0 then none else some (M.tab w t (i - 1))) (M.tab w t i) (M.tab w t (i + 1)) :=
    NTM.tab_succ M w
  refine ⟨hB, rfl, by show 1 ≤ (prefW x).length; omega, hc₂, Nat.le_add_right_of_le (Nat.le_succ _), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · -- the prefix
    intro c hc
    simp only [dOf] at hc ⊢
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ (by simpa using hc),
      List.getElem_map, List.getElem_range, tab0, getD_w, if_pos hc]
    unfold symC baseCode
    rcases (prefW x).getI c with _ | _ <;> by_cases h0 : c = 0 <;> simp [h0, symCode]
  · -- the cells holding `1`
    intro i h1 h2
    simp only [dOf] at h1 h2 ⊢
    have := length_prefW x
    rw [tab0, getD_w, if_neg (by omega), if_pos h2, if_neg (by omega)]
  · -- the blank cells
    intro i h1 h2
    simp only [dOf] at h1 h2 ⊢
    have := length_prefW x
    rw [tab0, getD_w, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · -- the middle, sound
    intro e he t i hi _ hl hc hr
    simp only [dOf, midL, List.mem_flatMap, List.mem_map] at he
    obtain ⟨l, -, c, -, r, -, rfl⟩ := he
    rw [hsucc, if_neg (by omega), symC_inj hl, symC_inj hc, symC_inj hr]
  · -- the middle, complete
    intro t i hi _ _
    simp only [dOf, midL, List.mem_flatMap, List.mem_map]
    refine ⟨M.tab w t (i - 1), mem_allSyms _, M.tab w t i, mem_allSyms _, M.tab w t (i + 1),
      mem_allSyms _, ?_⟩
    rw [hsucc, if_neg (by omega)]
  · -- cell `0`, sound
    intro e he t hc hr
    simp only [dOf, lftL, List.mem_flatMap, List.mem_map] at he
    obtain ⟨c, -, r, -, rfl⟩ := he
    rw [hsucc, if_pos rfl, symC_inj hc, symC_inj hr]
  · -- cell `0`, complete
    intro t _
    simp only [dOf, lftL, List.mem_flatMap, List.mem_map]
    exact ⟨M.tab w t 0, mem_allSyms _, M.tab w t 1, mem_allSyms _, by rw [hsucc, if_pos rfl]⟩
  · -- the last cell, sound
    intro e he t ht hl hc
    simp only [dOf] at he ht hl hc ⊢
    simp only [rgtL, List.mem_flatMap, List.mem_map] at he
    obtain ⟨l, -, c, -, rfl⟩ := he
    have hR : (M.tab w t (2 ^ Bl.length - 1 + 1)).1 = none := by
      rcases h : (M.tab w t (2 ^ Bl.length - 1 + 1)).1 with _ | q'
      · rfl
      · have := (NTM.tab_fst_eq_some M h).1
        have := NTM.head_run_le M w t
        omega
    have hR' : M.tab w t (2 ^ Bl.length - 1 + 1) = (none, (M.tab w t (2 ^ Bl.length - 1 + 1)).2) :=
      Prod.ext hR rfl
    rw [hsucc, if_neg (by omega), symC_inj hl, symC_inj hc, hR', NTM.F_right]
  · -- the last cell, complete
    intro t ht
    simp only [dOf] at ht ⊢
    simp only [rgtL, List.mem_flatMap, List.mem_map]
    refine ⟨_, mem_allSyms (M.tab w t (2 ^ Bl.length - 1 - 1)), _,
      mem_allSyms (M.tab w t (2 ^ Bl.length - 1)), ?_⟩
    have hR : (M.tab w t (2 ^ Bl.length - 1 + 1)).1 = none := by
      rcases h : (M.tab w t (2 ^ Bl.length - 1 + 1)).1 with _ | q'
      · rfl
      · have := (NTM.tab_fst_eq_some M h).1
        have := NTM.head_run_le M w t
        omega
    have hR' : M.tab w t (2 ^ Bl.length - 1 + 1) = (none, (M.tab w t (2 ^ Bl.length - 1 + 1)).2) :=
      Prod.ext hR rfl
    rw [hsucc, if_neg (by omega), hR', NTM.F_right]

/-- **The problem has a solution iff the machine accepts the padded word within `2 ^ B - 1`
steps.** -/
theorem solvable_dOf_iff (hdet : ∀ q γ, (M.step q γ).Subsingleton) (hblank : M.blank = none)
    {q : Polynomial ℕ} {Bl : List Unit} {x : List Bool} (hB : 1 ≤ Bl.length)
    (hc₂ : (prefW x).length + 1 + 2 ^ q.eval x.length < 2 ^ Bl.length) :
    (dOf M Bl x (2 ^ q.eval x.length)).desc.toProblem.Solvable ↔
      M.AcceptsWithin ((Cx.padExp q x).map some) (2 ^ Bl.length - 1) := by
  classical
  rw [TabData.solvable_iff (good_dOf M hdet hblank hB hc₂), NTM.acceptsWithin_iff_run hdet,
    NTM.run_accept_iff_tab]
  simp only [dOf, accL, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, a, ⟨-, q', hq', ha⟩, he⟩
    obtain ⟨o, γ⟩ := a
    simp only at ha
    subst ha
    refine ⟨i, ?_, q', hq', γ, (symC_inj he).symm⟩
    by_contra hn
    have := Nat.two_pow_pos Bl.length
    have h := NTM.tab_fst_eq_some M (by rw [← symC_inj he] : (M.tab _ _ i).1 = some q')
    have := NTM.head_run_le M ((Cx.padExp q x).map some) (2 ^ Bl.length - 1)
    omega
  · rintro ⟨i, hi, q', hq', γ, h⟩
    have := Nat.two_pow_pos Bl.length
    exact ⟨i, by omega, _, ⟨mem_allSyms _, q', hq', by rw [h]⟩, rfl⟩

/-! ### Polynomial time -/

theorem natOfBits_replicate_true : ∀ n : ℕ, natOfBits (List.replicate n true) = 2 ^ n - 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, natOfBits_cons, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    simp; omega

theorem pt_prefW : PT prefW :=
  PT.append (PT.flatMap PT.id (PT.cons PT.snd (PT.single PT.snd))) (PT.const _)

theorem pt_dOf {Bl : List Bool → List Unit} {Nl : List Bool → List Unit} (hBl : PT Bl) (hNl : PT Nl) :
    PT fun x => (dOf M (Bl x) x (2 ^ (Nl x).length)).desc := by
  have hp := pt_prefW
  have hN : PT fun x => 2 ^ (Nl x).length :=
    (PT.ofBits (PT.append (PT.map (g := fun _ _ => false) hNl (PT.const false)) (PT.const [true]))).of_eq fun x => by
      rw [natOfBits_append]; simp [natOfBits_replicate_false, natOfBits_cons]
  have hmx : PT fun x => 2 ^ (Bl x).length - 1 :=
    (PT.ofBits (PT.map (g := fun _ _ => true) hBl (PT.const true))).of_eq fun x => by
      rw [show (Bl x).map (fun _ => true) = List.replicate (Bl x).length true by simp]
      exact natOfBits_replicate_true _
  have hbase : PT fun x => (List.range (prefW x).length).map (baseCode M.init.val x) := by
    refine PT.map (PT.rangeLength hp) ?_
    unfold baseCode
    exact PT.add (PT.ite (PT.eq PT.snd (PT.const 0)) (PT.const _) (PT.const 0))
      (PT.ite (PT.eq (PT.getI (hp.comp PT.fst) PT.snd) (PT.const true)) (PT.const 2) (PT.const 1))
  have h := pt_tabDesc (L := Bl) (L₁ := fun x => (prefW x).map fun _ => ())
    (c₂ := fun x => (prefW x).length + 1 + 2 ^ (Nl x).length)
    (mx := fun x => 2 ^ (Bl x).length - 1) hBl (PT.map (g := fun _ _ => ()) hp (PT.const ()))
    (PT.add (PT.succ (PT.length hp)) hN) hmx
    (PT.const (symC ((none, some true) : Option (Fin k) × Option Bool)))
    (PT.const (symC ((none, none) : Option (Fin k) × Option Bool))) hbase
    (PT.const (accL M)) (PT.const (midL M)) (PT.const (lftL M)) (PT.const (rgtL M))
  exact h.of_eq fun x => by simp [dOf]

/-! ### The theorem -/

/-- **Theorem 4.3.6.** `PlanEx^{UNRES ∩ TO}_htn` is EXPTIME-hard. -/
theorem thm_4_3_6 : Cx.Hard Cx.EXPTIME (PlanEx fun P => P.IsTO) := by
  intro L ⟨q, hP⟩
  obtain ⟨k, M, r, hblank, hdet, hM⟩ := Mach.exists_dtm_of_inP hP
  -- the number of bits
  obtain ⟨q', hq'⟩ := Mach.exists_two_pow_bound (Polynomial.X + r + 1) (q + Polynomial.X + 2)
  obtain ⟨Bl, hBl, hBlen⟩ := exists_pt_polyLen (q' + 1)
  obtain ⟨Nl, hNl, hNlen⟩ := exists_pt_polyLen q
  have hbound : ∀ x : List Bool, (prefW x).length + 1 + 2 ^ q.eval x.length +
      r.eval ((prefW x).length + 1 + 2 ^ q.eval x.length) < 2 ^ (Bl x).length := by
    intro x
    have hc : (prefW x).length + 1 + 2 ^ q.eval x.length ≤
        2 ^ (q + Polynomial.X + 2).eval x.length := by
      simp only [prefW, List.length_append, List.length_flatMap, List.length_cons,
        List.length_nil, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, pow_add]
      simp only [zero_add, List.map_const', List.sum_replicate, smul_eq_mul]
      have h1 : x.length < 2 ^ x.length := Nat.lt_two_pow_self
      have h2 : 1 ≤ 2 ^ q.eval x.length := Nat.one_le_two_pow
      nlinarith
    have := hq' x.length _ hc
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at this
    rw [hBlen, Polynomial.eval_add, Polynomial.eval_one, pow_succ]
    omega
  have hB1 : ∀ x : List Bool, 1 ≤ (Bl x).length := fun x => by rw [hBlen]; simp
  set f : List Bool → ProbDesc := fun x => (dOf M (Bl x) x (2 ^ (Nl x).length)).desc
  have hf : PT f := pt_dOf M hBl hNl
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun x => ?_⟩
  show L x ↔ codeLang ProbDesc (fun p => p.Valid ∧ p.toProblem.IsTO ∧ p.toProblem.Solvable) (enc (f x))
  rw [codeLang_enc]
  have hc₂ : (prefW x).length + 1 + 2 ^ q.eval x.length < 2 ^ (Bl x).length := by
    have := hbound x; omega
  have hNx : (Nl x).length = q.eval x.length := hNlen x
  have hfx : f x = (dOf M (Bl x) x (2 ^ q.eval x.length)).desc := by simp only [f, hNx]
  rw [hfx, solvable_dOf_iff M hdet hblank (hB1 x) hc₂]
  have hv := (dOf M (Bl x) x (2 ^ q.eval x.length)).desc_valid (by simp [dOf, prefW])
  have hto := (dOf M (Bl x) x (2 ^ q.eval x.length)).desc_isTO
  have hlen : ((Cx.padExp q x).map some).length = (prefW x).length + 1 + 2 ^ q.eval x.length := by
    simp [padExp_eq]; omega
  constructor
  · intro hx
    have hpad : Cx.padLang q L (Cx.padExp q x) := ⟨x, rfl, hx⟩
    have hacc := (hM _).1 hpad
    refine ⟨hv, hto, NTM.acceptsWithin_mono M ?_ hacc⟩
    have := hbound x
    rw [List.length_map] at hlen
    rw [hlen]
    omega
  · rintro ⟨-, -, n, -, c, hr, hc⟩
    obtain ⟨x', hx', hLx'⟩ := (hM _).2 ⟨n, c, hr, hc⟩
    have : x = x' := by
      have := congrArg unpairS hx'
      simp only [Cx.padExp, unpairS_pairStr, Prod.mk.injEq] at this
      exact this.1
    rw [this]; exact hLx'

end Article

end HTN
