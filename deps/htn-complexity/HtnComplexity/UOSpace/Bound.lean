import HtnComplexity.UOSpace.ShortRun
import HtnComplexity.UODecide.Concrete
/-!
# The single-exponential bound, concretely

* `HTN.UOAbs.uoBoundP_le` — the bound `uoBoundP` is at most `2 ^ (32·L⁴)`, where `L` adds up the
  numbers of initial labels, compound names, *facts* (not states), actions and the maximal body
  size: a solution of polynomially many bits;
* `HTN.Syn.uoBndP` — the bound for a described problem, and
  `HTN.Syn.solvable_iff_short_uo` — **an unordered described problem is solvable iff its abstract
  progression system reaches a goal configuration in at most `uoBndP d q` steps**;
* `HTN.UOAbs.card_le_of_reachIn` — along a run of length `m` the number of open tasks grows by at
  most `m · Mb`.
-/

namespace HTN

namespace UOAbs

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem mul_le_two_pow {a b x y : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ y) : a * b ≤ 2 ^ (x + y) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem add_le_two_pow {a b x : ℕ} (ha : a ≤ 2 ^ x) (hb : b ≤ 2 ^ x) : a + b ≤ 2 ^ (x + 1) := by
  rw [pow_succ]; omega

theorem pow_le_two_pow {a x n : ℕ} (ha : a ≤ 2 ^ x) : a ^ n ≤ 2 ^ (x * n) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left ha n

theorem le_two_pow_of_le {a x y : ℕ} (ha : a ≤ 2 ^ x) (h : x ≤ y) : a ≤ 2 ^ y :=
  ha.trans (two_pow_mono h)

/-- The arithmetic core of `uoBoundP_le`. -/
theorem uoBoundP_le_aux (nI bC bS nA L E : ℕ) (hbC : bC ≤ 2 ^ E) (hbS : bS ≤ 2 ^ E)
    (hnI : nI ≤ 2 ^ L) (hnA : nA ≤ L) :
    (1 + nI * bC + bS) + Steinitz.zsP nA ((1 + nI * bC + bS) + bC + bS) *
        ((1 + nI * bC + bS) + bC + bS) ≤ 2 ^ ((2 * L + E + 6) * L + L + E + 5) := by
  have h1 : 1 ≤ 2 ^ (L + E) := Nat.one_le_two_pow
  have h2 : nI * bC ≤ 2 ^ (L + E) := mul_le_two_pow hnI hbC
  have h3 : bS ≤ 2 ^ (L + E) := le_two_pow_of_le hbS (by omega)
  have hbase : 1 + nI * bC + bS ≤ 2 ^ (L + E + 2) := by
    rw [pow_add]; norm_num; omega
  have hab : (1 + nI * bC + bS) + bC + bS ≤ 2 ^ (L + E + 4) := by
    have h4 : bC ≤ 2 ^ (L + E + 2) := le_two_pow_of_le hbC (by omega)
    have h5 : bS ≤ 2 ^ (L + E + 2) := le_two_pow_of_le hbS (by omega)
    rw [show L + E + 4 = (L + E + 2) + 2 by ring, pow_add]; norm_num; omega
  generalize (1 + nI * bC + bS) + bC + bS = ab at hab ⊢
  generalize 1 + nI * bC + bS = base at hbase ⊢
  have hnA' : nA ≤ 2 ^ L := hnA.trans Nat.lt_two_pow_self.le
  have h6 : 2 * nA * ab + 1 ≤ 2 ^ (2 * L + E + 6) := by
    have h7 : 2 * nA * ab ≤ 2 ^ (1 + L + (L + E + 4)) :=
      mul_le_two_pow (mul_le_two_pow (by norm_num) hnA') hab
    have h8 : 1 ≤ 2 ^ (1 + L + (L + E + 4)) := Nat.one_le_two_pow
    have := add_le_two_pow h7 h8
    exact le_two_pow_of_le this (by omega)
  have hz : Steinitz.zsP nA ab ≤ 2 ^ ((2 * L + E + 6) * L) := by
    unfold Steinitz.zsP
    exact (pow_le_two_pow h6).trans (two_pow_mono (Nat.mul_le_mul_left _ hnA))
  have h9 : Steinitz.zsP nA ab * ab ≤ 2 ^ ((2 * L + E + 6) * L + (L + E + 4)) :=
    mul_le_two_pow hz hab
  have h10 : base ≤ 2 ^ ((2 * L + E + 6) * L + (L + E + 4)) := le_two_pow_of_le hbase (by omega)
  have := add_le_two_pow h10 h9
  exact le_two_pow_of_le this (by omega)

/-- **The bound has polynomially many bits.** -/
theorem uoBoundP_le (nI nC f nA Mx : ℕ) :
    uoBoundP nI nC (2 ^ f) nA Mx ≤ 2 ^ (32 * (nI + nC + f + nA + Mx + 1) ^ 4) := by
  have e : uoBoundP nI nC (2 ^ f) nA Mx =
      (1 + nI * (Mx + 1) ^ (nC * nC + 2 * nC + 2) + 3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2)) +
        Steinitz.zsP nA ((1 + nI * (Mx + 1) ^ (nC * nC + 2 * nC + 2) +
          3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2)) + (Mx + 1) ^ (nC * nC + 2 * nC + 2) +
          3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2)) *
        ((1 + nI * (Mx + 1) ^ (nC * nC + 2 * nC + 2) + 3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2)) +
          (Mx + 1) ^ (nC * nC + 2 * nC + 2) + 3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2)) := rfl
  rw [e]
  generalize hL : nI + nC + f + nA + Mx + 1 = L
  have hL1 : 1 ≤ L := by omega
  have hLpow : L ≤ 2 ^ L := Nat.lt_two_pow_self.le
  have hLL : L ≤ L ^ 3 := by nlinarith [Nat.one_le_pow 2 L hL1]
  have hL2 : L ^ 2 ≤ L ^ 3 := by nlinarith
  have hL34 : L ^ 3 ≤ L ^ 4 := by nlinarith
  have hbC : (Mx + 1) ^ (nC * nC + 2 * nC + 2) ≤ 2 ^ (6 * L ^ 3) := by
    have hM : Mx + 1 ≤ 2 ^ L := (show Mx + 1 ≤ L by omega).trans hLpow
    refine le_two_pow_of_le (pow_le_two_pow hM) ?_
    have hnC : nC ≤ L := by omega
    have : nC * nC ≤ L * L := Nat.mul_le_mul hnC hnC
    nlinarith
  have hbS : 3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2) ≤ 2 ^ (6 * L ^ 3) := by
    have hf : 2 ^ f ≤ 2 ^ L := two_pow_mono (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 3 * (2 ^ f * 2 ^ f + 2 * 2 ^ f + 2) ≤ 2 ^ (4 + (L + L)) := by
      rw [pow_add, pow_add]
      have := Nat.mul_le_mul hf hf
      nlinarith
    exact le_two_pow_of_le h2 (by nlinarith)
  have hnI : nI ≤ 2 ^ L := (show nI ≤ L by omega).trans hLpow
  refine (uoBoundP_le_aux nI _ _ nA L _ hbC hbS hnI (by omega)).trans (two_pow_mono ?_)
  have e2 : (2 * L + 6 * L ^ 3 + 6) * L + L + 6 * L ^ 3 + 5 =
      6 * L ^ 4 + 6 * L ^ 3 + 2 * L ^ 2 + 7 * L + 5 := by ring
  rw [e2]
  have h5 : L ≤ L ^ 4 := hLL.trans hL34
  have h6 : L ^ 2 ≤ L ^ 4 := hL2.trans hL34
  have h7 : 1 ≤ L ^ 4 := Nat.one_le_pow _ _ hL1
  nlinarith

/-- `uoBoundP` is monotone in all its arguments. -/
theorem uoBoundP_mono {nI nI' nC nC' nS nS' nA nA' Mx Mx' : ℕ} (h1 : nI ≤ nI') (h2 : nC ≤ nC')
    (h3 : nS ≤ nS') (h4 : nA ≤ nA') (h5 : Mx ≤ Mx') :
    uoBoundP nI nC nS nA Mx ≤ uoBoundP nI' nC' nS' nA' Mx' := by
  unfold uoBoundP
  simp only
  have hbC : (Mx + 1) ^ (nC * nC + 2 * nC + 2) ≤ (Mx' + 1) ^ (nC' * nC' + 2 * nC' + 2) :=
    (Nat.pow_le_pow_left (by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.mul_le_mul h2 h2]))
  have hbS : 3 * (nS * nS + 2 * nS + 2) ≤ 3 * (nS' * nS' + 2 * nS' + 2) := by
    nlinarith [Nat.mul_le_mul h3 h3]
  have hbase : 1 + nI * (Mx + 1) ^ (nC * nC + 2 * nC + 2) + 3 * (nS * nS + 2 * nS + 2) ≤
      1 + nI' * (Mx' + 1) ^ (nC' * nC' + 2 * nC' + 2) + 3 * (nS' * nS' + 2 * nS' + 2) := by
    have := Nat.mul_le_mul h1 hbC
    omega
  have hab := Nat.add_le_add (Nat.add_le_add hbase hbC) hbS
  have hz : ∀ {n n' a a' : ℕ}, n ≤ n' → a ≤ a' → Steinitz.zsP n a ≤ Steinitz.zsP n' a' := by
    intro n n' a a' hn ha
    unfold Steinitz.zsP
    calc (2 * n * a + 1) ^ n ≤ (2 * n' * a' + 1) ^ n :=
          Nat.pow_le_pow_left (by nlinarith [Nat.mul_le_mul hn ha]) _
      _ ≤ (2 * n' * a' + 1) ^ n' := Nat.pow_le_pow_right (by omega) hn
  exact Nat.add_le_add hbase (Nat.mul_le_mul (hz h4 hab) hab)

variable {S : Sys}

/-- Along a run of length `m` the number of open tasks grows by at most `m · Mb`. -/
theorem card_le_of_reachIn {Comps Acts F : Finset ℕ} {Mb : ℕ} (hC : Closed S Comps Acts F Mb) :
    ∀ {m : ℕ} {x y : Cfg}, ReachIn S m x y →
      Multiset.card y.2 ≤ Multiset.card x.2 + m * Mb := by
  intro m x y h
  induction h with
  | refl => simp
  | @step n x y z hs _ ih =>
    have : Multiset.card y.2 ≤ Multiset.card x.2 + Mb := by
      cases hs with
      | dec s M c β hc hm =>
        have h1 := hC.meth_card c β hm
        have h2 := Multiset.card_erase_le (a := (true, c)) (s := M)
        show Multiset.card (M.erase (true, c) + β) ≤ Multiset.card M + Mb
        rw [Multiset.card_add]
        omega
      | exe s M a ha _ =>
        have h2 := Multiset.card_erase_le (a := (false, a)) (s := M)
        show Multiset.card (M.erase (false, a)) ≤ Multiset.card M + Mb
        omega
    rw [Nat.succ_mul]
    omega

end UOAbs

namespace Syn

open UOAbs

/-- **The single-exponential bound for a described unordered problem.** -/
def uoBndP (d : DomDesc) (q : InstDesc) : ℕ :=
  uoBoundP q.tnI.ids.length (allLbls d q).length (2 ^ (allFacts d q).length) (allLbls d q).length
    (q.tnI.ids.length + maxBody d + 2)

/-- **Short solutions for unordered descriptions**: an unordered described problem is solvable
exactly when its abstract progression system reaches a goal configuration in at most
`uoBndP d q` steps. -/
theorem solvable_iff_short_uo {d : DomDesc} {q : InstDesc} (hd : d.MethodsUO) (hq : q.IsUO) :
    Solvable d q ↔ ∃ m ≤ uoBndP d q, ∃ y, ReachIn (uoSys d q) m (uoAbs (initConfig q)) y ∧
      IsGoal (uoSys d q) y := by
  have hinv := uoInv_initConfig hq
  constructor
  · intro h
    obtain ⟨c, hr, hg⟩ := exists_pReach_of_solvable h
    obtain ⟨cs, hcs, hend⟩ := exists_ppath_of_pReach hr
    have hrun := reachIn_of_ppath (q := q) hd hinv hcs
    rw [hend] at hrun
    have hgoal : IsGoal (uoSys d q) (uoAbs c) := isGoalB_iff_uo.1 hg
    have hs₀ : (uoAbs (initConfig q)).1 ⊆ (allFacts d q).toFinset := by
      intro f hf
      simp only [uoAbs, initConfig, List.mem_toFinset] at hf ⊢
      simp [allFacts, hf]
    obtain ⟨m, hm, y', hy', hgy'⟩ :=
      short_runP (closed_uoSys d q) hs₀ (labOK_init d q) hrun hgoal
    refine ⟨m, le_trans hm (uoBoundP_mono ?_ ?_ ?_ ?_ ?_), y', hy', hgy'⟩
    · exact card_init_le q
    · simpa [uoNames] using List.toFinset_card_le ((allLbls d q).map Prod.snd)
    · exact Nat.pow_le_pow_right (by norm_num) (List.toFinset_card_le _)
    · simpa [uoNames] using List.toFinset_card_le ((allLbls d q).map Prod.snd)
    · have := card_init_le q
      omega
  · rintro ⟨m, -, y, hy, hg⟩
    obtain ⟨cs, hcs, -, hend⟩ := ppath_of_reachIn hd hy hinv rfl
    refine solvable_of_pReach (pReach_of_ppath hcs) ?_
    exact isGoalB_iff_uo.2 (hend ▸ hg)

end Syn

end HTN
