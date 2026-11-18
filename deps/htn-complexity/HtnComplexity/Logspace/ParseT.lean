import HtnComplexity.Logspace.Parse
/-!
# The parser as a term of the fold language

`HTN.Logspace.parseT F d p L s` computes the parser `HTN.Logspace.prs F` on the first `L` bits
of the location `(d, p)` from position `s` (`HTN.Logspace.eval_parseT`).  The content of a nested
string at position `s` of the location `(d, p)` is at the location `(d + 1, p + 2^d (s + 1))`
(`HTN.Logspace.cstr_virt`), so the parser of a list calls the parser of its entries one level
deeper.
-/

namespace HTN

namespace Logspace

open Cx Cx.LTerm Syn

/-- `2 t`. -/
def dbl (t : LTerm) : LTerm := .add t t

/-- The length of the content of the self-delimiting string at `s`. -/
def layLenT (d : ℕ) (p L s : LTerm) : LTerm :=
  firstB L (not (btT d (lift 2 p) (lift 2 L) (.add (lift 2 s) (dbl (.var 0)))))

/-- **The parser as a term.** -/
def parseT : Fmt → ℕ → LTerm → LTerm → LTerm → LTerm
  | .nat, d, p, L, s =>
    .ite (and (and (.lt (.add s (dbl (layLenT d p L s))) L) (not (btT d p L (.add s (dbl (layLenT d p L s))))))
        (or (not (layLenT d p L s)) (btT d p L (.sub (.add s (dbl (layLenT d p L s))) (.lit 1)))))
      (.add (.add s (dbl (layLenT d p L s))) (.lit 1)) (.add L (.lit 1))
  | .bool, _, _, L, s => .ite (.lt s L) (.add s (.lit 1)) (.add L (.lit 1))
  | .pair F G, d, p, L, s =>
    .ite (.lt (parseT F d p L s) (.add L (.lit 1))) (parseT G d p L (parseT F d p L s)) (.add L (.lit 1))
  | .list F, d, p, L, s =>
    .ite (and (not (btT d p L (.fold (.add L (.lit 1)) s (lbodyT (parseT F (d + 1)) d p L))))
        (.lt (.fold (.add L (.lit 1)) s (lbodyT (parseT F (d + 1)) d p L)) L))
      (.add (.fold (.add L (.lit 1)) s (lbodyT (parseT F (d + 1)) d p L)) (.lit 1)) (.add L (.lit 1))
where
  /-- The body of the walk through a list (`HTN.Logspace.lstep`); the accumulator is variable
  `0`. -/
  lbodyT (q : LTerm → LTerm → LTerm → LTerm) (d : ℕ) (p L : LTerm) : LTerm :=
    .ite (btT d (lift 2 p) (lift 2 L) (.var 0))
      (.ite (and (.lt (.add (.add (.var 0) (.lit 1)) (dbl (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1)))))
            (lift 2 L))
          (not (btT d (lift 2 p) (lift 2 L)
            (.add (.add (.var 0) (.lit 1)) (dbl (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1))))))))
        (.ite (eq (q (posT d (lift 2 p) (.add (.var 0) (.lit 2))) (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1)))
              (.lit 0))
            (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1))))
          (.add (.add (.add (.var 0) (.lit 1)) (dbl (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1)))))
            (.lit 1))
          (.add (lift 2 L) (.lit 1)))
        (.add (lift 2 L) (.lit 1)))
      (.var 0)

variable {x : List Bool} {M : ℕ}

theorem virt_min (hM : x.length ≤ M) (d q L : ℕ) : virt x d (min q M) L = virt x d q L := by
  unfold virt
  refine List.map_congr_left fun k _ => ?_
  unfold rd
  rcases le_total q M with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getD_eq_default _ _ (by nlinarith [Nat.zero_le (2 ^ d * k)]),
      List.getD_eq_default _ _ (by nlinarith [Nat.zero_le (2 ^ d * k)])]

/-- **The content of a nested string, located.** -/
theorem cstr_virt (d p L s j : ℕ) (h : s + 2 * j ≤ L) :
    cstr (virt x d p L) s j = virt x (d + 1) (p + 2 ^ d * (s + 1)) j := by
  unfold cstr
  conv_rhs => rw [virt]
  refine List.map_congr_left fun k hk => ?_
  rw [List.mem_range] at hk
  rw [bt_virt]
  simp only [show s + 2 * k + 1 < L by omega, decide_true, Bool.true_and, rd]
  congr 1; ring

theorem min_lt_iff' {a L : ℕ} (hL : L ≤ M) : min a M < L ↔ a < L := by
  constructor
  · intro h; rcases le_total a M with h' | h'
    · rwa [min_eq_left h'] at h
    · rw [min_eq_right h'] at h; omega
  · intro h; rw [min_eq_left (by omega)]; exact h

theorem eval_layLenT (hM : x.length ≤ M) (env : List ℕ) (d : ℕ) (p L s : LTerm)
    (hL : eval x M env L ≤ M) :
    eval x M env (layLenT d p L s) =
      layLen (virt x d (eval x M env p) (eval x M env L)) (eval x M env s) := by
  rw [layLenT, eval_firstB, layLen, firstIdx, length_virt]
  congr 2
  funext j
  simp only [eval_not, eval_btT hM, eval_lift2, dbl, eval, List.getD_cons_zero]
  have e : min (eval x M env s + min (j + j) M) M = min (eval x M env s + 2 * j) M := by omega
  rw [e, bt_virt_min hL]
  by_cases h : bt (virt x d (eval x M env p) (eval x M env L)) (eval x M env s + 2 * j) <;> simp [h]

theorem layLen_le (w : List Bool) (s : ℕ) : layLen w s ≤ w.length := firstIdx_le _ _

/-- **The parser term computes the parser.** -/
theorem eval_parseT (hM : x.length + 2 ≤ M) : ∀ (F : Fmt) (d : ℕ) (p L s : LTerm) (env : List ℕ),
    eval x M env L ≤ x.length →
    eval x M env (parseT F d p L s) =
      prs F (virt x d (eval x M env p) (eval x M env L)) (eval x M env s)
  | .nat, d, p, L, s, env, hL => by
    have hM' : x.length ≤ M := by omega
    have hJ := eval_layLenT hM' env d p L s (by omega)
    simp only [parseT, eval, eval_and, eval_not, eval_or, eval_btT hM', dbl, hJ]
    have hLM : eval x M env L ≤ M := by omega
    generalize hw : virt x d (eval x M env p) (eval x M env L) = w at *
    have hwl : w.length = eval x M env L := by rw [← hw]; simp
    have hbm : ∀ i, bt w (min i M) = bt w i := fun i => by rw [← hw]; exact bt_virt_min hLM i
    rw [prs, hwl]
    have hJle : layLen w (eval x M env s) ≤ eval x M env L := by
      have := layLen_le w (eval x M env s); omega
    generalize eval x M env s = s' at *
    generalize hJ' : layLen w s' = J at *
    generalize eval x M env L = L' at *
    have e : min (s' + min (J + J) M) M = min (s' + 2 * J) M := by omega
    have hm : min (L' + 1) M = L' + 1 := min_eq_left (by omega)
    simp only [e, hm, hbm]
    by_cases h1 : s' + 2 * J < L'
    · have h2 : min (s' + 2 * J) M = s' + 2 * J := min_eq_left (by omega)
      have hm' : min (s' + 2 * J + 1) M = s' + 2 * J + 1 := min_eq_left (by omega)
      simp only [h2, hm', hbm]
      by_cases hb : bt w (s' + 2 * J) <;> by_cases hJ0 : J = 0 <;>
        by_cases hb' : bt w (s' + 2 * J - 1) <;> simp [h1, hb, hJ0, hb']
    · have h1' : ¬ min (s' + 2 * J) M < L' := by rw [min_lt_iff' (by omega)]; exact h1
      simp [h1, h1']
  | .bool, d, p, L, s, env, hL => by
    simp only [parseT, eval, prs, length_virt]
    have hm : min (eval x M env L + 1) M = eval x M env L + 1 := min_eq_left (by omega)
    by_cases h : eval x M env s < eval x M env L
    · have : min (eval x M env s + 1) M = eval x M env s + 1 := min_eq_left (by omega)
      simp [h, this]
    · simp [h, hm]
  | .pair F G, d, p, L, s, env, hL => by
    have hm : min (eval x M env L + 1) M = eval x M env L + 1 := min_eq_left (by omega)
    simp only [parseT, eval, prs, length_virt, hm]
    rw [eval_parseT hM F d p L s env hL, eval_parseT hM G d p L _ env hL, eval_parseT hM F d p L s env hL]
    by_cases h : prs F (virt x d (eval x M env p) (eval x M env L)) (eval x M env s) ≤ eval x M env L
    · simp [h, Nat.lt_succ_of_le h]
    · simp [h, show ¬ prs F (virt x d (eval x M env p) (eval x M env L)) (eval x M env s) < eval x M env L + 1
        by omega]
  | .list F, d, p, L, s, env, hL => by
    have hM' : x.length ≤ M := by omega
    have hLM : eval x M env L ≤ M := by omega
    have hbody : ∀ acc j, eval x M (acc :: j :: env) (parseT.lbodyT (parseT F (d + 1)) d p L) =
        lstep (prs F) (virt x d (eval x M env p) (eval x M env L)) acc := by
      intro acc j
      have hJ : eval x M (acc :: j :: env) (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1))) =
          layLen (virt x d (eval x M env p) (eval x M env L)) (min (acc + 1) M) := by
        rw [eval_layLenT hM' _ _ _ _ _ (by rw [eval_lift2]; exact hLM)]
        simp [eval_lift2, eval]
      have hJle : layLen (virt x d (eval x M env p) (eval x M env L)) (min (acc + 1) M) ≤
          eval x M env L := by
        have := layLen_le (virt x d (eval x M env p) (eval x M env L)) (min (acc + 1) M)
        simpa using this
      have hin : eval x M (acc :: j :: env) (parseT F (d + 1) (posT d (lift 2 p) (.add (.var 0) (.lit 2)))
          (layLenT d (lift 2 p) (lift 2 L) (.add (.var 0) (.lit 1))) (.lit 0)) =
          prs F (virt x (d + 1) (eval x M env p + 2 ^ d * min (acc + 2) M)
            (layLen (virt x d (eval x M env p) (eval x M env L)) (min (acc + 1) M))) 0 := by
        rw [eval_parseT hM F (d + 1) _ _ _ _ (by rw [hJ]; omega), hJ, eval_posT]
        simp only [eval_lift2, eval, List.getD_cons_zero]
        rw [virt_min hM']
      simp only [parseT.lbodyT, eval, eval_and, eval_not, eval_btT hM', eval_lift2, List.getD_cons_zero,
        dbl, eval_eq _ _ _ (show 1 ≤ M by omega), hJ, hin]
      generalize hw : virt x d (eval x M env p) (eval x M env L) = w at *
      have hwl : w.length = eval x M env L := by rw [← hw]; simp
      have hbm : ∀ i, bt w (min i M) = bt w i := fun i => by rw [← hw]; exact bt_virt_min hLM i
      generalize eval x M env L = L' at *
      unfold lstep
      rw [hwl]
      by_cases hb : bt w acc = true
      · have hacc : acc < L' := by
          rw [← hw, bt_virt] at hb; simp only [Bool.and_eq_true, decide_eq_true_eq] at hb; exact hb.1
        have ha1 : min (acc + 1) M = acc + 1 := min_eq_left (by omega)
        have ha2 : min (acc + 2) M = acc + 2 := min_eq_left (by omega)
        simp only [hb, if_true, ha1, ha2, hbm]
        generalize hJ' : layLen w (acc + 1) = J at *
        have e : min (acc + 1 + min (J + J) M) M = min (acc + 1 + 2 * J) M := by omega
        have hm : min (L' + 1) M = L' + 1 := min_eq_left (by omega)
        simp only [e, hm]
        by_cases h1 : acc + 1 + 2 * J < L'
        · have h2 : min (acc + 1 + 2 * J) M = acc + 1 + 2 * J := min_eq_left (by omega)
          have hc : virt x (d + 1) (eval x M env p + 2 ^ d * (acc + 2)) J = cstr w (acc + 1) J := by
            rw [← hw, cstr_virt d _ L' (acc + 1) J (by omega)]
          have hm3 : min (acc + 1 + 2 * J + 1) M = acc + 2 + 2 * J := by
            rw [min_eq_left (by omega)]; ring
          have e2 : min (J + J) M = 2 * J := by omega
          simp only [h2, hbm, hc, hm3, e2]
          by_cases hb2 : bt w (acc + 1 + 2 * J) <;> by_cases hq : prs F (cstr w (acc + 1) J) 0 = J <;>
            simp [h1, hb2, hq]
        · have h1' : ¬ min (acc + 1 + 2 * J) M < L' := by rw [min_lt_iff' (by omega)]; exact h1
          simp [h1, h1']
      · simp [hb]
    simp only [parseT, eval, eval_and, eval_not, eval_btT hM', hbody]
    rw [prs]
    generalize hw : virt x d (eval x M env p) (eval x M env L) = w at *
    have hwl : w.length = eval x M env L := by rw [← hw]; simp
    rw [hwl]
    have hm : min (eval x M env L + 1) M = eval x M env L + 1 := min_eq_left (by omega)
    simp only [hm]
    generalize (List.range (eval x M env L + 1)).foldl (fun acc _ => lstep (prs F) w acc)
      (eval x M env s) = a
    generalize eval x M env L = L' at *
    by_cases h : bt w a = false ∧ a < L'
    · have ha : min (a + 1) M = a + 1 := min_eq_left (by omega)
      simp [h, ha]
    · by_cases hb : bt w a = true
      · simp [hb]
      · have : ¬ a < L' := fun h' => h ⟨by simpa using hb, h'⟩
        simp [hb, this]

end Logspace

end HTN
