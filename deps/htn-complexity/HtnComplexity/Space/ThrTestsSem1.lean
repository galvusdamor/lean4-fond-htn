import HtnComplexity.Space.ThrTests
import HtnComplexity.Space.SeqSem7
/-!
# The tests of the thread machine: pair entries

The entries of the pair facts `edge x y`, `cl x y`, `nc x y` (`HTN.Space.Thr.entN_cfN`), the
meaning of the shape test `pairEnd` and of the comparisons `pos21`, `pos22`, and the meaning of
the kind tests `kEdge`, `kCl`, `kNc` on the entries of a configuration.
-/

namespace HTN

namespace Space

namespace Thr

open Syn SeqG SeqM PTime

/-! ### The entries of pair facts -/

/-- The tag of a pair fact. -/
def ntag : NF → List Bool
  | .edge _ _ => tE3
  | .cl _ _ => tC3
  | .nc _ _ => tN3

/-- The first position of a pair fact. -/
def npos1 : NF → ℕ
  | .edge x _ => x
  | .cl x _ => x
  | .nc x _ => x

/-- The second position of a pair fact. -/
def npos2 : NF → ℕ
  | .edge _ y => y
  | .cl _ y => y
  | .nc _ y => y

theorem length_ntag (e : NF) : (ntag e).length = 3 := by cases e <;> rfl

theorem nbits_eq (e : NF) : nbits e = ntag e ++ unary (npos1 e) ++ unary (npos2 e) := by
  cases e <;> rfl

theorem entN_cfN (e : NF) :
    entN (cfN e) = kp (ntag e) ++ (dbl (unary (npos1 e)) ++ (dbl (unary (npos2 e)) ++ [false])) := by
  rw [entN, bitsOfNat_cfN, nbits_eq, bstr_eq_dbl]
  simp [kp, dbl_append]

theorem drop_entN_cfN (e : NF) :
    (entN (cfN e)).drop 13 = dbl (unary (npos1 e)) ++ (dbl (unary (npos2 e)) ++ [false]) := by
  rw [entN_cfN, drop_kp (length_ntag e)]

theorem kp_entN_cfN (e : NF) : kp (ntag e) <+: entN (cfN e) := by
  rw [entN_cfN]; exact List.prefix_append _ _

theorem kp_entN_cfN_iff {t : List Bool} (ht : t.length = 3) (e : NF) :
    kp t <+: entN (cfN e) ↔ t = ntag e :=
  ⟨fun h => kp_eq_of_prefix ht (length_ntag e) h (kp_entN_cfN e), fun h => h ▸ kp_entN_cfN e⟩

theorem shR_drop (t : List Bool) : (shR t).drop 13 = t := by simp [shR]

/-! ### The shape test and the comparisons -/

theorem pairEnd_iff (E : List Bool) :
    pairEnd E = true ↔ ∃ x y, E.drop 13 = dbl (unary x) ++ (dbl (unary y) ++ [false]) := by
  rw [pairEnd, tailsE_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [pairEndBody, Bool.and_eq_true, isPosD_iff, posEnd_iff, shR_drop] at h
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
    refine ⟨x, y, ?_⟩
    rw [← hy, ← hx]
    exact (suffix_take_append hs).symm
  · rintro ⟨x, y, h⟩
    refine ⟨dbl (unary y) ++ [false], ⟨dbl (unary x), h.symm⟩, ?_⟩
    rw [pairEndBody, Bool.and_eq_true, isPosD_iff, posEnd_iff, shR_drop, cutAt_of_eq h]
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩

theorem pos21_iff {E E' R R' : List Bool} {x y p : ℕ}
    (hE : E.drop 13 = dbl (unary x) ++ (dbl (unary y) ++ R))
    (hE' : E'.drop 13 = dbl (unary p) ++ R') : pos21 E E' = true ↔ y = p := by
  rw [pos21, tailsE_posD hE (fun _ t b' => samePos (shR t) b') (fun _ _ _ => rfl)]
  exact samePos_iff (by rw [shR_drop]) hE'

theorem pos22_iff {E E' R R' : List Bool} {x y x' y' : ℕ}
    (hE : E.drop 13 = dbl (unary x) ++ (dbl (unary y) ++ R))
    (hE' : E'.drop 13 = dbl (unary x') ++ (dbl (unary y') ++ R')) :
    pos22 E E' = true ↔ y = y' := by
  rw [pos22, tailsE_posD hE (fun _ t b' => pos21 b' (shR t)) (fun _ _ _ => rfl),
    pos21_iff hE' (by rw [shR_drop])]
  exact eq_comm

theorem samePair_iff {E E' R R' : List Bool} {x y x' y' : ℕ}
    (hE : E.drop 13 = dbl (unary x) ++ (dbl (unary y) ++ R))
    (hE' : E'.drop 13 = dbl (unary x') ++ (dbl (unary y') ++ R')) :
    samePair E E' = true ↔ x = x' ∧ y = y' := by
  rw [samePair, Bool.and_eq_true, samePos_iff hE hE', pos22_iff hE hE']

/-- The entry of a pair fact, from its tag and its shape. -/
theorem eq_entN_cfN {t E : List Bool} (ht : t.length = 3) (hpre : kp t <+: E)
    (h : pairEnd E = true) :
    ∃ x y, E = kp t ++ (dbl (unary x) ++ (dbl (unary y) ++ [false])) := by
  obtain ⟨x, y, hxy⟩ := (pairEnd_iff E).1 h
  exact ⟨x, y, by rw [kp_split ht hpre, hxy]⟩

theorem entN_edge (x y : ℕ) :
    entN (cfN (.edge x y)) = kp tE3 ++ (dbl (unary x) ++ (dbl (unary y) ++ [false])) :=
  entN_cfN (.edge x y)

theorem entN_cl (x y : ℕ) :
    entN (cfN (.cl x y)) = kp tC3 ++ (dbl (unary x) ++ (dbl (unary y) ++ [false])) :=
  entN_cfN (.cl x y)

theorem entN_nc (x y : ℕ) :
    entN (cfN (.nc x y)) = kp tN3 ++ (dbl (unary x) ++ (dbl (unary y) ++ [false])) :=
  entN_cfN (.nc x y)

theorem drop_edge (x y : ℕ) :
    (entN (cfN (.edge x y))).drop 13 = dbl (unary x) ++ (dbl (unary y) ++ [false]) :=
  drop_entN_cfN (.edge x y)

theorem drop_cl (x y : ℕ) :
    (entN (cfN (.cl x y))).drop 13 = dbl (unary x) ++ (dbl (unary y) ++ [false]) :=
  drop_entN_cfN (.cl x y)

theorem drop_nc (x y : ℕ) :
    (entN (cfN (.nc x y))).drop 13 = dbl (unary x) ++ (dbl (unary y) ++ [false]) :=
  drop_entN_cfN (.nc x y)

theorem pairEnd_cfN (e : NF) : pairEnd (entN (cfN e)) = true :=
  (pairEnd_iff _).2 ⟨_, _, drop_entN_cfN e⟩

/-- An entry with the tag `tE3` and the shape of a pair is an `edge` entry. -/
theorem entry_edge {f : ℕ} (hpre : kp tE3 <+: entN f) (h : pairEnd (entN f) = true) :
    ∃ x y, f = cfN (.edge x y) := by
  obtain ⟨x, y, hxy⟩ := eq_entN_cfN rfl hpre h
  exact ⟨x, y, entN_injective (hxy.trans (entN_edge x y).symm)⟩

theorem entry_cl {f : ℕ} (hpre : kp tC3 <+: entN f) (h : pairEnd (entN f) = true) :
    ∃ x y, f = cfN (.cl x y) := by
  obtain ⟨x, y, hxy⟩ := eq_entN_cfN rfl hpre h
  exact ⟨x, y, entN_injective (hxy.trans (entN_cl x y).symm)⟩

theorem entry_nc {f : ℕ} (hpre : kp tN3 <+: entN f) (h : pairEnd (entN f) = true) :
    ∃ x y, f = cfN (.nc x y) := by
  obtain ⟨x, y, hxy⟩ := eq_entN_cfN rfl hpre h
  exact ⟨x, y, entN_injective (hxy.trans (entN_nc x y).symm)⟩

/-! ### Quantifiers over the listed pairs -/

theorem atL_ord_any (P : List Bool → List Bool → List Bool → List Bool → Bool) (q : InstDesc)
    (v₁ v₂ v₃ : List Bool) :
    atL 3 (anyE P) (instSer q) v₁ v₂ v₃ = true ↔
      ∃ e ∈ q.tnI.ordList, P (true :: bstr (serPair e)) v₁ v₂ v₃ = true := by
  rw [instSer_split, atL_succ, atL_succ, atL_succ, atL_zero, anyE_iff]; simp

end Thr

end Space

end HTN
