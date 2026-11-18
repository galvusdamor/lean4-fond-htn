import HtnComplexity.Space.SeqTests
/-!
# What the pieces of the gadget tests mean

The string-level reading of the pieces of `HtnComplexity/Space/SeqTests.lean`: the numerals
and entries of the compiled facts, the witness, position and label pieces.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### Numerals and entries of compiled facts -/

theorem bitsOfNat_cfG (g : GF) : bitsOfNat (cfG g) = gT ++ gbits g := by
  rw [cfG, bitsOfNat_four_add_two, bitsOfNat_gfNum]; rfl

theorem bitsOfNat_cfI (v : ℕ) : bitsOfNat (cfI v) = tagI3 ++ bitsOfNat v := by
  rw [cfI, bitsOfNat_four_add_two, bitsOfNat_two_mul_add_one]; rfl

theorem bitsOfNat_cRoot (d : DomDesc) :
    bitsOfNat (cRoot d) = [true, true] ++ bitsOfNat (leastFresh (vocC d)) := by
  rw [cRoot, bitsOfNat_four_add_three]; rfl

theorem ent_app (u v : List Bool) : true :: bstr (u ++ v) = true :: dbl u ++ (dbl v ++ [false]) := by
  rw [bstr_eq_dbl, dbl_append]; simp

@[simp] theorem length_kp {t : List Bool} (ht : t.length = 3) : (kp t).length = 13 := by
  simp [kp, gT, length_dbl, ht]

theorem drop_kp {t : List Bool} (ht : t.length = 3) (Y : List Bool) : (kp t ++ Y).drop 13 = Y := by
  rw [List.drop_append_of_le_length (by simp [ht]), List.drop_of_length_le (by simp [ht])]
  simp

theorem dbl_true : dbl [true] = [true, true] := rfl

theorem ent_gpos (t : List Bool) (p : ℕ) :
    true :: bstr (gT ++ (t ++ unary p)) = kp t ++ (dbl (unary p) ++ [false]) := by
  rw [← List.append_assoc, ent_app, dbl_append]; simp [kp, dbl_append]

theorem ent_gdata (t : List Bool) (p : ℕ) (r : List Bool) :
    true :: bstr (gT ++ (t ++ unary p ++ r ++ [true])) = kp t ++ (dbl (unary p) ++ (dbl r ++ ttf)) := by
  rw [show gT ++ (t ++ unary p ++ r ++ [true]) = (gT ++ t) ++ (unary p ++ r ++ [true]) by simp,
    ent_app]
  simp [kp, dbl_append, dbl_true, ttf]

theorem entG_wit (p a : ℕ) :
    true :: bstr (bitsOfNat (cfG (.wit p a))) = kp tWit ++ (dbl (unary p) ++ (dbl (serNat a) ++ ttf)) := by
  rw [bitsOfNat_cfG, ← ent_gdata]; rfl

theorem entG_lab (p : ℕ) (x : ℕ ⊕ ℕ) :
    true :: bstr (bitsOfNat (cfG (.lab p x))) = kp tLab ++ (dbl (unary p) ++ (dbl (lblBits x) ++ ttf)) := by
  rw [bitsOfNat_cfG, ← ent_gdata]; rfl

theorem entG_cur (p : ℕ) : true :: bstr (bitsOfNat (cfG (.cur p))) = kp tCur ++ (dbl (unary p) ++ [false]) := by
  rw [bitsOfNat_cfG, ← ent_gpos]; rfl

theorem entG_len (p : ℕ) : true :: bstr (bitsOfNat (cfG (.len p))) = kp tLen ++ (dbl (unary p) ++ [false]) := by
  rw [bitsOfNat_cfG, ← ent_gpos]; rfl

theorem entG_nop (p : ℕ) : true :: bstr (bitsOfNat (cfG (.nop p))) = kp tNop ++ (dbl (unary p) ++ [false]) := by
  rw [bitsOfNat_cfG, ← ent_gpos]; rfl

/-- The prefix `kp t` of an entry reads the first bits of the numeral. -/
theorem kp_prefix_iff (t w : List Bool) : kp t <+: true :: bstr w ↔ gT ++ t <+: w := by
  rw [kp, bstr_eq_dbl, List.cons_prefix_cons]
  simp only [true_and]
  exact dbl_prefix_iff _ _ []

/-! ### Two small facts about lists -/

theorem dbl_snoc_tt {D r0 : List Bool} (h : D ++ [true, true] = dbl r0) :
    ∃ r, r0 = r ++ [true] ∧ D = dbl r := by
  rcases List.eq_nil_or_concat r0 with rfl | ⟨r, b, rfl⟩
  · have := congrArg List.length h; simp [dbl] at this
  · rw [List.concat_eq_append] at h ⊢
    rw [dbl_append] at h
    have h2 : dbl [b] = [true, b] := rfl
    rw [h2] at h
    obtain ⟨h3, h4⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true, true_and] at h4
    exact ⟨r, by rw [← h4], h3⟩

theorem dbl_bstr_parse {u v r r' : List Bool} (h : dbl (bstr u) ++ r = dbl (bstr v) ++ r') :
    u = v ∧ r = r' := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons c v => simp [dbl_cons, dbl] at h
  | cons b u ih =>
    cases v with
    | nil => simp [dbl_bstr_cons, dbl_cons, dbl] at h
    | cons c v =>
      simp only [dbl_bstr_cons, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih h.2
      exact ⟨by rw [h.1, h1], h2⟩

theorem cutAt_of_eq {B Z s : List Bool} (h : B = Z ++ s) : cutAt B s = Z := by
  rw [h, cutAt_append]

/-! ### Witness entries -/

theorem witNode_parse {w D : List Bool} (h : witNode (true :: bstr w) D = true) :
    ∃ p r, w = gT ++ (tWit ++ unary p ++ r ++ [true]) ∧ D = dbl r := by
  simp only [witNode, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨s, hs⟩, hsuf⟩, hpos⟩ := h
  have hdrop : (true :: bstr w).drop 13 = s := by rw [← hs, drop_kp rfl]
  rw [hdrop] at hpos
  obtain ⟨p, hp⟩ := (isPosD_iff _).1 hpos
  have hne : cutAt s (D ++ ttf) ≠ [] := by rw [hp]; simp [unary, dbl]
  have hlen : (D ++ ttf).length ≤ s.length := by
    by_contra hc
    apply hne
    simp only [cutAt]
    rw [Nat.sub_eq_zero_of_le (by omega)]
    simp
  have hsuf' : (D ++ ttf) <:+ s :=
    List.suffix_of_suffix_length_le hsuf ⟨kp tWit, hs⟩ hlen
  have hs2 : s = dbl (unary p) ++ (D ++ ttf) := by
    rw [← hp]; exact (suffix_take_append hsuf').symm
  rw [hs2, ent_eq] at hs
  have h4 : dbl (gT ++ tWit) ++ (dbl (unary p) ++ (D ++ ttf)) = dbl w ++ [false] := by
    simpa [kp] using hs
  have hs3 : dbl (gT ++ tWit ++ unary p) ++ (D ++ [true, true] ++ [false]) = dbl w ++ [false] := by
    rw [← h4, dbl_append (gT ++ tWit)]
    simp [ttf]
  obtain ⟨r0, hw, hr0⟩ := dbl_split hs3
  have hr0' : D ++ [true, true] = dbl r0 := (List.append_inj' hr0 rfl).1
  obtain ⟨r, rfl, rfl⟩ := dbl_snoc_tt hr0'
  exact ⟨p, r, by rw [hw]; simp, rfl⟩

theorem witNode_mk (t : List Bool) (p : ℕ) (D : List Bool) (ht : t = tWit) :
    witNode (kp t ++ (dbl (unary p) ++ (D ++ ttf))) D = true := by
  subst ht
  simp only [witNode, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨List.prefix_append _ _, ?_⟩, ?_⟩
  · exact ⟨kp tWit ++ dbl (unary p), by simp⟩
  · rw [drop_kp rfl, cutAt_append]
    exact (isPosD_iff _).2 ⟨p, rfl⟩

/-- **A witness entry for a serialised node**: on the entry of a numeral, `witNode` with the
doubled serialisation of `a` holds exactly for the witness facts of `a`. -/
theorem witNode_ent_iff (f a : ℕ) :
    witNode (true :: bstr (bitsOfNat f)) (dbl (serNat a)) = true ↔ ∃ p, f = cfG (.wit p a) := by
  constructor
  · intro h
    obtain ⟨p, r, hw, hr⟩ := witNode_parse h
    have hr' : r = serNat a := dbl_injective hr.symm
    refine ⟨p, bitsOfNat_injective ?_⟩
    rw [hw, bitsOfNat_cfG, hr']
    rfl
  · rintro ⟨p, rfl⟩
    rw [entG_wit]
    exact witNode_mk _ p _ rfl

/-- The entry that passes `witNode` for the doubled serialisation of a node is a witness entry. -/
theorem witNode_canon {w : List Bool} (hw : IsCanon w) {a : ℕ}
    (h : witNode (true :: bstr w) (dbl (serNat a)) = true) : ∃ p, natOfBits w = cfG (.wit p a) := by
  rw [← hw] at h
  exact (witNode_ent_iff _ a).1 h

/-! ### Positions -/

theorem tailsE_posD {P : List Bool → List Bool → List Bool → List Bool → Bool}
    {B B' z R : List Bool} {p : ℕ} (hB : B = dbl (unary p) ++ R)
    (Q : List Bool → List Bool → List Bool → Bool)
    (hP : ∀ t b b', P t b b' z = (isPosD (cutAt b t) && Q (cutAt b t) t b')) :
    tailsE P B B B' z = true ↔ Q (dbl (unary p)) R B' = true := by
  rw [tailsE_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [hP, Bool.and_eq_true] at h
    have hsplit : cutAt B s ++ s = dbl (unary p) ++ R := by
      rw [← hB]; exact suffix_take_append hs
    obtain ⟨h1, h2⟩ := posD_unique h.1 ((isPosD_iff _).2 ⟨p, rfl⟩) hsplit
    rw [← h1, ← h2]; exact h.2
  · intro h
    refine ⟨R, ⟨dbl (unary p), hB.symm⟩, ?_⟩
    rw [hP, cutAt_of_eq hB, Bool.and_eq_true]
    exact ⟨(isPosD_iff _).2 ⟨p, rfl⟩, h⟩

theorem samePos_iff {E E' R R' : List Bool} {p p' : ℕ} (hE : E.drop 13 = dbl (unary p) ++ R)
    (hE' : E'.drop 13 = dbl (unary p') ++ R') : samePos E E' = true ↔ p = p' := by
  rw [samePos, tailsE_posD hE (fun Z _ b' => decide (Z <+: b')) (fun _ _ _ => rfl), hE',
    decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs⟩
    exact (dbl_unary_parse (r := s) (by rw [hs])).1
  · rintro rfl; exact List.prefix_append _ _

theorem succPos_iff {E E' R R' : List Bool} {p p' : ℕ} (hE : E.drop 13 = dbl (unary p) ++ R)
    (hE' : E'.drop 13 = dbl (unary p') ++ R') : succPos E E' = true ↔ p' = p + 1 := by
  rw [succPos, tailsE_posD hE (fun Z _ b' => decide (([true, false] ++ Z) <+: b'))
    (fun _ _ _ => rfl), hE', decide_eq_true_eq]
  have h1 : [true, false] ++ dbl (unary p) = dbl (unary (p + 1)) := by rw [dbl_unary_succ]; rfl
  rw [h1]
  constructor
  · rintro ⟨s, hs⟩
    exact (dbl_unary_parse (r := s) (by rw [hs])).1.symm
  · rintro rfl; exact List.prefix_append _ _

theorem dbl_rep_prefix_iff (p p' : ℕ) (R' : List Bool) :
    dbl (List.replicate p false) <+: dbl (unary p') ++ R' ↔ p ≤ p' := by
  induction p generalizing p' with
  | zero => simp [dbl]
  | succ p ih =>
    cases p' with
    | zero => simp [List.replicate_succ, dbl_cons, dbl_unary_zero]
    | succ p' =>
      rw [List.replicate_succ, dbl_cons, dbl_unary_succ]
      simp only [List.cons_append, List.cons_prefix_cons, true_and, ih]
      omega

theorem lePos_iff {E E' R R' : List Bool} {p p' : ℕ} (hE : E.drop 13 = dbl (unary p) ++ R)
    (hE' : E'.drop 13 = dbl (unary p') ++ R') : lePos E E' = true ↔ p ≤ p' := by
  rw [lePos, tailsE_posD hE (fun Z _ b' => decide (Z.take (Z.length - 2) <+: b'))
    (fun _ _ _ => rfl), hE', decide_eq_true_eq]
  have h1 : (dbl (unary p)).take ((dbl (unary p)).length - 2) = dbl (List.replicate p false) := by
    rw [unary, dbl_append]
    simp [length_dbl, dbl_true]
  rw [h1, dbl_rep_prefix_iff]

theorem posZero_iff {E R : List Bool} {p : ℕ} (hE : E.drop 13 = dbl (unary p) ++ R) :
    posZero E = true ↔ p = 0 := by
  rw [posZero, hE, decide_eq_true_eq]
  cases p with
  | zero => simp [dbl_unary_zero]
  | succ p => simp [dbl_unary_succ]

theorem sameNode_iff {E E' R R' : List Bool} {p p' : ℕ} (hE : E.drop 13 = dbl (unary p) ++ R)
    (hE' : E'.drop 13 = dbl (unary p') ++ R') : sameNode E E' = true ↔ R = R' := by
  rw [sameNode, tailsE_posD hE (fun _ t b' => decide (t <:+ b') && isPosD (cutAt b' t))
    (fun _ _ _ => by simp [sameNodeBody, Bool.and_assoc]), hE', Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hs, hpos⟩
    have hsplit : cutAt (dbl (unary p') ++ R') R ++ R = dbl (unary p') ++ R' :=
      suffix_take_append hs
    exact (posD_unique hpos ((isPosD_iff _).2 ⟨p', rfl⟩) hsplit).2
  · rintro rfl
    exact ⟨List.suffix_append _ _, by rw [cutAt_append]; exact (isPosD_iff _).2 ⟨p', rfl⟩⟩

theorem posEnd_iff (E : List Bool) : posEnd E = true ↔ ∃ p, E.drop 13 = dbl (unary p) ++ [false] := by
  rw [posEnd, Bool.and_eq_true, decide_eq_true_eq, isPosD_iff]
  constructor
  · rintro ⟨⟨p, hp⟩, hs⟩
    refine ⟨p, ?_⟩
    rw [← hp]
    have := suffix_take_append hs
    simpa using this.symm
  · rintro ⟨p, hp⟩
    rw [hp]
    exact ⟨⟨p, by simp⟩, List.suffix_append _ _⟩

end SeqM

end Space

end HTN
