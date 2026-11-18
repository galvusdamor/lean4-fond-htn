import HtnComplexity.Logspace.ParseT
/-!
# Navigating in a located code

`HTN.Logspace.At y d p F a`: the code of the value `a` of the format `F` is written at the location
`(d, p)` of the input `y`.  Terms that move through codes, with their meaning:

* `endT` — the length of the code (`HTN.Logspace.eval_endT`); `sndT` — the location of the second
  component of a pair (`HTN.Logspace.At.snd`);
* `hdrT`, `entryT`, `lenT` — the position of the `k`-th entry of a list, its location one level
  deeper, the length of the list (`HTN.Logspace.At.entry`, `HTN.Logspace.eval_lenT`);
* `natEqT` — equality of two numbers written anywhere (`HTN.Logspace.eval_natEqT`);
* `boolT` — a bit (`HTN.Logspace.eval_boolT`).
-/

namespace HTN

namespace Logspace

open Cx Cx.LTerm Syn PTime

/-- **The value `a` is written at the location `(d, p)`.** -/
def At (y : List Bool) (d p : ℕ) (F : Fmt) (a : F.ty) : Prop := LocS y d p (F.enc a)

variable {y : List Bool} {M : ℕ}

theorem LocS.drop {d p : ℕ} {w : List Bool} (h : LocS y d p w) (s : ℕ) :
    LocS y d (p + 2 ^ d * s) (w.drop s) := by
  intro k hk
  simp only [List.length_drop] at hk
  obtain ⟨e1, e2⟩ := h (s + k) (by omega)
  refine ⟨by rw [mul_add] at e1; omega, ?_⟩
  unfold rd at e2 ⊢
  rw [show p + 2 ^ d * s + 2 ^ d * k = p + 2 ^ d * (s + k) by ring, e2]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem LocS.pos_lt {d p : ℕ} {w : List Bool} (h : LocS y d p w) (hw : w ≠ []) : p < y.length := by
  have := (h 0 (List.length_pos_iff.2 hw)).1
  simpa using this

theorem At.virt {d p : ℕ} {F : Fmt} {a : F.ty} (h : At y d p F a) :
    ∃ r, virt y d p y.length = F.enc a ++ r :=
  ⟨_, LocS.virt_append h (LocS.length_le h)⟩

/-! ### Ends and pairs -/

/-- The length of the code at `(d, p)`. -/
def endT (F : Fmt) (d : ℕ) (p : LTerm) : LTerm := parseT F d p .len (.lit 0)

theorem eval_endT (hM : y.length + 2 ≤ M) {F : Fmt} {d : ℕ} {p : LTerm} {env : List ℕ} {a : F.ty}
    (h : At y d (eval y M env p) F a) : eval y M env (endT F d p) = (F.enc a).length := by
  rw [endT, eval_parseT hM F d p .len (.lit 0) env (by simp [eval])]
  obtain ⟨r, hr⟩ := h.virt
  simp only [eval]
  rw [prs_enc F _ 0 a r (by simpa using hr)]
  simp

/-- The location of the second component of a pair at `(d, p)`. -/
def sndT (F : Fmt) (d : ℕ) (p : LTerm) : LTerm := posT d p (endT F d p)

theorem At.fst {d p : ℕ} {F G : Fmt} {a : F.ty} {b : G.ty} (h : At y d p (.pair F G) (a, b)) :
    At y d p F a := (LocS.append.1 h).1

theorem At.snd' {d p : ℕ} {F G : Fmt} {a : F.ty} {b : G.ty} (h : At y d p (.pair F G) (a, b)) :
    At y d (p + 2 ^ d * (F.enc a).length) G b := (LocS.append.1 h).2

theorem At.snd (hM : y.length + 2 ≤ M) {F G : Fmt} {d : ℕ} {p : LTerm} {env : List ℕ} {a : F.ty} {b : G.ty}
    (h : At y d (eval y M env p) (.pair F G) (a, b)) : At y d (eval y M env (sndT F d p)) G b := by
  have h2 := h.snd'
  rw [sndT, eval_posT, eval_endT hM h.fst, min_eq_left]
  · exact h2
  · have := LocS.pos_lt h2 (Fmt.enc_ne_nil G b); omega

/-! ### Lists -/

/-- The position of the `k`-th entry of a list (its leading `true`). -/
def hdrs (l : List (List Bool)) (k : ℕ) : ℕ := ((l.take k).map fun e => 2 * e.length + 2).sum

theorem hdrs_cons_succ (e : List Bool) (l : List (List Bool)) (k : ℕ) :
    hdrs (e :: l) (k + 1) = ((bstr e).length + 1) + hdrs l k := by
  simp only [hdrs, List.take_succ_cons, List.map_cons, List.sum_cons, length_bstr]

theorem drop_blist_hdrs : ∀ (l : List (List Bool)) (k : ℕ), k ≤ l.length →
    (blist l).drop (hdrs l k) = blist (l.drop k)
  | l, 0, _ => by simp [hdrs]
  | [], k + 1, h => by simp at h
  | e :: l, k + 1, h => by
    have := drop_blist_hdrs l k (by simpa using h)
    rw [hdrs_cons_succ, ← List.drop_drop, blist_cons, List.drop_succ_cons, List.drop_left, this,
      List.drop_succ_cons]

theorem hdrs_succ (l : List (List Bool)) (k : ℕ) (hk : k < l.length) :
    hdrs l (k + 1) = hdrs l k + 2 * l[k].length + 2 := by
  simp only [hdrs, List.take_succ, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem hdrs_lt (l : List (List Bool)) (k : ℕ) (hk : k ≤ l.length) : hdrs l k < (blist l).length := by
  have h := drop_blist_hdrs l k hk
  have hne := blist_ne_nil (l.drop k)
  rw [← h] at hne
  have : (blist l).drop (hdrs l k) ≠ [] := hne
  rw [Ne, List.drop_eq_nil_iff] at this
  omega

/-- The header position of the `k`-th entry of the list at `(d, p)`. -/
def hdrT (d : ℕ) (p k : LTerm) : LTerm :=
  .fold k (.lit 0) (.add (.add (.var 0) (.lit 2)) (dbl (layLenT d (lift 2 p) .len (.add (.var 0) (.lit 1)))))

section Lists

variable {F : Fmt} {d : ℕ} {p : LTerm} {env : List ℕ} {l : List F.ty}

theorem virt_drop_hdrs (h : At y d (eval y M env p) (.list F) l) (k : ℕ) (hk : k ≤ l.length) :
    ∃ r, (virt y d (eval y M env p) y.length).drop (hdrs (l.map F.enc) k) =
      blist ((l.map F.enc).drop k) ++ r := by
  obtain ⟨r, hr⟩ := h.virt
  refine ⟨r, ?_⟩
  rw [hr, Fmt.enc_list, List.drop_append_of_le_length, drop_blist_hdrs _ _ (by simpa using hk)]
  exact (hdrs_lt _ _ (by simpa using hk)).le

theorem eval_hdrT (hM : y.length + 2 ≤ M) (h : At y d (eval y M env p) (.list F) l) :
    ∀ (k : ℕ), k ≤ l.length → ∀ (kT : LTerm), eval y M env kT = k →
      eval y M env (hdrT d p kT) = hdrs (l.map F.enc) k := by
  have hlen : (blist (l.map F.enc)).length ≤ y.length := LocS.length_le h
  have step : ∀ k < l.length, ∀ j, eval y M (hdrs (l.map F.enc) k :: j :: env)
      (.add (.add (.var 0) (.lit 2)) (dbl (layLenT d (lift 2 p) .len (.add (.var 0) (.lit 1))))) =
      hdrs (l.map F.enc) (k + 1) := by
    intro k hk j
    have hk' : k < (l.map F.enc).length := by simpa using hk
    have hlt := hdrs_lt (l.map F.enc) (k + 1) (by simpa using hk)
    obtain ⟨r, hr⟩ := virt_drop_hdrs h k hk.le
    rw [List.drop_eq_getElem_cons (l := l.map F.enc) hk'] at hr
    have hr' : (virt y d (eval y M env p) y.length).drop (hdrs (l.map F.enc) k) =
        blist ((l.map F.enc)[k] :: (l.map F.enc).drop (k + 1)) ++ r := hr
    obtain ⟨-, h2, -⟩ := drop_blist_cons hr'
    obtain ⟨-, -, -, hlay, -⟩ := bstr_at h2
    rw [hdrs_succ _ _ hk'] at hlt ⊢
    simp only [dbl, eval, List.getD_cons_zero]
    rw [eval_layLenT (by omega) _ _ _ _ _ (by simp [eval]; omega)]
    simp only [eval_lift2, eval, List.getD_cons_zero]
    rw [min_eq_left (show hdrs (l.map F.enc) k + 1 ≤ M by omega), hlay]
    omega
  intro k
  induction k with
  | zero => intro _ kT hkT; simp [hdrT, eval, hkT, hdrs]
  | succ k ih =>
    intro hk kT hkT
    have := ih (by omega) (.lit k) rfl
    simp only [hdrT, eval, hkT] at this ⊢
    rw [List.range_succ, List.foldl_append, this]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step k (by omega) k

/-- The location (one level deeper) of the `k`-th entry of the list at `(d, p)`. -/
def entryT (d : ℕ) (p k : LTerm) : LTerm := posT d p (.add (hdrT d p k) (.lit 2))

theorem At.entry (hM : y.length + 2 ≤ M) (h : At y d (eval y M env p) (.list F) l) {k : ℕ} (hk : k < l.length)
    {kT : LTerm} (hkT : eval y M env kT = k) :
    At y (d + 1) (eval y M env (entryT d p kT)) F l[k] := by
  have hk' : k < (l.map F.enc).length := by simpa using hk
  have hd := LocS.drop h (hdrs (l.map F.enc) k)
  rw [Fmt.enc_list, drop_blist_hdrs _ _ hk'.le, List.drop_eq_getElem_cons hk', blist_cons] at hd
  have hd2 := LocS.drop hd 1
  simp only [List.drop_succ_cons, List.drop_zero] at hd2
  have hlay := LocS.layer hd2
  have hpos : eval y M env p + 2 ^ d * hdrs (l.map F.enc) k + 2 ^ d * 1 + 2 ^ d =
      eval y M env p + 2 ^ d * (hdrs (l.map F.enc) k + 2) := by ring
  rw [hpos, List.getElem_map] at hlay
  have hlt := LocS.pos_lt hlay (Fmt.enc_ne_nil F _)
  rw [entryT, eval_posT]
  simp only [eval]
  rw [eval_hdrT hM h k hk.le kT hkT, min_eq_left (show hdrs (l.map F.enc) k + 2 ≤ M by
    have : hdrs (l.map F.enc) k + 2 ≤ 2 ^ d * (hdrs (l.map F.enc) k + 2) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos d)
    omega), min_eq_left (by omega)]
  exact hlay

/-- The length of the list at `(d, p)`. -/
def lenT (d : ℕ) (p : LTerm) : LTerm := firstB .len (not (btT d (lift 2 p) .len (hdrT d (lift 2 p) (.var 0))))

theorem eval_lenT (hM : y.length + 2 ≤ M) (h : At y d (eval y M env p) (.list F) l) :
    eval y M env (lenT d p) = l.length := by
  have hlen : (blist (l.map F.enc)).length ≤ y.length := LocS.length_le h
  have hb : ∀ k ≤ l.length, bt (virt y d (eval y M env p) y.length) (hdrs (l.map F.enc) k) =
      decide (k < l.length) := by
    intro k hk
    obtain ⟨r, hr⟩ := virt_drop_hdrs h k hk
    rcases Nat.lt_or_ge k l.length with hlt | hge
    · rw [List.drop_eq_getElem_cons (l := l.map F.enc) (by simpa using hlt), blist_cons,
        List.cons_append] at hr
      rw [show hdrs (l.map F.enc) k = hdrs (l.map F.enc) k + 0 by rfl, ← bt_drop, hr]; simp [bt, hlt]
    · have : k = l.length := by omega
      subst this
      have hnil : (l.map F.enc).drop l.length = [] := by simp
      rw [hnil, blist_nil, List.cons_append] at hr
      rw [show hdrs (l.map F.enc) l.length = hdrs (l.map F.enc) l.length + 0 by rfl, ← bt_drop, hr]; simp [bt]
  have hl : l.length < y.length := by
    have := length_le_blist (l.map F.enc); simp at this; omega
  rw [lenT, eval_firstB]
  simp only [eval]
  change firstIdx _ y.length = l.length
  have h' : ∀ i N, At y d (eval y M (i :: N :: env) (lift 2 p)) (.list F) l := fun i N => by
    rwa [eval_lift2]
  apply firstIdx_eq hl
  · simp only [eval_not, eval_btT (by omega : y.length ≤ M), eval_lift2, eval]
    rw [eval_hdrT hM (h' _ _) l.length le_rfl (.var 0) (by simp [eval]), hb _ le_rfl]; simp
  · intro i hi
    simp only [eval_not, eval_btT (by omega : y.length ≤ M), eval_lift2, eval]
    rw [eval_hdrT hM (h' _ _) i hi.le (.var 0) (by simp [eval]), hb _ hi.le]; simp [hi]

end Lists

/-! ### Numbers and bits -/

/-- The number of binary digits of the number at `(d, p)`. -/
def natLenT (d : ℕ) (p : LTerm) : LTerm := layLenT d p .len (.lit 0)

/-- Binary digit `j` of the number at `(d, p)`. -/
def nbitT (d : ℕ) (p j : LTerm) : LTerm := .bit (posT (d + 1) (posT d p (.lit 1)) j)

theorem eval_natLenT (hM : y.length + 2 ≤ M) {d : ℕ} {p : LTerm} {env : List ℕ} {n : ℕ}
    (h : At y d (eval y M env p) .nat n) : eval y M env (natLenT d p) = (bitsOfNat n).length := by
  obtain ⟨r, hr⟩ := At.virt h
  rw [natLenT, eval_layLenT (by omega) _ _ _ _ _ (by simp [eval]; omega)]
  simp only [eval]
  obtain ⟨-, -, -, hlay, -⟩ := bstr_at (s := 0) (c := bitsOfNat n) (r := r) (by simpa using hr)
  exact hlay

theorem eval_nbitT (hM : y.length + 2 ≤ M) {d : ℕ} {p j : LTerm} {env : List ℕ} {n : ℕ}
    (h : At y d (eval y M env p) .nat n) (hj : eval y M env j < (bitsOfNat n).length) :
    eval y M env (nbitT d p j) = if (bitsOfNat n)[eval y M env j] then 1 else 0 := by
  have hc : LocS y (d + 1) (eval y M env p + 2 ^ d) (bitsOfNat n) :=
    LocS.layer (r := []) (by simpa [At, Fmt.enc, serNat] using h)
  obtain ⟨e1, e2⟩ := hc _ hj
  have : eval y M env p + 2 ^ d ≤ eval y M env p + 2 ^ d + 2 ^ (d + 1) * eval y M env j := by omega
  simp only [nbitT, eval, eval_posT]
  rw [min_eq_left (show eval y M env p + 2 ^ d * 1 ≤ M by omega), mul_one,
    min_eq_left (show eval y M env p + 2 ^ d + 2 ^ (d + 1) * eval y M env j ≤ M by omega)]
  unfold rd at e2
  rw [e2, List.getD_eq_getElem _ _ hj]

/-- **Equality of the numbers at `(d₁, p₁)` and `(d₂, p₂)`.** -/
def natEqT (d₁ : ℕ) (p₁ : LTerm) (d₂ : ℕ) (p₂ : LTerm) : LTerm :=
  and (eq (natLenT d₁ p₁) (natLenT d₂ p₂))
    (forallB (natLenT d₁ p₁) (eq (nbitT d₁ (lift 2 p₁) (.var 1)) (nbitT d₂ (lift 2 p₂) (.var 1))))

theorem eval_natEqT (hM : y.length + 2 ≤ M) {d₁ d₂ : ℕ} {p₁ p₂ : LTerm} {env : List ℕ} {n₁ n₂ : ℕ}
    (h₁ : At y d₁ (eval y M env p₁) .nat n₁) (h₂ : At y d₂ (eval y M env p₂) .nat n₂) :
    eval y M env (natEqT d₁ p₁ d₂ p₂) = if n₁ = n₂ then 1 else 0 := by
  have h1M : 1 ≤ M := by omega
  simp only [natEqT, eval_and, eval_eq _ _ _ h1M, eval_forallB, eval_natLenT hM h₁, eval_natLenT hM h₂]
  have hiff : ((bitsOfNat n₁).length = (bitsOfNat n₂).length ∧
      ∀ i < (bitsOfNat n₁).length, eval y M (1 :: i :: env) (nbitT d₁ (lift 2 p₁) (.var 1)) =
        eval y M (1 :: i :: env) (nbitT d₂ (lift 2 p₂) (.var 1))) ↔ n₁ = n₂ := by
    constructor
    · rintro ⟨hl, hb⟩
      apply bitsOfNat_injective
      apply List.ext_getElem hl
      intro i hi1 hi2
      have := hb i hi1
      have h₁' : At y d₁ (eval y M (1 :: i :: env) (lift 2 p₁)) .nat n₁ := by rwa [eval_lift2]
      have h₂' : At y d₂ (eval y M (1 :: i :: env) (lift 2 p₂)) .nat n₂ := by rwa [eval_lift2]
      rw [eval_nbitT hM h₁' (by simpa [eval] using hi1),
        eval_nbitT hM h₂' (by simpa [eval] using hi2)] at this
      simp only [eval, List.getD_cons_succ, List.getD_cons_zero] at this
      cases hb1 : (bitsOfNat n₁)[i] <;> cases hb2 : (bitsOfNat n₂)[i] <;> simp_all
    · rintro rfl
      refine ⟨rfl, fun i hi => ?_⟩
      have h₁' : At y d₁ (eval y M (1 :: i :: env) (lift 2 p₁)) .nat n₁ := by rwa [eval_lift2]
      rw [eval_nbitT hM h₁' (by simpa [eval] using hi),
        eval_nbitT hM (by rwa [eval_lift2]) (by simpa [eval] using hi)]
  by_cases h : n₁ = n₂
  · have := hiff.2 h
    rw [if_pos h]
    rw [if_pos (by simpa using this)]
  · rw [if_neg h]
    by_cases hl : (bitsOfNat n₁).length = (bitsOfNat n₂).length
    · have : ¬ ∀ i < (bitsOfNat n₁).length, eval y M (1 :: i :: env) (nbitT d₁ (lift 2 p₁) (.var 1)) =
          eval y M (1 :: i :: env) (nbitT d₂ (lift 2 p₂) (.var 1)) := fun hb => h (hiff.1 ⟨hl, hb⟩)
      rw [if_pos hl]
      rw [if_neg (show ¬ ∀ i < (bitsOfNat n₁).length, (if eval y M (1 :: i :: env) (nbitT d₁ (lift 2 p₁) (.var 1)) =
          eval y M (1 :: i :: env) (nbitT d₂ (lift 2 p₂) (.var 1)) then 1 else 0) ≠ 0 from
        fun hb => this fun i hi => by simpa using hb i hi)]
      simp
    · simp [hl]

/-- The bit at `(d, p)`. -/
def boolT (d : ℕ) (p : LTerm) : LTerm := .bit (posT d p (.lit 0))

theorem eval_boolT (hM : y.length + 2 ≤ M) {d : ℕ} {p : LTerm} {env : List ℕ} {b : Bool}
    (h : At y d (eval y M env p) .bool b) : eval y M env (boolT d p) = if b then 1 else 0 := by
  obtain ⟨e1, e2⟩ := h 0 (by simp [Fmt.enc])
  simp only [boolT, eval, eval_posT, mul_zero, add_zero] at e1 ⊢
  rw [min_eq_left (by omega)]
  unfold rd at e2
  simp only [mul_zero, add_zero] at e2
  rw [e2]; simp [Fmt.enc]

end Logspace

end HTN
