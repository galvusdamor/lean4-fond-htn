import HtnComplexity.Space.SeqInit
import ComplexityTheory.Complexity.CobhamDFA
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# String tools for the initial test of the gadget machine

The initial test of the machine for unrooted totally ordered instances (step A3 of
`TABLE4-PLAN.md`) takes the entries of the configuration apart.  An entry is the doubled form
`true :: bstr w` of a numeral `w`, and the numerals of the gadget's facts contain unary positions
and serialised identifiers.  This file provides the pieces:

* three finite-state recognisers — `HTN.Space.SeqM.isPosD` (a doubled unary position
  `dbl (unary p)`), `HTN.Space.SeqM.isBD` (a doubled self-delimiting string `dbl (bstr u)`) and
  `HTN.Space.SeqM.isDblD` (a doubled string `dbl u`) — with their meaning and their membership
  in Cobham's class (`HTN.Space.SeqM.cobhamB_dfa`);
* the splitting lemma `HTN.Space.SeqM.dbl_split` for doubled strings with a terminator;
* the prefix-uniqueness of doubled positions.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### Finite-state recognisers are predicates of Cobham's class -/

theorem cobhamB_dfa {σ : Type} [Fintype σ] [DecidableEq σ] (init : σ) (step : σ → Bool → σ) (out : σ → Bool)
    {a : Fn} (ha : Cobham a) : CobhamB fun args => out ((a args).foldl step init) := by
  obtain ⟨f, hf, hFf⟩ := (polyTimeFun_dfa init step out).cobham
  refine (Cobham.comp hf (hs := [a]) (by simpa using ha)).of_eq' fun args => ?_
  simp only [compFn, List.map_cons, List.map_nil]
  exact (hFf (a args)).symm

/-! ### Doubled unary positions -/

/-- The states of the recogniser of doubled unary positions. -/
inductive PosSt
  | start | one | acc | dead
  deriving DecidableEq, Fintype

/-- The transition of the recogniser of `(10)*(11)`. -/
def posStep : PosSt → Bool → PosSt
  | .start, true => .one
  | .one, false => .start
  | .one, true => .acc
  | _, _ => .dead

/-- **Is the string a doubled unary position `dbl (unary p)`?** -/
def isPosD (Z : List Bool) : Bool := decide (Z.foldl posStep .start = .acc)

theorem foldl_posStep_dead (x : List Bool) : x.foldl posStep .dead = .dead := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [posStep] using ih

theorem foldl_posStep_acc (x : List Bool) (hx : x ≠ []) : x.foldl posStep .acc = .dead := by
  cases x with
  | nil => exact absurd rfl hx
  | cons b x => cases b <;> simpa [posStep] using foldl_posStep_dead x

theorem dbl_unary_zero : dbl (unary 0) = [true, true] := rfl

theorem dbl_unary_succ (p : ℕ) : dbl (unary (p + 1)) = true :: false :: dbl (unary p) := by
  simp [unary, List.replicate_succ, dbl_cons]

theorem posD_of_foldl : ∀ Z : List Bool, Z.foldl posStep .start = .acc → ∃ p, Z = dbl (unary p)
  | [], h => by simp at h
  | [false], h => by simp [posStep] at h
  | [true], h => by simp [posStep] at h
  | false :: _ :: Z, h => by simp [posStep, foldl_posStep_dead] at h
  | true :: false :: Z, h => by
    obtain ⟨p, rfl⟩ := posD_of_foldl Z (by simpa [posStep] using h)
    exact ⟨p + 1, by rw [dbl_unary_succ]⟩
  | true :: true :: Z, h => by
    rcases eq_or_ne Z [] with rfl | hZ
    · exact ⟨0, rfl⟩
    · simp [posStep, foldl_posStep_acc Z hZ] at h

theorem isPosD_iff (Z : List Bool) : isPosD Z = true ↔ ∃ p, Z = dbl (unary p) := by
  rw [isPosD, decide_eq_true_eq]
  constructor
  · exact posD_of_foldl Z
  · rintro ⟨p, rfl⟩
    induction p with
    | zero => rfl
    | succ p ih => rw [dbl_unary_succ]; simpa [posStep] using ih

theorem dbl_unary_parse {p p' : ℕ} {r r' : List Bool}
    (h : dbl (unary p) ++ r = dbl (unary p') ++ r') : p = p' ∧ r = r' := by
  induction p generalizing p' with
  | zero =>
    cases p' with
    | zero => simpa [dbl_unary_zero] using h
    | succ p' => simp [dbl_unary_zero, dbl_unary_succ] at h
  | succ p ih =>
    cases p' with
    | zero => simp [dbl_unary_zero, dbl_unary_succ] at h
    | succ p' =>
      simp only [dbl_unary_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by rw [h1], h2⟩

/-- Two doubled positions that are prefixes of the same string are equal. -/
theorem posD_unique {Z Z' r r' : List Bool} (hZ : isPosD Z = true) (hZ' : isPosD Z' = true)
    (h : Z ++ r = Z' ++ r') : Z = Z' ∧ r = r' := by
  obtain ⟨p, rfl⟩ := (isPosD_iff Z).1 hZ
  obtain ⟨p', rfl⟩ := (isPosD_iff Z').1 hZ'
  obtain ⟨rfl, rfl⟩ := dbl_unary_parse h
  exact ⟨rfl, rfl⟩

/-! ### Doubled self-delimiting strings -/

/-- The states of the recogniser of `(111b)*(10)`. -/
inductive BSt
  | g0 | g1 | g2 | g3 | acc | dead
  deriving DecidableEq, Fintype

/-- The transition of the recogniser of doubled self-delimiting strings. -/
def bStep : BSt → Bool → BSt
  | .g0, true => .g1
  | .g1, false => .acc
  | .g1, true => .g2
  | .g2, true => .g3
  | .g3, _ => .g0
  | _, _ => .dead

/-- **Is the string a doubled self-delimiting string `dbl (bstr u)`?** -/
def isBD (D : List Bool) : Bool := decide (D.foldl bStep .g0 = .acc)

theorem foldl_bStep_dead (x : List Bool) : x.foldl bStep .dead = .dead := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [bStep] using ih

theorem foldl_bStep_acc (x : List Bool) (hx : x ≠ []) : x.foldl bStep .acc = .dead := by
  cases x with
  | nil => exact absurd rfl hx
  | cons b x => cases b <;> simpa [bStep] using foldl_bStep_dead x

theorem dbl_bstr_cons (b : Bool) (u : List Bool) :
    dbl (bstr (b :: u)) = true :: true :: true :: b :: dbl (bstr u) := by
  simp [bstr_cons, dbl_cons]

theorem bD_of_foldl : ∀ D : List Bool, D.foldl bStep .g0 = .acc → ∃ u, D = dbl (bstr u)
  | [], h => by simp at h
  | [false], h => by simp [bStep] at h
  | [true], h => by simp [bStep] at h
  | false :: _ :: D, h => by simp [bStep, foldl_bStep_dead] at h
  | true :: false :: D, h => by
    rcases eq_or_ne D [] with rfl | hD
    · exact ⟨[], rfl⟩
    · simp [bStep, foldl_bStep_acc D hD] at h
  | [true, true], h => by simp [bStep] at h
  | true :: true :: false :: D, h => by simp [bStep, foldl_bStep_dead] at h
  | [true, true, true], h => by simp [bStep] at h
  | true :: true :: true :: b :: D, h => by
    obtain ⟨u, rfl⟩ := bD_of_foldl D (by cases b <;> simpa [bStep] using h)
    exact ⟨b :: u, by rw [dbl_bstr_cons]⟩

theorem isBD_iff (D : List Bool) : isBD D = true ↔ ∃ u, D = dbl (bstr u) := by
  rw [isBD, decide_eq_true_eq]
  constructor
  · exact bD_of_foldl D
  · rintro ⟨u, rfl⟩
    induction u with
    | nil => rfl
    | cons b u ih => rw [dbl_bstr_cons]; cases b <;> simpa [bStep] using ih

/-! ### Doubled strings -/

/-- The states of the recogniser of `(1b)*`. -/
inductive DSt
  | e0 | e1 | dead
  deriving DecidableEq, Fintype

/-- The transition of the recogniser of doubled strings. -/
def dStep : DSt → Bool → DSt
  | .e0, true => .e1
  | .e1, _ => .e0
  | _, _ => .dead

/-- **Is the string a doubled string `dbl u`?** -/
def isDblD (D : List Bool) : Bool := decide (D.foldl dStep .e0 = .e0)

theorem foldl_dStep_dead (x : List Bool) : x.foldl dStep .dead = .dead := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simpa [dStep] using ih

theorem dblD_of_foldl : ∀ D : List Bool, D.foldl dStep .e0 = .e0 → ∃ u, D = dbl u
  | [], _ => ⟨[], rfl⟩
  | [false], h => by simp [dStep] at h
  | [true], h => by simp [dStep] at h
  | false :: _ :: D, h => by simp [dStep, foldl_dStep_dead] at h
  | true :: b :: D, h => by
    obtain ⟨u, rfl⟩ := dblD_of_foldl D (by cases b <;> simpa [dStep] using h)
    exact ⟨b :: u, by rw [dbl_cons]⟩

theorem isDblD_iff (D : List Bool) : isDblD D = true ↔ ∃ u, D = dbl u := by
  rw [isDblD, decide_eq_true_eq]
  constructor
  · exact dblD_of_foldl D
  · rintro ⟨u, rfl⟩
    induction u with
    | nil => rfl
    | cons b u ih => rw [dbl_cons]; cases b <;> simpa [dStep] using ih

theorem cobhamB_isPosD {a : Fn} (ha : Cobham a) : CobhamB fun args => isPosD (a args) :=
  (cobhamB_dfa PosSt.start posStep (fun s => decide (s = .acc)) ha).of_eq fun _ => rfl

theorem cobhamB_isBD {a : Fn} (ha : Cobham a) : CobhamB fun args => isBD (a args) :=
  (cobhamB_dfa BSt.g0 bStep (fun s => decide (s = .acc)) ha).of_eq fun _ => rfl

theorem cobhamB_isDblD {a : Fn} (ha : Cobham a) : CobhamB fun args => isDblD (a args) :=
  (cobhamB_dfa DSt.e0 dStep (fun s => decide (s = .e0)) ha).of_eq fun _ => rfl

/-! ### Splitting doubled strings -/

theorem dbl_injective : Function.Injective dbl := by
  intro u v h
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => simp [dbl_cons] at h
  | cons b u ih => cases v with
    | nil => simp [dbl_cons] at h
    | cons c v =>
      simp only [dbl_cons, List.cons.injEq, true_and] at h
      rw [h.1, ih h.2]

/-- **Splitting a doubled string with a terminator.** -/
theorem dbl_split : ∀ {u w s : List Bool}, dbl u ++ s = dbl w ++ [false] →
    ∃ r, w = u ++ r ∧ s = dbl r ++ [false]
  | [], w, s, h => ⟨w, rfl, by simpa [dbl] using h⟩
  | b :: u, [], s, h => by simp [dbl_cons, dbl] at h
  | b :: u, c :: w, s, h => by
    simp only [dbl_cons, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨r, rfl, rfl⟩ := dbl_split h.2
    exact ⟨r, by rw [h.1]; rfl, rfl⟩

/-- The encoded entry of a numeral. -/
theorem ent_eq (w : List Bool) : true :: bstr w = true :: (dbl w ++ [false]) := by
  rw [bstr_eq_dbl]

/-! ### Curried quantifiers

The quantifiers of `HtnComplexity/Complexity/SerAny.lean` and `Space/Tests.lean` take their
body as a predicate on an argument list.  The versions here take a curried body of four strings,
which keeps the definitions of the tests readable. -/

/-- A curried body of four strings, as a predicate on an argument list. -/
def unc4 (P : List Bool → List Bool → List Bool → List Bool → Bool) (a : Args) : Bool :=
  P (a.getD 0 []) (a.getD 1 []) (a.getD 2 []) (a.getD 3 [])

/-- The body is a predicate of Cobham's class. -/
def CobhamB4 (P : List Bool → List Bool → List Bool → List Bool → Bool) : Prop :=
  CobhamB (unc4 P)

theorem argDep_unc4 (P : List Bool → List Bool → List Bool → List Bool → Bool) :
    ArgDep 4 (unc4 P) := by
  intro args
  simp only [unc4, getD_padArgs (by norm_num : (0 : ℕ) < 4),
    getD_padArgs (by norm_num : (1 : ℕ) < 4), getD_padArgs (by norm_num : (2 : ℕ) < 4),
    getD_padArgs (by norm_num : (3 : ℕ) < 4)]

theorem CobhamB4.app {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB4 P) {a b c d : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c)
    (hd : Cobham d) : CobhamB fun args => P (a args) (b args) (c args) (d args) :=
  (hP.comp4 ha hb hc hd).of_eq fun args => by simp [unc4]

theorem CobhamB4.of {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (h : CobhamB fun a : Args => P (a.getD 0 []) (a.getD 1 []) (a.getD 2 []) (a.getD 3 [])) :
    CobhamB4 P := h

/-- **Some suffix of `x` satisfies the body.** -/
def tailsE (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (x v₁ v₂ v₃ : List Bool) : Bool :=
  anyTailsB (unc4 P) [v₁, v₂, v₃] x

theorem tailsE_iff {P : List Bool → List Bool → List Bool → List Bool → Bool}
    {x v₁ v₂ v₃ : List Bool} : tailsE P x v₁ v₂ v₃ = true ↔ ∃ s, s <:+ x ∧ P s v₁ v₂ v₃ = true := by
  rw [tailsE, anyTailsB_eq_true]
  simp [unc4]

theorem cobhamB4_tailsE {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB4 P) : CobhamB4 (tailsE P) :=
  ((cobhamB_anyTails hP (argDep_unc4 P)).comp4 (Cobham.proj 0) (Cobham.proj 1)
    (Cobham.proj 2) (Cobham.proj 3)).of_eq fun args => by simp [unc4, tailsE, proj]

/-- **Some entry of the serialised list that starts `y` satisfies the body.** -/
def anyE (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (y v₁ v₂ v₃ : List Bool) : Bool :=
  anyEntB (unc4 P) y v₁ v₂ v₃

/-- **Every entry of the serialised list that starts `y` satisfies the body.** -/
def allE (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (y v₁ v₂ v₃ : List Bool) : Bool :=
  allEntB (unc4 P) y v₁ v₂ v₃

theorem anyE_iff (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    anyE P (blist l ++ z) v₁ v₂ v₃ = true ↔ ∃ w ∈ l, P (true :: bstr w) v₁ v₂ v₃ = true := by
  rw [anyE, anyEntB_iff]
  simp [unc4]

theorem allE_iff (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    allE P (blist l ++ z) v₁ v₂ v₃ = true ↔ ∀ w ∈ l, P (true :: bstr w) v₁ v₂ v₃ = true := by
  rw [allE, allEntB_iff]
  simp [unc4]

theorem anyE_blist_iff (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (l : List (List Bool)) (v₁ v₂ v₃ : List Bool) :
    anyE P (blist l) v₁ v₂ v₃ = true ↔ ∃ w ∈ l, P (true :: bstr w) v₁ v₂ v₃ = true := by
  simpa using anyE_iff P l [] v₁ v₂ v₃

theorem allE_blist_iff (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (l : List (List Bool)) (v₁ v₂ v₃ : List Bool) :
    allE P (blist l) v₁ v₂ v₃ = true ↔ ∀ w ∈ l, P (true :: bstr w) v₁ v₂ v₃ = true := by
  simpa using allE_iff P l [] v₁ v₂ v₃

theorem cobhamB4_anyE {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB4 P) : CobhamB4 (anyE P) :=
  (cobhamB_anyEntB hP (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2) (Cobham.proj 3)).of_eq
    fun args => by simp [unc4, anyE, proj]

theorem cobhamB4_allE {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB4 P) : CobhamB4 (allE P) :=
  (cobhamB_allEntB hP (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2) (Cobham.proj 3)).of_eq
    fun args => by simp [unc4, allE, proj]

/-- **The body, at the suffix that follows the `k` leading serialised lists of `y`.** -/
def atL : ℕ → (List Bool → List Bool → List Bool → List Bool → Bool) →
    List Bool → List Bool → List Bool → List Bool → Bool
  | 0, P, y, v₁, v₂, v₃ => P y v₁ v₂ v₃
  | k + 1, P, y, v₁, v₂, v₃ => afterB (unc4 (atL k P)) y v₁ v₂ v₃

theorem atL_zero (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (y v₁ v₂ v₃ : List Bool) : atL 0 P y v₁ v₂ v₃ = P y v₁ v₂ v₃ := rfl

theorem atL_succ (k : ℕ) (P : List Bool → List Bool → List Bool → List Bool → Bool)
    (l : List (List Bool)) (z v₁ v₂ v₃ : List Bool) :
    atL (k + 1) P (blist l ++ z) v₁ v₂ v₃ = atL k P z v₁ v₂ v₃ := by
  rw [atL, Bool.eq_iff_iff, afterB_iff]
  simp [unc4]

theorem cobhamB4_atL (k : ℕ) {P : List Bool → List Bool → List Bool → List Bool → Bool}
    (hP : CobhamB4 P) : CobhamB4 (atL k P) := by
  induction k with
  | zero => exact hP.of_eq fun args => by simp [unc4, atL]
  | succ k ih =>
    exact (cobhamB_afterB ih (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2)
      (Cobham.proj 3)).of_eq fun args => by simp [unc4, atL, proj]

/-! ### Small closure facts -/

theorem cobham_p0 : Cobham fun a : Args => a.getD 0 [] := Cobham.proj 0
theorem cobham_p1 : Cobham fun a : Args => a.getD 1 [] := Cobham.proj 1
theorem cobham_p2 : Cobham fun a : Args => a.getD 2 [] := Cobham.proj 2
theorem cobham_p3 : Cobham fun a : Args => a.getD 3 [] := Cobham.proj 3

theorem cobham_cutAt {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => cutAt (a args) (b args) :=
  (cobham_trunc hb ha).of_eq' fun args => by simp [cutAt]

theorem cobham_dropK (k : ℕ) {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).drop k :=
  (cobham_drop (cobham_const (List.replicate k false)) ha).of_eq' fun args => by simp

theorem cobham_dropLastK (k : ℕ) {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).take ((a args).length - k) :=
  (cobham_trunc (cobham_const (List.replicate k false)) ha).of_eq' fun args => by simp

end SeqM

end Space

end HTN
