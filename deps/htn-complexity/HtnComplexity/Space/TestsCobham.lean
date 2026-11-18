import HtnComplexity.Space.Tests
/-!
# The tests of the target-side machine are polynomial time

Every test of `HtnComplexity/Space/Tests.lean` is a predicate of Cobham's class
(`ComplexityTheory/Complexity/Cobham.lean`), for arguments computed by functions of the class.
This is what the machine model of `ComplexityTheory/Space/Model.lean` demands of its three
tests.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### Small closure properties, for computed arguments -/

theorem cobham_app {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => a args ++ b args :=
  (cobham_c2 cobham_append ha hb).of_eq' fun args => by simp [compFn, proj]

theorem cobham_consT {a : Fn} (ha : Cobham a) : Cobham fun args => true :: a args :=
  (cobham_c1 (Cobham.cons true) ha).of_eq' fun args => by simp [compFn, consFn, proj]

theorem cobham_tl {a : Fn} (ha : Cobham a) : Cobham fun args => (a args).tail :=
  (cobham_c1 cobham_tailFn ha).of_eq' fun args => by simp [compFn, tailFn_apply, proj]

/-- The string without its last character. -/
theorem cobham_init {a : Fn} (ha : Cobham a) :
    Cobham fun args => (a args).take ((a args).length - 1) :=
  (cobham_trunc (cobham_const [false]) ha).of_eq' fun args => by simp

/-! ### The suffix after the leading serialised list -/

theorem cobhamB_afterTest {p : Args → Bool} (hp : CobhamB p) : CobhamB (afterTest p) :=
  ((cobhamB_blistB cobham_cutAt10).and
    (hp.comp4 (Cobham.proj 0) (Cobham.proj 2) (Cobham.proj 3) (Cobham.proj 4)).not).of_eq
      fun args => by simp [afterTest, proj]

theorem argDep_afterTest (p : Args → Bool) : ArgDep 5 (afterTest p) := by
  intro args
  simp only [afterTest, getD_padArgs (by norm_num : (0 : ℕ) < 5),
    getD_padArgs (by norm_num : (1 : ℕ) < 5), getD_padArgs (by norm_num : (2 : ℕ) < 5),
    getD_padArgs (by norm_num : (3 : ℕ) < 5), getD_padArgs (by norm_num : (4 : ℕ) < 5)]

theorem cobhamB_afterB {p : Args → Bool} (hp : CobhamB p) {a b₁ b₂ b₃ : Fn} (ha : Cobham a)
    (hb₁ : Cobham b₁) (hb₂ : Cobham b₂) (hb₃ : Cobham b₃) :
    CobhamB fun args => afterB p (a args) (b₁ args) (b₂ args) (b₃ args) :=
  (((cobhamB_anyTails (cobhamB_afterTest hp) (argDep_afterTest p)).comp5 ha ha hb₁ hb₂
    hb₃).not).of_eq fun args => by simp [afterB]

/-! ### Reading and building the entries of the advice -/

theorem cobhamB_extB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => extB (a args) (b args) :=
  (cobhamB_isPrefix (cobham_init ha) hb).of_eq fun _ => rfl

theorem cobham_restOf {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => restOf (a args) (b args) :=
  (cobham_drop (cobham_init ha) hb).of_eq' fun args => by
    rw [restOf, List.length_take]
    congr 1
    omega

theorem cobhamB_tagIsB (t : List Bool) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => tagIsB t (a args) (b args) :=
  (cobhamB_isPrefix (cobham_const (dbl t)) (cobham_restOf ha hb)).of_eq fun _ => rfl

theorem cobham_factOf {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => factOf (a args) (b args) :=
  (cobham_consT (cobham_drop (cobham_const [false, false, false, false])
    (cobham_restOf ha hb))).of_eq' fun args => by simp [factOf]

theorem cobham_mkEnt (t : List Bool) {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham fun args => mkEnt t (a args) (b args) :=
  (cobham_app (cobham_app (cobham_init ha) (cobham_const (dbl t)))
    (cobham_tl hb)).of_eq' fun _ => rfl

theorem cobhamB_canonEntB {a : Fn} (ha : Cobham a) : CobhamB fun args => canonEntB (a args) :=
  ((cobhamB_eqStr ha (cobham_const [true, false])).or
    (cobhamB_isSuffix (cobham_const [true, true, false]) ha)).of_eq fun _ => rfl

/-! ### The tests of the machine -/

theorem cobhamB_inOkB (t : List Bool) {a b c : Fn} (ha : Cobham a) (hb : Cobham b)
    (hc : Cobham c) : CobhamB fun args => inOkB t (a args) (b args) (c args) :=
  (cobhamB_allEntB
    (((cobhamB_extB (Cobham.proj 1) (Cobham.proj 0)).and
        (cobhamB_tagIsB t (Cobham.proj 1) (Cobham.proj 0))).not.or
      (cobhamB_occB (Cobham.proj 2) (cobham_factOf (Cobham.proj 1) (Cobham.proj 0))))
    hb ha hc Cobham.empty).of_eq fun args => by simp [inOkB, proj]

theorem cobhamB_keepOkB {a b c d : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c)
    (hd : Cobham d) : CobhamB fun args => keepOkB (a args) (b args) (c args) (d args) :=
  (cobhamB_allEntB
    ((cobhamB_occB (Cobham.proj 2) (cobham_mkEnt tagDel (Cobham.proj 1) (Cobham.proj 0))).or
      (cobhamB_occB (Cobham.proj 3) (Cobham.proj 0)))
    hc ha hb hd).of_eq fun args => by simp [keepOkB, proj]

theorem cobhamB_postOkB {a b c d : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c)
    (hd : Cobham d) : CobhamB fun args => postOkB (a args) (b args) (c args) (d args) :=
  (cobhamB_allEntB
    ((cobhamB_occB (Cobham.proj 2) (cobham_mkEnt tagAdd (Cobham.proj 1) (Cobham.proj 0))).or
      ((cobhamB_occB (Cobham.proj 3) (Cobham.proj 0)).and
        (cobhamB_occB (Cobham.proj 2)
          (cobham_mkEnt tagDel (Cobham.proj 1) (Cobham.proj 0))).not))
    hd ha hb hc).of_eq fun args => by simp [postOkB, proj]

theorem cobhamB_rowStepB {a b c d : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c)
    (hd : Cobham d) : CobhamB fun args => rowStepB (a args) (b args) (c args) (d args) :=
  ((((cobhamB_inOkB tagPrec ha hb hc).and (cobhamB_inOkB tagAdd ha hb hd)).and
    (cobhamB_keepOkB ha hb hc hd)).and (cobhamB_postOkB ha hb hc hd)).of_eq fun _ => rfl

theorem cobhamB_stepCoreB {a b c : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => stepCoreB (a args) (b args) (c args) := by
  have hrow : CobhamB fun args2 : Args =>
      rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 []) (args2.getD 3 []) :=
    (cobhamB_rowStepB (Cobham.proj 0) (Cobham.proj 1) (Cobham.proj 2) (Cobham.proj 3)).of_eq
      fun args => by simp [proj]
  have hany : CobhamB fun args : Args =>
      anyEntB (fun args2 => rowStepB (args2.getD 0 []) (args2.getD 1 []) (args2.getD 2 [])
        (args2.getD 3 [])) (args.getD 1 []) (args.getD 0 []) (args.getD 2 []) (args.getD 3 []) :=
    (cobhamB_anyEntB hrow (Cobham.proj 1) (Cobham.proj 0) (Cobham.proj 2)
      (Cobham.proj 3)).of_eq fun args => by simp [proj]
  exact (cobhamB_afterB hany ha ha hb hc).of_eq fun _ => rfl

theorem cobhamB_initCoreB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => initCoreB (a args) (b args) :=
  ((cobhamB_subEntB ha hb).and (cobhamB_subEntB hb ha)).of_eq fun _ => rfl

theorem cobhamB_accCoreB {a b c : Fn} (ha : Cobham a) (hb : Cobham b) (hc : Cobham c) :
    CobhamB fun args => accCoreB (a args) (b args) (c args) := by
  have hsub : CobhamB fun args : Args => subEntB (args.getD 0 []) (args.getD 1 []) :=
    (cobhamB_subEntB (Cobham.proj 0) (Cobham.proj 1)).of_eq fun args => by simp [proj]
  exact ((cobhamB_head (cobham_rev hc)).and
    (cobhamB_afterB hsub hb ha Cobham.empty Cobham.empty)).of_eq fun _ => rfl

theorem cobhamB_wfB {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    CobhamB fun args => wfB (a args) (b args) := by
  have hcan : CobhamB fun args : Args => canonEntB (args.getD 0 []) :=
    (cobhamB_canonEntB (Cobham.proj 0)).of_eq fun args => by simp [proj]
  exact (((cobhamB_blistB ha).and
    (cobhamB_allEntB hcan ha Cobham.empty Cobham.empty Cobham.empty)).and
      (cobhamB_lenLE ha hb)).of_eq fun _ => rfl

end Space

end HTN
