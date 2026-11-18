import ComplexityTheory.Collapse.Quant
import ComplexityTheory.Complexity.PolyExp
/-!
# A self-delimiting code for the questions "does configuration `c` accept within `t` steps?"

The advice-elimination argument of `ComplexityTheory/Collapse/Collapse.lean` applies the
hypothesis "the class is contained in `PSPACE/poly`" not to the language of a machine but to the
language of its *configuration questions*: a word codes an input `x`, a configuration `c` and a
step counter `t`, and lies in the language when `c` accepts within `t` steps on `x`.  For the
advice to be usable, the codes of all the questions about one input must have **one and the same
length**, and for a machine to read a code it must be decodable by functions of Cobham's class.

The code used is

    encS u c t x  =  u ++ [false] ++ c ++ t ++ x

with `u` the all-one string whose length is the width of a configuration: the leading block of
ones announces, in unary, how long `c` is, so `c`, `t` and `x` can be cut out by taking and
dropping as many bits as a computed string is long — the primitives `HTN.PTime.cobham_take` and
`HTN.PTime.cobham_drop`.  The counter `t` is one bit longer than a configuration.

This file provides the code, its decoders, their correctness, and the fact that all of them are
functions of Cobham's class.  It also provides the polynomial padding
`HTN.PSpace.exists_cobham_len_ge`: for every polynomial there is a function of Cobham's class
whose output is at least that long, which is what supplies the *template* strings that the
quantifiers of `ComplexityTheory/Collapse/Quant.lean` run over.
-/

namespace HTN

namespace PSpace

open PTime

/-! ### All-one strings -/

/-- The all-one string of a given length. -/
def ones (m : ℕ) : List Bool := List.replicate m true

@[simp] theorem length_ones (m : ℕ) : (ones m).length = m := by simp [ones]

theorem val_ones (m : ℕ) : val (ones m) = 2 ^ m - 1 := val_replicate_true m

theorem ones_succ (m : ℕ) : ones (m + 1) = true :: ones m := by
  simp [ones, List.replicate_succ]

/-- The all-one string of the length of the first argument. -/
def onesLenFn : Fn :=
  brnFn (fun _ => []) (compFn (consFn true) [proj 1]) (compFn (consFn true) [proj 1])

theorem brnAux_onesLen (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) (compFn (consFn true) [proj 1]) (compFn (consFn true) [proj 1]) x v
      = ones x.length
  | [] => rfl
  | b :: x => by
    have hb : brnAux (fun _ => []) (compFn (consFn true) [proj 1])
        (compFn (consFn true) [proj 1]) (b :: x) v
        = compFn (consFn true) [proj 1]
          (x :: brnAux (fun _ => []) (compFn (consFn true) [proj 1])
            (compFn (consFn true) [proj 1]) x v :: v) := by
      cases b <;> rfl
    rw [hb, brnAux_onesLen v x]
    simp [compFn, consFn, proj, ones_succ]

theorem onesLenFn_apply (args : Args) : onesLenFn args = ones (args.getD 0 []).length := by
  rw [onesLenFn, brnFn, brnAux_onesLen]

theorem cobham_onesLenFn : Cobham onesLenFn := by
  refine Cobham.brn Cobham.empty (cobham_c1 (Cobham.cons true) (Cobham.proj 1))
    (cobham_c1 (Cobham.cons true) (Cobham.proj 1)) (Cobham.proj 0) fun args => ?_
  have h : brnFn (fun _ => []) (compFn (consFn true) [proj 1])
      (compFn (consFn true) [proj 1]) = onesLenFn := rfl
  rw [h, onesLenFn_apply]
  simp [proj]

/-- The longest prefix of ones of a string. -/
def onesPrefix : List Bool → List Bool
  | [] => []
  | true :: x => true :: onesPrefix x
  | false :: _ => []

/-- The longest prefix of ones, as a function of Cobham's class. -/
def onesPrefixFn : Fn := brnFn (fun _ => []) (fun _ => []) (compFn (consFn true) [proj 1])

theorem brnAux_onesPrefix (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) (fun _ => []) (compFn (consFn true) [proj 1]) x v = onesPrefix x
  | [] => rfl
  | false :: _ => rfl
  | true :: x => by
    have hb : brnAux (fun _ => []) (fun _ => []) (compFn (consFn true) [proj 1]) (true :: x) v
        = compFn (consFn true) [proj 1]
          (x :: brnAux (fun _ => []) (fun _ => []) (compFn (consFn true) [proj 1]) x v :: v) := rfl
    rw [hb, brnAux_onesPrefix v x]
    simp [compFn, consFn, proj, onesPrefix]

theorem onesPrefixFn_apply (args : Args) : onesPrefixFn args = onesPrefix (args.getD 0 []) := by
  rw [onesPrefixFn, brnFn, brnAux_onesPrefix]

theorem length_onesPrefix_le : ∀ x : List Bool, (onesPrefix x).length ≤ x.length
  | [] => by simp [onesPrefix]
  | false :: _ => by simp [onesPrefix]
  | true :: x => by
    have h := length_onesPrefix_le x
    simp only [onesPrefix, List.length_cons]
    omega

theorem cobham_onesPrefixFn : Cobham onesPrefixFn := by
  refine Cobham.brn Cobham.empty Cobham.empty (cobham_c1 (Cobham.cons true) (Cobham.proj 1))
    (Cobham.proj 0) fun args => ?_
  have h : brnFn (fun _ => []) (fun _ => []) (compFn (consFn true) [proj 1]) = onesPrefixFn := rfl
  rw [h, onesPrefixFn_apply]
  simpa [proj] using length_onesPrefix_le (args.getD 0 [])

/-- The prefix of ones of a code: the unary block is recovered exactly. -/
theorem onesPrefix_ones_append (m : ℕ) (rest : List Bool) :
    onesPrefix (ones m ++ false :: rest) = ones m := by
  induction m with
  | zero => simp [ones, onesPrefix]
  | succ m ih => rw [ones_succ, List.cons_append, onesPrefix, ih]

/-! ### Taking and dropping at a computed place -/

theorem drop_eq_of_length (l r : List Bool) {k : ℕ} (hk : k = l.length) : (l ++ r).drop k = r := by
  subst hk; simp

theorem take_eq_of_length (l r : List Bool) {k : ℕ} (hk : k = l.length) : (l ++ r).take k = l := by
  subst hk; simp

/-! ### The code -/

/-- The code of a configuration question: the unary width, a separator, the configuration, the
step counter and the input. -/
def encS (u c t x : List Bool) : List Bool := u ++ [false] ++ c ++ t ++ x

theorem length_encS (u c t x : List Bool) :
    (encS u c t x).length = u.length + 1 + c.length + t.length + x.length := by
  simp [encS]
  omega

/-- The unary width read off a code. -/
def decU (z : List Bool) : List Bool := onesPrefix z

/-- The configuration read off a code. -/
def decC (z : List Bool) : List Bool :=
  (z.drop (decU z ++ [false]).length).take (decU z).length

/-- The step counter read off a code; it is one bit longer than a configuration. -/
def decT (z : List Bool) : List Bool :=
  (z.drop (decU z ++ decU z ++ [false]).length).take (decU z ++ [false]).length

/-- The input read off a code. -/
def decX (z : List Bool) : List Bool :=
  z.drop (decU z ++ decU z ++ decU z ++ [false, false]).length

section decode

variable {c t x : List Bool} {m : ℕ}

@[simp] theorem decU_encS : decU (encS (ones m) c t x) = ones m := by
  have h : encS (ones m) c t x = ones m ++ false :: (c ++ t ++ x) := by
    simp [encS]
  rw [decU, h, onesPrefix_ones_append]

theorem encS_group (u c t x : List Bool) :
    encS u c t x = (u ++ [false]) ++ (c ++ (t ++ x)) := by
  simp [encS]

theorem decC_encS (hc : c.length = m) : decC (encS (ones m) c t x) = c := by
  rw [decC, decU_encS, encS_group]
  rw [drop_eq_of_length _ _ (by simp), take_eq_of_length _ _ (by simp [hc])]

theorem decT_encS (hc : c.length = m) (ht : t.length = m + 1) :
    decT (encS (ones m) c t x) = t := by
  have hgroup : encS (ones m) c t x = ((ones m ++ [false]) ++ c) ++ (t ++ x) := by
    simp [encS]
  rw [decT, decU_encS, hgroup]
  rw [drop_eq_of_length _ _ (by simp [hc]), take_eq_of_length _ _ (by simp [ht])]

theorem decX_encS (hc : c.length = m) (ht : t.length = m + 1) :
    decX (encS (ones m) c t x) = x := by
  have hgroup : encS (ones m) c t x = (((ones m ++ [false]) ++ c) ++ t) ++ x := by
    simp [encS]
  rw [decX, decU_encS, hgroup]
  rw [drop_eq_of_length _ _ (by simp [hc, ht]; omega)]

/-- **The code is injective.** -/
theorem encS_inj (hc : c.length = m) (ht : t.length = m + 1) {c' t' x' : List Bool} {m' : ℕ}
    (hc' : c'.length = m') (ht' : t'.length = m' + 1)
    (h : encS (ones m) c t x = encS (ones m') c' t' x') :
    m = m' ∧ c = c' ∧ t = t' ∧ x = x' := by
  have hu : (ones m : List Bool) = ones m' := by
    have h2 := congrArg decU h
    rwa [decU_encS, decU_encS] at h2
  have hm : m = m' := by simpa using congrArg List.length hu
  subst hm
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have h2 := congrArg decC h
    rwa [decC_encS hc, decC_encS hc'] at h2
  · have h2 := congrArg decT h
    rwa [decT_encS hc ht, decT_encS hc' ht'] at h2
  · have h2 := congrArg decX h
    rwa [decX_encS hc ht, decX_encS hc' ht'] at h2

end decode

/-! ### The decoders and the encoder belong to Cobham's class -/

theorem cobham_decU {a : Fn} (ha : Cobham a) : Cobham (fun args => decU (a args)) :=
  (cobham_c1 cobham_onesPrefixFn ha).of_eq' fun args => by
    simp [compFn, onesPrefixFn_apply, decU]

theorem cobham_app2 {a b : Fn} (ha : Cobham a) (hb : Cobham b) :
    Cobham (fun args => a args ++ b args) :=
  (cobham_c2 cobham_append ha hb).of_eq' fun args => by simp [compFn, proj]

theorem cobham_decC {a : Fn} (ha : Cobham a) : Cobham (fun args => decC (a args)) := by
  have hu : Cobham (fun args => decU (a args)) := cobham_decU ha
  have hsep : Cobham (fun args => decU (a args) ++ [false]) :=
    cobham_app2 hu (cobham_const [false])
  exact cobham_take hu (cobham_drop hsep ha)

theorem cobham_decT {a : Fn} (ha : Cobham a) : Cobham (fun args => decT (a args)) := by
  have hu : Cobham (fun args => decU (a args)) := cobham_decU ha
  have hsep : Cobham (fun args => decU (a args) ++ [false]) :=
    cobham_app2 hu (cobham_const [false])
  have h2 : Cobham (fun args => decU (a args) ++ decU (a args) ++ [false]) :=
    cobham_app2 (cobham_app2 hu hu) (cobham_const [false])
  exact cobham_take hsep (cobham_drop h2 ha)

theorem cobham_decX {a : Fn} (ha : Cobham a) : Cobham (fun args => decX (a args)) := by
  have hu : Cobham (fun args => decU (a args)) := cobham_decU ha
  have h3 : Cobham (fun args => decU (a args) ++ decU (a args) ++ decU (a args) ++
      [false, false]) :=
    cobham_app2 (cobham_app2 (cobham_app2 hu hu) hu) (cobham_const [false, false])
  exact cobham_drop h3 ha

theorem cobham_encS {u c t x : Fn} (hu : Cobham u) (hc : Cobham c) (ht : Cobham t)
    (hx : Cobham x) : Cobham (fun args => encS (u args) (c args) (t args) (x args)) :=
  cobham_app2 (cobham_app2 (cobham_app2 (cobham_app2 hu (cobham_const [false])) hc) ht) hx

/-! ### Polynomial padding -/

/-- A function of Cobham's class whose output has length `(|x| + 1) ^ k`. -/
def powPad : ℕ → Fn
  | 0 => compFn (consFn false) [fun _ => []]
  | k + 1 => compFn smashFn [powPad k, compFn (consFn false) [proj 0]]

theorem length_powPad : ∀ (k : ℕ) (args : Args),
    (powPad k args).length = ((args.getD 0 []).length + 1) ^ k
  | 0, args => by simp [powPad, compFn, consFn]
  | k + 1, args => by
    have ih := length_powPad k args
    simp only [powPad, compFn, smashFn, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, List.length_replicate, consFn, List.length_cons, proj]
    rw [ih, pow_succ]

theorem cobham_powPad : ∀ k : ℕ, Cobham (powPad k)
  | 0 => cobham_c1 (Cobham.cons false) Cobham.empty
  | k + 1 => cobham_c2 Cobham.smash (cobham_powPad k)
      (cobham_c1 (Cobham.cons false) (Cobham.proj 0))

/-- **Polynomial padding**: for every polynomial there is a function of Cobham's class whose
output is at least that long. -/
theorem exists_cobham_len_ge (r : Polynomial ℕ) :
    ∃ f : Fn, Cobham f ∧ ∀ x : List Bool, r.eval x.length ≤ (f [x]).length := by
  obtain ⟨k, hk⟩ := exists_pow_bound r
  refine ⟨compFn smashFn [powPad k, fun _ => List.replicate k false],
    cobham_c2 Cobham.smash (cobham_powPad k) (cobham_const (List.replicate k false)),
    fun x => ?_⟩
  have h : (compFn smashFn [powPad k, fun _ => List.replicate k false] [x]).length
      = (x.length + 1) ^ k * k := by
    simp only [compFn, smashFn, List.map_cons, List.map_nil, List.length_replicate,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [length_powPad k [x]]
    simp
  rw [h]
  calc r.eval x.length ≤ k * (x.length + 1) ^ k := hk x.length
    _ = (x.length + 1) ^ k * k := by ring

end PSpace

end HTN
