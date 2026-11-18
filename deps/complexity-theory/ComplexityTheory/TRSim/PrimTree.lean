import Mathlib.Computability.Primrec.List

/-!
# Program trees with a primitive recursive encoding

`HTN.TRSim.GT L`: trees with leaves in `L` and the three combinators sequence, choice and
iteration.  For a denumerable `L` the trees are denumerable by a bijection `n ↦ (n mod 4,
n / 4)` that decodes the components of a node from smaller numbers, so

* the constructors are primitive recursive (`primrec_leaf`, `primrec_seq`, …), and
* **folds are primitive recursive** (`HTN.TRSim.GT.primrec_fold`), by strong recursion on the
  codes.
-/

namespace HTN

namespace TRSim

/-- **Program trees.** -/
inductive GT (L : Type) where
  | leaf : L → GT L
  | seq : GT L → GT L → GT L
  | alt : GT L → GT L → GT L
  | star : GT L → GT L

namespace GT

variable {L : Type} [Denumerable L]

/-- The code of a tree. -/
def enc : GT L → ℕ
  | leaf x => 4 * Encodable.encode x
  | seq p q => 4 * Nat.pair (enc p) (enc q) + 1
  | alt p q => 4 * Nat.pair (enc p) (enc q) + 2
  | star p => 4 * enc p + 3

/-- The tree of a code. -/
def dec (n : ℕ) : GT L :=
  if n % 4 = 0 then leaf (Denumerable.ofNat L (n / 4))
  else if n % 4 = 1 then seq (dec (n / 4).unpair.1) (dec (n / 4).unpair.2)
  else if n % 4 = 2 then alt (dec (n / 4).unpair.1) (dec (n / 4).unpair.2)
  else star (dec (n / 4))
termination_by n
decreasing_by
  all_goals
    have := Nat.unpair_left_le (n / 4)
    have := Nat.unpair_right_le (n / 4)
    omega

theorem dec_enc : ∀ t : GT L, dec (enc t) = t
  | leaf x => by
    rw [dec, enc]
    simp
  | seq p q => by
    rw [dec, enc, if_neg (by omega), if_pos (by omega)]
    simp only [show (4 * Nat.pair (enc p) (enc q) + 1) / 4 = Nat.pair (enc p) (enc q) by omega,
      Nat.unpair_pair, dec_enc p, dec_enc q]
  | alt p q => by
    rw [dec, enc, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp only [show (4 * Nat.pair (enc p) (enc q) + 2) / 4 = Nat.pair (enc p) (enc q) by omega,
      Nat.unpair_pair, dec_enc p, dec_enc q]
  | star p => by
    rw [dec, enc, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [show (4 * enc p + 3) / 4 = enc p by omega, dec_enc p]

theorem enc_dec (n : ℕ) : enc (dec (L := L) n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [dec]
    have h1 := Nat.unpair_left_le (n / 4)
    have h2 := Nat.unpair_right_le (n / 4)
    split_ifs with h0 h1' h2'
    · simp only [enc, Denumerable.encode_ofNat]; omega
    · simp only [enc]
      rw [ih _ (by omega), ih _ (by omega), Nat.pair_unpair]; omega
    · simp only [enc]
      rw [ih _ (by omega), ih _ (by omega), Nat.pair_unpair]; omega
    · simp only [enc]
      rw [ih _ (by omega)]; omega

/-- The bijection. -/
def equivNat : GT L ≃ ℕ := ⟨enc, dec, dec_enc, enc_dec⟩

instance : Denumerable (GT L) := Denumerable.mk' equivNat

theorem encode_eq (t : GT L) : Encodable.encode t = enc t := rfl

theorem primrec_leaf : Primrec (@leaf L) :=
  Primrec.encode_iff.1 <| (Primrec.nat_mul.comp (Primrec.const 4) Primrec.encode).of_eq
    fun x => by rw [encode_eq, enc]

theorem primrec_seq : Primrec₂ (@seq L) :=
  Primrec₂.encode_iff.1 <| (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)))
    (Primrec.const 1)).to₂.of_eq fun p q => by simp only [encode_eq, enc]

theorem primrec_alt : Primrec₂ (@alt L) :=
  Primrec₂.encode_iff.1 <| (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) (Primrec.encode.comp Primrec.snd)))
    (Primrec.const 2)).to₂.of_eq fun p q => by simp only [encode_eq, enc]

theorem primrec_star : Primrec (@star L) :=
  Primrec.encode_iff.1 <| (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
    Primrec.encode) (Primrec.const 3)).of_eq fun p => by simp only [encode_eq, enc]

/-! ### Folds -/

/-- The fold of a tree. -/
def fold {σ : Type} (lf : L → σ) (sq al : σ → σ → σ) (st : σ → σ) : GT L → σ
  | leaf x => lf x
  | seq p q => sq (fold lf sq al st p) (fold lf sq al st q)
  | alt p q => al (fold lf sq al st p) (fold lf sq al st q)
  | star p => st (fold lf sq al st p)

section Fold

variable {α σ : Type} [Primcodable α] [Primcodable σ] [Inhabited σ]
  {lf : α → L → σ} {sq al : α → σ → σ → σ} {st : α → σ → σ}

/-- One step of the strong recursion. -/
def foldStep (lf : α → L → σ) (sq al : α → σ → σ → σ) (st : α → σ → σ) (a : α) (l : List σ) :
    σ :=
  let q := l.length / 4
  bif l.length % 4 == 0 then lf a (Denumerable.ofNat L q)
  else bif l.length % 4 == 1 then sq a (l.getD q.unpair.1 default) (l.getD q.unpair.2 default)
  else bif l.length % 4 == 2 then al a (l.getD q.unpair.1 default) (l.getD q.unpair.2 default)
  else st a (l.getD q default)

theorem foldStep_eq (a : α) (n : ℕ) :
    foldStep lf sq al st a ((List.range n).map fun m => fold (lf a) (sq a) (al a) (st a) (dec m)) =
      fold (lf a) (sq a) (al a) (st a) (dec n) := by
  have hget : ∀ i < n, ((List.range n).map fun m => fold (lf a) (sq a) (al a) (st a)
      (dec (L := L) m)).getD i default = fold (lf a) (sq a) (al a) (st a) (dec i) := by
    intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  have h1 := Nat.unpair_left_le (n / 4)
  have h2 := Nat.unpair_right_le (n / 4)
  conv_rhs => rw [dec]
  simp only [foldStep, List.length_map, List.length_range]
  by_cases c0 : n % 4 = 0
  · simp [c0, fold]
  by_cases c1 : n % 4 = 1
  · rw [hget _ (by omega), hget _ (by omega)]
    simp [c1, fold]
  by_cases c2 : n % 4 = 2
  · rw [hget _ (by omega), hget _ (by omega)]
    simp [c2, fold]
  · have hb0 : (n % 4 == 0) = false := by simpa using c0
    have hb1 : (n % 4 == 1) = false := by simpa using c1
    have hb2 : (n % 4 == 2) = false := by simpa using c2
    simp only [hb0, hb1, hb2, cond_false, c0, c1, c2, if_false, fold]
    rw [hget _ (by omega)]

theorem primrec_foldStep (hlf : Primrec₂ lf) (hsq : Primrec₂ fun a (x : σ × σ) => sq a x.1 x.2)
    (hal : Primrec₂ fun a (x : σ × σ) => al a x.1 x.2) (hst : Primrec₂ st) :
    Primrec₂ (foldStep (L := L) lf sq al st) := by
  have hlen : Primrec₂ fun (_ : α) (l : List σ) => l.length := Primrec.list_length.comp Primrec.snd
  have hq : Primrec₂ fun (_ : α) (l : List σ) => l.length / 4 :=
    Primrec.nat_div.comp hlen (Primrec.const 4)
  have hr : ∀ c : ℕ, Primrec₂ fun (_ : α) (l : List σ) => l.length % 4 == c := fun c =>
    Primrec.beq.comp (Primrec.nat_mod.comp hlen (Primrec.const 4)) (Primrec.const c)
  have hg : ∀ {f : α × List σ → ℕ}, Primrec f → Primrec fun x : α × List σ => x.2.getD (f x) default :=
    fun hf => (Primrec.list_getD default).comp Primrec.snd hf
  have hu1 := Primrec.fst.comp (Primrec.unpair.comp hq)
  have hu2 := Primrec.snd.comp (Primrec.unpair.comp hq)
  refine Primrec.cond (hr 0) (hlf.comp Primrec.fst ((Primrec.ofNat L).comp hq)) ?_
  refine Primrec.cond (hr 1) (hsq.comp Primrec.fst (Primrec.pair (hg hu1) (hg hu2))) ?_
  exact Primrec.cond (hr 2) (hal.comp Primrec.fst (Primrec.pair (hg hu1) (hg hu2)))
    (hst.comp Primrec.fst (hg hq))

/-- **Folds are primitive recursive.** -/
theorem primrec_fold (hlf : Primrec₂ lf) (hsq : Primrec₂ fun a (x : σ × σ) => sq a x.1 x.2)
    (hal : Primrec₂ fun a (x : σ × σ) => al a x.1 x.2) (hst : Primrec₂ st) :
    Primrec₂ fun a (t : GT L) => fold (lf a) (sq a) (al a) (st a) t := by
  have hF : Primrec₂ fun a n => fold (lf a) (sq a) (al a) (st a) (dec (L := L) n) :=
    Primrec.nat_strong_rec _ (g := fun a l => some (foldStep (L := L) lf sq al st a l))
      (Primrec.option_some.comp (primrec_foldStep hlf hsq hal hst))
      fun a n => by simp only [foldStep_eq]
  exact Primrec₂.of_eq (hF.comp Primrec.fst (Primrec.encode.comp Primrec.snd)).to₂ fun a t => by
    simp only [encode_eq, dec_enc]

end Fold

end GT

end TRSim

end HTN
