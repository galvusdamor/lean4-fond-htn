import FondHtn.Alt.ExpTime
/-!
# `2-EXPTIME`

The library defines `EXPTIME` as `P` on exponentially padded inputs.  We define `2-EXPTIME` the
same way with doubly exponential padding `2 ^ 2 ^ q(|x|)` (`HTN.Cx.EXPTIME2`), and prove:

* `HTN.Syn.PolyDom.inExp2Time_codeLang` — a language of codes decided in polynomial time on the
  doubly exponentially padded input is in `2-EXPTIME`;
* `HTN.Syn.PolyDom.inExp2Time_codeLang_of_andOr` — an AND-OR game over configurations of
  exponential size `2 ^ q(|x|)`, decided by its least fixpoint, is in `2-EXPTIME`.
-/

namespace HTN

namespace Cx

open Syn

/-- `x` padded with `2 ^ 2 ^ q(|x|)` ones. -/
def padExp2 (q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairStr x (List.replicate (2 ^ 2 ^ q.eval x.length) true)

/-- The doubly exponentially padded language. -/
def padLang2 (q : Polynomial ℕ) (L : Language) : Language := fun y => ∃ x, y = padExp2 q x ∧ L x

/-- **`2-EXPTIME`**: some doubly exponential padding of the language is in `P`. -/
def EXPTIME2 : LangClass := fun L => ∃ q : Polynomial ℕ, P (padLang2 q L)

end Cx

namespace Syn

namespace PolyDom

open PTime

/-- The test `|w| = 2 ^ M`, by the binary numeral of `|w|`. -/
def isPowLen (M : ℕ) (w : List Bool) : Bool :=
  let b := bitsOfNat w.length
  decide (b = b.tail.map (fun _ => false) ++ [true]) && (b.length == M + 1)

theorem isPowLen_iff (M : ℕ) (w : List Bool) : isPowLen M w = true ↔ w.length = 2 ^ M := by
  unfold isPowLen
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨hb, hl⟩
    have hd : (bitsOfNat w.length).tail.length = M := by simp [hl]
    have hb' : bitsOfNat w.length = List.replicate M false ++ [true] := by
      rw [hb, List.map_const', hd]
    have := congrArg natOfBits hb'
    rwa [natOfBits_pow, natOfBits_bitsOfNat] at this
  · intro h
    have hb : bitsOfNat w.length = List.replicate M false ++ [true] := by
      rw [h, ← natOfBits_pow, bitsOfNat_natOfBits, strip_append_true]
    rw [hb]
    refine ⟨?_, by simp⟩
    cases M with
    | zero => simp
    | succ M =>
      simp only [List.replicate_succ, List.cons_append, List.tail_cons, List.map_cons,
        List.map_append, List.map_replicate, List.map_cons, List.map_nil]
      rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ']

theorem pt_isPowLen {β : Type} [BEnc β] {M : β → ℕ} {w : β → List Bool} (hM : PT M) (hw : PT w) :
    PT fun x => isPowLen (M x) (w x) := by
  unfold isPowLen
  have hb : PT fun x => bitsOfNat (w x).length := PT.bits.comp (PT.length hw)
  have hdl : PT fun x => (bitsOfNat (w x).length).tail := PT.tail hb
  exact PT.and (PT.eq hb (PT.append (PT.map (g := fun _ (_ : Bool) => false) hdl (PT.const false))
    (PT.const [true]))) (PT.beq (PT.length hb) (PT.succ hM))

/-- **A language of codes decided in polynomial time with doubly exponential padding is in
`2-EXPTIME`.** -/
theorem inExp2Time_codeLang {α : Type} [BEnc α] [BDec α] {Q : α → Prop}
    {r : α × List Bool → Bool} (hr : PT r) (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ r (a, List.replicate (2 ^ 2 ^ q.eval (sz a)) true) = true) :
    Cx.EXPTIME2 (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  let dA : List Bool → α := fun x => (decR x : α × List Bool).1
  let d : List Bool → Bool := fun y =>
    isCode α (unpairS y).1 && (unpairS y).2.all (fun b => b) &&
      isPowLen (natOfBits ((g (unpairS y).1).map (fun _ => false) ++ [true])) (unpairS y).2 &&
      decide (y = pairStr (unpairS y).1 (unpairS y).2) && r (dA (unpairS y).1, (unpairS y).2)
  have hd : PT d := by
    have hu1 : PT fun y : List Bool => (unpairS y).1 := PT.fst.comp pt_unpairS
    have hu2 : PT fun y : List Bool => (unpairS y).2 := PT.snd.comp pt_unpairS
    exact PT.and (PT.and (PT.and (PT.and ((pt_isCode α).comp hu1)
      (PT.all (p := fun _ (b : Bool) => b) hu2 PT.snd))
      (pt_isPowLen (PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
        (hg.comp hu1) (PT.const false)) (PT.const [true]))) hu2))
      (PT.eq PT.id (pt_pairStr.comp (PT.pair hu1 hu2))))
      (hr.comp (PT.pair ((PT.fst.comp BDec.pt_decR).comp hu1) hu2))
  have hdec : ∀ (c : α), (decR (enc c) : α × List Bool).1 = c := fun c => decR_enc' c
  have hM : ∀ x : List Bool, natOfBits ((g x).map (fun _ => false) ++ [true]) = 2 ^ q.eval x.length :=
    fun x => by rw [List.map_const', hglen, natOfBits_pow]
  refine ⟨q, (congrArg Cx.P ?_).mp (inP_of_pt hd)⟩
  funext y
  apply propext
  constructor
  · intro hy
    simp only [d, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hM, isPowLen_iff] at hy
    obtain ⟨⟨⟨⟨hc, hall⟩, hlen⟩, hy⟩, hrr⟩ := hy
    obtain ⟨a, ha⟩ := (isCode_iff _).1 hc
    set x := (unpairS y).1 with hx
    set w := (unpairS y).2 with hw
    have hwrep : w = List.replicate (2 ^ 2 ^ q.eval x.length) true := by
      rw [List.eq_replicate_iff]
      exact ⟨hlen, fun b hb => by simpa using hall b hb⟩
    refine ⟨x, ?_, a, ha, ?_⟩
    · rw [hy, hwrep]; rfl
    · rw [hQ]
      have : sz a = x.length := by rw [← ha]; rfl
      rw [this, ← hwrep]
      simpa [dA, ← ha, hdec] using hrr
  · rintro ⟨x, rfl, a, rfl, hQa⟩
    simp only [d, Cx.padExp2, unpairS_pairStr, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, (isCode_iff _).2 ⟨a, rfl⟩, true_and, dA, hdec, hM, isPowLen_iff]
    exact ⟨⟨⟨fun b hb => List.eq_of_mem_replicate hb, by rw [List.length_replicate]⟩, trivial⟩,
      (hQ a).1 hQa⟩

section AndOr

variable {α σ : Type} [BEnc α] [BDec α] [BEnc σ] [BDec σ] [DecidableEq σ]

/-- **AND-OR games over configurations of exponential size are in `2-EXPTIME`.** -/
theorem inExp2Time_codeLang_of_andOr {Q : α → Prop} {init acc uni : α × σ → Bool}
    {step : α × σ × σ → Bool} (hi : PT init) (ha : PT acc) (hu : PT uni) (hs : PT step)
    (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ ∃ c₀, sz c₀ ≤ 2 ^ q.eval (sz a) ∧ init (a, c₀) = true ∧
      AOWin (2 ^ q.eval (sz a)) acc uni step a c₀) :
    Cx.EXPTIME2 (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  have hB : PT fun a : α => 2 ^ q.eval (sz a) := by
    have h := PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
      (hg.comp (BDec.pt_encL (α := α))) (PT.const false)) (PT.const [true]))
    exact h.of_eq fun a => by rw [List.map_const', hglen, natOfBits_pow]; rfl
  let All : α × List Bool → List σ := fun x => aoCands σ (2 ^ q.eval (sz x.1)) x.2
  have hAll : PT All := pt_aoCands (hB.comp PT.fst) PT.snd
  let r : α × List Bool → Bool := fun x =>
    (aoFix acc uni step (x.1, All x)).any fun c => init (x.1, c)
  have hp : PT fun x : α × List Bool => (x.1, All x) := PT.pair PT.fst hAll
  have hr : PT r := PT.any (f := fun x => aoFix acc uni step (x.1, All x))
    (p := fun x c => init (x.1, c)) ((pt_aoFix ha hu hs).comp hp)
    (show PT fun z : (α × List Bool) × σ => init (z.1.1, z.2) from
      hi.comp (PT.pair (PT.fst.comp PT.fst) PT.snd))
  refine inExp2Time_codeLang hr (q + 1) fun a => ?_
  have hpad : 2 ^ (2 ^ q.eval (sz a) + 1) ≤
      (List.replicate (2 ^ 2 ^ (q + 1).eval (sz a)) true).length := by
    have h1 : 2 ^ q.eval (sz a) + 1 ≤ 2 ^ (q + 1).eval (sz a) := by
      rw [Polynomial.eval_add, Polynomial.eval_one, pow_succ]
      have : 1 ≤ 2 ^ q.eval (sz a) := Nat.one_le_two_pow
      omega
    rw [List.length_replicate]
    exact Nat.pow_le_pow_right (by norm_num) h1
  have hmem := mem_aoCands (σ := σ) hpad
  rw [hQ]
  simp only [r, List.any_eq_true]
  constructor
  · rintro ⟨c₀, -, hi₀, hw⟩
    exact ⟨c₀, (mem_aoFix_iff hmem c₀).2 hw, hi₀⟩
  · rintro ⟨c₀, hc₀, hi₀⟩
    have hw := (mem_aoFix_iff hmem c₀).1 hc₀
    refine ⟨c₀, ?_, hi₀, hw⟩
    cases hw <;> assumption

end AndOr

end PolyDom

end Syn

end HTN
