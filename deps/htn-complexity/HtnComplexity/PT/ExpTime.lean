import HtnComplexity.PT.Search
import ComplexityTheory.Lang.ExpTime
/-!
# Languages of codes in `EXPTIME`

* **`HTN.Syn.PolyDom.inExpTime_codeLang`** — if `Q a` holds iff a polynomial-time Boolean
  function `r` accepts `a` together with `2 ^ q(|code of a|)` ones, then the language of the codes
  of the values satisfying `Q` is in `EXPTIME` (`HTN.Cx.EXPTIME`).

The decider of the padded language splits its input at the separator of `HTN.Syn.pairStr`
(`HTN.Syn.PolyDom.unpairS`, a left fold), checks the code, the length of the padding (compared
with `natOfBits` of a binary numeral `0…01` of `q(|x|)` digits) and the shape of the input, and
runs `r`.
-/

namespace HTN

namespace Syn

namespace PolyDom

open PTime

/-- The state of the splitter: separator passed, a pending bit (flag, bit), the two parts. -/
abbrev UpState : Type := Bool × Bool × Bool × List Bool × List Bool

/-- One step of the splitter. -/
def upStep (s : UpState) (b : Bool) : UpState :=
  bif s.1 then (true, false, false, s.2.2.2.1, s.2.2.2.2 ++ [b])
  else bif !s.2.1 then (false, true, b, s.2.2.2.1, s.2.2.2.2)
  else bif s.2.2.1 == b then (false, false, false, s.2.2.2.1 ++ [s.2.2.1], s.2.2.2.2)
  else (true, false, false, s.2.2.2.1, s.2.2.2.2)

/-- **Splitting `pairStr x w`.** -/
def unpairS (y : List Bool) : List Bool × List Bool :=
  let s := y.foldl upStep (false, false, false, [], [])
  (s.2.2.2.1, s.2.2.2.2)

theorem foldl_upStep_dbl (x xs : List Bool) :
    (x.flatMap fun b => [b, b]).foldl upStep (false, false, false, xs, []) =
      (false, false, false, xs ++ x, []) := by
  induction x generalizing xs with
  | nil => simp
  | cons b x ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
    simp only [upStep, cond_false, Bool.not_false, cond_true, beq_self_eq_true, Bool.not_true]
    rw [ih]; simp

theorem foldl_upStep_snd (w ws : List Bool) :
    w.foldl upStep (true, false, false, xs, ws) = (true, false, false, xs, ws ++ w) := by
  induction w generalizing ws with
  | nil => simp
  | cons b w ih => simp only [List.foldl_cons, upStep, cond_true]; rw [ih]; simp

theorem unpairS_pairStr (x w : List Bool) : unpairS (pairStr x w) = (x, w) := by
  unfold unpairS pairStr
  rw [List.foldl_append, List.foldl_append, foldl_upStep_dbl]
  simp only [List.nil_append, List.foldl_cons, List.foldl_nil, upStep, cond_false, Bool.not_false,
    cond_true, Bool.not_true]
  rw [show (false == true) = false from rfl, cond_false, foldl_upStep_snd]
  simp

theorem pt_upStep : PT fun q : List Bool × UpState × Bool => upStep q.2.1 q.2.2 := by
  unfold upStep
  have hs : PT fun q : List Bool × UpState × Bool => q.2.1 := PT.fst.comp PT.snd
  have hb : PT fun q : List Bool × UpState × Bool => q.2.2 := PT.snd.comp PT.snd
  have h1 := PT.fst.comp hs
  have h2 := PT.fst.comp (PT.snd.comp hs)
  have h3 := PT.fst.comp (PT.snd.comp (PT.snd.comp hs))
  have hx := PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hs)))
  have hw := PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hs)))
  exact PT.cond h1 (PT.pair (PT.const true) (PT.pair (PT.const false) (PT.pair (PT.const false)
      (PT.pair hx (PT.append hw (PT.single hb))))))
    (PT.cond (PT.not h2) (PT.pair (PT.const false) (PT.pair (PT.const true) (PT.pair hb
      (PT.pair hx hw))))
      (PT.cond (PT.beq h3 hb) (PT.pair (PT.const false) (PT.pair (PT.const false)
        (PT.pair (PT.const false) (PT.pair (PT.append hx (PT.single h3)) hw))))
        (PT.pair (PT.const true) (PT.pair (PT.const false) (PT.pair (PT.const false)
          (PT.pair hx hw))))))

theorem sz_upStep_le (s : UpState) (b : Bool) : sz (upStep s b) ≤ sz s + 8 := by
  obtain ⟨ph, hp, a, xs, ws⟩ := s
  have hsz : ∀ (ph hp a : Bool) (xs ws : List Bool),
      sz ((ph, hp, a, xs, ws) : UpState) = 3 + sz xs + sz ws := by
    intro ph hp a xs ws; simp only [sz_prod, sz_bool]; ring
  have happ : ∀ (l : List Bool) (c : Bool), sz (l ++ [c]) = sz l + 4 := by
    intro l c; rw [sz_append_single]; simp [sz_bool]
  unfold upStep
  cases ph <;> cases hp <;> cases a <;> cases b <;>
    simp only [cond_true, cond_false, Bool.not_true, Bool.not_false, beq_self_eq_true,
      show (true == false) = false from rfl, show (false == true) = false from rfl, hsz, happ] <;>
    omega

theorem pt_unpairS : PT unpairS := by
  unfold unpairS
  have hf : PT fun y : List Bool => y.foldl upStep (false, false, false, [], []) :=
    PT.foldl (α := List Bool) (β := Bool) (σ := UpState) (g := fun _ s b => upStep s b) PT.id
      (PT.const _) pt_upStep (c := 0) (d := 8) fun _ s b _ => by
        have := sz_upStep_le s b; simpa using this
  exact PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hf))))
    (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hf))))

theorem pt_pairStr : PT fun q : List Bool × List Bool => pairStr q.1 q.2 := by
  unfold pairStr
  exact PT.append (PT.append (PT.flatMap PT.fst (PT.cons PT.snd (PT.single PT.snd)))
    (PT.const _)) PT.snd

theorem natOfBits_pow (k : ℕ) : natOfBits (List.replicate k false ++ [true]) = 2 ^ k := by
  induction k with
  | zero => simp [natOfBits]
  | succ k ih => simp [List.replicate_succ, natOfBits, ih, pow_succ]; ring

/-- A polynomial-time decider of bit strings gives a language in `P`. -/
theorem inP_of_pt {d : List Bool → Bool} (hd : PT d) : Cx.P fun y => d y = true :=
  ⟨_, polyTimeFun_of_uc (uc_of_pt_bool hd), fun x => by simp⟩

/-- **A language of codes decided in polynomial time with exponential padding is in
`EXPTIME`.** -/
theorem inExpTime_codeLang {α : Type} [BEnc α] [BDec α] {Q : α → Prop}
    {r : α × List Bool → Bool} (hr : PT r) (q : Polynomial ℕ)
    (hQ : ∀ a, Q a ↔ r (a, List.replicate (2 ^ q.eval (sz a)) true) = true) :
    Cx.EXPTIME (codeLang α Q) := by
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  let dA : List Bool → α := fun x => (decR x : α × List Bool).1
  let d : List Bool → Bool := fun y =>
    isCode α (unpairS y).1 && (unpairS y).2.all (fun b => b) &&
      ((unpairS y).2.length == natOfBits ((g (unpairS y).1).map (fun _ => false) ++ [true])) &&
      decide (y = pairStr (unpairS y).1 (unpairS y).2) && r (dA (unpairS y).1, (unpairS y).2)
  have hd : PT d := by
    have hu1 : PT fun y : List Bool => (unpairS y).1 := PT.fst.comp pt_unpairS
    have hu2 : PT fun y : List Bool => (unpairS y).2 := PT.snd.comp pt_unpairS
    exact PT.and (PT.and (PT.and (PT.and ((pt_isCode α).comp hu1)
      (PT.all (p := fun _ (b : Bool) => b) hu2 PT.snd))
      (PT.beq (PT.length hu2) (PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
        (hg.comp hu1) (PT.const false)) (PT.const [true])))))
      (PT.eq PT.id (pt_pairStr.comp (PT.pair hu1 hu2))))
      (hr.comp (PT.pair ((PT.fst.comp BDec.pt_decR).comp hu1) hu2))
  have hdec : ∀ (c : α), (decR (enc c) : α × List Bool).1 = c := fun c => decR_enc' c
  refine ⟨q, (congrArg Cx.P ?_).mp (inP_of_pt hd)⟩
  funext y
  apply propext
  constructor
  · intro hy
    simp only [d, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
    obtain ⟨⟨⟨⟨hc, hall⟩, hlen⟩, hy⟩, hrr⟩ := hy
    obtain ⟨a, ha⟩ := (isCode_iff _).1 hc
    set x := (unpairS y).1 with hx
    set w := (unpairS y).2 with hw
    have hwrep : w = List.replicate (2 ^ q.eval x.length) true := by
      rw [List.eq_replicate_iff]
      refine ⟨?_, fun b hb => by simpa using hall b hb⟩
      rw [hlen, List.map_const', hglen, natOfBits_pow]
    refine ⟨x, ?_, a, ha, ?_⟩
    · rw [hy, hwrep]; rfl
    · rw [hQ]
      have : sz a = x.length := by rw [← ha]; rfl
      rw [this, ← hwrep]
      simpa [dA, ← ha, hdec] using hrr
  · rintro ⟨x, rfl, a, rfl, hQa⟩
    simp only [d, Cx.padExp, unpairS_pairStr, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq, (isCode_iff _).2 ⟨a, rfl⟩, true_and, dA, hdec]
    exact ⟨⟨⟨fun b hb => List.eq_of_mem_replicate hb, by
      rw [List.length_replicate, List.map_const', hglen, natOfBits_pow]⟩, trivial⟩, (hQ a).1 hQa⟩

end PolyDom

end Syn

end HTN
