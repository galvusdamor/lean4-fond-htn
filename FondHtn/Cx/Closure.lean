import HtnComplexity.PT.ExpTime
import HtnComplexity.PT.NP
import HtnComplexity.PT.NExp
import HtnComplexity.PT.Search
/-!
# Closure of the complexity classes under polynomial-time reductions (part 1)

The library `ComplexityTheory` defines `HTN.Cx.P`, `NP`, `PSPACE`, `EXPTIME`, `NEXPTIME` and
`EXPSPACE` by different machine models and proves hardness to be inherited along reductions, but
it does not state that the classes themselves are closed under polynomial-time many-one
reductions.  Upper bounds by compilation (e.g. [CB21, Lemma 4.3]) need exactly this:

    L ≤ₚ L' ∧ L' ∈ 𝒞  ⟹  L ∈ 𝒞.

This file proves it for `P`, `NP`, `PSPACE` and `EXPTIME`; `FondHtn.Cx.Closure2` treats the
machine-defined classes `NEXPTIME` and `EXPSPACE`.

The bridge is `HTN.Cx.pt_of_polyTimeFun`: a polynomial-time function on raw bit strings is a
function of the polynomial-time calculus `PT` (on codes of bit strings).
-/

namespace HTN

namespace Cx

open Syn Syn.PolyDom PTime

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
theorem poly_eval_mono (q : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : q.eval m ≤ q.eval n := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simp only [Polynomial.eval_add]; omega
  | monomial k c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- A polynomial-time function on raw strings is unary Cobham. -/
theorem uc_of_polyTimeFun {F : List Bool → List Bool} (hF : PolyTimeFun F) : UC F := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  have h : Cobham fun args : Args => f [args.getD 0 []] :=
    (Cobham.comp hf (hs := [fun args : Args => args.getD 0 []])
      (by intro h hh; rw [List.mem_singleton.1 hh]; exact Cobham.proj 0)).of_fun_eq fun _ => rfl
  exact h.of_fun_eq fun args => (hFf _).symm

/-- **A polynomial-time function on raw strings is a function of the calculus.** -/
theorem pt_of_polyTimeFun {F : List Bool → List Bool} (hF : PolyTimeFun F) : PT F :=
  ⟨fun x => lift (F (unlift x)), uc_lift.comp ((uc_of_polyTimeFun hF).comp uc_unlift),
    fun x => by show lift (F (unlift (lift x))) = _; rw [unlift_lift]; rfl⟩

theorem headI_eq_getD (l : List Bool) : l.headI = l.getD 0 false := by cases l <;> rfl

/-! ### `P` -/

theorem P.of_redP {L L' : Language} (h : RedP L L') (h' : P L') : P L := by
  obtain ⟨f, hf, hff⟩ := h
  obtain ⟨G, hG, hGG⟩ := h'
  exact ⟨fun x => G (f x), hG.comp hf, fun x => (hff x).trans (hGG _)⟩

/-! ### `NP` -/

theorem pow_bound_of_polyBd (c d k : ℕ) :
    ∃ k' : ℕ, ∀ n, 1 ≤ n → (d * (n + 1) ^ c + 1) ^ k ≤ (n + 1) ^ k' := by
  refine ⟨c * k + d * k, fun n hn => ?_⟩
  have h2 : 2 ≤ n + 1 := by omega
  have hd : d + 1 ≤ (n + 1) ^ d := by
    calc d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
      _ ≤ (n + 1) ^ d := Nat.pow_le_pow_left h2 d
  have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  calc (d * (n + 1) ^ c + 1) ^ k ≤ ((d + 1) * (n + 1) ^ c) ^ k := by
        apply Nat.pow_le_pow_left; nlinarith
    _ = (d + 1) ^ k * (n + 1) ^ (c * k) := by rw [mul_pow, pow_mul]
    _ ≤ ((n + 1) ^ d) ^ k * (n + 1) ^ (c * k) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hd k)
    _ = (n + 1) ^ (c * k + d * k) := by rw [← pow_mul, ← pow_add]; ring_nf

theorem NP.of_redP {L L' : Language} (h : RedP L L') (h' : NP L') : NP L := by
  classical
  obtain ⟨f, hf, hff⟩ := h
  obtain ⟨V, k, hV, hVV⟩ := h'
  obtain ⟨P, hP⟩ := hf.poly_length
  obtain ⟨c, d, hcd⟩ := HTN.Syn.PolyDom.polyBd_poly P
  obtain ⟨k', hk'⟩ := pow_bound_of_polyBd c d k
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen ((Polynomial.X + 1) ^ k)
  have hglen' : ∀ z, (g z).length = (z.length + 1) ^ k := fun z => by simp [hglen]
  let b₀ : Bool := decide (L [])
  let V' : List Bool → List Bool := fun y =>
    bif (unpairS y).1.isEmpty then [b₀] else
      [decide ((unpairS y).2.length ≤ (g (f (unpairS y).1)).length) &&
        (V (pairStr (f (unpairS y).1) (unpairS y).2)).headI]
  have hV'pt : PT V' := by
    have hu1 : PT fun y : List Bool => (unpairS y).1 := PT.fst.comp pt_unpairS
    have hu2 : PT fun y : List Bool => (unpairS y).2 := PT.snd.comp pt_unpairS
    have hF := (pt_of_polyTimeFun hf).comp hu1
    exact PT.cond (PT.isEmpty hu1) (PT.const _)
      (PT.single (PT.and (PT.le (PT.length hu2) (PT.length (hg.comp hF)))
        (PT.headI ((pt_of_polyTimeFun hV).comp (pt_pairStr.comp (PT.pair hF hu2))))))
  refine ⟨V', k + k', polyTimeFun_of_uc (uc_of_pt_list hV'pt), fun x => ?_⟩
  simp only [V', unpairS_pairStr]
  rcases x with _ | ⟨b, x⟩
  · simp only [List.isEmpty_nil, cond_true, List.getD_cons_zero, b₀, decide_eq_true_eq]
    exact ⟨fun h => ⟨[], by simp, h⟩, fun ⟨_, _, h⟩ => h⟩
  · simp only [List.isEmpty_cons, cond_false, List.getD_cons_zero, Bool.and_eq_true,
      decide_eq_true_eq, hglen', headI_eq_getD]
    rw [hff, hVV]
    have hb : ((f (b :: x)).length + 1) ^ k ≤ ((b :: x).length + 1) ^ (k + k') := by
      calc ((f (b :: x)).length + 1) ^ k ≤ (d * ((b :: x).length + 1) ^ c + 1) ^ k := by
            apply Nat.pow_le_pow_left
            have := (hP (b :: x)).trans (hcd _); omega
        _ ≤ ((b :: x).length + 1) ^ k' := hk' _ (by simp)
        _ ≤ ((b :: x).length + 1) ^ (k + k') :=
            Nat.pow_le_pow_right (by simp) (by omega)
    constructor
    · rintro ⟨w, hw, hv⟩; exact ⟨w, hw.trans hb, hw, hv⟩
    · rintro ⟨w, -, hw, hv⟩; exact ⟨w, hw, hv⟩

/-! ### `PSPACE` -/

theorem PSPACE.of_redP {L L' : Language} (h : RedP L L') (h' : PSPACE L') : PSPACE L := by
  obtain ⟨f, hf, hff⟩ := h
  obtain ⟨p, hp, hpp⟩ := h'
  refine ⟨fun args => p [f (args.getD 0 [])], ?_, fun x => (hff x).trans (hpp _)⟩
  have : PSpace.PSpaceF (compFn (fun args => [p args]) [fun args => f (args.getD 0 [])]) :=
    PSpace.PSpaceF.comp hp (by
      intro h hh; rw [List.mem_singleton.1 hh]
      exact PSpace.PSpaceF.cobham (uc_of_polyTimeFun hf))
  exact this

/-! ### `EXPTIME` -/

theorem padExp_inj {q : Polynomial ℕ} {x x' : List Bool} (h : padExp q x = padExp q x') :
    x = x' := by
  have := congrArg (fun y => (unpairS y).1) h
  simpa [padExp, unpairS_pairStr] using this

theorem padLang_padExp {q : Polynomial ℕ} {L : Language} (x : List Bool) :
    padLang q L (padExp q x) ↔ L x :=
  ⟨fun ⟨_, h, hx⟩ => padExp_inj h ▸ hx, fun hx => ⟨x, rfl, hx⟩⟩

/-- The first `N` entries of a list of `true`s, written as a filter over its index range. -/
def takeTrue (N : ℕ) (l : List Bool) : List Bool :=
  ((List.range l.length).filter fun i => decide (i < N)).map fun _ => true

theorem length_filter_range_lt (N n : ℕ) :
    ((List.range n).filter fun i => decide (i < N)).length = min n N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : n < N <;> simp [h] <;> omega

theorem takeTrue_eq {N : ℕ} {l : List Bool} (h : N ≤ l.length) :
    takeTrue N l = List.replicate N true := by
  unfold takeTrue
  rw [List.map_const', length_filter_range_lt, Nat.min_eq_right h]

theorem EXPTIME.of_redP {L L' : Language} (h : RedP L L') (h' : EXPTIME L') : EXPTIME L := by
  obtain ⟨f, hf, hff⟩ := h
  obtain ⟨q, G, hG, hGG⟩ := h'
  obtain ⟨Pf, hPf⟩ := hf.poly_length
  let q' : Polynomial ℕ := q.comp Pf
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen q
  obtain ⟨g', hg', hglen'⟩ := exists_pt_polyLen q'
  have hpow : ∀ z : List Bool, natOfBits ((g z).map (fun _ => false) ++ [true]) =
      2 ^ q.eval z.length := fun z => by
    rw [List.map_const', ← natOfBits_pow, hglen]
  have hpow' : ∀ z : List Bool, natOfBits ((g' z).map (fun _ => false) ++ [true]) =
      2 ^ q'.eval z.length := fun z => by
    rw [List.map_const', ← natOfBits_pow, hglen']
  let d : List Bool → Bool := fun y =>
    decide (y = pairStr (unpairS y).1 (unpairS y).2) && (unpairS y).2.all (fun b => b) &&
      ((unpairS y).2.length == natOfBits ((g' (unpairS y).1).map (fun _ => false) ++ [true])) &&
      (G (pairStr (f (unpairS y).1) (takeTrue (natOfBits ((g (f (unpairS y).1)).map
        (fun _ => false) ++ [true])) (unpairS y).2))).headI
  have hd : PT d := by
    have hu1 : PT fun y : List Bool => (unpairS y).1 := PT.fst.comp pt_unpairS
    have hu2 : PT fun y : List Bool => (unpairS y).2 := PT.snd.comp pt_unpairS
    have hF := (pt_of_polyTimeFun hf).comp hu1
    have hN : PT fun y : List Bool =>
        natOfBits ((g (f (unpairS y).1)).map (fun _ => false) ++ [true]) :=
      PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false) (hg.comp hF) (PT.const false))
        (PT.const [true]))
    have hT : PT fun y : List Bool => takeTrue (natOfBits ((g (f (unpairS y).1)).map
        (fun _ => false) ++ [true])) (unpairS y).2 := by
      unfold takeTrue
      exact PT.map (g := fun _ _ => true)
        (PT.filter (PT.rangeLength hu2) (PT.lt PT.snd (hN.comp PT.fst))) (PT.const true)
    exact PT.and (PT.and (PT.and (PT.eq PT.id (pt_pairStr.comp (PT.pair hu1 hu2)))
      (PT.all (p := fun _ (b : Bool) => b) hu2 PT.snd))
      (PT.beq (PT.length hu2) (PT.ofBits (PT.append (PT.map (g := fun _ (_ : Unit) => false)
        (hg'.comp hu1) (PT.const false)) (PT.const [true])))))
      (PT.headI ((pt_of_polyTimeFun hG).comp (pt_pairStr.comp (PT.pair hF hT))))
  refine ⟨q', (congrArg P ?_).mp (inP_of_pt hd)⟩
  funext y
  apply propext
  simp only [d, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, hpow, hpow',
    headI_eq_getD]
  constructor
  · rintro ⟨⟨⟨hy, hall⟩, hlen⟩, hG'⟩
    refine ⟨(unpairS y).1, ?_, (hff _).2 ?_⟩
    · have hpad : (unpairS y).2 = List.replicate (2 ^ q'.eval (unpairS y).1.length) true := by
        rw [← hlen]; exact List.eq_replicate_iff.2 ⟨rfl, fun b hb => hall b hb⟩
      rw [padExp, ← hpad]; exact hy
    · have hle : 2 ^ q.eval (f (unpairS y).1).length ≤ (unpairS y).2.length := by
        rw [hlen]
        exact Nat.pow_le_pow_right (by norm_num) (by
          simp only [q', Polynomial.eval_comp]; exact poly_eval_mono q (hPf _))
      rw [takeTrue_eq hle] at hG'
      exact (padLang_padExp _).1 ((hGG _).2 hG')
  · rintro ⟨x, rfl, hx⟩
    simp only [padExp, unpairS_pairStr, List.length_replicate]
    refine ⟨⟨⟨by simp, fun b hb => (List.eq_of_mem_replicate hb)⟩, by simp⟩, ?_⟩
    have hle : 2 ^ q.eval (f x).length ≤ 2 ^ q'.eval x.length :=
      Nat.pow_le_pow_right (by norm_num) (by
        simp only [q', Polynomial.eval_comp]; exact poly_eval_mono q (hPf _))
    rw [takeTrue_eq (by simpa using hle)]
    exact (hGG _).1 ((padLang_padExp (f x)).2 ((hff x).1 hx))

end Cx

end HTN
