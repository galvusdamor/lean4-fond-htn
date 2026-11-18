import HtnComplexity.Space.AltCorrect
import HtnComplexity.Space.ToAlt
import HtnComplexity.Space.Norm
import HtnComplexity.Space.RegSize
import HtnComplexity.Space.InstBound
import HtnComplexity.Space.Bridge
import HtnComplexity.Computable.DescEnum
/-!
# The target side for totally ordered HTN: an `EXPTIME` planner with the domain as advice

This file proves

    HTN.Syn.AltDecidableAdv codingSer SynClass.TO_HTN_root

— "plan existence for totally ordered HTN with a rooted instance is decidable in alternating
polynomial space (`= EXPTIME`), the domain description being supplied as advice" — **with no
hypothesis left**, and the bridge `HTN.Syn.inAltSpacePoly_of_inPolyAdvice` which turns polynomial
advice for such a class into membership in `EXPTIME/poly` (`HTN.Space.InAltSpacePoly`).

The ingredients:

* `HTN.Space.solvable_to_iff_cReach` — plan existence *is* reachability with calls in the table
  `toPlain d`/`toCalls d` of the domain description, from and to the lists of the instance used in
  the regular case (`regInitR q`, `regGoalR q`);
* `HTN.Space.aReach_layout_iff` — reachability with calls is reachability in the *layout*
  `toLayout d`, a single list of rows in which the push row of every call pair is marked by the
  fact `kPush = 1` and its return row, the next one, by `kRet = 5`;
* `HTN.Space.aSolvable_map_iff` with `HTN.Space.tblNorm` — the facts of the table are renamed so
  that they all fit into a polynomial number of bits, the facts of the instance and the two
  markers being fixed;
* `HTN.Space.altMachine_accepts_iff` — the alternating machine accepts exactly the solvable
  problems.

As for regular HTN (`HtnCompilability/Space/RegSpace.lean`), **no assumption is made on the cost
of the domain compilation**: only the *length* of the advice is constrained.
-/

namespace HTN

namespace Space

open Syn PTime

/-! ### The layout of a totally ordered domain description -/

/-- **The action table with calls of a totally ordered domain description**, laid out as one list
of rows with the push rows marked by `kPush` and the return rows by `kRet`. -/
def toLayout (d : DomDesc) : List Row := layout kPush kRet (toPlain d) (toCalls d)

/-- No fact of a row is `1` modulo `4`. -/
def NoOneMod4 (r : Row) : Prop := ∀ f, f ∈ r.1 ∨ f ∈ r.2.1 ∨ f ∈ r.2.2 → f % 4 ≠ 1

theorem noOneMod4_of_mem_toPlain {d : DomDesc} {r : Row} (hr : r ∈ toPlain d) : NoOneMod4 r := by
  obtain ⟨m, -, h⟩ := (mem_toPlain d).1 hr
  intro f hf
  rcases h with rfl | rfl | ⟨j, -, a, -, rfl⟩
  · simp only [begRow, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;> (try simp only [toCall, toCur]) <;> omega
  · simp only [finRow, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;> (try simp only [toCur]) <;> omega
  · simp only [execRow, List.mem_cons, List.mem_map] at hf
    rcases hf with (rfl | ⟨v, -, rfl⟩) | (rfl | ⟨v, -, rfl⟩) | (rfl | ⟨v, -, rfl⟩) <;>
      simp only [toCur, toF] <;> omega

theorem noOneMod4_of_mem_toCalls {d : DomDesc} {p r : Row} (hpr : (p, r) ∈ toCalls d) :
    NoOneMod4 p ∧ NoOneMod4 r := by
  obtain ⟨m, -, j, -, c, -, rfl, rfl⟩ := (mem_toCalls d).1 hpr
  constructor
  · intro f hf
    simp only [pushRow, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;> (try simp only [toCall, toCur]) <;> omega
  · intro f hf
    simp only [retRow, List.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl <;> (try simp only [toCur]) <;> omega

/-- **The side conditions of the layout hold**: the markers `1` and `5` are `1` modulo `4`, which
no fact of the table is. -/
theorem layoutOk_to (d : DomDesc) : LayoutOk kPush kRet (toPlain d) (toCalls d) where
  ne := by decide
  plain := fun r hr => by
    have h := noOneMod4_of_mem_toPlain hr
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · exact h _ (Or.inr (Or.inr h')) (by decide)
    · exact h _ (Or.inr (Or.inr h')) (by decide)
    · exact h _ (Or.inr (Or.inl h')) (by decide)
    · exact h _ (Or.inr (Or.inl h')) (by decide)
  push := fun pr hpr => by
    have h := (noOneMod4_of_mem_toCalls (p := pr.1) (r := pr.2) hpr).1
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · exact h _ (Or.inr (Or.inl h')) (by decide)
    · exact h _ (Or.inr (Or.inl h')) (by decide)
    · exact h _ (Or.inr (Or.inr h')) (by decide)
  ret := fun pr hpr => by
    have h := (noOneMod4_of_mem_toCalls (p := pr.1) (r := pr.2) hpr).2
    refine ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
    · exact h _ (Or.inr (Or.inl h')) (by decide)
    · exact h _ (Or.inr (Or.inl h')) (by decide)
    · exact h _ (Or.inr (Or.inr h')) (by decide)

/-- The initial state of the instance carries no marker. -/
theorem markFree_regInitR (q : InstDesc) : MarkFree kPush kRet {f | f ∈ regInitR q} := by
  rw [regInitR_eq_st]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · simp only [st, Set.mem_union, Set.mem_image, Set.mem_singleton_iff, toF, toCall, kPush,
      kRet] at h
    omega

/-! ### The size of the layout -/

/-- The number of facts a row lists. -/
def rowSz (r : Row) : ℕ := r.1.length + r.2.1.length + r.2.2.length

theorem tblSize_le_of_rowSz {tbl : List Row} {B : ℕ} (h : ∀ r ∈ tbl, rowSz r ≤ B) :
    tblSize tbl ≤ tbl.length * (B + 1) := by
  have hs := List.sum_le_card_nsmul (tbl.map fun r => r.1.length + r.2.1.length + r.2.2.length) B
    (by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
      exact h r hr)
  simp only [List.length_map, smul_eq_mul] at hs
  rw [tblSize, Nat.mul_succ]
  omega

theorem length_flatMap_le' {α β : Type*} {l : List α} {g : α → List β} {B : ℕ}
    (h : ∀ a ∈ l, (g a).length ≤ B) : (l.flatMap g).length ≤ l.length * B := by
  rw [List.length_flatMap]
  have hs := List.sum_le_card_nsmul (l.map fun a => (g a).length) B (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact h a ha)
  simpa using hs

theorem length_toPlain_le (d : DomDesc) : (toPlain d).length ≤ d.size * (d.size + 3) := by
  have h : (toPlain d).length ≤ d.methods.length * (d.size + 3) := by
    rw [toPlain]
    refine le_trans (length_flatMap_le' (B := d.size + 3) fun m _ => ?_) (by simp)
    simp only [List.length_cons]
    have h1 : ((List.range (d.bd m).length).flatMap (execRows d m)).length
        ≤ (List.range (d.bd m).length).length * 1 := by
      refine length_flatMap_le' fun j _ => ?_
      rw [execRows]
      split <;> simp
    have h2 := DomDesc.length_bd_le d m
    simp only [List.length_range, Nat.mul_one] at h1
    omega
  exact le_trans h (Nat.mul_le_mul_right _ (DomDesc.length_methods_le_size d))

theorem length_toCalls_le (d : DomDesc) : (toCalls d).length ≤ d.size * (d.size + 1) := by
  have h : (toCalls d).length ≤ d.methods.length * (d.size + 1) := by
    rw [toCalls]
    refine le_trans (length_flatMap_le' (B := d.size + 1) fun m _ => ?_) (by simp)
    have h1 : ((List.range (d.bd m).length).flatMap (callRows d m)).length
        ≤ (List.range (d.bd m).length).length * 1 := by
      refine length_flatMap_le' fun j _ => ?_
      rw [callRows]
      split <;> simp
    have h2 := DomDesc.length_bd_le d m
    simp only [List.length_range, Nat.mul_one] at h1
    omega
  exact le_trans h (Nat.mul_le_mul_right _ (DomDesc.length_methods_le_size d))

theorem rowSz_of_mem_toLayout {d : DomDesc} {r : Row} (hr : r ∈ toLayout d) :
    rowSz r ≤ d.size + 4 := by
  rcases List.mem_append.1 hr with hr | hr
  · obtain ⟨m, -, h⟩ := (mem_toPlain d).1 hr
    rcases h with rfl | rfl | ⟨j, -, a, -, rfl⟩
    · simp [rowSz, begRow]
    · simp [rowSz, finRow]
    · have := rowSize_actOf_le d a
      simp only [rowSz, execRow, List.length_cons, List.length_map]
      omega
  · obtain ⟨⟨p, r'⟩, hpr, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨m, -, j, -, c, -, rfl, rfl⟩ := (mem_toCalls d).1 hpr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [rowSz, markRow, pushRow]
    · simp [rowSz, markRow, retRow]

/-- **The layout has polynomially many symbols** in the size of the domain description. -/
theorem tblSize_toLayout_le (d : DomDesc) :
    tblSize (toLayout d) ≤ 3 * d.size * (d.size + 3) * (d.size + 5) := by
  have h := tblSize_le_of_rowSz (tbl := toLayout d) (B := d.size + 4)
    fun r hr => rowSz_of_mem_toLayout hr
  have hlen : (toLayout d).length ≤ 3 * d.size * (d.size + 3) := by
    rw [toLayout, length_layout]
    have h1 := length_toPlain_le d
    have h2 := length_toCalls_le d
    have h3 : d.size * (d.size + 1) ≤ d.size * (d.size + 3) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  calc tblSize (toLayout d) ≤ (toLayout d).length * (d.size + 4 + 1) := h
    _ ≤ 3 * d.size * (d.size + 3) * (d.size + 5) := Nat.mul_le_mul hlen (by omega)

/-! ### Plan existence as solvability of the layout -/

/-- **Plan existence for a totally ordered description with a rooted instance is solvability of
its layout.** -/
theorem solvable_to_iff_aSolvable {d : DomDesc} {q : InstDesc} (hTO : d.MethodsTO)
    (hq : q.IsRooted) :
    Solvable d q ↔ ASolvable kPush kRet (toLayout d) {f | f ∈ regInitR q} {f | f ∈ regGoalR q} := by
  rw [solvable_to_iff_cReach hTO hq, ASolvable]
  exact exists_congr fun s => and_congr_left'
    (aReach_layout_iff (layoutOk_to d) (markFree_regInitR q)).symm

end Space

namespace Syn

open PTime Table Space

variable {ℰ : Family} {T : SynClass ℰ} {L : List Bool → Prop} {c : BitCoding InstDesc}

/-- **Plan existence for `T` is decidable in alternating polynomial space (`= EXPTIME`), the
domain description being supplied as advice.**  The alternating counterpart of
`HTN.Syn.SpaceDecidableAdv`. -/
def AltDecidableAdv (c : BitCoding InstDesc) (T : SynClass ℰ) : Prop :=
  ∀ (D : ℕ → DomDesc) (r rq : Polynomial ℕ), (∀ n, T.domOk (D n)) →
    (∀ n, (D n).size ≤ r.eval n) →
    ∃ (M : AltSpace) (A : ℕ → List Bool) (s : Polynomial ℕ),
      (∀ n, (A n).length ≤ s.eval n) ∧
        ∀ (n : ℕ) (q : InstDesc), T.instOk q → (c.code q).length ≤ rq.eval n →
          (Solvable (D n) q ↔ M.Accepts (c.code q) (A n))

/-- **The bridge**: a class whose plan-existence problem is solvable in alternating polynomial
space with the domain as advice decides, with polynomial advice, only languages of
`EXPTIME/poly`. -/
theorem inAltSpacePoly_of_inPolyAdvice (hT : AltDecidableAdv c T)
    (h : Coded.InPolyAdvice c T L) : InAltSpacePoly L := by
  obtain ⟨E, D, r, hE, hDsize, -, hDok, hEok, hcorr⟩ := h
  obtain ⟨F, hF, hFE⟩ := hE
  obtain ⟨rq, hrq⟩ := hF.poly_length
  obtain ⟨M, A, s, hA, hM⟩ := hT D r rq hDok hDsize
  refine inAltSpacePoly_of_precomp M (F := F) hF A s hA fun w => ?_
  have hlen : (c.code (E w)).length ≤ rq.eval w.length := by
    rw [← hFE w]; exact hrq w
  rw [hFE w, ← hM w.length (E w) (hEok w) hlen]
  exact (hcorr w).symm

end Syn

namespace Space

open Syn PTime

/-- **Plan existence for totally ordered HTN with a rooted instance is decidable in alternating
polynomial space, the domain description being supplied as advice.**  The machine is
`HTN.Space.altMachine`; the advice for the inputs of length `n` is the layout of `D n`, its facts
renamed by `tblNorm` so that they fit into polynomially many bits. -/
theorem altDecidableAdv_TO_HTN_root : AltDecidableAdv codingSer SynClass.TO_HTN_root := by
  intro D r rq hdomOk hsize
  let pT : Polynomial ℕ := 3 * Polynomial.X * (Polynomial.X + 3) * (Polynomial.X + 5)
  refine ⟨altMachine, fun n => tblAdv true ((toLayout (D n)).map
      (mapRow (tblNorm (rq.eval n + 3) (toLayout (D n))))),
    8 * (2 * pT.comp r + rq + 6) ^ 3, fun n => ?_, fun n q hq hlen => ?_⟩
  · show (tblAdv true ((toLayout (D n)).map
      (mapRow (tblNorm (rq.eval n + 3) (toLayout (D n)))))).length ≤ _
    set T := toLayout (D n) with hT
    set Lq := rq.eval n + 3 with hLq
    have hm : ∀ f ∈ tblFacts (T.map (mapRow (tblNorm Lq T))),
        (bitsOfNat f).length ≤ Lq + tblSize T := by
      intro f hf
      obtain ⟨c, hc, rfl⟩ := mem_tblFacts_of_mem_map hf
      exact length_bitsOfNat_le_of_lt_two_pow (tblNorm_lt hc)
    have h := length_tblAdv_le true (T.map (mapRow (tblNorm Lq T))) (Lq + tblSize T) hm
    rw [tblSize_map_mapRow] at h
    have hTs : tblSize T ≤ (pT.comp r).eval n := by
      have h1 : tblSize T ≤ 3 * (D n).size * ((D n).size + 3) * ((D n).size + 5) :=
        tblSize_toLayout_le (D n)
      have h2 := hsize n
      have h3 : 3 * (D n).size * ((D n).size + 3) * ((D n).size + 5)
          ≤ 3 * r.eval n * (r.eval n + 3) * (r.eval n + 5) := by
        gcongr
      simp only [pT, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have hmono : 8 * (tblSize T + (Lq + tblSize T) + 3) ^ 3
        ≤ (8 * (2 * pT.comp r + rq + 6) ^ 3).eval n := by
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_ofNat]
      have : tblSize T + (Lq + tblSize T) + 3 ≤ 2 * (pT.comp r).eval n + rq.eval n + 6 := by
        omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 3)
    omega
  · set T := toLayout (D n) with hT
    set Lq := rq.eval n + 3 with hLq
    set ρ := tblNorm Lq T with hρ
    have hlen' : (instSer q).length ≤ rq.eval n := by simpa using hlen
    have hpow : (2 : ℕ) ^ (rq.eval n + 2) ≤ 2 ^ Lq := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8 : (8 : ℕ) ≤ 2 ^ Lq := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ Lq := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hs : ∀ f ∈ regInitR q ++ [kPush, kRet], f < 2 ^ Lq := by
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · exact lt_of_lt_of_le (mem_regInitR_lt hlen' hf) hpow
      · simp only [List.mem_cons, List.not_mem_nil, or_false, kPush, kRet] at hf
        omega
    have hg : ∀ f ∈ regGoalR q, f < 2 ^ Lq := fun f hf =>
      lt_of_lt_of_le (mem_regGoalR_lt hlen' hf) hpow
    have hinj := injOnRel_tblNorm (tbl := T) hs hg
    set X : Set ℕ := {f | f ∈ relFacts T (regInitR q ++ [kPush, kRet]) (regGoalR q)} with hX
    have hXt : ∀ f ∈ tblFacts T, f ∈ X := fun f hf => by
      simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append]
      exact Or.inl (Or.inl hf)
    have hkp : kPush ∈ X := by simp [hX, relFacts]
    have hkr : kRet ∈ X := by simp [hX, relFacts]
    have hs₀ : {f | f ∈ regInitR q} ⊆ X := fun f hf => by
      simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append] at hf ⊢
      exact Or.inl (Or.inr (Or.inl hf))
    have hgX : {f | f ∈ regGoalR q} ⊆ X := fun f hf => by
      simp only [hX, Set.mem_setOf_eq, relFacts, List.mem_append] at hf ⊢
      exact Or.inr hf
    have key := aSolvable_map_iff (ρ := ρ) (X := X) (kp := kPush) (kr := kRet) (tbl := T)
      (fun a ha b hb hab => hinj a ha b hb hab) hXt hkp hkr hs₀ hgX
    have hfix : ∀ f, f < 2 ^ Lq → ρ f = f := fun f hf => tblNorm_of_lt hf
    have e1 : ρ kPush = kPush := hfix _ (by simp only [kPush]; omega)
    have e2 : ρ kRet = kRet := hfix _ (by simp only [kRet]; omega)
    have eimg : ∀ l : List ℕ, (∀ f ∈ l, f < 2 ^ Lq) → ρ '' {f | f ∈ l} = {f | f ∈ l} := by
      intro l hl
      ext f
      constructor
      · rintro ⟨a, ha, rfl⟩
        rw [hfix a (hl a ha)]
        exact ha
      · intro hf
        exact ⟨f, hf, hfix f (hl f hf)⟩
    rw [e1, e2, eimg _ (fun f hf => hs f (List.mem_append_left _ hf)), eimg _ hg] at key
    rw [codingSer_code, altMachine_accepts_iff, key]
    exact solvable_to_iff_aSolvable (hdomOk n) hq

end Space

end HTN
