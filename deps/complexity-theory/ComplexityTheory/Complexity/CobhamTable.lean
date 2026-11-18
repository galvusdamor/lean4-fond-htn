import ComplexityTheory.Complexity.Blocks
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Two closure properties of Cobham's class: finite tables, and reversal

`ComplexityTheory/Complexity/Cobham.lean` defines polynomial time as Cobham's class, and
`ComplexityTheory/Complexity/Blocks.lean` exhibits the functions that *write* a description
down.  What the polynomial-time reading of the rooting schema
(`HtnComplexity/Complexity/PolyResource.lean`) needs is the opposite direction — functions
that **read** a bit string — and both of the following are prerequisites for it.

* `HTN.PTime.cobham_ofTake` — a function determined by the first `k` bits of its argument, with
  outputs of bounded length, belongs to the class.  This is the "finite table" rule: any finite
  lookup table is a polynomial-time function.  The proof is an induction on `k` whose step is a
  bounded recursion on notation used purely as a case distinction on the leading bit;
* `HTN.PTime.cobham_revFn`, `HTN.PTime.polyTimeFun_reverse` — reversal.  It converts a
  right-to-left scan of a string (which is what the recursion on notation of Cobham's class
  performs) into a left-to-right one, which is how self-delimiting codes are parsed.
-/

namespace HTN

namespace PTime

/-! ### Finite tables -/

/-- **A finite table belongs to Cobham's class.**  If `T` depends only on the first `k` bits of
its argument and its outputs have length at most `m`, then reading `T` off the first argument is
a function of the class. -/
theorem cobham_ofTake : ∀ (k m : ℕ) (T : List Bool → List Bool),
    (∀ x, T x = T (x.take k)) → (∀ x, (T x).length ≤ m) →
    Cobham (fun args => T (args.getD 0 [])) := by
  intro k
  induction k with
  | zero =>
    intro m T hdep _
    have h : (fun args : Args => T (args.getD 0 [])) = fun _ => T [] := by
      funext args
      rw [hdep]
      simp
    rw [h]
    exact cobham_const _
  | succ k ih =>
    intro m T hdep hlen
    have hdep0 : ∀ x, T (false :: x) = T (false :: x.take k) := by
      intro x
      rw [hdep (false :: x)]
      simp
    have hdep1 : ∀ x, T (true :: x) = T (true :: x.take k) := by
      intro x
      rw [hdep (true :: x)]
      simp
    have h0 : Cobham (fun args : Args => T (false :: args.getD 0 [])) :=
      ih m (fun x => T (false :: x)) hdep0 (fun x => hlen _)
    have h1 : Cobham (fun args : Args => T (true :: args.getD 0 [])) :=
      ih m (fun x => T (true :: x)) hdep1 (fun x => hlen _)
    have haux : ∀ (v : Args) (x : List Bool),
        brnAux (fun _ => T []) (fun args => T (false :: args.getD 0 []))
          (fun args => T (true :: args.getD 0 [])) x v = T x := by
      intro v x
      induction x with
      | nil => rfl
      | cons b x _ => cases b <;> simp [brnAux]
    have hfn : brnFn (fun _ => T []) (fun args => T (false :: args.getD 0 []))
        (fun args => T (true :: args.getD 0 [])) = fun args => T (args.getD 0 []) := by
      funext args
      rw [brnFn, haux]
    have hb : ∀ args : Args,
        (brnFn (fun _ => T []) (fun args => T (false :: args.getD 0 []))
          (fun args => T (true :: args.getD 0 [])) args).length ≤
        ((fun _ : Args => List.replicate m false) args).length := by
      intro args
      rw [hfn]
      simpa using hlen _
    have hcob :=
      Cobham.brn (cobham_const (T [])) h0 h1 (cobham_const (List.replicate m false)) hb
    rwa [hfn] at hcob

/-! ### Reversal -/

/-- The step of the recursion computing the reversal: append the current bit to the recursive
value. -/
def revRec (b : Bool) : Fn :=
  compFn (fun args => args.getD 0 [] ++ args.getD 1 []) [proj 1, fun _ => [b]]

theorem revRec_apply (b : Bool) (args : Args) : revRec b args = args.getD 1 [] ++ [b] := by
  simp [revRec, compFn, proj]

theorem cobham_revRec (b : Bool) : Cobham (revRec b) :=
  Cobham.comp cobham_append (by
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact Cobham.proj 1
    · rw [List.mem_singleton.1 hh]
      exact cobham_const [b])

/-- The reversal of the first argument, as a function of Cobham's class. -/
def revFn : Fn := brnFn (fun _ => []) (revRec false) (revRec true)

theorem brnAux_rev (v : Args) : ∀ x : List Bool,
    brnAux (fun _ => []) (revRec false) (revRec true) x v = x.reverse := by
  intro x
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [brnAux, revRec_apply, ih]

theorem revFn_apply (args : Args) : revFn args = (args.getD 0 []).reverse := by
  rw [revFn, brnFn, brnAux_rev]

/-- **Reversal belongs to Cobham's class.** -/
theorem cobham_revFn : Cobham revFn := by
  have hb : ∀ args : Args, (revFn args).length ≤ (proj 0 args).length := by
    intro args
    rw [revFn_apply]
    simp [proj]
  exact Cobham.brn (cobham_const []) (cobham_revRec false) (cobham_revRec true)
    (Cobham.proj 0) hb

/-- **Reversal is polynomial time.** -/
theorem polyTimeFun_reverse : PolyTimeFun (fun x : List Bool => x.reverse) :=
  CobhamFun.polyTimeFun ⟨revFn, cobham_revFn, fun x => by simp [revFn_apply]⟩

/-! ### Combining one-bit answers -/

theorem getD_take_two (y : List Bool) (i : ℕ) (hi : i < 2) :
    (y.take 2).getD i false = y.getD i false := by
  match y, i, hi with
  | [], _, _ => simp
  | _ :: _, 0, _ => simp
  | [_], 1, _ => simp
  | _ :: _ :: _, 1, _ => simp

/-- Truncating an answer to its first bit stays polynomial time. -/
theorem PolyTimeFun.firstBit {F : List Bool → List Bool} (hF : PolyTimeFun F) :
    PolyTimeFun (fun x => [(F x).getD 0 false]) := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  have htab : Cobham (fun args : Args => [(args.getD 0 []).getD 0 false]) :=
    cobham_ofTake 1 1 (fun y => [y.getD 0 false])
      (fun y => by cases y <;> simp) (fun y => by simp)
  refine CobhamFun.polyTimeFun ⟨compFn (fun args : Args => [(args.getD 0 []).getD 0 false]) [f],
    Cobham.comp htab (by
      intro h hh
      rw [List.mem_singleton.1 hh]
      exact hf), fun x => ?_⟩
  simp [compFn, hFf x]

/-- **Two one-bit answers may be combined by any Boolean operation**, in polynomial time. -/
theorem PolyTimeFun.comb {F G : List Bool → List Bool} (hF : PolyTimeFun F)
    (hG : PolyTimeFun G) (hF1 : ∀ x, (F x).length = 1) (hG1 : ∀ x, (G x).length = 1)
    (op : Bool → Bool → Bool) :
    PolyTimeFun (fun x => [op ((F x).getD 0 false) ((G x).getD 0 false)]) := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  obtain ⟨g, hg, hGg⟩ := hG.cobham
  have htab : Cobham (fun args : Args =>
      [op ((args.getD 0 []).getD 0 false) ((args.getD 0 []).getD 1 false)]) :=
    cobham_ofTake 2 1 (fun y => [op (y.getD 0 false) (y.getD 1 false)])
      (fun y => by
        show [op (y.getD 0 false) (y.getD 1 false)]
          = [op ((y.take 2).getD 0 false) ((y.take 2).getD 1 false)]
        rw [getD_take_two y 0 (by omega), getD_take_two y 1 (by omega)])
      (fun y => by simp)
  have happ : Cobham (compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 []) [f, g]) :=
    Cobham.comp cobham_append (by
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · exact hf
      · rw [List.mem_singleton.1 hh]
        exact hg)
  refine CobhamFun.polyTimeFun ⟨compFn (fun args : Args =>
      [op ((args.getD 0 []).getD 0 false) ((args.getD 0 []).getD 1 false)])
    [compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 []) [f, g]],
    Cobham.comp htab (by
      intro h hh
      rw [List.mem_singleton.1 hh]
      exact happ), fun x => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, F x = [a] := List.length_eq_one_iff.1 (hF1 x)
  obtain ⟨b, hb⟩ : ∃ b, G x = [b] := List.length_eq_one_iff.1 (hG1 x)
  simp only [compFn, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [← hFf x, ← hGg x, ha, hb]
  simp

end PTime

end HTN
