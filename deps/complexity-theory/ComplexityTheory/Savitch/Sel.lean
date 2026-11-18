import ComplexityTheory.Savitch.State
/-!
# Case distinction inside Cobham's class

The step of the depth-first search of `ComplexityTheory/Savitch/State.lean` is a nest of case
distinctions, so showing it to be a function of the polynomial-time class needs one closure
property the library of `ComplexityTheory/Complexity/CobhamString.lean` does not yet have:
a *string-valued* case distinction.  `HTN.Savitch.cobham_ite` provides it, and
`HTN.Savitch.selFn` is the three-argument selector it is built from — the recursion on notation
that reads the first bit of its first argument and returns its second or its third argument
accordingly.
-/

namespace HTN

namespace Savitch

open PTime PSpace

/-- **The selector**: the second argument if the first one starts with `1`, the third one
otherwise. -/
def selFn : Fn := brnFn (proj 1) (proj 3) (proj 2)

theorem selFn_apply (args : Args) :
    selFn args = if (args.getD 0 []).headD false = true then args.getD 1 [] else args.getD 2 [] := by
  rcases hb : args.getD 0 [] with _ | ⟨b, t⟩
  · show brnAux (proj 1) (proj 3) (proj 2) (args.getD 0 []) args.tail = _
    rw [hb]
    simp only [brnAux, proj, List.headD_nil]
    rw [if_neg (by simp)]
    simp
  · show brnAux (proj 1) (proj 3) (proj 2) (args.getD 0 []) args.tail = _
    rw [hb]
    have hstep : brnAux (proj 1) (proj 3) (proj 2) (b :: t) args.tail
        = (bif b then (proj 2 : Fn) else proj 3)
          (t :: brnAux (proj 1) (proj 3) (proj 2) t args.tail :: args.tail) := rfl
    rw [hstep]
    rcases b with _ | _
    · simp only [cond_false, proj, List.headD_cons, Bool.false_eq_true, if_false]
      simp
    · simp only [cond_true, proj, List.headD_cons, if_true]
      simp

theorem cobham_selFn : Cobham selFn := by
  refine Cobham.brn (Cobham.proj 1) (Cobham.proj 3) (Cobham.proj 2)
    (cobham_c2 cobham_append (Cobham.proj 1) (Cobham.proj 2)) fun args => ?_
  have hb : (compFn (fun args : Args => args.getD 0 [] ++ args.getD 1 []) [proj 1, proj 2]
      args).length = (args.getD 1 []).length + (args.getD 2 []).length := by
    simp [compFn, proj]
  rw [show brnFn (proj 1) (proj 3) (proj 2) = selFn from rfl, selFn_apply, hb]
  by_cases h : (args.getD 0 []).headD false = true
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **A case distinction on a predicate of the class**, with the two branches computed by
functions of the class. -/
theorem cobham_ite {p : Args → Bool} (hp : CobhamB p) {f g : Fn} (hf : Cobham f)
    (hg : Cobham g) {P : Args → Prop} [inst : ∀ args, Decidable (P args)]
    (hP : ∀ args, P args ↔ p args = true) :
    Cobham (fun args => if P args then f args else g args) :=
  (cobham_c3 cobham_selFn hp hf hg).of_eq' fun args => by
    simp only [compFn, selFn_apply]
    by_cases h : P args
    · rw [if_pos h, if_pos (by simpa using (hP args).1 h)]
      simp
    · have hpf : p args = false := by
        rcases hb : p args with _ | _
        · rfl
        · exact absurd ((hP args).2 hb) h
      rw [if_neg h, if_neg (by simp [hpf])]
      simp

end Savitch

end HTN
