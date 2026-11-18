import HtnComplexity.Complexity.AltMemUniform
import ComplexityTheory.Complexity.CobhamTable
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# Prefixing a word with the length of another word, in unary

`HTN.PTime.lenPad n c = 0ⁿ 1 c` — the word `c` behind `n` zeros and a one.  It is the input the
exponential-time planner of the target side receives (`HTN.Space.ScaleDecidableAdv`): the length
`n` the domain belongs to, in unary, followed by the code of the instance.  Without the unary
prefix, a machine whose time bound is exponential in the length of its input would have too
little time for instances with short codes over large domains; see `NOTES.md` §57.

* `HTN.PTime.PolyTimeFun.append` — the concatenation of two polynomial-time functions is
  polynomial time;
* `HTN.PTime.polyTimeFun_lenPad` — `w ↦ lenPad |w| (F w)` is polynomial time when `F` is.
-/

namespace HTN

namespace PTime

/-- **The concatenation of two polynomial-time functions is polynomial time.** -/
theorem PolyTimeFun.append {F G : List Bool → List Bool} (hF : PolyTimeFun F)
    (hG : PolyTimeFun G) : PolyTimeFun (fun w => F w ++ G w) := by
  obtain ⟨f, hf, hFf⟩ := hF.cobham
  obtain ⟨g, hg, hGg⟩ := hG.cobham
  refine CobhamFun.polyTimeFun ⟨compFn (fun args => args.getD 0 [] ++ args.getD 1 []) [f, g],
    Cobham.comp cobham_append ?_, fun x => ?_⟩
  · intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact hf
    · rw [List.mem_singleton.1 hh]; exact hg
  · simp [compFn, hFf, hGg]

/-- A constant function is polynomial time. -/
theorem polyTimeFun_const (C : List Bool) : PolyTimeFun (fun _ => C) :=
  CobhamFun.polyTimeFun ⟨fun _ => C, cobham_const C, fun _ => rfl⟩

/-- `|w|` zeros, as a polynomial-time function of `w`. -/
theorem polyTimeFun_zeros : PolyTimeFun (fun w => List.replicate w.length false) :=
  CobhamFun.polyTimeFun ⟨Syn.zeroLinFn 1, Syn.cobham_zeroLinFn 1, fun x => by rw [Syn.zeroLinFn_apply]; simp⟩

/-- **The word `c` behind the length `n` in unary**: `n` zeros, a one, then `c`. -/
def lenPad (n : ℕ) (c : List Bool) : List Bool := List.replicate n false ++ true :: c

@[simp] theorem length_lenPad (n : ℕ) (c : List Bool) : (lenPad n c).length = n + 1 + c.length := by
  simp [lenPad]; omega

/-- The unary prefix and the word can be read back. -/
theorem lenPad_injective {n n' : ℕ} {c c' : List Bool} (h : lenPad n c = lenPad n' c') :
    n = n' ∧ c = c' := by
  induction n generalizing n' with
  | zero =>
      cases n' with
      | zero => simpa [lenPad] using h
      | succ n' => simp [lenPad, List.replicate_succ] at h
  | succ n ih =>
      cases n' with
      | zero => simp [lenPad, List.replicate_succ] at h
      | succ n' =>
          have h' : lenPad n c = lenPad n' c' := by
            simpa [lenPad, List.replicate_succ] using h
          obtain ⟨h1, h2⟩ := ih h'
          exact ⟨by omega, h2⟩

/-- **`w ↦ lenPad |w| (F w)` is polynomial time** when `F` is. -/
theorem polyTimeFun_lenPad {F : List Bool → List Bool} (hF : PolyTimeFun F) :
    PolyTimeFun (fun w => lenPad w.length (F w)) := by
  have h := polyTimeFun_zeros.append ((polyTimeFun_const [true]).append hF)
  simpa [lenPad] using h

end PTime

end HTN
