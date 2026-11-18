import ComplexityTheory.Compile.CobCirc
import HtnComplexity.Compile.Uni
import HtnComplexity.Complexity.RecMemUniform
/-!
# An alternating machine with a polynomial memory, as a uniform family of recursive machines

This is the heart of the source bridge.  Given an alternating machine with a polynomial memory
in the Cobham-described model `HTN.PSpace.ASpace`, it produces a **uniform family of recursive
alternating machines with a memory** (`HTN.Syn.UniRecMem`) accepting the same language — the
model in which the hardness family in `TO-HTN-1` of
`HtnComplexity/Complexity/RecMemUniform.lean` is written.

The passage has three ingredients.

1. The three tests and the two functions of the machine are of Cobham's class, so each of them
   is computed, on arguments of a bounded length, by a **uniform family of circuits of
   polynomial size** (`HTN.Compile.cobham_circFam'`).
2. A circuit is evaluated by a straight-line block of an **alternating bit program**
   (`HtnComplexity/Compile/Prog.lean`), whose memory holds the current configuration, the
   guessed successor, the input word and the wires of the circuit.  The program is the obvious
   loop: accept if the configuration is accepting; otherwise guess the bits of a successor
   existentially or universally, according to the classification of the configuration, and go on
   if the guess is a real successor.  Its layout is
   `HtnComplexity/Compile/Layout.lean`, its correctness
   `HtnComplexity/Compile/Loop.lean` and `HtnComplexity/Compile/Pro.lean`, its
   well-formedness `HtnComplexity/Compile/Wf.lean`, and its uniformity and size
   `HtnComplexity/Compile/Uni.lean`.
3. The alternating machine accepts exactly when some finite computation does, which is the
   language read off at the horizon (`HTN.PSpace.ASpace.L_iff_exists`).

The result is `HTN.Compile.exists_uniRecMem`.
-/

namespace HTN

namespace Compile

open Syn PSpace PTime

namespace Sim

variable {S : Sim} {x : List Bool}

/-- **The machine of the compiled program accepts exactly the words the alternating machine
accepts**, at the length the program was built for. -/
theorem accepts_iff (hx : x.length = S.n) :
    (progMach S.lay.prog S.lay.mm).Accepts x ↔ S.M.L x := by
  rw [accepts_progMach_iff wf_prog hx, pro_iff,
    loop_iff hx (S.M.initF_length x) (memOk_p8 hx), S.M.L_iff_exists x]

variable (M : ASpace) (FW : CircFam M.widthF 1) (FI : CircFam M.initF 1)
  (FA : CircFam (fun args => [M.accB args]) 2) (FU : CircFam (fun args => [M.univB args]) 2)
  (FS : CircFam (fun args => [M.stepB args]) 3)

/-- **The uniform family of recursive alternating machines of an alternating machine with a
polynomial memory.** -/
noncomputable def uniOf : UniRecMem where
  mach := fun n => progMach (simAt M FW FI FA FU FS n).lay.prog (simAt M FW FI FA FU FS n).lay.mm
  bound := Polynomial.C 2000 * sizeP M FW FI FA FU FS * sizeP M FW FI FA FU FS
  mach_primrec := primrec_progMach_fam primrec_prog primrec_mm
  pos_below := fun _ => posBelow_progMach wf_prog
  dom_size := fun n => by
    refine le_trans (rmConst_progMach_le _ _) ?_
    have h := size_le (M := M) (FW := FW) (FI := FI) (FA := FA) (FU := FU) (FS := FS) n
    have h2 := Nat.mul_le_mul h h
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    calc 2000 * ((simAt M FW FI FA FU FS n).lay.prog.length
              + (simAt M FW FI FA FU FS n).lay.mm + 1)
            * ((simAt M FW FI FA FU FS n).lay.prog.length
              + (simAt M FW FI FA FU FS n).lay.mm + 1)
        = 2000 * (((simAt M FW FI FA FU FS n).lay.prog.length
              + (simAt M FW FI FA FU FS n).lay.mm + 1)
            * ((simAt M FW FI FA FU FS n).lay.prog.length
              + (simAt M FW FI FA FU FS n).lay.mm + 1)) := by ring
      _ ≤ 2000 * ((sizeP M FW FI FA FU FS).eval n * (sizeP M FW FI FA FU FS).eval n) :=
          Nat.mul_le_mul_left _ h2
      _ = 2000 * (sizeP M FW FI FA FU FS).eval n * (sizeP M FW FI FA FU FS).eval n := by ring

/-- **The uniform family accepts the language of the machine.** -/
theorem L_uniOf (w : List Bool) : (uniOf M FW FI FA FU FS).L w ↔ M.L w :=
  accepts_iff (S := simAt M FW FI FA FU FS w.length) rfl

end Sim

/-- **Every language of alternating polynomial space is the language of a uniform family of
recursive alternating machines with a memory.** -/
theorem exists_uniRecMem (M : ASpace) : ∃ F : UniRecMem, ∀ w, F.L w ↔ M.L w := by
  obtain ⟨FW⟩ := cobham_circFam' M.cobham_widthF 1
  obtain ⟨FI⟩ := cobham_circFam' M.cobham_initF 1
  obtain ⟨FA⟩ := cobham_circFam' M.cobhamB_accB 2
  obtain ⟨FU⟩ := cobham_circFam' M.cobhamB_univB 2
  obtain ⟨FS⟩ := cobham_circFam' M.cobhamB_stepB 3
  exact ⟨Sim.uniOf M FW FI FA FU FS, Sim.L_uniOf M FW FI FA FU FS⟩

end Compile

end HTN
