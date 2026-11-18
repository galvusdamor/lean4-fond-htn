import HtnComplexity.Compile.Prog
/-!
# The machine of a program is produced by an algorithm

`HtnComplexity/Compile/Prog.lean` translates an alternating bit program into a recursive
alternating machine with a memory.  A uniform family of machines
(`HTN.Syn.UniRecMem`) additionally asks that the components of the machine be **primitive
recursive in the input length**, and that is what this file supplies: from a primitive recursive
family of programs and of memory widths, the family of machines
`HTN.Compile.progMach` is primitive recursive (`HTN.Compile.primrec_progMach_fam`).

Nothing here is mathematical; it is the bookkeeping that turns the definition by cases on the
opcode into a nest of `Primrec.ite`s, and the small lists the definition writes out into
`Primrec.list_flatMap`s over the two-element list of bits.
-/

namespace HTN

namespace Compile

open Syn

section Prim

variable {Pf : ℕ → List Instr}

/-- The instruction at a program point, as a function of the pair. -/
private theorem primrec_instr (hP : Primrec Pf) :
    Primrec fun p : ℕ × ℕ => (Pf p.1).getI p.2 :=
  Primrec.list_getI.comp (hP.comp Primrec.fst) Primrec.snd

/-- **The existential transitions of a program point are primitive recursive.** -/
theorem primrec_progEx_fam (hP : Primrec Pf) :
    Primrec fun p : ℕ × ℕ => progEx (Pf p.1) p.2 := by
  have hI := primrec_instr hP
  have hop : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).1 := Primrec.fst.comp hI
  have hx : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).2.1 :=
    Primrec.fst.comp (Primrec.snd.comp hI)
  have hy : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hI))
  have hz : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hI))
  have hsrc : Primrec fun p : ℕ × ℕ => 3 * p.2 :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd
  have hnext : Primrec fun p : ℕ × ℕ => 3 * (p.2 + 1) :=
    Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 1))
  have heq : ∀ m : ℕ, PrimrecPred fun p : ℕ × ℕ => ((Pf p.1).getI p.2).1 = m :=
    fun m => PrimrecRel.comp Primrec.eq hop (Primrec.const m)
  unfold progEx
  refine Primrec.ite (heq 1) ?_ (Primrec.ite (heq 2) ?_ (Primrec.ite (heq 3) ?_
    (Primrec.ite (heq 4) ?_ (Primrec.ite (heq 5) ?_ (Primrec.ite (heq 7) ?_
      (Primrec.ite (heq 8) ?_ (Primrec.ite (heq 9) ?_ (Primrec.ite (heq 10) ?_
        (Primrec.const [])))))))))
  -- `iNand i j d`
  · refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
    refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
    refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : (((ℕ × ℕ) × Bool) × Bool) × Bool => w.1.1.1 :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    have ha : Primrec fun w : (((ℕ × ℕ) × Bool) × Bool) × Bool => w.1.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have hbb : Primrec fun w : (((ℕ × ℕ) × Bool) × Bool) × Bool => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hold : Primrec fun w : (((ℕ × ℕ) × Bool) × Bool) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair
        (Primrec.list_cons.comp (Primrec.pair (hx.comp hb) ha)
          (Primrec.list_cons.comp (Primrec.pair (hy.comp hb) hbb) (Primrec.const [])))
        (Primrec.pair
          (Primrec.pair (hz.comp hb) (Primrec.pair hold
            ((Primrec.dom_bool₂ fun a b => !(a && b)).comp ha hbb)))
          (hnext.comp hb))))
  -- `iRdIn p d`
  · refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
    refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hbit : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hold : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb)
      (Primrec.pair
        (Primrec.list_cons.comp (Primrec.pair (hx.comp hb) hbit) (Primrec.const []))
        (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold hbit))
            (hnext.comp hb))))
  -- `iBrIf i t`
  · refine Primrec.list_cons.comp ?_ (Primrec.list_cons.comp ?_ (Primrec.const []))
    · exact Primrec.pair hsrc (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.list_cons.comp (Primrec.pair hx (Primrec.const true))
            (Primrec.const []))
          (Primrec.pair (Primrec.pair hx (Primrec.pair (Primrec.const true)
              (Primrec.const true)))
            (Primrec.nat_mul.comp (Primrec.const 3) hy))))
    · exact Primrec.pair hsrc (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.list_cons.comp (Primrec.pair hx (Primrec.const false))
            (Primrec.const []))
          (Primrec.pair (Primrec.pair hx (Primrec.pair (Primrec.const false)
              (Primrec.const false)))
            hnext)))
  -- `iEx d`
  · refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
    refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hold : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hnew : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold hnew))
          (hnext.comp hb))))
  -- `iAll d`
  · refine Primrec.list_append.comp ?_ ?_
    · refine Primrec.list_map (Primrec.const [false, true]) ?_
      have hb : Primrec fun w : (ℕ × ℕ) × Bool => w.1 := Primrec.fst
      have hold : Primrec fun w : (ℕ × ℕ) × Bool => w.2 := Primrec.snd
      exact Primrec.pair (Primrec.nat_add.comp (hsrc.comp hb) (Primrec.const 1))
        (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold (Primrec.const false)))
            (hnext.comp hb))))
    · refine Primrec.list_map (Primrec.const [false, true]) ?_
      have hb : Primrec fun w : (ℕ × ℕ) × Bool => w.1 := Primrec.fst
      have hold : Primrec fun w : (ℕ × ℕ) × Bool => w.2 := Primrec.snd
      exact Primrec.pair (Primrec.nat_add.comp (hsrc.comp hb) (Primrec.const 2))
        (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const [])
          (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold (Primrec.const true)))
            (hnext.comp hb))))
  -- `iJmp t`
  · refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : (ℕ × ℕ) × Bool => w.1 := Primrec.fst
    have hv : Primrec fun w : (ℕ × ℕ) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair
        (Primrec.list_cons.comp (Primrec.pair (Primrec.const 0) hv) (Primrec.const []))
        (Primrec.pair (Primrec.pair (Primrec.const 0) (Primrec.pair hv hv))
          (Primrec.nat_mul.comp (Primrec.const 3) (hy.comp hb)))))
  -- `iSet0 d`
  · refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : (ℕ × ℕ) × Bool => w.1 := Primrec.fst
    have hold : Primrec fun w : (ℕ × ℕ) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold (Primrec.const false)))
          (hnext.comp hb))))
  -- `iSet1 d`
  · refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : (ℕ × ℕ) × Bool => w.1 := Primrec.fst
    have hold : Primrec fun w : (ℕ × ℕ) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold (Primrec.const true)))
          (hnext.comp hb))))
  -- `iCopy s d`
  · refine Primrec.list_flatMap (Primrec.const [false, true]) ?_
    refine Primrec.list_map (Primrec.const [false, true]) ?_
    have hb : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hv : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.1.2 :=
      Primrec.snd.comp Primrec.fst
    have hold : Primrec fun w : ((ℕ × ℕ) × Bool) × Bool => w.2 := Primrec.snd
    exact Primrec.pair (hsrc.comp hb) (Primrec.pair (Primrec.const [])
      (Primrec.pair
        (Primrec.list_cons.comp (Primrec.pair (hx.comp hb) hv) (Primrec.const []))
        (Primrec.pair (Primrec.pair (hz.comp hb) (Primrec.pair hold hv))
          (hnext.comp hb))))

/-- **The universal transitions of a program point are primitive recursive.** -/
theorem primrec_progUn_fam (hP : Primrec Pf) :
    Primrec fun p : ℕ × ℕ => progUn (Pf p.1) p.2 := by
  have hI := primrec_instr hP
  have hop : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).1 := Primrec.fst.comp hI
  have hsrc : Primrec fun p : ℕ × ℕ => 3 * p.2 :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd
  unfold progUn
  refine Primrec.ite (PrimrecRel.comp Primrec.eq hop (Primrec.const 5)) ?_ (Primrec.const [])
  refine Primrec.list_cons.comp ?_ (Primrec.const [])
  exact Primrec.pair hsrc (Primrec.pair (Primrec.const []) (Primrec.pair (Primrec.const [])
    (Primrec.pair (Primrec.nat_add.comp hsrc (Primrec.const 1))
      (Primrec.nat_add.comp hsrc (Primrec.const 2)))))

/-- **The accepting conditions of a program point are primitive recursive.** -/
theorem primrec_progAcc_fam (hP : Primrec Pf) :
    Primrec fun p : ℕ × ℕ => progAcc (Pf p.1) p.2 := by
  have hI := primrec_instr hP
  have hop : Primrec fun p : ℕ × ℕ => ((Pf p.1).getI p.2).1 := Primrec.fst.comp hI
  have hsrc : Primrec fun p : ℕ × ℕ => 3 * p.2 :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd
  unfold progAcc
  refine Primrec.ite (PrimrecRel.comp Primrec.eq hop (Primrec.const 6)) ?_ (Primrec.const [])
  refine Primrec.list_cons.comp ?_ (Primrec.const [])
  exact Primrec.pair hsrc (Primrec.pair (Primrec.const []) (Primrec.const []))

end Prim

/-- The machine of a program is produced by an algorithm. -/
theorem primrec_progMach_fam {Pf : ℕ → List Instr} {mmf : ℕ → ℕ} (hP : Primrec Pf)
    (hmm : Primrec mmf) : RecMachFamPrimrec fun n => progMach (Pf n) (mmf n) := by
  have hrange : Primrec fun n : ℕ => List.range (Pf n).length :=
    Primrec.list_range.comp (Primrec.list_length.comp hP)
  exact
    { mem := hmm
      start := Primrec.const 0
      acc := Primrec.list_flatMap hrange (primrec_progAcc_fam hP)
      ex := Primrec.list_flatMap hrange (primrec_progEx_fam hP)
      un := Primrec.list_flatMap hrange (primrec_progUn_fam hP) }

end Compile

end HTN
