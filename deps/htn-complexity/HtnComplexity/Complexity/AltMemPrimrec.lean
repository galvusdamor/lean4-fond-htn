import HtnComplexity.Complexity.AltMemFamily
/-!
# The encoding of an alternating machine with a memory, for a *varying* machine

`HtnComplexity/Complexity/AltMemFamily.lean` proves that the description
`HTN.Syn.amDom M n` is primitive recursive in `n` for a **fixed** machine `M`.  A hardness
family whose machine may grow with the input length — which is what a space-bounded
construction needs, since the number of memory bits and the number of transitions both have to
grow — needs the same statement for a machine that *depends* on `n`, and for a number of steps
that is not the length of the input word but a function of it.

This file proves exactly that:

    HTN.Syn.computable_amDom_fam :
      MachFamPrimrec Mf → Primrec T → Computable fun n => amDom (Mf n) (T n)

together with the component lemmas it is assembled from.  The hypotheses are collected in
`HTN.Syn.MachFamPrimrec`, which says that the five components of the machine are primitive
recursive functions of the index.  Taking `Mf` constant and `T = id` recovers
`HTN.Syn.computable_amDom`.

The file is pure computability bookkeeping; the semantics of the encoding are untouched, so the
correctness theorem `HTN.Syn.solvable_amDom_iff` applies verbatim to every `amDom (Mf n) (T n)`.
-/

namespace HTN

namespace Syn

open Binarise

/-- **The components of a family of alternating machines with a memory are primitive
recursive.**  This is the uniformity hypothesis of a hardness family whose machine grows with
the input length. -/
structure MachFamPrimrec (Mf : ℕ → BitAltMem) : Prop where
  /-- The number of memory bits. -/
  mem : Primrec fun n => (Mf n).mem
  /-- The initial state. -/
  start : Primrec fun n => (Mf n).start
  /-- The accepting conditions. -/
  acc : Primrec fun n => (Mf n).acc
  /-- The existential transitions. -/
  ex : Primrec fun n => (Mf n).ex
  /-- The universal transitions. -/
  un : Primrec fun n => (Mf n).un

variable {Mf : ℕ → BitAltMem} {T : ℕ → ℕ}

/-- The data of the actions, for a varying machine. -/
theorem primrec_amActData_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun p : ℕ × ℕ => amActData (Mf p.1) (T p.1) p.2 := by
  have hn : Primrec fun p : ℕ × ℕ => T p.1 := hT.comp Primrec.fst
  have hex : Primrec fun p : ℕ × ℕ => (Mf p.1).ex := h.ex.comp Primrec.fst
  have hun : Primrec fun p : ℕ × ℕ => (Mf p.1).un := h.un.comp Primrec.fst
  have hacc : Primrec fun p : ℕ × ℕ => (Mf p.1).acc := h.acc.comp Primrec.fst
  have hmem : Primrec fun p : ℕ × ℕ => (Mf p.1).mem := h.mem.comp Primrec.fst
  have hexlen : Primrec fun p : ℕ × ℕ => (Mf p.1).ex.length := Primrec.list_length.comp hex
  have hunlen : Primrec fun p : ℕ × ℕ => (Mf p.1).un.length := Primrec.list_length.comp hun
  have hacclen : Primrec fun p : ℕ × ℕ => (Mf p.1).acc.length := Primrec.list_length.comp hacc
  have hd4 : Primrec fun p : ℕ × ℕ => p.2 / 4 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hm4 : Primrec fun p : ℕ × ℕ => p.2 % 4 :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hkex : Primrec fun p : ℕ × ℕ => p.2 / 4 / (Mf p.1).ex.length :=
    Primrec.nat_div.comp hd4 hexlen
  have hiex : Primrec fun p : ℕ × ℕ => p.2 / 4 % (Mf p.1).ex.length :=
    Primrec.nat_mod.comp hd4 hexlen
  have hkun : Primrec fun p : ℕ × ℕ => p.2 / 4 / (Mf p.1).un.length :=
    Primrec.nat_div.comp hd4 hunlen
  have hiun : Primrec fun p : ℕ × ℕ => p.2 / 4 % (Mf p.1).un.length :=
    Primrec.nat_mod.comp hd4 hunlen
  have hmapof : Primrec₂ fun (p : ℕ × ℕ) (l : MemLit) => amRailOf (T p.1) l :=
    primrec_amRailOf.comp (Primrec.pair (hn.comp Primrec.fst) Primrec.snd)
  have hfwd : Primrec fun p : ℕ × ℕ =>
      amFwdData (Mf p.1) (T p.1) (p.2 / 4 / (Mf p.1).ex.length)
        (p.2 / 4 % (Mf p.1).ex.length) := by
    have htex := Primrec.list_getI.comp hex hiex
    have h2 := Primrec.snd.comp htex
    have hbitB := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hguardL := Primrec.fst.comp h3
    have h4 := Primrec.snd.comp h3
    have hwr := Primrec.fst.comp h4
    have hidx := Primrec.fst.comp hwr
    have hwr2 := Primrec.snd.comp hwr
    have hold := Primrec.fst.comp hwr2
    have hnew := Primrec.snd.comp hwr2
    have hbit := primrec_posFactPair.comp (Primrec.pair hkex hbitB)
    have hrailold := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hold))
    have hrailnew := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hnew))
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair (Primrec.list_cons.comp hbit (Primrec.list_cons.comp hrailold hguard))
      (Primrec.pair (Primrec.list_cons.comp hrailnew (Primrec.const []))
        (Primrec.list_cons.comp hrailold (Primrec.const [])))
  have hundo : Primrec fun p : ℕ × ℕ => amUndoData (Mf p.1) (T p.1) (p.2 / 4) := by
    have htex := Primrec.list_getI.comp hex hd4
    have h2 := Primrec.snd.comp htex
    have h3 := Primrec.snd.comp h2
    have h4 := Primrec.snd.comp h3
    have hwr := Primrec.fst.comp h4
    have hidx := Primrec.fst.comp hwr
    have hwr2 := Primrec.snd.comp hwr
    have hold := Primrec.fst.comp hwr2
    have hnew := Primrec.snd.comp hwr2
    have hrailold := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hold))
    have hrailnew := primrec_amRailTriple.comp (Primrec.pair hn (Primrec.pair hidx hnew))
    exact Primrec.pair (Primrec.list_cons.comp hrailnew (Primrec.const []))
      (Primrec.pair (Primrec.list_cons.comp hrailold (Primrec.const []))
        (Primrec.list_cons.comp hrailnew (Primrec.const [])))
  have hgrd : Primrec fun p : ℕ × ℕ =>
      amGrdData (Mf p.1) (T p.1) (p.2 / 4 / (Mf p.1).un.length)
        (p.2 / 4 % (Mf p.1).un.length) := by
    have htun := Primrec.list_getI.comp hun hiun
    have h2 := Primrec.snd.comp htun
    have hbitB := Primrec.fst.comp h2
    have h3 := Primrec.snd.comp h2
    have hguardL := Primrec.fst.comp h3
    have hbit := primrec_posFactPair.comp (Primrec.pair hkun hbitB)
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair (Primrec.list_cons.comp hbit hguard)
      (Primrec.pair (Primrec.const []) (Primrec.const []))
  have haccd : Primrec fun p : ℕ × ℕ => amAccData (Mf p.1) (T p.1) (p.2 / 4) := by
    have htacc := Primrec.list_getI.comp hacc hd4
    have hguardL := Primrec.snd.comp htacc
    have hguard := Primrec.list_map hguardL hmapof
    exact Primrec.pair hguard (Primrec.pair (Primrec.const []) (Primrec.const []))
  have hinit : Primrec fun p : ℕ × ℕ => amInitData (Mf p.1) (T p.1) := by
    have hmapinit : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) => amRail (T p.1) i false :=
      primrec_amRailTriple.comp (Primrec.pair (hn.comp Primrec.fst)
        (Primrec.pair Primrec.snd (Primrec.const false)))
    have hmap := Primrec.list_map (Primrec.list_range.comp hmem) hmapinit
    exact Primrec.pair (Primrec.const []) (Primrec.pair hmap (Primrec.const []))
  refine (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 0)
    (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 0)) hfwd
    (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 1)
      (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 1)) hundo
      (Primrec.ite (c := fun p : ℕ × ℕ => p.2 % 4 = 2)
        (PrimrecRel.comp Primrec.eq hm4 (Primrec.const 2)) hgrd
        (Primrec.ite (c := fun p : ℕ × ℕ => p.2 / 4 < (Mf p.1).acc.length)
          (PrimrecRel.comp Primrec.nat_lt hd4 hacclen)
          haccd hinit)))).of_eq fun p => rfl

/-- The actions, for a varying machine. -/
theorem primrec_amActions_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amActions (Mf n) (T n) := by
  refine Primrec.list_map (Primrec.list_range.comp ?_) ?_
  · have hexlen : Primrec fun n : ℕ => (Mf n).ex.length := Primrec.list_length.comp h.ex
    have hunlen : Primrec fun n : ℕ => (Mf n).un.length := Primrec.list_length.comp h.un
    have hacclen : Primrec fun n : ℕ => (Mf n).acc.length := Primrec.list_length.comp h.acc
    have hkey : Primrec fun n : ℕ =>
        4 * (T n * (Mf n).ex.length + T n * (Mf n).un.length + (Mf n).ex.length
          + (Mf n).acc.length + 1) :=
      Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp
            (Primrec.nat_add.comp
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp hT hexlen)
                (Primrec.nat_mul.comp hT hunlen))
              hexlen)
            hacclen)
          (Primrec.const 1))
    exact hkey.of_eq fun n => rfl
  · exact Primrec.pair Primrec.snd (primrec_amActData_fam h hT)

/-- The root method, with the two-task body written out. -/
theorem amRootMethods_fam_raw (Mf : ℕ → BitAltMem) (T : ℕ → ℕ) (n : ℕ) :
    amRootMethods (Mf n) (T n) =
      [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * (Mf n).acc.length + 3), (1, true, 4 * Nat.pair (T n) (Mf n).start + 1)] :
          List (ℕ × Bool × ℕ))))] := rfl

/-- The root method, for a varying machine. -/
theorem primrec_amRootMethods_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amRootMethods (Mf n) (T n) := by
  have hacclen : Primrec fun n : ℕ => (Mf n).acc.length := Primrec.list_length.comp h.acc
  have key : Primrec fun n : ℕ =>
      [((0 : ℕ), (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
        ([(0, false, 4 * (Mf n).acc.length + 3),
          (1, true, 4 * Nat.pair (T n) (Mf n).start + 1)] : List (ℕ × Bool × ℕ))))] := by
    have hname : Primrec fun n : ℕ => 4 * Nat.pair (T n) (Mf n).start + 1 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp hT h.start))
        (Primrec.const 1)
    have hinit : Primrec fun n : ℕ => 4 * (Mf n).acc.length + 3 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) hacclen) (Primrec.const 3)
    refine Primrec.list_cons.comp ?_ (Primrec.const [])
    refine Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const [0, 1]) (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hinit))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hname))
        (Primrec.const []))
  exact key.of_eq fun n => (amRootMethods_fam_raw Mf T n).symm

/-- The existential methods, with the two-task bodies written out. -/
theorem amExMethods_fam_raw (Mf : ℕ → BitAltMem) (T : ℕ → ℕ) (n : ℕ) :
    amExMethods (Mf n) (T n) =
      List.flatMap (fun k => (List.range (Mf n).ex.length).map fun i =>
        ((4 * Nat.pair (k + 1) ((Mf n).ex.getI i).src + 1 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, 4 * (i + (Mf n).ex.length * k)), (1, true, 4 * Nat.pair k i + 3)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := rfl

/-- The methods of the existential transitions, for a varying machine. -/
theorem primrec_amExMethods_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amExMethods (Mf n) (T n) := by
  have key : Primrec fun n : ℕ =>
      List.flatMap (fun k => (List.range (Mf n).ex.length).map fun i =>
        ((4 * Nat.pair (k + 1) ((Mf n).ex.getI i).src + 1 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, 4 * (i + (Mf n).ex.length * k)), (1, true, 4 * Nat.pair k i + 3)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hT) ?_
    have hexOut : Primrec fun p : ℕ × ℕ => (Mf p.1).ex := h.ex.comp Primrec.fst
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hexOut)) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have ii : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hex : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).ex := h.ex.comp nn
    have hexlen : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).ex.length :=
      Primrec.list_length.comp hex
    have hget := Primrec.list_getI.comp hex ii
    have hsrc := Primrec.fst.comp hget
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) hsrc))
      (Primrec.const 1)
    have hfwd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * (w.2 + (Mf w.1.1).ex.length * w.1.2) :=
      Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec.nat_add.comp ii (Primrec.nat_mul.comp hexlen kk))
    have hd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * Nat.pair w.1.2 w.2 + 3 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ii))
        (Primrec.const 3)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hfwd))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hd))
        (Primrec.const []))
  exact key.of_eq fun n => (amExMethods_fam_raw Mf T n).symm

/-- The undoing methods, with the two-task bodies written out. -/
theorem amDMethods_fam_raw (Mf : ℕ → BitAltMem) (T : ℕ → ℕ) (n : ℕ) :
    amDMethods (Mf n) (T n) =
      List.flatMap (fun k => (List.range (Mf n).ex.length).map fun i =>
        ((4 * Nat.pair k i + 3 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, true, 4 * Nat.pair k ((Mf n).ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := rfl

/-- The undoing methods, for a varying machine. -/
theorem primrec_amDMethods_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amDMethods (Mf n) (T n) := by
  have key : Primrec fun n : ℕ =>
      List.flatMap (fun k => (List.range (Mf n).ex.length).map fun i =>
        ((4 * Nat.pair k i + 3 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, true, 4 * Nat.pair k ((Mf n).ex.getI i).tgt + 1), (1, false, 4 * i + 1)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hT) ?_
    have hexOut : Primrec fun p : ℕ × ℕ => (Mf p.1).ex := h.ex.comp Primrec.fst
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hexOut)) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have ii : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hex : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).ex := h.ex.comp nn
    have hget := Primrec.list_getI.comp hex ii
    have htgt := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget)))
    have hname : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * Nat.pair w.1.2 w.2 + 3 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ii))
        (Primrec.const 3)
    have hc := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk htgt))
      (Primrec.const 1)
    have hu : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * w.2 + 1 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) ii) (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const false) hu))
        (Primrec.const []))
  exact key.of_eq fun n => (amDMethods_fam_raw Mf T n).symm

/-- The universal methods, with the two-task bodies written out. -/
theorem amUnMethods_fam_raw (Mf : ℕ → BitAltMem) (T : ℕ → ℕ) (n : ℕ) :
    amUnMethods (Mf n) (T n) =
      List.flatMap (fun k => (List.range (Mf n).un.length).map fun j =>
        ((4 * Nat.pair (k + 1) ((Mf n).un.getI j).src + 1 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, 4 * (j + (Mf n).un.length * k) + 2),
              (1, true, 4 * Nat.pair k (Nat.pair ((Mf n).un.getI j).tgt₁
                ((Mf n).un.getI j).tgt₂) + 2)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := rfl

/-- The methods of the universal transitions, for a varying machine. -/
theorem primrec_amUnMethods_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amUnMethods (Mf n) (T n) := by
  have key : Primrec fun n : ℕ =>
      List.flatMap (fun k => (List.range (Mf n).un.length).map fun j =>
        ((4 * Nat.pair (k + 1) ((Mf n).un.getI j).src + 1 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, false, 4 * (j + (Mf n).un.length * k) + 2),
              (1, true, 4 * Nat.pair k (Nat.pair ((Mf n).un.getI j).tgt₁
                ((Mf n).un.getI j).tgt₂) + 2)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hT) ?_
    have hunOut : Primrec fun p : ℕ × ℕ => (Mf p.1).un := h.un.comp Primrec.fst
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hunOut)) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have jj : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hun : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).un := h.un.comp nn
    have hunlen : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).un.length :=
      Primrec.list_length.comp hun
    have hget := Primrec.list_getI.comp hun jj
    have hsrc := Primrec.fst.comp hget
    have hrest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    have ht1 := Primrec.fst.comp hrest
    have ht2 := Primrec.snd.comp hrest
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.nat_add.comp kk (Primrec.const 1)) hsrc))
      (Primrec.const 1)
    have hgrd : Primrec fun w : (ℕ × ℕ) × ℕ => 4 * (w.2 + (Mf w.1.1).un.length * w.1.2) + 2 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec.nat_add.comp jj (Primrec.nat_mul.comp hunlen kk)))
        (Primrec.const 2)
    have hbr := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp ht1 ht2)))
      (Primrec.const 2)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hgrd))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hbr))
        (Primrec.const []))
  exact key.of_eq fun n => (amUnMethods_fam_raw Mf T n).symm

/-- The branching methods, with the two-task bodies written out. -/
theorem amBrMethods_fam_raw (Mf : ℕ → BitAltMem) (T : ℕ → ℕ) (n : ℕ) :
    amBrMethods (Mf n) (T n) =
      List.flatMap (fun k => (List.range (Mf n).un.length).map fun j =>
        ((4 * Nat.pair k (Nat.pair ((Mf n).un.getI j).tgt₁ ((Mf n).un.getI j).tgt₂) + 2 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, true, 4 * Nat.pair k ((Mf n).un.getI j).tgt₁ + 1),
              (1, true, 4 * Nat.pair k ((Mf n).un.getI j).tgt₂ + 1)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := rfl

/-- The branching methods, for a varying machine. -/
theorem primrec_amBrMethods_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Primrec fun n => amBrMethods (Mf n) (T n) := by
  have key : Primrec fun n : ℕ =>
      List.flatMap (fun k => (List.range (Mf n).un.length).map fun j =>
        ((4 * Nat.pair k (Nat.pair ((Mf n).un.getI j).tgt₁ ((Mf n).un.getI j).tgt₂) + 2 : ℕ),
          (([0, 1] : List ℕ), ([(0, 1)] : List (ℕ × ℕ)),
            ([(0, true, 4 * Nat.pair k ((Mf n).un.getI j).tgt₁ + 1),
              (1, true, 4 * Nat.pair k ((Mf n).un.getI j).tgt₂ + 1)] :
              List (ℕ × Bool × ℕ))))) (List.range (T n)) := by
    refine Primrec.list_flatMap (Primrec.list_range.comp hT) ?_
    have hunOut : Primrec fun p : ℕ × ℕ => (Mf p.1).un := h.un.comp Primrec.fst
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp hunOut)) ?_
    have nn : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.1 := Primrec.fst.comp Primrec.fst
    have kk : Primrec fun w : (ℕ × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
    have jj : Primrec fun w : (ℕ × ℕ) × ℕ => w.2 := Primrec.snd
    have hun : Primrec fun w : (ℕ × ℕ) × ℕ => (Mf w.1.1).un := h.un.comp nn
    have hget := Primrec.list_getI.comp hun jj
    have hrest := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hget))
    have ht1 := Primrec.fst.comp hrest
    have ht2 := Primrec.snd.comp hrest
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp kk (Primrec₂.natPair.comp ht1 ht2)))
      (Primrec.const 2)
    have hc1 := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ht1))
      (Primrec.const 1)
    have hc2 := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec₂.natPair.comp kk ht2))
      (Primrec.const 1)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0, 1])
      (Primrec.pair (Primrec.const [(0, 1)]) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const true) hc1))
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const true) hc2))
        (Primrec.const []))
  exact key.of_eq fun n => (amBrMethods_fam_raw Mf T n).symm

/-- The accepting methods, with the bodies written out. -/
theorem amAccMethods_fam_raw (Mf : ℕ → BitAltMem) (n : ℕ) :
    amAccMethods (Mf n) =
      (List.range (Mf n).acc.length).map fun a =>
        ((4 * Nat.pair 0 ((Mf n).acc.getI a).st + 1 : ℕ),
          (([0] : List ℕ), ([] : List (ℕ × ℕ)),
            ([(0, false, 4 * a + 3)] : List (ℕ × Bool × ℕ)))) := rfl

/-- The accepting methods, for a varying machine. -/
theorem primrec_amAccMethods_fam (h : MachFamPrimrec Mf) :
    Primrec fun n => amAccMethods (Mf n) := by
  have key : Primrec fun n : ℕ =>
      (List.range (Mf n).acc.length).map fun a =>
        ((4 * Nat.pair 0 ((Mf n).acc.getI a).st + 1 : ℕ),
          (([0] : List ℕ), ([] : List (ℕ × ℕ)),
            ([(0, false, 4 * a + 3)] : List (ℕ × Bool × ℕ)))) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp h.acc)) ?_
    have nn : Primrec fun w : ℕ × ℕ => w.1 := Primrec.fst
    have aa : Primrec fun w : ℕ × ℕ => w.2 := Primrec.snd
    have hacc : Primrec fun w : ℕ × ℕ => (Mf w.1).acc := h.acc.comp nn
    have hget := Primrec.list_getI.comp hacc aa
    have hst := Primrec.fst.comp hget
    have hname := Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 4)
        (Primrec₂.natPair.comp (Primrec.const 0) hst))
      (Primrec.const 1)
    have hact : Primrec fun w : ℕ × ℕ => 4 * w.2 + 3 :=
      Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) aa) (Primrec.const 3)
    refine Primrec.pair hname (Primrec.pair (Primrec.const [0])
      (Primrec.pair (Primrec.const []) ?_))
    exact Primrec.list_cons.comp
      (Primrec.pair (Primrec.const 0) (Primrec.pair (Primrec.const false) hact))
      (Primrec.const [])
  exact key.of_eq fun n => (amAccMethods_fam_raw Mf n).symm

/-- **The description is computable in the index**, for a machine and a number of steps that
both depend on it. -/
theorem computable_amDom_fam (h : MachFamPrimrec Mf) (hT : Primrec T) :
    Computable fun n => amDom (Mf n) (T n) :=
  (Primrec.pair (primrec_amActions_fam h hT)
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp (primrec_amRootMethods_fam h hT)
              (primrec_amExMethods_fam h hT))
            (primrec_amDMethods_fam h hT))
          (primrec_amUnMethods_fam h hT))
        (primrec_amBrMethods_fam h hT))
      (primrec_amAccMethods_fam h))).to_comp

end Syn

end HTN
