import HtnComplexity.AcVerify.Paths
import HtnComplexity.AcVerify.Kit
/-!
# The advice and the certificate of the path-witness verifier

* `HTN.Syn.AcVer.recOf d q x` — the **record** of a step: the numerals of its network index, of
  its task identifier, and of its label (`0, a` for the action `a`, `1, c` for the compound task
  `c`);
* the five tables of a domain description, each a list of strings: the records of the method
  steps (`mstepT`), the records of the dummy steps of methods with an empty network (`dummyT`),
  the heads of the methods (`headT`), the ordering of the method networks (`ordT`) and the
  actions with their precondition, add and delete lists (`actT`); the **advice** `advOf d` is the
  concatenation of their serialisations;
* `HTN.Syn.AcVer.encEnt` — the content of an entry of the certificate: the records of the path,
  the state after the entry, the precondition, add and delete lists of its action (all empty for
  an empty leaf), and the flag.
-/

namespace HTN

namespace Syn

namespace AcVer

open PTime TOPlan Compress Classical

/-! ### Records -/

/-- The numerals of a label. -/
def lblSer : ℕ ⊕ ℕ → List Bool
  | Sum.inl a => serNat 0 ++ serNat a
  | Sum.inr c => serNat 1 ++ serNat c

/-- **The record of a step**: network index, task identifier, label. -/
def recOf (d : DomDesc) (q : InstDesc) (x : PStep) : List Bool :=
  serNat x.1 ++ serNat x.2 ++ lblSer (stepLabel d q x)

/-- The record of a step of a method network (independent of the instance). -/
def recM (d : DomDesc) (x : PStep) : List Bool :=
  serNat x.1 ++ serNat x.2 ++ lblSer ((methodAt d x.1).2.label x.2)

theorem recOf_eq_recM {d : DomDesc} {q : InstDesc} {x : PStep} (hx : x.1 ≠ 0) :
    recOf d q x = recM d x := by
  simp [recOf, recM, stepLabel, netOf, hx]

/-! ### The tables -/

/-- The network indices of the methods: `1, …, #methods`. -/
def mIdx (d : DomDesc) : List ℕ := (List.range d.methods.length).map (· + 1)

/-- The records of the method steps. -/
def mstepT (d : DomDesc) : List (List Bool) :=
  (mIdx d).flatMap fun k => (methodAt d k).2.ids.map fun j => recM d (k, j)

/-- The records of the dummy steps `(k, 0)` of the methods with an empty network. -/
def dummyT (d : DomDesc) : List (List Bool) :=
  ((mIdx d).filter fun k => decide ((methodAt d k).2.ids = [])).map fun k => recM d (k, 0)

/-- The heads of the methods. -/
def headT (d : DomDesc) : List (List Bool) :=
  (mIdx d).map fun k => serNat k ++ serNat (methodAt d k).1

/-- The ordering of the method networks. -/
noncomputable def ordT (d : DomDesc) : List (List Bool) :=
  (mIdx d).flatMap fun k =>
    (((methodAt d k).2.ids ×ˢ (methodAt d k).2.ids).filter fun p =>
      decide ((methodAt d k).2.ordOf p.1 p.2)).map fun p => serNat k ++ serNat p.1 ++ serNat p.2

/-- The precondition, add and delete lists of an action, as lists of numerals. -/
def actLists (d : DomDesc) (a : ℕ) : List ℕ × List ℕ × List ℕ :=
  (d.actions.lookup a).elim ([], [], []) fun x => (x.1, x.2.1, x.2.2)

/-- The three lists of an action, serialised. -/
def actSer (d : DomDesc) (a : ℕ) : List Bool :=
  blist ((actLists d a).1.map bitsOfNat) ++ blist ((actLists d a).2.1.map bitsOfNat) ++
    blist ((actLists d a).2.2.map bitsOfNat)

/-- The described actions with their three lists. -/
def actT (d : DomDesc) : List (List Bool) :=
  (d.actions.map (·.1)).map fun a => serNat a ++ actSer d a

/-- **The advice**: the five tables, serialised one after the other. -/
noncomputable def advOf (d : DomDesc) : List Bool :=
  blist (mstepT d) ++ blist (dummyT d) ++ blist (headT d) ++ blist (ordT d) ++ blist (actT d)

/-! ### Reading the advice -/

/-- The table of dummy steps. -/
def tD (a : List Bool) : List Bool := dropBL a
/-- The table of heads. -/
def tH (a : List Bool) : List Bool := dropBL (tD a)
/-- The table of orderings. -/
def tO (a : List Bool) : List Bool := dropBL (tH a)
/-- The table of actions. -/
def tA (a : List Bool) : List Bool := dropBL (tO a)

theorem tD_advOf (d : DomDesc) :
    tD (advOf d) = blist (dummyT d) ++ blist (headT d) ++ blist (ordT d) ++ blist (actT d) := by
  simp only [tD, advOf, List.append_assoc, dropBL_blist]

theorem tH_advOf (d : DomDesc) :
    tH (advOf d) = blist (headT d) ++ blist (ordT d) ++ blist (actT d) := by
  simp only [tH, tD_advOf, List.append_assoc, dropBL_blist]

theorem tO_advOf (d : DomDesc) : tO (advOf d) = blist (ordT d) ++ blist (actT d) := by
  simp only [tO, tH_advOf, List.append_assoc, dropBL_blist]

theorem tA_advOf (d : DomDesc) : tA (advOf d) = blist (actT d) := by
  have h := dropBL_blist (ordT d) (blist (actT d))
  simp only [tA, tO_advOf]
  exact h

/-! ### Entries of the certificate -/

/-- **The content of an entry**: the records of the path, the state after the entry, the three
lists of the action, and the flag. -/
def encEnt (recs st pr ad de : List (List Bool)) (f : Bool) : List Bool :=
  blist recs ++ (blist st ++ (blist pr ++ (blist ad ++ (blist de ++ [f]))))

/-- The part of a content from the state on. -/
def stOf (c : List Bool) : List Bool := dropBL c
/-- The part of a content from the precondition on. -/
def prOf (c : List Bool) : List Bool := dropBL (stOf c)
/-- The part of a content from the add list on. -/
def adOf (c : List Bool) : List Bool := dropBL (prOf c)
/-- The part of a content from the delete list on. -/
def deOf (c : List Bool) : List Bool := dropBL (adOf c)
/-- The part of a content after the delete list (the flag). -/
def fOf (c : List Bool) : List Bool := dropBL (deOf c)
/-- The flag of a content. -/
def flagOf (c : List Bool) : Bool := (fOf c).headD false
/-- The three lists of the action of a content, exactly. -/
def p3Of (c : List Bool) : List Bool := cutS (prOf c) (fOf c)

/-- **The content parses.** -/
def parseB (c : List Bool) : Bool :=
  blOK c && blOK (stOf c) && blOK (prOf c) && blOK (adOf c) && blOK (deOf c) &&
    decide ((fOf c).length = 1)

section
variable (recs st pr ad de : List (List Bool)) (f : Bool)

@[simp] theorem stOf_encEnt :
    stOf (encEnt recs st pr ad de f) = blist st ++ (blist pr ++ (blist ad ++ (blist de ++ [f]))) :=
  dropBL_blist _ _

@[simp] theorem prOf_encEnt :
    prOf (encEnt recs st pr ad de f) = blist pr ++ (blist ad ++ (blist de ++ [f])) := by
  rw [prOf, stOf_encEnt, dropBL_blist]

@[simp] theorem adOf_encEnt : adOf (encEnt recs st pr ad de f) = blist ad ++ (blist de ++ [f]) := by
  rw [adOf, prOf_encEnt, dropBL_blist]

@[simp] theorem deOf_encEnt : deOf (encEnt recs st pr ad de f) = blist de ++ [f] := by
  rw [deOf, adOf_encEnt, dropBL_blist]

@[simp] theorem fOf_encEnt : fOf (encEnt recs st pr ad de f) = [f] := by
  rw [fOf, deOf_encEnt, dropBL_blist]

@[simp] theorem flagOf_encEnt : flagOf (encEnt recs st pr ad de f) = f := by
  simp [flagOf]

@[simp] theorem p3Of_encEnt : p3Of (encEnt recs st pr ad de f) = blist pr ++ blist ad ++ blist de := by
  rw [p3Of, prOf_encEnt, fOf_encEnt]
  simpa [List.append_assoc] using cutS_append (blist pr ++ blist ad ++ blist de) [f]

theorem parseB_encEnt : parseB (encEnt recs st pr ad de f) = true := by
  simp only [parseB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨blOK_blist _ _, ?_⟩, ?_⟩, ?_⟩, ?_⟩, by simp⟩
  · rw [stOf_encEnt]; exact blOK_blist _ _
  · rw [prOf_encEnt]; exact blOK_blist _ _
  · rw [adOf_encEnt]; exact blOK_blist _ _
  · rw [deOf_encEnt]; exact blOK_blist _ _

end

theorem eq_encEnt_of_parseB {c : List Bool} (h : parseB c = true) :
    ∃ recs st pr ad de f, c = encEnt recs st pr ad de f := by
  simp only [parseB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  obtain ⟨recs, e1⟩ := eq_of_blOK h1
  obtain ⟨st, e2⟩ := eq_of_blOK h2
  obtain ⟨pr, e3⟩ := eq_of_blOK h3
  obtain ⟨ad, e4⟩ := eq_of_blOK h4
  obtain ⟨de, e5⟩ := eq_of_blOK h5
  obtain ⟨f, hf⟩ : ∃ f, fOf c = [f] := by
    rcases hc : fOf c with _ | ⟨f, _ | ⟨g, l⟩⟩
    · rw [hc] at h6; simp at h6
    · exact ⟨f, rfl⟩
    · rw [hc] at h6; simp at h6
  refine ⟨recs, st, pr, ad, de, f, ?_⟩
  have e5' : deOf c = blist de ++ fOf c := e5
  have e4' : adOf c = blist ad ++ deOf c := e4
  have e3' : prOf c = blist pr ++ adOf c := e3
  have e2' : stOf c = blist st ++ prOf c := e2
  have e1' : c = blist recs ++ stOf c := e1
  calc c = blist recs ++ stOf c := e1'
    _ = encEnt recs st pr ad de f := by rw [e2', e3', e4', e5', hf]; rfl

end AcVer

end Syn

end HTN
