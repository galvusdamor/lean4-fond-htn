import HtnPlanning.Computable.Classes
import HtnComplexity.Complexity.FamilyDecide
import ComplexityTheory.Complexity.Blocks
import HtnComplexity.Computable.Guard
import HtnComplexity.Computable.AcDecideCell
import ComplexityTheory.Complexity.PolyTimeTM
/-!
# A polynomial-time hardness family, written down

The Karp–Lipton bundle of `HtnCompilability/Complexity/CodedKarpLipton.lean` has three
fields, the first of which is the existence of a **polynomial-time hardness family** for the
language in the source class.  Nothing so far showed that field to be satisfiable at all: a
family is a domain description per input length together with an instance description per word,
produced in polynomial time, and exhibiting one means exhibiting a function of Cobham's class
that writes a description down.  Were the field unsatisfiable, every bundle would hold
vacuously and the cells derived from them would say nothing.

This file removes that doubt by constructing one:

* `HTN.Syn.guardEnc w` — the guard instance (`HtnComplexity/Computable/Guard.lean`) whose
  initial state lists the bits of `w`, in order, as the facts `0` and `1`;
* `HTN.Syn.polyTimeCode_guardEnc` — its serialisation is the word with every bit replaced by a
  fixed block, followed by a fixed string, hence a function of Cobham's class
  (`HTN.PTime.polyTimeFun_blockMap`).  This is the step that the Gödel coding makes impossible
  in practice, and the reason `HtnComplexity/Complexity/Serial.lean` exists;
* `HTN.Syn.guardFamily` — the family itself, for the language `HTN.Syn.LSomeTrue` of words with
  at least one `true` bit, in the class `TO-HTN-AC`: the domain description is the constant
  guard domain with the single guard `1`, so a guarded action is applicable exactly when the
  word has a `true` bit;
* `HTN.Syn.Coded.nonempty_hardFamilyPT_*` — the family transported along the class inclusions
  into the three source classes of the eight open cells, `TO-HTN`, `HTN-TR` and `HTN-AC`.

The language is decidable, as it must be: `HTN.Syn.Coded.computablePred_of_hardFamilyPT` shows
that a class with a decision procedure admits polynomial-time hardness families only for
decidable languages.  What the family establishes is that the *shape* required by the bundle is
inhabited — the hardness families of the literature differ from this one in the language they
encode, not in their form.
-/

namespace HTN

namespace Syn

open PTime

/-! ### The encoding of a word -/

/-- The facts coding a word: its bits in order, `true` as the fact `1` and `false` as the fact
`0`.  As a *description* this is injective — the initial state of a description is a list, and
the list remembers the order — even though the state it denotes is a set. -/
def bitFacts (w : List Bool) : List ℕ := w.map fun b => if b then 1 else 0

theorem bitFacts_injective : Function.Injective bitFacts := by
  intro w w' h
  refine List.map_injective_iff.2 (fun b b' hb => ?_) h
  cases b <;> cases b' <;> simp at hb ⊢

theorem mem_bitFacts_iff {w : List Bool} : (1 : ℕ) ∈ bitFacts w ↔ true ∈ w := by
  constructor
  · intro h
    obtain ⟨b, hb, hb1⟩ := List.mem_map.1 h
    cases b
    · simp at hb1
    · exact hb
  · intro h
    exact List.mem_map.2 ⟨true, h, rfl⟩

/-- **The instance description coding a word**: the guard instance whose initial state lists the
bits of the word. -/
def guardEnc (w : List Bool) : InstDesc := guardInst (bitFacts w)

theorem guardEnc_injective : Function.Injective guardEnc := by
  intro w w' h
  exact bitFacts_injective (congrArg InstDesc.initList h)

/-- The language the family encodes: the words with at least one `true` bit. -/
def LSomeTrue (w : List Bool) : Prop := true ∈ w

/-! ### The serialisation of the encoding is a block code -/

/-- The block of bits that serialises the fact `1`. -/
def blockTrue : List Bool := [true, true, true, false]

/-- The block of bits that serialises the fact `0`. -/
def blockFalse : List Bool := [true, false]

/-- The fixed tail of the serialisation: the end of the initial-state list, the empty goal, and
the initial task network of a guard instance. -/
def guardTail : List Bool :=
  [false] ++ serNatList [] ++ tnSer (([0], [], [(0, true, 0)]) : TnDesc)

theorem instSer_guardEnc (w : List Bool) :
    instSer (guardEnc w) = (w.flatMap fun b => bif b then blockTrue else blockFalse) ++
      guardTail := by
  have hmap : ∀ v : List Bool,
      (bitFacts v).map bitsOfNat = v.map fun b => bitsOfNat (if b then 1 else 0) := by
    intro v
    simp [bitFacts, List.map_map, Function.comp_def]
  have hlist : ∀ v : List Bool,
      blist (v.map fun b => bitsOfNat (if b then 1 else 0)) =
        (v.flatMap fun b => bif b then blockTrue else blockFalse) ++ [false] := by
    intro v
    induction v with
    | nil => simp
    | cons b v ih =>
      cases b <;>
        simp [blist_cons, ih, blockTrue, blockFalse, bitsOfNat_one, List.flatMap_cons]
  rw [guardEnc, instSer, guardTail]
  simp only [guardInst_initList, guardInst_goalList, guardInst_tnI, serNatList, hmap, hlist,
    List.append_assoc]

/-- **The encoding runs in polynomial time**: its serialisation replaces every bit of the word
by a fixed block and appends a fixed string, and such a function belongs to Cobham's class. -/
theorem polyTimeCode_guardEnc : PolyTimeCode codingSer guardEnc :=
  ⟨fun w => (w.flatMap fun b => bif b then blockTrue else blockFalse) ++ guardTail,
    polyTimeFun_blockMap blockTrue blockFalse guardTail,
    fun w => by rw [codingSer_code, instSer_guardEnc]⟩

/-- The serialisation of the encoding is short: linear in the length of the word.  (The Gödel
code of the same description is exponentially longer — this is why the serialisation is the
coding with respect to which "polynomial time" is the intended notion.) -/
theorem length_instSer_guardEnc_le (w : List Bool) :
    (instSer (guardEnc w)).length ≤ 4 * w.length + guardTail.length := by
  rw [instSer_guardEnc, List.length_append]
  have hflat : ∀ v : List Bool,
      (v.flatMap fun b => bif b then blockTrue else blockFalse).length ≤ 4 * v.length := by
    intro v
    induction v with
    | nil => simp
    | cons b v ih =>
      have hb : ((bif b then blockTrue else blockFalse) : List Bool).length ≤ 4 := by
        cases b <;> simp [blockTrue, blockFalse]
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      omega
  have := hflat w
  omega

/-! ### The family -/

/-- The domain description of the family: the guard domain with the single guard `1`, the same
for every input length. -/
def guardDomOne : DomDesc := guardDom [[1]]

theorem solvable_guardDomOne_iff (w : List Bool) :
    Solvable guardDomOne (guardEnc w) ↔ LSomeTrue w := by
  rw [guardDomOne, guardEnc, solvable_guard_iff']
  constructor
  · rintro ⟨p, hp, hsub⟩
    have hp1 : p = [1] := by simpa using hp
    exact mem_bitFacts_iff.1 (hsub 1 (by rw [hp1]; simp))
  · intro h
    exact ⟨[1], by simp, by
      intro f hf
      have : f = 1 := by simpa using hf
      rw [this]
      exact mem_bitFacts_iff.2 h⟩

theorem size_guardDomOne : guardDomOne.size = 5 := by
  simp [guardDomOne, guardDom, DomDesc.size, DomDesc.actions, DomDesc.methods,
    ActionDesc.size, MethodDesc.size, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

theorem size_guardEnc (w : List Bool) : (guardEnc w).size = w.length + 2 := by
  simp [guardEnc, guardInst, InstDesc.size, InstDesc.initList, InstDesc.goalList, InstDesc.tnI,
    bitFacts, TnDesc.size, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]

/-- **A polynomial-time hardness family in `TO-HTN-AC` for the language of words with a `true`
bit.**  This inhabits the first field of the Karp–Lipton bundle. -/
noncomputable def guardFamily :
    Coded.HardFamilyPT codingSer SynClass.TO_HTN_AC_root LSomeTrue where
  dom := fun _ => guardDomOne
  inst := guardEnc
  bound := Polynomial.X + Polynomial.C 5
  dom_size := fun n => by simp [size_guardDomOne]
  inst_size := fun w => by simp [size_guardEnc]
  dom_ok := fun _ => domOk_guardDom_TO_HTN_AC_root
  inst_ok := fun _ => instOk_guardInst_TO_HTN_AC_root
  inst_injective := guardEnc_injective
  correct := solvable_guardDomOne_iff
  dom_computable := Computable.const _
  inst_polyTime := polyTimeCode_guardEnc

namespace Coded

/-- **The hardness field of the bundle is satisfiable in `TO-HTN-AC`.** -/
theorem nonempty_hardFamilyPT_TO_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_AC_root LSomeTrue) := ⟨guardFamily⟩

/-- … and in `TO-HTN`, the source class of two of the eight open cells. -/
theorem nonempty_hardFamilyPT_TO_HTN :
    Nonempty (HardFamilyPT codingSer SynClass.TO_HTN_root LSomeTrue) :=
  ⟨guardFamily.mono (S' := SynClass.TO_HTN_root) ⟨fun _ hd => hd.1, fun _ hq => hq⟩⟩

/-- … and in `HTN-TR`, the source class of two more. -/
theorem nonempty_hardFamilyPT_HTN_TR :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_TR_root LSomeTrue) :=
  ⟨guardFamily.mono (S' := SynClass.HTN_TR_root)
    ⟨fun _ hd => SynClass.isAcyclic_isTailRec hd.2, fun _ hq => hq⟩⟩

/-- … and in `HTN-AC`, the source class of the remaining four. -/
theorem nonempty_hardFamilyPT_HTN_AC :
    Nonempty (HardFamilyPT codingSer SynClass.HTN_AC_root LSomeTrue) :=
  ⟨guardFamily.mono (S' := SynClass.HTN_AC_root) ⟨fun _ hd => hd.2, fun _ hq => hq⟩⟩

/-- The language of the family is decidable, as every language with a polynomial-time hardness
family in a class with a decision procedure must be. -/
theorem computablePred_LSomeTrue : ComputablePred LSomeTrue :=
  computablePred_of_hardFamilyPT
    (SynClass.Decider.of_sub (S := SynClass.TO_HTN_AC_root) ⟨fun _ hd => hd.2, fun _ _ => trivial⟩
      decider_HTN_AC) guardFamily

end Coded

end Syn

end HTN
