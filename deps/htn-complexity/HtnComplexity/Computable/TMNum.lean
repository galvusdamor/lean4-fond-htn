import HtnComplexity.Guard.TMFamily
/-!
# Numbering the signature of the Turing-machine encoding

The encoding of Theorem 4.3.7 (`HtnComplexity/TMEnc/TMEncoding.lean`) and its family form
(`HtnComplexity/Guard/TMFamily.lean`) live over the abstract signature

* `HTN.TMEnc.Fam.GFact Q Γ` — facts (input facts and the facts of the encoding),
* `HTN.TMEnc.Fam.GAct Q Γ` — action names (guards and the actions of the encoding),
* `HTN.TMEnc.TMTask Q Γ` — compound task names,
* `ℕ × ℕ` — task identifiers,

where `Q` is the state set and `Γ` the tape alphabet of the machine.  A *description*
(`HtnPlanning/Computable/Syntax.lean`) uses `ℕ` for all four components, and the bridge
`HTN.Syn.Rendering` (`HtnComplexity/Computable/Render.lean`) asks for injective numberings
`eF`, `eA`, `eC` of the first three.  This file supplies them, which is the first of the five
items that §51.3 of `NOTES.md` lists for the syntactic half of the source side.

Given injections `q : Q → ℕ` and `g : Γ → ℕ` the file defines

* `HTN.TMEnc.encTMFact q g`, `HTN.TMEnc.encTMAct q g`, `HTN.TMEnc.encTMTask` on the signature of
  the plain encoding, and
* `HTN.TMEnc.Fam.encGFact q g`, `HTN.TMEnc.Fam.encGAct q g` on the enlarged one,

and proves all of them injective.  The pattern is the one of
`HtnComplexity/Computable/AcEnc.lean`: each constructor gets a tag, the residue modulo the
number of constructors, and its arguments are packed — linearly where they are bounded, with
`Nat.pair` where they are not.  The numbering of the compound task names is recursive, since
`cSeq` and `cPar` carry a task name; unlike the other two it needs nothing of `Q` and `Γ`
beyond the numbering of the alphabet, and unlike `AcEnc.encTask` it is genuinely recursive in a
type with nineteen further constructors.
-/

namespace HTN

namespace TMEnc

open TM

variable {Q Γ : Type}

/-! ### Auxiliary numberings -/

/-- The three synchronisation channels, numbered. -/
def encSync : SyncKind → ℕ
  | SyncKind.head => 0
  | SyncKind.check => 1
  | SyncKind.sync => 2

theorem encSync_injective : Function.Injective encSync := by
  intro x y h
  cases x <;> cases y <;> simp_all [encSync]

/-- A tape symbol — `none` being the separator `#` — numbered. -/
def encSym (g : Γ → ℕ) : Option Γ → ℕ
  | none => 0
  | some c => g c + 1

theorem encSym_injective {g : Γ → ℕ} (hg : Function.Injective g) :
    Function.Injective (encSym g) := by
  rintro (_ | x) (_ | y) h <;> simp only [encSym] at h
  · rfl
  · omega
  · omega
  · exact congrArg some (hg (by omega))

private lemma pair_inj {x y z w : ℕ} (h : Nat.pair x y = Nat.pair z w) : x = z ∧ y = w := by
  have h1 := congrArg Nat.unpair h
  simpa using h1

/-! ### The facts of the encoding -/

/-- **The facts of the encoding, numbered.** -/
def encTMFact (q : Q → ℕ) (g : Γ → ℕ) : TMFact Q Γ → ℕ
  | TMFact.sym c => 6 * encSym g c
  | TMFact.st s => 6 * q s + 1
  | TMFact.head => 2
  | TMFact.noHead => 3
  | TMFact.stepF x => 6 * encSync x + 4
  | TMFact.steppedF x => 6 * encSync x + 5

variable {q : Q → ℕ} {g : Γ → ℕ}

theorem encTMFact_injective (hq : Function.Injective q) (hg : Function.Injective g) :
    Function.Injective (encTMFact q g) := by
  intro x y h
  cases x <;> cases y <;> simp only [encTMFact] at h <;>
    first
      | omega
      | rfl
      | (congr 1;
          first
            | omega
            | (refine hq ?_; omega)
            | (refine encSym_injective hg ?_; omega)
            | (refine encSync_injective ?_; omega))

/-! ### The actions of the encoding -/

/-- **The actions of the encoding, numbered.** -/
def encTMAct (q : Q → ℕ) (g : Γ → ℕ) : TMAct Q Γ → ℕ
  | TMAct.assert c => 9 * encSym g c
  | TMAct.check f => 9 * encTMFact q g f + 1
  | TMAct.call x => 9 * encSync x + 2
  | TMAct.start x => 9 * encSync x + 3
  | TMAct.respond x => 9 * encSync x + 4
  | TMAct.wait x => 9 * encSync x + 5
  | TMAct.assertHead => 6
  | TMAct.retractHead => 7
  | TMAct.step s c s' c' =>
      9 * Nat.pair (Nat.pair (q s) (encSym g c)) (Nat.pair (q s') (encSym g c')) + 8

theorem encTMAct_injective (hq : Function.Injective q) (hg : Function.Injective g) :
    Function.Injective (encTMAct q g) := by
  intro x y h
  cases x <;> cases y <;> simp only [encTMAct] at h <;> try omega
  · exact congrArg _ (encSym_injective hg (by omega))
  · exact congrArg _ (encTMFact_injective hq hg (by omega))
  · exact congrArg _ (encSync_injective (by omega))
  · exact congrArg _ (encSync_injective (by omega))
  · exact congrArg _ (encSync_injective (by omega))
  · exact congrArg _ (encSync_injective (by omega))
  · rfl
  · rfl
  · rename_i s c s' c' s₂ c₂ s₂' c₂'
    obtain ⟨h1, h2⟩ :=
      pair_inj (show Nat.pair (Nat.pair (q s) (encSym g c)) (Nat.pair (q s') (encSym g c'))
        = Nat.pair (Nat.pair (q s₂) (encSym g c₂)) (Nat.pair (q s₂') (encSym g c₂')) by omega)
    obtain ⟨h3, h4⟩ := pair_inj h1
    obtain ⟨h5, h6⟩ := pair_inj h2
    rw [hq h3, encSym_injective hg h4, hq h5, encSym_injective hg h6]

/-! ### The compound task names of the encoding -/

/-- **The compound task names of the encoding, numbered.**  The type has twenty constructors,
two of which — `cSeq` and `cPar` — are recursive. -/
def encTMTask (g : Γ → ℕ) : TMTask Q Γ → ℕ
  | TMTask.acquire x => 20 * encSync x
  | TMTask.release x => 20 * encSync x + 1
  | TMTask.produce => 2
  | TMTask.produceSym c => 20 * encSym g c + 3
  | TMTask.tapeProduce => 4
  | TMTask.waitCell => 5
  | TMTask.waitN i => 20 * i + 6
  | TMTask.chk => 7
  | TMTask.headCell => 8
  | TMTask.noHeadCell => 9
  | TMTask.heads => 10
  | TMTask.transition => 11
  | TMTask.transitionAndCheck => 12
  | TMTask.checkers i => 20 * i + 13
  | TMTask.produceInit => 14
  | TMTask.produceWord i => 20 * i + 15
  | TMTask.done => 16
  | TMTask.cSeq t k => 20 * Nat.pair (encTMTask g t) k + 17
  | TMTask.cPar t k => 20 * Nat.pair (encTMTask g t) k + 18
  | TMTask.sI => 19

theorem encTMTask_injective (hg : Function.Injective g) :
    Function.Injective (encTMTask (Q := Q) g) := by
  intro x
  induction x with
  | acquire x =>
    intro y h; cases y <;> simp only [encTMTask] at h <;>
      first | omega | exact congrArg _ (encSync_injective (by omega))
  | release x =>
    intro y h; cases y <;> simp only [encTMTask] at h <;>
      first | omega | exact congrArg _ (encSync_injective (by omega))
  | produce => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | produceSym c =>
    intro y h; cases y <;> simp only [encTMTask] at h <;>
      first | omega | exact congrArg _ (encSym_injective hg (by omega))
  | tapeProduce => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | waitCell => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | waitN i =>
    intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | (congr 1; omega)
  | chk => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | headCell => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | noHeadCell => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | heads => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | transition => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | transitionAndCheck =>
    intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | checkers i =>
    intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | (congr 1; omega)
  | produceInit => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | produceWord i =>
    intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | (congr 1; omega)
  | done => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl
  | cSeq t k ih =>
    intro y h
    cases y <;> simp only [encTMTask] at h <;> try omega
    rename_i t' k'
    obtain ⟨h1, h2⟩ :=
      pair_inj (show Nat.pair (encTMTask g t) k = Nat.pair (encTMTask g t') k' by omega)
    rw [ih h1, h2]
  | cPar t k ih =>
    intro y h
    cases y <;> simp only [encTMTask] at h <;> try omega
    rename_i t' k'
    obtain ⟨h1, h2⟩ :=
      pair_inj (show Nat.pair (encTMTask g t) k = Nat.pair (encTMTask g t') k' by omega)
    rw [ih h1, h2]
  | sI => intro y h; cases y <;> simp only [encTMTask] at h <;> first | omega | rfl

namespace Fam

/-! ### The enlarged signature of the family construction -/

/-- **The facts of the family construction, numbered**: the input facts on the even numbers, the
facts of the encoding on the odd ones. -/
def encGFact (q : Q → ℕ) (g : Γ → ℕ) : GFact Q Γ → ℕ
  | Sum.inl p => 2 * Nat.pair p.1 (g p.2)
  | Sum.inr f => 2 * encTMFact q g f + 1

theorem encGFact_injective (hq : Function.Injective q) (hg : Function.Injective g) :
    Function.Injective (encGFact q g) := by
  rintro (⟨i, c⟩ | f) (⟨j, d⟩ | f') h <;> simp only [encGFact] at h
  · obtain ⟨h1, h2⟩ := pair_inj (show Nat.pair i (g c) = Nat.pair j (g d) by omega)
    rw [h1, hg h2]
  · omega
  · omega
  · exact congrArg _ (encTMFact_injective hq hg (by omega))

/-- **The actions of the family construction, numbered**: the guards on the even numbers, the
actions of the encoding on the odd ones. -/
def encGAct (q : Q → ℕ) (g : Γ → ℕ) : GAct Q Γ → ℕ
  | Sum.inl none => 0
  | Sum.inl (some p) => 2 * (Nat.pair p.1 (g p.2) + 1)
  | Sum.inr a => 2 * encTMAct q g a + 1

theorem encGAct_injective (hq : Function.Injective q) (hg : Function.Injective g) :
    Function.Injective (encGAct q g) := by
  rintro ((_ | ⟨i, c⟩) | a) ((_ | ⟨j, d⟩) | a') h <;> simp only [encGAct] at h
  · rfl
  · omega
  · omega
  · omega
  · obtain ⟨h1, h2⟩ := pair_inj (show Nat.pair i (g c) = Nat.pair j (g d) by omega)
    rw [h1, hg h2]
  · omega
  · omega
  · omega
  · exact congrArg _ (encTMAct_injective hq hg (by omega))

end Fam

end TMEnc

end HTN
