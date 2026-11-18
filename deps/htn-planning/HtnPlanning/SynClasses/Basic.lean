import Mathlib
import ComplexityTheory.TM.Basic
import ComplexityTheory.Complexity.Basic
import HtnPlanning.Basic
import HtnPlanning.Classes.Basic
import HtnPlanning.Computable.ClassesSound
/-!
# The classes of descriptions

**Definitions only.**  The classes of the computable tables (Tables 2–5): a class of
descriptions `HTN.Syn.SynClass 𝒟` is a condition on domain descriptions and a condition on
instance descriptions, together with the proof that every description satisfying both denotes a
problem of the semantic class `𝒟` (these soundness proofs are in
`HtnPlanning/Computable/ClassesSound.lean`).  For every class `C` there is the
unrestricted class `HTN.Syn.SynClass.C` (arbitrary initial task network, subject to the class's
own restriction) and the rooted class `HTN.Syn.SynClass.C_root` (a single initial compound task),
written `C` and `C-1` in the tables.
-/

/-! ## The structure and the unrestricted classes -/

namespace HTN

namespace Syn

open Table

/-- A **class of descriptions**: a condition on domain descriptions and a condition on instance
descriptions which together guarantee that the described problem belongs to the semantic class
family `𝒟`.  Splitting the condition is what allows a compilation to be modular. -/
structure SynClass (𝒟 : Table.Family) where
  /-- The condition on domain descriptions. -/
  domOk : DomDesc → Prop
  /-- The condition on instance descriptions. -/
  instOk : InstDesc → Prop
  /-- Soundness: a description satisfying both conditions denotes a problem of the class. -/
  sound : ∀ d q, domOk d → instOk q → problem d q ∈ 𝒟 ℕ ℕ ℕ ℕ

namespace SynClass

/-- **`HTN`**: no condition. -/
def HTN : SynClass Cls.HTN where
  domOk := fun _ => True
  instOk := fun _ => True
  sound := fun _ _ _ _ => trivial

/-- **`TO-HTN`**. -/
def TO_HTN : SynClass Cls.TO_HTN where
  domOk := DomDesc.MethodsTO
  instOk := InstDesc.IsTO
  sound := fun _ _ hd hq => isTO_problem hd hq

/-- **`HTN-NOOP`**. -/
def HTN_NOOP : SynClass Cls.HTN_NOOP where
  domOk := DomDesc.IsNoop
  instOk := fun _ => True
  sound := fun _ _ hd _ => isNoop_problem hd

/-- **`TO-HTN-NOOP`**. -/
def TO_HTN_NOOP : SynClass Cls.TO_HTN_NOOP where
  domOk := fun d => d.MethodsTO ∧ d.IsNoop
  instOk := InstDesc.IsTO
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq, isNoop_problem hd.2⟩

/-- **`HTN-TR`**. -/
def HTN_TR : SynClass Cls.HTN_TR where
  domOk := DomDesc.IsTailRec
  instOk := fun _ => True
  sound := fun _ _ hd _ => isTailRecursive_problem hd

/-- **`TO-HTN-TR`**. -/
def TO_HTN_TR : SynClass Cls.TO_HTN_TR where
  domOk := fun d => d.MethodsTO ∧ d.IsTailRec
  instOk := InstDesc.IsTO
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq, isTailRecursive_problem hd.2⟩

/-- **`HTN-REG`**: regular methods and a **regular initial task network** (Erol et al.'s
definition; a partially ordered set of primitive tasks followed by at most one compound task). -/
def HTN_REG : SynClass Cls.HTN_REG where
  domOk := DomDesc.MethodsReg
  instOk := InstDesc.IsRegular
  sound := fun _ _ hd hq => isRegular_problem hd hq

/-- **`TO-HTN-REG`**: totally ordered regular methods and a totally ordered regular initial task
network (a sequence of primitive tasks, possibly followed by one compound task). -/
def TO_HTN_REG : SynClass Cls.TO_HTN_REG where
  domOk := fun d => d.MethodsTO ∧ d.MethodsReg
  instOk := fun q => q.IsTO ∧ q.IsRegular
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.1, isRegular_problem hd.2 hq.2⟩

/-- **`HTN-AC`**. -/
def HTN_AC : SynClass Cls.HTN_AC where
  domOk := DomDesc.IsAcyclic
  instOk := fun _ => True
  sound := fun _ _ hd _ => isAcyclic_problem hd

/-- **`TO-HTN-AC`**. -/
def TO_HTN_AC : SynClass Cls.TO_HTN_AC where
  domOk := fun d => d.MethodsTO ∧ d.IsAcyclic
  instOk := InstDesc.IsTO
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq, isAcyclic_problem hd.2⟩

/-- **`STRIPS`**. -/
def STRIPS : SynClass Cls.STRIPS where
  domOk := DomDesc.IsStrips
  instOk := InstDesc.IsStrips
  sound := fun _ _ hd hq => isStripsLike_problem hd hq

end SynClass

end Syn

end HTN

/-! ## Rooted instance descriptions -/

namespace HTN

namespace Syn


namespace SynClass

open Table

/-- **`TO-HTN-REG` with a rooted instance**: the methods are totally ordered and regular, and
the initial task network of the instance is a single compound task. -/
def TO_HTN_REG_root : SynClass Cls.TO_HTN_REG where
  domOk := fun d => d.MethodsTO ∧ d.MethodsReg
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.isTO, isRegular_problem hd.2 hq.isRegular⟩

end SynClass

end Syn

end HTN

/-! ## `HTN-AC-1` -/

namespace HTN

namespace Syn

namespace SynClass

open Table

/-- **`HTN-AC` in the reading of the paper**: an acyclic domain description together with an
instance description whose initial task network is a single compound task. -/
def HTN_AC_root : SynClass Cls.HTN_AC where
  domOk := DomDesc.IsAcyclic
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd _ => isAcyclic_problem hd

end SynClass

end Syn

end HTN

/-! ## `TO-HTN-1` -/

namespace HTN

namespace Syn

open Table

/-- **`TO-HTN` with a rooted instance description**: every listed method is totally ordered and
the initial task network of the instance is a single compound task. -/
def SynClass.TO_HTN_root : SynClass Cls.TO_HTN where
  domOk := DomDesc.MethodsTO
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => isTO_problem hd hq.isTO

end Syn

end HTN

/-! ## `HTN-NOOP-1`, `TO-HTN-NOOP-1`, `HTN-TR-1` -/

namespace HTN

namespace Syn

open Table

namespace SynClass

/-- **`HTN-NOOP` in the paper's reading**: every action is a no-op and the initial task network
of the instance is a single compound task. -/
def HTN_NOOP_root : SynClass Cls.HTN_NOOP where
  domOk := DomDesc.IsNoop
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd _ => isNoop_problem hd

/-- **`TO-HTN-NOOP` in the paper's reading**. -/
def TO_HTN_NOOP_root : SynClass Cls.TO_HTN_NOOP where
  domOk := fun d => d.MethodsTO ∧ d.IsNoop
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.isTO, isNoop_problem hd.2⟩

/-- **`HTN-TR` in the paper's reading**. -/
def HTN_TR_root : SynClass Cls.HTN_TR where
  domOk := DomDesc.IsTailRec
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd _ => isTailRecursive_problem hd

end SynClass

end Syn

end HTN

/-! ## `HTN-1` -/

namespace HTN

namespace Syn

open Table

/-- **`HTN` with a rooted instance**: no condition on the domain, and the initial task network
of the instance is a single compound task. -/
def SynClass.HTN_root : SynClass Cls.HTN where
  domOk := fun _ => True
  instOk := InstDesc.IsRooted
  sound := fun _ _ _ _ => trivial

end Syn

end HTN

/-! ## `HTN-REG-1` -/

namespace HTN

namespace Syn

open Primrec

namespace SynClass

open Table

/-- **`HTN-REG` with a rooted instance**: the methods are regular — but need not be totally
ordered — and the initial task network of the instance is a single compound task. -/
def HTN_REG_root : SynClass Cls.HTN_REG where
  domOk := DomDesc.MethodsReg
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => isRegular_problem hd hq.isRegular

end SynClass

end Syn

end HTN

/-! ## `TO-HTN-TR-1`, `TO-HTN-AC-1` -/

namespace HTN

namespace Syn

namespace SynClass

open Table

/-- **`TO-HTN-TR` with a rooted instance**: the methods are totally ordered, the domain is tail
recursive, and the initial task network of the instance is a single compound task. -/
def TO_HTN_TR_root : SynClass Cls.TO_HTN_TR where
  domOk := fun d => d.MethodsTO ∧ d.IsTailRec
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.isTO, isTailRecursive_problem hd.2⟩

/-- **`TO-HTN-AC` with a rooted instance**. -/
def TO_HTN_AC_root : SynClass Cls.TO_HTN_AC where
  domOk := fun d => d.MethodsTO ∧ d.IsAcyclic
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.isTO, isAcyclic_problem hd.2⟩

end SynClass

end Syn

end HTN
