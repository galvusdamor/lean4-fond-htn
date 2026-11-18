import HtnPlanning.Classes.UOHD
import HtnComplexity.Computable.Rooted
/-!
# `UO-HTN`, `1-HD-HTN` and their sub-types as classes of descriptions

The classes of descriptions (`HTN.Syn.SynClass`) for the two restrictions of
`HtnPlanning/Classes/UOHD.lean`, each in the two readings of the tables of the project:

| class | domain condition | instance condition |
| --- | --- | --- |
| `UO-HTN` (`SynClass.UO_HTN`) | every listed method is unordered | the initial network is unordered |
| `UO-HTN-1` (`SynClass.UO_HTN_root`) | every listed method is unordered | a single compound task |
| `1-HD-HTN` (`SynClass.HD1_HTN`) | every listed method has ≤ 1 compound task | the initial network has ≤ 1 compound task |
| `1-HD-HTN-1` (`SynClass.HD1_HTN_root`) | every listed method has ≤ 1 compound task | a single compound task |

together with the two natural sub-types (again unrooted and rooted)

* `TO-1-HD-HTN` (`SynClass.TO_HD1_HTN`, `SynClass.TO_HD1_HTN_root`) — totally ordered and
  one-hole-digging; it contains `TO-HTN-REG` and `STRIPS`;
* `UO-1-HD-HTN` (`SynClass.UO_HD1_HTN`, `SynClass.UO_HD1_HTN_root`) — unordered and
  one-hole-digging, the common sub-type of the two new classes.

As for every other class of the project, the conditions are imposed on *all listed* methods
(which is what makes them conditions on the domain description alone), and the soundness proofs
(`isUO_problem`, `isHD1_problem`) connect them with the semantic classes.

The second half of the file proves the inclusions (`HTN.Syn.SynSub`) between the new classes and
between them and the classes already in the tables.
-/

namespace HTN

namespace Syn

/-! ### The conditions on descriptions -/

namespace DomDesc

/-- **`UO-M` for descriptions**: every listed method has an unordered subtask network. -/
def MethodsUO (d : DomDesc) : Prop := ∀ e ∈ d.methods, e.2.toTaskNetwork.IsUnordered

/-- **`1-HD` for domain descriptions**: every listed method has at most one compound task. -/
def MethodsHD1 (d : DomDesc) : Prop := ∀ e ∈ d.methods, e.2.toTaskNetwork.IsOneHole

/-- A regular domain description is one-hole-digging. -/
theorem MethodsReg.methodsHD1 {d : DomDesc} (h : d.MethodsReg) : d.MethodsHD1 :=
  fun e he => (h e he).isOneHole

end DomDesc

namespace InstDesc

/-- **`UO-tn_I` for descriptions**: the initial task network is unordered. -/
def IsUO (q : InstDesc) : Prop := q.tnI.toTaskNetwork.IsUnordered

/-- **`1-HD` for instance descriptions**: the initial task network has at most one compound
task. -/
def IsHD1 (q : InstDesc) : Prop := q.tnI.toTaskNetwork.IsOneHole

/-- A rooted instance description is unordered (a single task is never ordered with itself,
since a described ordering is irreflexive). -/
theorem IsRooted.isUO {q : InstDesc} (h : q.IsRooted) : q.IsUO := by
  obtain ⟨t, c, hT, -⟩ := h
  intro x hx y hy
  rw [hT, Finset.mem_singleton] at hx hy
  rw [hx, hy]
  exact q.tnI.toTaskNetwork_wf.irrefl t

/-- A rooted instance description is one-hole. -/
theorem IsRooted.isHD1 {q : InstDesc} (h : q.IsRooted) : q.IsHD1 :=
  h.isRegular.isOneHole

end InstDesc

/-! ### Soundness -/

section Sound

variable {d : DomDesc} {q : InstDesc}

/-- **`MethodsUO` and `IsUO` are sound**: they describe an unordered problem. -/
theorem isUO_problem (hd : d.MethodsUO) (hq : q.IsUO) : (problem d q).IsUO := by
  refine ⟨hq, ?_⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

/-- **`MethodsHD1` and `IsHD1` are sound**: they describe a one-hole-digging problem. -/
theorem isHD1_problem (hd : d.MethodsHD1) (hq : q.IsHD1) : (problem d q).IsHD1 := by
  refine ⟨hq, ?_⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

end Sound

/-! ### The classes -/

namespace SynClass

open Table

/-- **`UO-HTN`**: unordered methods and an unordered initial task network. -/
def UO_HTN : SynClass Cls.UO_HTN where
  domOk := DomDesc.MethodsUO
  instOk := InstDesc.IsUO
  sound := fun _ _ hd hq => isUO_problem hd hq

/-- **`UO-HTN-1`**: unordered methods and a single initial compound task. -/
def UO_HTN_root : SynClass Cls.UO_HTN where
  domOk := DomDesc.MethodsUO
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => isUO_problem hd hq.isUO

/-- **`1-HD-HTN`**: every method and the initial task network have at most one compound task. -/
def HD1_HTN : SynClass Cls.HD1_HTN where
  domOk := DomDesc.MethodsHD1
  instOk := InstDesc.IsHD1
  sound := fun _ _ hd hq => isHD1_problem hd hq

/-- **`1-HD-HTN-1`**: every method has at most one compound task, and the initial task network
is a single compound task. -/
def HD1_HTN_root : SynClass Cls.HD1_HTN where
  domOk := DomDesc.MethodsHD1
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => isHD1_problem hd hq.isHD1

/-- **`TO-1-HD-HTN`** (sub-type): totally ordered and one-hole-digging. -/
def TO_HD1_HTN : SynClass Cls.TO_HD1_HTN where
  domOk := fun d => d.MethodsTO ∧ d.MethodsHD1
  instOk := fun q => q.IsTO ∧ q.IsHD1
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.1, isHD1_problem hd.2 hq.2⟩

/-- **`TO-1-HD-HTN-1`** (sub-type): totally ordered one-hole-digging methods and a single
initial compound task. -/
def TO_HD1_HTN_root : SynClass Cls.TO_HD1_HTN where
  domOk := fun d => d.MethodsTO ∧ d.MethodsHD1
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isTO_problem hd.1 hq.isTO, isHD1_problem hd.2 hq.isHD1⟩

/-- **`UO-1-HD-HTN`** (sub-type): unordered and one-hole-digging. -/
def UO_HD1_HTN : SynClass Cls.UO_HD1_HTN where
  domOk := fun d => d.MethodsUO ∧ d.MethodsHD1
  instOk := fun q => q.IsUO ∧ q.IsHD1
  sound := fun _ _ hd hq => ⟨isUO_problem hd.1 hq.1, isHD1_problem hd.2 hq.2⟩

/-- **`UO-1-HD-HTN-1`** (sub-type): unordered one-hole-digging methods and a single initial
compound task. -/
def UO_HD1_HTN_root : SynClass Cls.UO_HD1_HTN where
  domOk := fun d => d.MethodsUO ∧ d.MethodsHD1
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => ⟨isUO_problem hd.1 hq.isUO, isHD1_problem hd.2 hq.isHD1⟩

/-! ### Inclusions: rooted ⊆ unrooted -/

theorem sub_UO_HTN_root_UO_HTN : SynSub UO_HTN_root UO_HTN :=
  ⟨fun _ hd => hd, fun _ hq => hq.isUO⟩

theorem sub_HD1_HTN_root_HD1_HTN : SynSub HD1_HTN_root HD1_HTN :=
  ⟨fun _ hd => hd, fun _ hq => hq.isHD1⟩

theorem sub_TO_HD1_HTN_root_TO_HD1_HTN : SynSub TO_HD1_HTN_root TO_HD1_HTN :=
  ⟨fun _ hd => hd, fun _ hq => ⟨hq.isTO, hq.isHD1⟩⟩

theorem sub_UO_HD1_HTN_root_UO_HD1_HTN : SynSub UO_HD1_HTN_root UO_HD1_HTN :=
  ⟨fun _ hd => hd, fun _ hq => ⟨hq.isUO, hq.isHD1⟩⟩

/-! ### Inclusions into `HTN-1` -/

theorem sub_UO_HTN_root_HTN_root : SynSub UO_HTN_root HTN_root :=
  ⟨fun _ _ => trivial, fun _ hq => hq⟩

theorem sub_HD1_HTN_root_HTN_root : SynSub HD1_HTN_root HTN_root :=
  ⟨fun _ _ => trivial, fun _ hq => hq⟩

/-! ### Inclusions of the sub-types -/

theorem sub_TO_HD1_HTN_HD1_HTN : SynSub TO_HD1_HTN HD1_HTN :=
  ⟨fun _ hd => hd.2, fun _ hq => hq.2⟩

theorem sub_TO_HD1_HTN_TO_HTN : SynSub TO_HD1_HTN TO_HTN :=
  ⟨fun _ hd => hd.1, fun _ hq => hq.1⟩

theorem sub_TO_HD1_HTN_root_HD1_HTN_root : SynSub TO_HD1_HTN_root HD1_HTN_root :=
  ⟨fun _ hd => hd.2, fun _ hq => hq⟩

theorem sub_TO_HD1_HTN_root_TO_HTN_root : SynSub TO_HD1_HTN_root TO_HTN_root :=
  ⟨fun _ hd => hd.1, fun _ hq => hq⟩

theorem sub_TO_HD1_HTN_root_TO_HTN : SynSub TO_HD1_HTN_root TO_HTN :=
  ⟨fun _ hd => hd.1, fun _ hq => hq.isTO⟩

theorem sub_UO_HD1_HTN_UO_HTN : SynSub UO_HD1_HTN UO_HTN :=
  ⟨fun _ hd => hd.1, fun _ hq => hq.1⟩

theorem sub_UO_HD1_HTN_HD1_HTN : SynSub UO_HD1_HTN HD1_HTN :=
  ⟨fun _ hd => hd.2, fun _ hq => hq.2⟩

theorem sub_UO_HD1_HTN_root_UO_HTN_root : SynSub UO_HD1_HTN_root UO_HTN_root :=
  ⟨fun _ hd => hd.1, fun _ hq => hq⟩

theorem sub_UO_HD1_HTN_root_HD1_HTN_root : SynSub UO_HD1_HTN_root HD1_HTN_root :=
  ⟨fun _ hd => hd.2, fun _ hq => hq⟩

/-! ### Inclusions of the regular classes and of `STRIPS` into `1-HD` -/

theorem sub_HTN_REG_HD1_HTN : SynSub HTN_REG HD1_HTN :=
  ⟨fun _ hd => hd.methodsHD1, fun _ hq => TaskNetwork.IsRegular.isOneHole hq⟩

theorem sub_TO_HTN_REG_TO_HD1_HTN : SynSub TO_HTN_REG TO_HD1_HTN :=
  ⟨fun _ hd => ⟨hd.1, hd.2.methodsHD1⟩, fun _ hq => ⟨hq.1, TaskNetwork.IsRegular.isOneHole hq.2⟩⟩

theorem sub_HTN_REG_root_HD1_HTN_root : SynSub HTN_REG_root HD1_HTN_root :=
  ⟨fun _ hd => DomDesc.MethodsReg.methodsHD1 hd, fun _ hq => hq⟩

theorem sub_TO_HTN_REG_root_TO_HD1_HTN_root : SynSub TO_HTN_REG_root TO_HD1_HTN_root :=
  ⟨fun _ hd => ⟨hd.1, hd.2.methodsHD1⟩, fun _ hq => hq⟩

/-- **`STRIPS ⊆ TO-1-HD-HTN-1`**: a described `STRIPS` problem is a rooted, totally ordered,
one-hole-digging problem. -/
theorem sub_STRIPS_TO_HD1_HTN_root : SynSub STRIPS TO_HD1_HTN_root :=
  sub_STRIPS_TO_HTN_REG_root.trans sub_TO_HTN_REG_root_TO_HD1_HTN_root

end SynClass

end Syn

end HTN
