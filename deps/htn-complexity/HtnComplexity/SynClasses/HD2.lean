import HtnPlanning.Classes.HD2
import HtnComplexity.SynClasses.UOHD
/-!
# `2-HD-HTN` as a class of descriptions

The classes of descriptions (`HTN.Syn.SynClass`) for the restriction of
`HtnPlanning/Classes/HD2.lean`, in the two readings of the tables of the project:

| class | domain condition | instance condition |
| --- | --- | --- |
| `2-HD-HTN` (`SynClass.HD2_HTN`) | every listed method has ≤ 1 compound task | the initial network has ≤ 2 compound tasks |
| `2-HD-HTN-1` (`SynClass.HD2_HTN_root`) | every listed method has ≤ 1 compound task | a single compound task |

The domain condition is that of `1-HD-HTN` (`DomDesc.MethodsHD1`); the two classes differ only in
the instance condition.  In the rooted reading they therefore have the *same* conditions:
`2-HD-HTN-1` and `1-HD-HTN-1` contain the same descriptions (`sub_HD2_HTN_root_HD1_HTN_root`,
`sub_HD1_HTN_root_HD2_HTN_root`); only the semantic family they are tagged with differs.

As for every other class of the project, the condition is imposed on *all listed* methods, and
the soundness proof (`isHD2_problem`) connects it with the semantic class.

The second half of the file proves the inclusions (`HTN.Syn.SynSub`) between the new classes and
between them and the classes already in the tables.
-/

namespace HTN

namespace Syn

/-! ### The condition on instance descriptions -/

namespace InstDesc

/-- **`2-HD` for instance descriptions**: the initial task network has at most two compound
tasks. -/
def IsHD2 (q : InstDesc) : Prop := q.tnI.toTaskNetwork.IsTwoHole

/-- A one-hole instance description is two-hole. -/
theorem IsHD1.isHD2 {q : InstDesc} (h : q.IsHD1) : q.IsHD2 :=
  TaskNetwork.IsOneHole.isTwoHole h

/-- A rooted instance description is two-hole. -/
theorem IsRooted.isHD2 {q : InstDesc} (h : q.IsRooted) : q.IsHD2 :=
  h.isHD1.isHD2

end InstDesc

/-! ### Soundness -/

/-- **`MethodsHD1` and `IsHD2` are sound**: they describe a two-hole-digging problem. -/
theorem isHD2_problem {d : DomDesc} {q : InstDesc} (hd : d.MethodsHD1) (hq : q.IsHD2) :
    (problem d q).IsHD2 := by
  refine ⟨hq, ?_⟩
  intro m hm
  obtain ⟨e, he, rfl⟩ := exists_methodDesc_of_reachable hm
  exact hd e he

/-! ### The classes -/

namespace SynClass

open Table

/-- **`2-HD-HTN`**: every method has at most one compound task, and the initial task network at
most two. -/
def HD2_HTN : SynClass Cls.HD2_HTN where
  domOk := DomDesc.MethodsHD1
  instOk := InstDesc.IsHD2
  sound := fun _ _ hd hq => isHD2_problem hd hq

/-- **`2-HD-HTN-1`**: every method has at most one compound task, and the initial task network
is a single compound task. -/
def HD2_HTN_root : SynClass Cls.HD2_HTN where
  domOk := DomDesc.MethodsHD1
  instOk := InstDesc.IsRooted
  sound := fun _ _ hd hq => isHD2_problem hd hq.isHD2

/-! ### Inclusions: rooted ⊆ unrooted -/

theorem sub_HD2_HTN_root_HD2_HTN : SynSub HD2_HTN_root HD2_HTN :=
  ⟨fun _ hd => hd, fun _ hq => hq.isHD2⟩

/-! ### Inclusions of `1-HD` into `2-HD` -/

theorem sub_HD1_HTN_HD2_HTN : SynSub HD1_HTN HD2_HTN :=
  ⟨fun _ hd => hd, fun _ hq => hq.isHD2⟩

theorem sub_HD1_HTN_root_HD2_HTN_root : SynSub HD1_HTN_root HD2_HTN_root :=
  ⟨fun _ hd => hd, fun _ hq => hq⟩

/-- **In the rooted reading `2-HD` collapses to `1-HD`**: a single initial compound task is a
one-hole network. -/
theorem sub_HD2_HTN_root_HD1_HTN_root : SynSub HD2_HTN_root HD1_HTN_root :=
  ⟨fun _ hd => hd, fun _ hq => hq⟩

/-! ### Inclusions into `HTN-1` -/

theorem sub_HD2_HTN_root_HTN_root : SynSub HD2_HTN_root HTN_root :=
  ⟨fun _ _ => trivial, fun _ hq => hq⟩

/-! ### Inclusions of the regular classes and of `STRIPS` into `2-HD` -/

theorem sub_HTN_REG_HD2_HTN : SynSub HTN_REG HD2_HTN :=
  sub_HTN_REG_HD1_HTN.trans sub_HD1_HTN_HD2_HTN

theorem sub_HTN_REG_root_HD2_HTN_root : SynSub HTN_REG_root HD2_HTN_root :=
  sub_HTN_REG_root_HD1_HTN_root.trans sub_HD1_HTN_root_HD2_HTN_root

/-- **`STRIPS ⊆ 2-HD-HTN-1`**. -/
theorem sub_STRIPS_HD2_HTN_root : SynSub STRIPS HD2_HTN_root :=
  sub_STRIPS_TO_HD1_HTN_root.trans
    ((sub_TO_HD1_HTN_root_HD1_HTN_root).trans sub_HD1_HTN_root_HD2_HTN_root)

end SynClass

end Syn

end HTN
