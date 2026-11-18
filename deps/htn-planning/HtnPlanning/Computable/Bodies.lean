import HtnPlanning.Computable.Classes
import HtnPlanning.Computable.Linearise
import HtnPlanning.Core.TONormalForm
/-!
# The body of a described totally ordered method

`HtnPlanning/Computable/Linearise.lean` computes the linearisation `TnDesc.lin` of a
described totally ordered task network, and — for a *regular* network — the body in the sense
of `HTN.Method.HasBody` (a list of actions followed by an optional compound task).  A
*tail-recursive* method is not regular: its body is an arbitrary sequence of primitive and
compound tasks.  This file computes that sequence,

* `HTN.Syn.TnDesc.seqBody t = (lin t).map t.label`,

and proves that it is *the* body of the described method in the sense of
`HTN.Method.HasSeqBody` of `HtnPlanning/Core/ProofTuples.lean`
(`HTN.Syn.DomDesc.hasSeqBody_bd`, `HTN.Syn.DomDesc.seqBody_iff`), so that the context-free
reading of totally ordered HTN planning (`HTN.Problem.solvable_iff_yieldSeq`) becomes a
statement about the finitely many *lists* `HTN.Syn.DomDesc.bd d m`, `m < d.methods.length`.

The last section links the *position* of a subtask in the body with the semantic notion
`HTN.TaskNetwork.IsLastId`, and reads the rank condition of a tail-recursive domain
description off the body: a compound task at a non-final position strictly decreases the rank,
a compound task at the final position does not increase it
(`HTN.Syn.DomDesc.rank_lt_of_bd_getElem`, `HTN.Syn.DomDesc.rank_le_of_bd_getElem_last`).
-/

namespace HTN

namespace Syn

namespace TnDesc

/-- **The body of a described totally ordered task network**: its identifiers in the order of
`TnDesc.lin`, labelled. -/
def seqBody (t : TnDesc) : List (ℕ ⊕ ℕ) := (lin t).map t.label

/-- The described network, presented as the sequence network of its body. -/
theorem isSeqNet_lin {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered) :
    t.toTaskNetwork.IsSeqNet (lin t) (seqBody t) :=
  ⟨nodup_lin t, fun s => ((isLinearization_lin hTO).2.1 s).symm, rfl,
    TaskNetwork.ord_iff_idxOf_lt (toTaskNetwork_wf t) hTO (isLinearization_lin hTO)⟩

theorem length_seqBody (t : TnDesc) : (seqBody t).length = (lin t).length :=
  List.length_map _

theorem length_seqBody_le (t : TnDesc) : (seqBody t).length ≤ t.ids.length + 1 := by
  rw [length_seqBody]
  exact length_lin_le t

end TnDesc

/-- A listed position of the method list is a listed method. -/
theorem getI_mem_methods {d : DomDesc} {m : ℕ} (hm : m < d.methods.length) :
    d.methods.getI m ∈ d.methods := by
  rw [List.getI_eq_getElem (l := d.methods) hm]
  exact List.getElem_mem hm

namespace DomDesc

variable {d : DomDesc}

/-- The compound task name the method at position `m` of the description decomposes. -/
def hd (d : DomDesc) (m : ℕ) : ℕ := (d.methods.getI m).1

/-- **The body of the method at position `m`** of a totally ordered domain description. -/
def bd (d : DomDesc) (m : ℕ) : List (ℕ ⊕ ℕ) := TnDesc.seqBody (d.methods.getI m).2

theorem hasSeqBody_bd (hTO : d.MethodsTO) {m : ℕ} (hm : m < d.methods.length) :
    (d.methods.getI m).toMethod.HasSeqBody (d.bd m) :=
  Method.hasSeqBody_of_isSeqNet
    (TnDesc.isSeqNet_lin (hTO _ (getI_mem_methods hm)))

/-- **The bodies of a totally ordered domain description are the lists `bd d m`.** -/
theorem seqBody_iff (hTO : d.MethodsTO) {c : ℕ} {bs : List (ℕ ⊕ ℕ)} :
    d.toDomain.SeqBody c bs ↔ ∃ m, m < d.methods.length ∧ d.hd m = c ∧ d.bd m = bs := by
  constructor
  · rintro ⟨mm, ⟨e, he, rfl⟩, hc, hbody⟩
    obtain ⟨m, hm, hgm⟩ := List.mem_iff_getElem.1 he
    have hgetI : d.methods.getI m = e := by
      rw [List.getI_eq_getElem (l := d.methods) hm, hgm]
    refine ⟨m, hm, by rw [hd, hgetI]; exact hc, ?_⟩
    have := (Method.hasSeqBody_iff_of_isSeqNet
      (TnDesc.isSeqNet_lin (hTO _ (getI_mem_methods hm)))).1
        (show (d.methods.getI m).toMethod.HasSeqBody bs by rw [hgetI]; exact hbody)
    rw [bd, this]
  · rintro ⟨m, hm, rfl, rfl⟩
    exact ⟨(d.methods.getI m).toMethod, ⟨_, getI_mem_methods hm, rfl⟩, rfl, hasSeqBody_bd hTO hm⟩

/-! ### Positions of the body and last tasks -/

/-- The identifier at position `j` of the linearisation is a last identifier exactly when `j`
is the final position. -/
theorem isLastId_getElem_iff {tn : TaskNetwork ℕ ℕ ℕ} {l : List ℕ} {xs : List (ℕ ⊕ ℕ)}
    (hseq : tn.IsSeqNet l xs) {j : ℕ} (hj : j < l.length) :
    tn.IsLastId (l[j]) ↔ j + 1 = l.length := by
  constructor
  · rintro ⟨-, hlast⟩
    by_contra hne
    have hlen : l.length - 1 < l.length := by omega
    have hmem : l[l.length - 1]'hlen ∈ tn.T := hseq.mem_of_mem (List.getElem_mem hlen)
    have hne' : l[l.length - 1]'hlen ≠ l[j] := by
      intro hcon
      have := (List.Nodup.getElem_inj_iff hseq.nodup).1 hcon
      omega
    have h2 := ((hseq.ord _ _).1 (hlast _ hmem hne')).2.2
    rw [List.Nodup.idxOf_getElem hseq.nodup, List.Nodup.idxOf_getElem hseq.nodup] at h2
    omega
  · intro hj'
    refine ⟨hseq.mem_of_mem (List.getElem_mem hj), fun y hy hne => ?_⟩
    have hyl : y ∈ l := (hseq.memT y).1 hy
    have hidx : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hyl
    have hgy : l[l.idxOf y]'hidx = y := List.getElem_idxOf hidx
    refine (hseq.ord y _).2 ⟨hyl, List.getElem_mem hj, ?_⟩
    rw [List.Nodup.idxOf_getElem hseq.nodup]
    rcases Nat.lt_or_ge (l.idxOf y) j with h | h
    · exact h
    · exfalso
      have hij : l.idxOf y = j := by omega
      refine hne ?_
      rw [← hgy]
      simp only [hij]

/-- The identifier at position `j` of the linearisation of a described totally ordered network
is a last identifier exactly when `j` is the final position. -/
theorem isLastId_lin_iff {t : TnDesc} (hTO : t.toTaskNetwork.IsTotallyOrdered) {j : ℕ}
    (hj : j < (TnDesc.lin t).length) :
    t.toTaskNetwork.IsLastId ((TnDesc.lin t)[j]) ↔ j + 1 = (TnDesc.lin t).length :=
  isLastId_getElem_iff (TnDesc.isSeqNet_lin hTO) hj

/-- A compound task at a **non-final** position of the body of a listed method strictly
decreases the rank of a tail-recursive domain description. -/
theorem rank_lt_of_bd_getElem {rk : ℕ → ℕ} (hTO : d.MethodsTO) (hrk : d.TailRecBy rk) {m : ℕ}
    (hm : m < d.methods.length) {j : ℕ} (hj : j < (d.bd m).length)
    (hlast : j + 1 < (d.bd m).length) {c : ℕ} (hc : (d.bd m)[j] = Sum.inr c) :
    rk c < rk (d.hd m) := by
  set t := (d.methods.getI m).2 with ht
  have htTO : t.toTaskNetwork.IsTotallyOrdered := hTO _ (getI_mem_methods hm)
  have hlen : (d.bd m).length = (TnDesc.lin t).length := TnDesc.length_seqBody t
  have hj' : j < (TnDesc.lin t).length := by omega
  have hlbl : t.label ((TnDesc.lin t)[j]) = Sum.inr c := by
    have hmap : (d.bd m)[j] = t.label ((TnDesc.lin t)[j]'hj') := by
      simp only [bd, TnDesc.seqBody, List.getElem_map]
      rfl
    rw [← hmap]; exact hc
  have hmemT : (TnDesc.lin t)[j] ∈ t.toTaskNetwork.T :=
    (TnDesc.isSeqNet_lin htTO).mem_of_mem (List.getElem_mem hj')
  have hnl : ¬ t.toTaskNetwork.IsLastId ((TnDesc.lin t)[j]) := by
    rw [isLastId_lin_iff htTO hj']
    omega
  exact (hrk _ (getI_mem_methods hm) _ hmemT c hlbl).2 hnl

/-- A compound task at the **final** position of the body of a listed method does not increase
the rank of a tail-recursive domain description. -/
theorem rank_le_of_bd_getElem_last {rk : ℕ → ℕ} (hTO : d.MethodsTO) (hrk : d.TailRecBy rk)
    {m : ℕ} (hm : m < d.methods.length) {j : ℕ} (hj : j < (d.bd m).length)
    {c : ℕ} (hc : (d.bd m)[j] = Sum.inr c) : rk c ≤ rk (d.hd m) := by
  set t := (d.methods.getI m).2 with ht
  have htTO : t.toTaskNetwork.IsTotallyOrdered := hTO _ (getI_mem_methods hm)
  have hlen : (d.bd m).length = (TnDesc.lin t).length := TnDesc.length_seqBody t
  have hj' : j < (TnDesc.lin t).length := by omega
  have hlbl : t.label ((TnDesc.lin t)[j]) = Sum.inr c := by
    have hmap : (d.bd m)[j] = t.label ((TnDesc.lin t)[j]'hj') := by
      simp only [bd, TnDesc.seqBody, List.getElem_map]
      rfl
    rw [← hmap]; exact hc
  have hmemT : (TnDesc.lin t)[j] ∈ t.toTaskNetwork.T :=
    (TnDesc.isSeqNet_lin htTO).mem_of_mem (List.getElem_mem hj')
  by_cases hlastId : t.toTaskNetwork.IsLastId ((TnDesc.lin t)[j])
  · exact (hrk _ (getI_mem_methods hm) _ hmemT c hlbl).1 hlastId
  · exact ((hrk _ (getI_mem_methods hm) _ hmemT c hlbl).2 hlastId).le

/-! ### Sizes -/

theorem length_bd_le (d : DomDesc) (m : ℕ) : (d.bd m).length ≤ d.size + 1 := by
  have h1 : (d.bd m).length ≤ (d.methods.getI m).2.ids.length + 1 :=
    TnDesc.length_seqBody_le _
  have h2 : (d.methods.getI m).2.ids.length ≤ d.size := by
    by_cases hm : m < d.methods.length
    · have hmem : d.methods.getI m ∈ d.methods := getI_mem_methods hm
      have h3 : MethodDesc.size (d.methods.getI m) ≤ (d.methods.map MethodDesc.size).sum :=
        DomDesc.mem_le_sum MethodDesc.size hmem
      have h4 : MethodDesc.size (d.methods.getI m) = 1 + (d.methods.getI m).2.size := rfl
      have h5 : (d.methods.getI m).2.size = (d.methods.getI m).2.ids.length +
        (d.methods.getI m).2.ordList.length + (d.methods.getI m).2.lbl.length := rfl
      simp only [DomDesc.size]
      omega
    · rw [List.getI_eq_default (l := d.methods) (by omega)]
      exact Nat.zero_le _
  omega

/-! ### Computability -/

open Primrec

theorem primrec_seqBody : Primrec TnDesc.seqBody := by
  have h : Primrec₂ fun (t : TnDesc) (i : ℕ) => t.label i := by
    have hc : Primrec₂ fun (t : TnDesc) (i : ℕ) => TnDesc.labelList true t.lbl i :=
      (primrec_labelList true).comp (primrec_lbl.comp Primrec.fst) Primrec.snd
    have ha : Primrec₂ fun (t : TnDesc) (i : ℕ) => TnDesc.labelList false t.lbl i :=
      (primrec_labelList false).comp (primrec_lbl.comp Primrec.fst) Primrec.snd
    have : Primrec₂ fun (t : TnDesc) (i : ℕ) =>
        if TnDesc.labelIsCompound t i then (Sum.inr (TnDesc.compOf t i) : ℕ ⊕ ℕ)
        else Sum.inl (TnDesc.actOf t i) := by
      apply Primrec.ite (c := fun w : TnDesc × ℕ => TnDesc.labelIsCompound w.1 w.2 = true)
      · exact PrimrecRel.comp Primrec.eq
          (TnDesc.primrec_labelIsCompound.comp Primrec.fst Primrec.snd) (Primrec.const true)
      · exact Primrec.sumInr.comp (TnDesc.primrec_compOf.comp Primrec.fst Primrec.snd)
      · exact Primrec.sumInl.comp (TnDesc.primrec_actOf.comp Primrec.fst Primrec.snd)
    refine this.of_eq fun t i => ?_
    by_cases hcomp : TnDesc.labelIsCompound t i = true
    · obtain ⟨c, hc'⟩ := TnDesc.labelIsCompound_iff.1 hcomp
      rw [if_pos hcomp, TnDesc.compOf_eq hc', hc']
    · simp only [Bool.not_eq_true] at hcomp
      have : ∃ a, t.label i = Sum.inl a := by
        rcases hl : t.label i with a | c
        · exact ⟨a, rfl⟩
        · exact absurd (TnDesc.labelIsCompound_iff.2 ⟨c, hl⟩) (by simp [hcomp])
      obtain ⟨a, ha⟩ := this
      rw [if_neg (by simp [hcomp]), TnDesc.actOf_eq ha, ha]
  exact Primrec.list_map TnDesc.primrec_lin h

theorem primrec_hd : Primrec₂ hd :=
  Primrec.fst.comp (Primrec.list_getI.comp (primrec_methods.comp Primrec.fst) Primrec.snd)

theorem primrec_bd : Primrec₂ bd :=
  primrec_seqBody.comp
    (Primrec.snd.comp (Primrec.list_getI.comp (primrec_methods.comp Primrec.fst) Primrec.snd))

end DomDesc

end Syn

end HTN
