import HtnComplexity.Space.SeqCode
import HtnComplexity.Space.TrTable
/-!
# The gadget instance as a table problem, with guessed rank witnesses

Step A2 of `TABLE4-PLAN.md`.  This file puts together the sequencing gadget
(`HtnComplexity/Space/SeqGadget.lean`), the rank witnesses
(`HtnComplexity/Space/SeqWitness.lean`), the concrete encodings
(`HtnComplexity/Space/SeqCode.lean`) and the compilation of tail-recursive domains into an
action table (`HtnComplexity/Space/TrTable.lean`).

The machine of step A3 will *guess* the initial configuration of its table problem: the compiled
initial state of a gadget instance, including the witness facts and the facts `lab p x`.  What it
has to check is that the guess is a rank witness (`HTN.Syn.SeqG.WitOk`) and that the labels agree
with it (`HTN.Space.SeqM.WitSeq`) — both local conditions.  The main result,
`HTN.Space.SeqM.solvable_iff_exists_wit`, states that this is exactly right:

  a totally ordered instance `q` over a totally ordered, tail-recursive domain `d` is solvable
  **iff** for some witness `ws` and label sequence `xs` that pass the checks, the compiled table
  problem of the gadget instance `seqInst (code d) d q xs ws` over `seqDom (code d) d N` is
  solvable.

The table `trTableR (seqDom (code d) d N)` depends on `d` and `N` only, so it can be the advice.
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG

/-- **The label sequence described by a witness**: it has one entry per identifier, and the entry
at the value of an identifier is the label of that identifier. -/
def WitSeq (t : TnDesc) (ws : List (ℕ × ℕ)) (xs : List (ℕ ⊕ ℕ)) : Prop :=
  xs.length = t.ids.toFinset.card ∧
    ∀ p i, i ∈ t.ids → (p, i) ∈ ws → xs[p]? = some (t.label i)

theorem length_of_isSeqNet {t : TnDesc} {l : List ℕ} {xs : List (ℕ ⊕ ℕ)}
    (h : t.toTaskNetwork.IsSeqNet l xs) : l.length = t.ids.toFinset.card := by
  rw [← List.toFinset_card_of_nodup h.nodup]
  congr 1
  ext x
  rw [List.mem_toFinset, List.mem_toFinset, ← h.memT, TnDesc.toTaskNetwork_T, List.mem_toFinset]

/-- A witness together with a label sequence it describes gives a sequence network. -/
theorem isSeqNet_of_witSeq {t : TnDesc} {ws : List (ℕ × ℕ)} {xs : List (ℕ ⊕ ℕ)}
    (hTO : t.toTaskNetwork.IsTotallyOrdered) (h : WitOk t ws) (hx : WitSeq t ws xs) :
    ∃ l, t.toTaskNetwork.IsSeqNet l xs := by
  obtain ⟨l, hl, hiff⟩ := exists_seqNet_of_witOk hTO h
  refine ⟨l, ?_⟩
  have hlen := length_of_isSeqNet hl
  have heq : l.map t.label = xs := by
    refine List.ext_getElem (by rw [List.length_map, hlen, hx.1]) fun p h1 h2 => ?_
    have hp : p < l.length := by simpa using h1
    have hmem : l[p] ∈ t.ids := by
      have := (hl.memT l[p]).2 (List.getElem_mem hp)
      rwa [TnDesc.toTaskNetwork_T, List.mem_toFinset] at this
    have hw : (p, l[p]) ∈ ws := (hiff p l[p] hmem).2 (List.getElem?_eq_getElem hp)
    have := hx.2 p l[p] hmem hw
    rw [List.getElem?_eq_getElem h2, Option.some.injEq] at this
    simp [this]
  exact heq ▸ hl

/-- Every rank witness describes some label sequence. -/
theorem exists_witSeq {t : TnDesc} {ws : List (ℕ × ℕ)}
    (hTO : t.toTaskNetwork.IsTotallyOrdered) (h : WitOk t ws) : ∃ xs, WitSeq t ws xs := by
  obtain ⟨l, hl, hiff⟩ := exists_seqNet_of_witOk hTO h
  refine ⟨l.map t.label, by rw [List.length_map, length_of_isSeqNet hl], fun p i hi hw => ?_⟩
  rw [List.getElem?_map, (hiff p i hi).1 hw]
  rfl

theorem length_le_of_witSeq {t : TnDesc} {ws : List (ℕ × ℕ)} {xs : List (ℕ ⊕ ℕ)}
    (hx : WitSeq t ws xs) : xs.length ≤ t.ids.length :=
  hx.1 ▸ List.toFinset_card_le _

/-- **The gadget instance for a checked witness is equisolvable with the original instance**, as
a table problem. -/
theorem solvable_iff_tbl_of_wit {d : DomDesc} {q : InstDesc} {N : ℕ} (hTO : d.MethodsTO)
    (hTR : d.IsTailRec) (hq : q.IsTO) (hN : q.tnI.ids.length ≤ N) {ws : List (ℕ × ℕ)}
    {xs : List (ℕ ⊕ ℕ)} (hw : WitOk q.tnI ws) (hx : WitSeq q.tnI ws xs) :
    Solvable d q ↔ (trDom (seqDom (code d) d N)).HasEmptyMethod ∧
      SolvableTbl (trTableR (seqDom (code d) d N)) (regInitR (seqInst (code d) d q xs ws))
        (regGoalR (seqInst (code d) d q xs ws)) := by
  obtain ⟨l, hl⟩ := isSeqNet_of_witSeq hq hw hx
  rw [solvable_seq_iff (code_fresh d) hTO hl ((length_le_of_witSeq hx).trans hN) ws,
    solvable_tr_iff_solvableTblR (methodsTO_seqDom hTO) (isTailRec_seqDom (code_fresh d) hTR)
      (isRooted_seqInst _ d q xs ws)]

/-- **Solvability of a totally ordered instance, through guessed rank witnesses.**  A totally
ordered instance `q` with at most `N` initial tasks, over a totally ordered tail-recursive domain
`d`, is solvable exactly when some rank witness `ws` (with values at most the number of
identifiers) and some label sequence `xs` it describes make the compiled table problem of the
gadget instance solvable. -/
theorem solvable_iff_exists_wit {d : DomDesc} {q : InstDesc} {N : ℕ} (hTO : d.MethodsTO)
    (hTR : d.IsTailRec) (hq : q.IsTO) (hN : q.tnI.ids.length ≤ N) :
    Solvable d q ↔ ∃ ws xs, WitOk q.tnI ws ∧ WitSeq q.tnI ws xs ∧
      (∀ e ∈ ws, e.1 ≤ q.tnI.ids.length) ∧
      (trDom (seqDom (code d) d N)).HasEmptyMethod ∧
      SolvableTbl (trTableR (seqDom (code d) d N)) (regInitR (seqInst (code d) d q xs ws))
        (regGoalR (seqInst (code d) d q xs ws)) := by
  constructor
  · intro hs
    have hw := witOk_canonWit hq
    obtain ⟨xs, hx⟩ := exists_witSeq hq hw
    exact ⟨_, xs, hw, hx, canonWit_le hq, (solvable_iff_tbl_of_wit hTO hTR hq hN hw hx).1 hs⟩
  · rintro ⟨ws, xs, hw, hx, -, ht⟩
    exact (solvable_iff_tbl_of_wit hTO hTR hq hN hw hx).2 ht

end SeqM

end Space

end HTN
