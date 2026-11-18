import ComplexityTheory.Petri.PrimCert
import ComplexityTheory.Petri.NetBlock
/-!
# Petri net reachability is decidable

* `HTN.Petri.KLM.rootB` — the concrete block of a reachability question `(N, m₀, m₁)`, over the
  places `< dimOf (N, m₀, m₁)`;
* `HTN.Petri.KLM.not_reach_iff_cert` — `m₁` is not reachable from `m₀` iff some certificate is
  accepted by the (primitive recursive) checker;
* **`HTN.Petri.petriReachDecidable`** — reachability is r.e. (`reach_re`) and co-r.e., hence
  computable (Mayr; Kosaraju; Lambert; Leroux–Schmitz).
-/

namespace HTN

namespace Petri

namespace KLM

open Primrec

/-- A reachability question: net, initial marking, target marking. -/
abbrev PNI : Type := List (Trans ℕ) × List ℕ × List ℕ

/-- The places mentioned by a question. -/
def places (x : PNI) : List ℕ := x.2.1 ++ x.2.2 ++ x.1.flatMap fun t => t.1 ++ t.2

/-- The number of coordinates used for a question. -/
def dimOf (x : PNI) : ℕ := (places x).foldr max 0 + 1

/-- The `ω`-vector of a marking (no `ω`). -/
def cntW (d : ℕ) (m : List ℕ) : CW := (List.range d).map fun j => some (cnt j m)

/-- The vector of a marking. -/
def posV (d : ℕ) (m : List ℕ) : CV := (List.range d).map fun j => (cnt j m : ℤ)

/-- The negated vector of a marking. -/
def negV (d : ℕ) (m : List ℕ) : CV := (List.range d).map fun j => -(cnt j m : ℤ)

/-- The concrete edges of the net block. -/
def netCE (d : ℕ) (N : List (Trans ℕ)) : List CE :=
  (List.range N.length).flatMap fun i =>
    [(0, negV d (N.getD i default).1, i + 1), (i + 1, posV d (N.getD i default).2, 0)]

/-- **The concrete block of a reachability question.** -/
def rootB (x : PNI) : CB :=
  ([], cntW (dimOf x) x.2.1, (List.range (x.1.length + 1), [], netCE (dimOf x) x.1, 0, 0),
    cntW (dimOf x) x.2.2)

/-! ### Decoding -/

theorem decW_cntW (d : ℕ) (m : List ℕ) :
    decW d (cntW d m) = fun j : Fin d => (((m : Multiset ℕ).count (j : ℕ) : ℕ) : ℕ∞) := by
  funext j
  simp only [decW, cntW]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, cnt_eq]
  rfl

theorem decV_posV (d : ℕ) (m : List ℕ) : decV d (posV d m) = mv d (m : Multiset ℕ) := by
  funext j
  simp only [decV, posV, mv]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, cnt_eq]

theorem decV_negV (d : ℕ) (m : List ℕ) : decV d (negV d m) = -mv d (m : Multiset ℕ) := by
  funext j
  simp only [decV, negV, mv, Pi.neg_apply]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, cnt_eq]

theorem zipIdx_eq_map_range {α : Type*} [Inhabited α] (l : List α) :
    l.zipIdx = (List.range l.length).map fun i => (l.getD i default, i) := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range, zero_add]
  rw [List.getD_eq_getElem _ _ (by simpa using h₁)]

theorem netCE_dec (d : ℕ) (N : List (Trans ℕ)) : (netCE d N).map (decE d) = netEdges d N := by
  rw [netEdges, zipIdx_eq_map_range, List.flatMap_map, netCE, List.map_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  simp [decE, decV_posV, decV_negV]

theorem decB_rootB (x : PNI) :
    decB (dimOf x) (rootB x) = netBlock (dimOf x) x.1 x.2.1 x.2.2 := by
  show Block.mk _ _ _ _ = Block.mk _ _ _ _
  have h0 : decV (dimOf x) [] = 0 := by funext j; simp [decV]
  simp only [rootB, cPre_mk, cInp_mk, cOut_mk, cComp_mk, decW_cntW, h0]
  congr 1
  simp only [decC, cNodes, cLabs, cEdges, cEntry, cExit, netCE_dec, Comp.mk.injEq, and_true,
    true_and]
  funext u
  simp [decW_nil]; rfl

/-! ### The dimension bounds all places -/

theorem lt_dimOf {x : PNI} {p : ℕ} (hp : p ∈ places x) : p < dimOf x := by
  unfold dimOf
  suffices ∀ l : List ℕ, p ∈ l → p ≤ l.foldr max 0 from Nat.lt_succ_of_le (this _ hp)
  intro l hl
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    rcases List.mem_cons.1 hl with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem pb_init (x : PNI) : PB (dimOf x) (x.2.1 : Multiset ℕ) := fun p hp =>
  lt_dimOf (by simp only [places, List.mem_append]; exact Or.inl (Or.inl hp))

theorem pb_target (x : PNI) : PB (dimOf x) (x.2.2 : Multiset ℕ) := fun p hp =>
  lt_dimOf (by simp only [places, List.mem_append]; exact Or.inl (Or.inr hp))

theorem nb_net (x : PNI) : NB (dimOf x) x.1 := fun t ht =>
  ⟨fun p hp => lt_dimOf (by
      simp only [places, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨t, ht, Or.inl hp⟩),
    fun p hp => lt_dimOf (by
      simp only [places, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨t, ht, Or.inr hp⟩)⟩

/-- **Non-reachability has checkable certificates.** -/
theorem not_reach_iff_cert (x : PNI) :
    ¬ Petri.Reach x.1 (x.2.1 : Multiset ℕ) (x.2.2 : Multiset ℕ) ↔
      ∃ cert, Accepts (dimOf x) [rootB x] cert := by
  rw [not_reach_iff_refutable (nb_net x) (pb_init x) (pb_target x), ← decB_rootB,
    ← refutable_iff_cert]
  rfl

/-! ### Primitive recursiveness -/

theorem pr_dimOf : Primrec dimOf :=
  (succ.comp (PR.list_maxN.comp (list_append.comp (list_append.comp (fst.comp snd) (snd.comp snd))
    (list_flatMap fst (list_append.comp (fst.comp snd) (snd.comp snd)).to₂)))).of_eq fun _ => rfl

theorem pr_cntW : Primrec₂ cntW :=
  (list_map (list_range.comp fst) (option_some.comp (primrec_cnt.comp snd (snd.comp fst))).to₂).of_eq
    fun _ => rfl

theorem pr_posV : Primrec₂ posV :=
  (list_map (list_range.comp fst) (IntPR.natCast.comp (primrec_cnt.comp snd (snd.comp fst))).to₂).of_eq
    fun _ => rfl

theorem pr_negV : Primrec₂ negV :=
  (list_map (list_range.comp fst)
    (IntPR.neg.comp (IntPR.natCast.comp (primrec_cnt.comp snd (snd.comp fst)))).to₂).of_eq
    fun _ => rfl

theorem pr_netCE : Primrec₂ netCE :=
  (list_flatMap (list_range.comp (list_length.comp snd))
    (list_cons.comp (pair (const 0) (pair (pr_negV.comp (fst.comp fst)
        (fst.comp ((list_getD default).comp (snd.comp fst) snd))) (succ.comp snd)))
      (list_cons.comp (pair (succ.comp snd) (pair (pr_posV.comp (fst.comp fst)
        (snd.comp ((list_getD default).comp (snd.comp fst) snd))) (const 0))) (const []))).to₂).of_eq
    fun _ => rfl

theorem pr_rootB : Primrec rootB :=
  (pair (const []) (pair (pr_cntW.comp pr_dimOf (fst.comp snd))
    (pair (pair (list_range.comp (succ.comp (list_length.comp fst))) (pair (const [])
      (pair (pr_netCE.comp pr_dimOf fst) (pair (const 0) (const 0)))))
      (pr_cntW.comp pr_dimOf (snd.comp snd))))).of_eq fun _ => rfl

end KLM

open KLM in
/-- **Petri net reachability is decidable** (Mayr 1981; Kosaraju 1982; here via the KLMST
decomposition with Lambert's perfectness argument, and a primitive recursive certificate checker
for non-reachability). -/
theorem petriReachDecidable : PetriReachDecidable := by
  refine ComputablePred.computable_iff_re_compl_re'.2 ⟨reach_re, ?_⟩
  have h := rePred_exists (α := PNI) (β := List CNode)
    (q := fun x cert => Accepts (dimOf x) [rootB x] cert)
    (pr_accepts.comp (Primrec.pair (pr_dimOf.comp Primrec.fst) (Primrec.pair
      (Primrec.list_cons.comp (pr_rootB.comp Primrec.fst) (Primrec.const [])) Primrec.snd)))
  exact h.of_eq fun x => (not_reach_iff_cert x).symm

end Petri

end HTN
