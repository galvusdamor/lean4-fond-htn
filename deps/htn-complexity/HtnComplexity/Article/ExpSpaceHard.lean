import HtnComplexity.Article.ExpSpacePT
/-!
# Tail-recursive HTN planning with a totally ordered initial network is EXPSPACE-hard (Thm. 4.3.7)

**`HTN.Article.thm_4_3_7_tr`** — `PlanEx^{TAIL-REC ∩ TO-tn_I}_htn` is EXPSPACE-hard.

A language of `EXPSPACE` is accepted by a nondeterministic machine within `2 ^ p(|w|)` cells.  The
reduction maps `w` to the tail-recursive encoding of `HtnComplexity/SpaceEnc/` (a round per
machine step, the tape stored in the tails of the words of two alternating loops, addresses
checked by binary counters), written down with the explicit numberings of
`HtnComplexity/Article/ExpSpaceNum.lean`, computed in polynomial time
(`HtnComplexity/Article/ExpSpacePT.lean`) and brought into the article's normal form
(`HTN.Article.artOf`).

The article extends its acyclic encoding of Thm. 4.3.7 (counters running in parallel with the
tape) by recursion; this formalisation uses the tail-recursive encoding of
`HtnComplexity/SpaceEnc/` instead, which was already proved correct (see `ARTICLE.md`).
-/

namespace HTN

namespace SpaceEnc

open TM Syn Syn.PolyDom PTime Article

/-- **The instance description of a word**, as numbers. -/
def instN (w : List Bool) : InstDesc :=
  (Nat.pair 0 0 :: (List.range w.length).map (fun i => finp i (w.getD i false).toNat), [],
    gridDesc [[(true, 0)]])

variable {k : ℕ} (m n' : ℕ) (N : NTM (Fin k) (Option Bool))

theorem instDesc_rendP (w : List Bool) : (rendP m n' N w).instDesc = instN w := by
  simp [Rendering.instDesc, rendP, rend, instN, inpL, cFP, finp, Shape.desc, gridAfterDescOf,
    gridAfterDesc_zero, encLabel, eCP, List.map_map, Function.comp_def]

theorem pt_instN : PT instN := by
  unfold instN finp
  refine PT.pair (PT.cons (PT.const _) (PT.map (PT.rangeLength PT.id) ?_)) (PT.const _)
  refine pt_pairC 1 (PT.natPair PT.snd (pt_toNat ((PT.getI PT.fst PT.snd).of_eq fun q => ?_)))
  rw [← List.getD_default_eq_getI]; rfl

/-- The actions of the written-out bodies are action descriptions of the encoding. -/
theorem mem_bodyActs_nbP {a : ActionDesc} (h : a ∈ (nbP m n' N).flatMap bodyActs) :
    ∃ o, a = actDP m n' N o := by
  simp only [nbP, List.flatMap_map, List.mem_flatMap] at h
  obtain ⟨b, -, hb⟩ := h
  rw [mem_bodyActs] at hb
  simp only [← List.map_flatten, List.mem_map] at hb
  obtain ⟨x, -, hx⟩ := hb
  rcases x with o | c
  · exact ⟨o, by simpa using hx.symm⟩
  · simp at hx

/-- **The article's description of the encoding.** -/
noncomputable def trDesc (w : List Bool) : ProbDesc :=
  artOf (nDom (nbN m w.length N.init.val (symCode N.blank) (transN N) (accN N))) (instN w)

theorem trDesc_eq (w : List Bool) :
    trDesc m N w = artOf (rendP m w.length N w).domDesc (rendP m w.length N w).instDesc := by
  rw [trDesc, domDesc_rendP, nbP_eq, instDesc_rendP]

theorem valid_trDesc (w : List Bool) : (trDesc m N w).Valid := by
  rw [trDesc, ← nbP_eq]
  refine valid_artOf_nDom ?_ ⟨nodup_cellIds, ?_, ?_⟩
  · intro a ha a' ha' h
    obtain ⟨o, rfl⟩ := mem_bodyActs_nbP m w.length N ha
    obtain ⟨o', rfl⟩ := mem_bodyActs_nbP m w.length N ha'
    rw [cAP_injective (h : cAP o = cAP o')]
  · show ((cellLbl [[(true, 0)]]).map Prod.fst).Perm (cellIds [[(true, 0)]])
    rw [map_fst_cellLbl]
  · intro r hr hf
    have := mem_cellLbl hr
    simp at this
    rw [this] at hf
    simp at hf

theorem isTailREC_trDesc (w : List Bool) : (trDesc m N w).toProblem.IsTailREC := by
  rw [trDesc_eq]
  exact isTailREC_artOf _ (isTailRec_rendP m w.length N w)

theorem isTO_tnI_trDesc (w : List Bool) : (trDesc m N w).toProblem.IsTO_tnI := by
  rw [trDesc_eq]
  exact isTO_tnI_artOf _ (isRooted_rendP m w.length N w).isTO

theorem solvable_trDesc_iff (w : List Bool) :
    (trDesc m N w).toProblem.Solvable ↔ N.AcceptsInSpace (w.map some) (2 ^ m) := by
  rw [trDesc_eq, solvable_artOf_iff]
  exact solvable_rendP_iff m w.length N rfl

end SpaceEnc

namespace Article

open SpaceEnc Syn Syn.PolyDom PTime

/-- **Theorem 4.3.7** (second part). `PlanEx^{TAIL-REC ∩ TO-tn_I}_htn` is EXPSPACE-hard. -/
theorem thm_4_3_7_tr : Cx.Hard Cx.EXPSPACE (PlanEx fun P => P.IsTailREC ∧ P.IsTO_tnI) := by
  rintro L ⟨k, N, p, hL⟩
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen p
  set f : List Bool → ProbDesc := fun w => trDesc (g w).length N w
  have hf : PT f := by
    have h := pt_artOf (pt_nDom (pt_nbN hg (L' := fun w : List Bool => w.map fun _ => ())
      (PT.map (g := fun _ _ => ()) PT.id (PT.const ())) N.init.val (symCode N.blank) (transN N)
      (accN N))) pt_instN
    exact h.of_eq fun w => by simp [f, trDesc]
  refine ⟨_, polyTimeFun_of_uc (uc_of_pt_list (BDec.pt_encL.comp hf)), fun w => ?_⟩
  show L w ↔ codeLang ProbDesc (fun p => p.Valid ∧ (p.toProblem.IsTailREC ∧ p.toProblem.IsTO_tnI) ∧
    p.toProblem.Solvable) (enc (f w))
  rw [codeLang_enc, hL w]
  simp only [f]
  rw [solvable_trDesc_iff, hglen]
  exact ⟨fun h => ⟨valid_trDesc _ N w, ⟨isTailREC_trDesc _ N w, isTO_tnI_trDesc _ N w⟩, h⟩,
    fun h => h.2.2⟩

end Article

end HTN
