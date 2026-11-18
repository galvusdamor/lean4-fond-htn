import HtnComplexity.HDDecide.NetSim
/-!
# Plan existence for one-hole-digging problems is Petri net reachability

`HTN.HD.hdReach_iff`: the final configuration of the rule system `hdRules d q` is reachable
from its initial configuration iff the pieces criterion holds; with
`HTN.HD.solvable_iff_piecesSolvable` and `HTN.Petri.reach_mk_iff` this makes plan existence of a
one-hole-digging description a reachability question in the Petri net `ruleNet (hdRules d q)`
(`HTN.HD.solvable_iff_reach`).
-/

namespace HTN

namespace HD

open Syn Syn.ToDec Petri

variable {d : DomDesc} {q : InstDesc}

theorem step_fst {r : HRule} {lf lb : List ℕ} {p : Tok} {x : ℕ}
    (hr : r ∈ progR d q lf lb p.1 p.2 x ∨ r ∈ regrR d q lf lb p.1 p.2 x ∨
      r ∈ decR d q lf lb p.1 p.2 x) : r.1.1 = 1 := by
    rcases hr with hr | hr | hr
    · simp only [progR, mem_cond_nil] at hr
      rw [hr.2]
    · simp only [regrR, List.mem_flatMap, mem_cond_nil] at hr
      obtain ⟨s, -, -, rfl⟩ := hr
      rfl
    · simp only [decR, List.mem_flatMap, mem_cond_nil] at hr
      obtain ⟨j, -, -, rfl⟩ := hr
      rfl

theorem rule_fst {r : HRule} (hr : r ∈ hdRules d q) : r.1 = startC ∨ r.1.1 = 1 := by
  rw [mem_hdRules] at hr
  rcases hr with ⟨s, -, -, rfl⟩ | ⟨lf, -, lb, -, p, -, x, -, hr⟩ | ⟨l, -, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (step_fst hr)
  · exact Or.inr rfl

theorem not_rstep_done {N : Multiset Tok} {y : Ctl × Multiset Tok} :
    ¬ RStep (hdRules d q) (doneC, N) y := by
  rintro ⟨r, hr, hc, -⟩
  rcases rule_fst hr with h | h
  · rw [h] at hc; simp [startC, doneC] at hc
  · rw [hc] at h; simp [doneC] at h

theorem eq_of_reach_done {N : Multiset Tok} {z : Ctl × Multiset Tok}
    (h : Relation.ReflTransGen (RStep (hdRules d q)) (doneC, N) z) : z = (doneC, N) := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨y, hy, -⟩
  · exact h.symm
  · exact absurd hy not_rstep_done

theorem valid_of_hreach {c c' : HCfg} (h : HReach d q c c') (hv : Valid d q c) : Valid d q c' := by
  induction h with
  | refl => exact hv
  | tail _ hs ih => exact (sim_step ih hs).2

theorem reach_of_hreach {c c' : HCfg} (h : HReach d q c c') (hv : Valid d q c) :
    Relation.ReflTransGen (RStep (hdRules d q)) (enc d q c) (enc d q c') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hr hs ih => exact ih.tail (sim_step (valid_of_hreach hr hv) hs).1

theorem hreach_of_reach {x : Ctl × Multiset Tok}
    (h : Relation.ReflTransGen (RStep (hdRules d q)) x hdDone) :
    ∀ c, Valid d q c → x = enc d q c → ∃ s, HReach d q c (s, s, 0) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c _ he
    simp [hdDone, enc, doneC] at he
  | head hs hr ih =>
    intro c hv he
    subst he
    rcases decode_step hv hs with ⟨c', hstep, rfl⟩ | ⟨heq, rfl⟩
    · obtain ⟨s, hs'⟩ := ih c' (sim_step hv hstep).2 rfl
      exact ⟨s, Relation.ReflTransGen.head hstep hs'⟩
    · have h0 := eq_of_reach_done hr
      simp only [hdDone, Prod.mk.injEq, true_and] at h0
      obtain ⟨sf, sb, M⟩ := c
      simp only at heq h0
      subst heq
      have hM : M = 0 := by simpa using h0.symm
      subst hM
      exact ⟨sf, Relation.ReflTransGen.refl⟩

theorem init_map : (tokOf 0 q.tnI.ids : Multiset Tok) = (initPieces q).map (pcL d q) := by
  have h := coe_tokOf (d := d) (q := q) 0 _ (subset_refl _)
  rw [pcL_full] at h
  exact h

theorem initList_subset_facts : q.initList.toFinset ⊆ facts d q := by
  intro f hf
  simp only [facts, allFacts, List.mem_toFinset, List.mem_append] at hf ⊢
  exact Or.inl hf

theorem valid_init {sω : Finset ℕ} (hsω : sω ⊆ facts d q) :
    Valid d q (q.initList.toFinset, sω, initPieces q) := by
  refine ⟨initList_subset_facts, hsω, fun p hp => ?_⟩
  obtain ⟨-, rfl⟩ := mem_piece.1 hp
  exact ⟨by simp, subset_refl _⟩

/-- **The rule system decides the pieces criterion.** -/
theorem hdReach_iff :
    Relation.ReflTransGen (RStep (hdRules d q)) (hdInit q) hdDone ↔ PiecesSolvable d q := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h0 | ⟨y, hy, hr⟩
    · simp [hdInit, hdDone, startC, doneC] at h0
    obtain ⟨r, hr', hc, -, rfl⟩ := hy
    rw [mem_hdRules] at hr'
    rcases hr' with ⟨s, hs, hg, rfl⟩ | ⟨lf, -, lb, -, p, -, x, -, hr'⟩ | ⟨l, -, rfl⟩
    · have hs' := toFinset_subset_facts hs
      obtain ⟨sf, hsf⟩ := hreach_of_reach hr _ (valid_init hs') (by
        simp [hdInit, enc, nrmF_eq, init_map (d := d)])
      refine ⟨s.toFinset, sf, hs', fun f hf => ?_, hsf⟩
      simp only [List.all_eq_true, memB_iff] at hg
      exact List.mem_toFinset.2 (hg f hf)
    · have h1 := step_fst hr'
      rw [hc] at h1
      simp [hdInit, startC] at h1
    · simp [hdInit, startC] at hc
  · rintro ⟨sω, s, hsω, hgoal, hr⟩
    have hv := valid_init hsω
    have h1 : RStep (hdRules d q) (hdInit q) (enc d q (q.initList.toFinset, sω, initPieces q)) := by
      refine ⟨(startC, none, (1, nrmF d q q.initList, nrmF d q (stL d q sω)), []), ?_, rfl,
        by simp, ?_⟩
      · rw [mem_hdRules]
        refine Or.inl ⟨_, stL_mem_subsets sω, ?_, rfl⟩
        simp only [List.all_eq_true, memB_iff, mem_stL]
        intro f hf
        exact ⟨List.mem_toFinset.1 (hsω (hgoal f hf)), hgoal f hf⟩
      · simp [hdInit, enc, nrmF_eq, init_map (d := d), toFinset_stL hsω]
    have h2 := reach_of_hreach hr hv
    obtain ⟨hs, -, -⟩ := valid_of_hreach hr hv
    have h3 : RStep (hdRules d q) (enc d q (s, s, 0)) hdDone := by
      refine ⟨((1, stL d q s, stL d q s), none, doneC, []), ?_, rfl, by simp, ?_⟩
      · rw [mem_hdRules]
        exact Or.inr (Or.inr ⟨_, stL_mem_subsets s, rfl⟩)
      · simp [enc, hdDone]
    exact (Relation.ReflTransGen.head h1 h2).tail h3

/-! ### The Petri net over natural numbers -/

/-- **The Petri net of a description**, its places coded as natural numbers. -/
def hdNet (d : DomDesc) (q : InstDesc) : List (Trans ℕ) :=
  mapNet (Encodable.encode : Ctl ⊕ Tok → ℕ) (ruleNet (hdRules d q))

/-- The initial marking: the start token and the token of the initial task network. -/
def hdM0 (q : InstDesc) : List ℕ :=
  Encodable.encode (Sum.inl startC : Ctl ⊕ Tok) ::
    (tokOf 0 q.tnI.ids).map fun t => Encodable.encode (Sum.inr t : Ctl ⊕ Tok)

/-- The final marking: the done token alone. -/
def hdM1 : List ℕ := [Encodable.encode (Sum.inl doneC : Ctl ⊕ Tok)]

theorem hdM0_eq : ((hdM0 q : List ℕ) : Multiset ℕ) = (mk (hdInit q)).map Encodable.encode := by
  simp [hdM0, mk, hdInit]
  rfl

theorem hdM1_eq : ((hdM1 : List ℕ) : Multiset ℕ) = (mk hdDone).map Encodable.encode := by
  simp [hdM1, mk, hdDone]

/-- **The pieces criterion is Petri net reachability.** -/
theorem piecesSolvable_iff_reach :
    PiecesSolvable d q ↔ Reach (hdNet d q) (hdM0 q : Multiset ℕ) (hdM1 : Multiset ℕ) := by
  rw [hdM0_eq, hdM1_eq, hdNet, reach_map_iff Encodable.encode_injective, reach_mk_iff,
    hdReach_iff]

/-- **Plan existence for one-hole-digging descriptions is Petri net reachability**
(Dekker and Behnke): a one-hole-digging description is solvable iff the final marking `hdM1`
is reachable from the initial marking `hdM0 q` in the Petri net `hdNet d q`. -/
theorem solvable_iff_reach (hd : d.MethodsHD1) (hq : q.IsHD1) :
    Solvable d q ↔ Reach (hdNet d q) (hdM0 q : Multiset ℕ) (hdM1 : Multiset ℕ) := by
  rw [solvable_iff_piecesSolvable hd hq, piecesSolvable_iff_reach]

end HD

end HTN
