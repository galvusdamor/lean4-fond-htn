import HtnComplexity.Article.Valid
import HtnComplexity.Computable.AcDecideCell
import HtnPlanning.Article.ToSyn
/-!
# HTN plan existence is semi-decidable (Thm. 4.1.4)

The article semi-decides plan existence by breadth-first search through the task networks
reachable from the initial one.  Here the search is the progression search of
`HtnComplexity/Computable/PoSearch.lean`, run on the dual-rail translation of the description
(`HtnPlanning/Article/ToSyn.lean`); breadth-first search to depth `n`
(`HTN.Syn.bfs`) is primitive recursive, and a solution exists iff some depth reaches a goal
configuration.

* `HTN.Article.rePred_exists` — `∃ b, g a b = true` is recursively enumerable for a computable
  `g`;
* `HTN.Article.solvable_iff_exists_bfs` — solvability of a description of `HTN.Syn` as a search to
  some depth;
* `HTN.Article.primrec_toSynDom`, `HTN.Article.primrec_toSynInst`;
* **`HTN.Article.thm_4_1_4`** — `PlanEx^UNRES-REC_htn` is semi-decidable.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom

/-! ### Recursively enumerable predicates -/

theorem rePred_exists {α β : Type} [Primcodable α] [Primcodable β] {g : α → β → Bool}
    (hg : Computable₂ g) : REPred fun a => ∃ b, g a b = true := by
  have hc : Computable₂ fun (a : α) (n : ℕ) => (Encodable.decode (α := β) n).elim false (g a) := by
    refine (Computable.option_casesOn (Computable.decode.comp Computable.snd)
      (Computable.const false) (hg.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).to₂.of_eq ?_
    intro x
    simp only
    cases Encodable.decode (α := β) x.2 <;> rfl
  have hp : Partrec₂ fun (a : α) (n : ℕ) =>
      (Part.some ((Encodable.decode (α := β) n).elim false (g a)) : Part Bool) := hc.partrec₂
  refine (Partrec.dom_re (Partrec.rfind hp)).of_eq fun a => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨n, hn⟩
    cases h : (Encodable.decode (α := β) n) with
    | none => rw [h] at hn; simp at hn
    | some b => rw [h] at hn; exact ⟨b, hn.symm⟩
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, by simp [hb]⟩

/-! ### Search to a depth -/

theorem pReach_mem_bfs {d : DomDesc} {c₀ c : PConfig} (h : PReach d c₀ c) :
    ∃ n, c ∈ bfs d c₀ n := by
  induction h with
  | refl => exact ⟨0, mem_bfs_start d c₀ 0⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, List.mem_append.2 (Or.inr (List.mem_flatMap.2 ⟨_, hn, hstep⟩))⟩

/-- **Solvability as a search to some depth.** -/
theorem solvable_iff_exists_bfs {d : DomDesc} {q : InstDesc} :
    Syn.Solvable d q ↔ ∃ n, (bfs d (initConfig q) n).any (isGoalB q) = true := by
  rw [solvable_iff_exists_pReach]
  constructor
  · rintro ⟨c, hr, hg⟩
    obtain ⟨n, hn⟩ := pReach_mem_bfs hr
    exact ⟨n, List.any_eq_true.2 ⟨c, hn, hg⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨c, hc, hg⟩ := List.any_eq_true.1 hn
    exact ⟨c, pReach_of_mem_bfs n hc, hg⟩

/-- The search predicate. -/
def searchB (d : DomDesc) (q : InstDesc) (n : ℕ) : Bool :=
  (bfs d (initConfig q) n).any (isGoalB q)

theorem primrec_searchB : Primrec fun x : (DomDesc × InstDesc) × ℕ => searchB x.1.1 x.1.2 x.2 := by
  unfold searchB
  have hinit : Primrec fun x : (DomDesc × InstDesc) × ℕ => initConfig x.1.2 :=
    primrec_initConfig.comp (Primrec.snd.comp Primrec.fst)
  have hbfs : Primrec fun x : (DomDesc × InstDesc) × ℕ => bfs x.1.1 (initConfig x.1.2) x.2 :=
    primrec_bfs.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) hinit) Primrec.snd)
  exact primrec_anyB hbfs (Primrec₂.mk (primrec_isGoalB.comp
    (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))

/-! ### The translation is primitive recursive -/

theorem primrec_notMem : PrimrecRel fun (a : ℕ) (l : List ℕ) => a ∉ l := by
  have h : PrimrecRel fun (l : List ℕ) (a : ℕ) => ∃ x ∈ l, x = a :=
    PrimrecRel.exists_mem_list Primrec.eq
  refine (PrimrecPred.not (h.comp Primrec.snd Primrec.fst)).of_eq fun p => ?_
  simp

theorem primrec_filter_notMem : Primrec₂ fun (l l' : List ℕ) => l.filter fun f => f ∉ l' :=
  (PrimrecRel.listFilter primrec_notMem).of_eq fun l l' => by congr

theorem primrec_posF : Primrec posF := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id

theorem primrec_negF : Primrec negF :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)

theorem primrec_map_posF : Primrec fun l : List ℕ => l.map posF :=
  Primrec.list_map Primrec.id (primrec_posF.comp Primrec.snd).to₂

theorem primrec_map_negF : Primrec fun l : List ℕ => l.map negF :=
  Primrec.list_map Primrec.id (primrec_negF.comp Primrec.snd).to₂

theorem primrec_actToSyn : Primrec actToSyn := by
  unfold actToSyn delOnly
  have hpp : Primrec fun a : ActDesc => a.2.1 := Primrec.fst.comp Primrec.snd
  have hpn : Primrec fun a : ActDesc => a.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have had : Primrec fun a : ActDesc => a.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hde : Primrec fun a : ActDesc => a.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hdo : Primrec fun a : ActDesc => a.2.2.2.2.filter fun f => f ∉ a.2.2.2.1 :=
    primrec_filter_notMem.comp hde had
  exact Primrec.pair Primrec.fst (Primrec.pair
    (Primrec.list_append.comp (primrec_map_posF.comp hpp) (primrec_map_negF.comp hpn))
    (Primrec.pair (Primrec.list_append.comp (primrec_map_posF.comp had) (primrec_map_negF.comp hdo))
      (Primrec.list_append.comp (primrec_map_negF.comp had) (primrec_map_posF.comp hdo))))

theorem primrec_toSynDom : Primrec toSynDom := by
  unfold toSynDom ProbDesc.actions ProbDesc.methods
  exact Primrec.pair (Primrec.list_map (Primrec.fst.comp Primrec.fst)
    (primrec_actToSyn.comp Primrec.snd).to₂) (Primrec.snd.comp Primrec.fst)

theorem primrec_facts : Primrec ProbDesc.facts := by
  unfold ProbDesc.facts ProbDesc.init ProbDesc.goalPos ProbDesc.goalNeg ProbDesc.actions
  have hi : Primrec fun p : ProbDesc => p.2.1 := Primrec.fst.comp Primrec.snd
  have hgp : Primrec fun p : ProbDesc => p.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hgn : Primrec fun p : ProbDesc => p.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hact : Primrec fun a : ActDesc => a.2.1 ++ a.2.2.1 ++ a.2.2.2.1 ++ a.2.2.2.2 :=
    Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp hi hgp) hgn)
    (Primrec.list_flatMap (Primrec.fst.comp Primrec.fst) (hact.comp Primrec.snd).to₂)

theorem primrec_toSynInst : Primrec toSynInst := by
  unfold toSynInst
  have hi : Primrec fun p : ProbDesc => p.init := Primrec.fst.comp Primrec.snd
  have hgp : Primrec fun p : ProbDesc => p.goalPos :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hgn : Primrec fun p : ProbDesc => p.goalNeg :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have htn : Primrec fun p : ProbDesc => p.tnI := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.pair (Primrec.list_append.comp (primrec_map_posF.comp hi)
      (primrec_map_negF.comp (primrec_filter_notMem.comp primrec_facts hi)))
    (Primrec.pair (Primrec.list_append.comp (primrec_map_posF.comp hgp) (primrec_map_negF.comp hgn))
      htn)

/-! ### Theorem 4.1.4 -/

/-- The certificate check: `(p, n)` certifies `w` iff `w` is the code of the well-formed
description `p` and the search of depth `n` on its translation reaches a goal. -/
def unresCertB (w : List Bool) (c : ProbDesc × ℕ) : Bool :=
  decide (enc c.1 = w) && validB c.1 && searchB (toSynDom c.1) (toSynInst c.1) c.2

theorem primrec_unresCertB : Primrec₂ unresCertB := by
  unfold unresCertB
  refine Primrec₂.mk (Primrec.and.comp (Primrec.and.comp ?_ ?_) ?_)
  · exact (PrimrecRel.decide Primrec.eq).comp (primrec_enc_probDesc.comp
      (Primrec.fst.comp Primrec.snd : Primrec fun x : List Bool × (ProbDesc × ℕ) => x.2.1))
      Primrec.fst
  · exact primrec_validB.comp (Primrec.fst.comp Primrec.snd)
  · exact primrec_searchB.comp (Primrec.pair (Primrec.pair
      (primrec_toSynDom.comp (Primrec.fst.comp Primrec.snd))
      (primrec_toSynInst.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))

theorem planEx_unres_iff (w : List Bool) : PlanEx UNRES w ↔ ∃ c, unresCertB w c = true := by
  simp only [unresCertB, Bool.and_eq_true, decide_eq_true_eq, validB_iff]
  constructor
  · rintro ⟨p, rfl, hv, -, hs⟩
    rw [solvable_toSyn_iff, solvable_iff_exists_bfs] at hs
    obtain ⟨n, hn⟩ := hs
    exact ⟨(p, n), ⟨rfl, hv⟩, hn⟩
  · rintro ⟨⟨p, n⟩, ⟨rfl, hv⟩, hn⟩
    refine ⟨p, rfl, hv, trivial, ?_⟩
    rw [solvable_toSyn_iff, solvable_iff_exists_bfs]
    exact ⟨n, hn⟩

/-- **Theorem 4.1.4.** `PlanEx^UNRES-REC_htn` is semi-decidable. -/
theorem thm_4_1_4 : Cx.SemiDecidable (PlanEx UNRES) :=
  (rePred_exists primrec_unresCertB.to_comp).of_eq fun w => (planEx_unres_iff w).symm

end Article

end HTN
