import HtnComplexity.Article.TODPPT
/-!
# Totally ordered HTN planning is in EXPTIME (Thm. 4.2.1)

The decider (`HTN.Article.toDec`) checks well-formedness, the class `TO` (the initial network and
the methods of the reachable names, computed by `HTN.Article.reachSetB`, are totally ordered),
and runs the dynamic program of the article's Alg. 1 (`HTN.Article.dpTab`) over all states of the
relevant facts, enumerated from a padding of `2 ^ |p|` ones.

* **`HTN.Article.thm_4_2_1`** — `PlanEx^{UNRES ∩ TO}_htn ∈ EXPTIME`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- The compound names of `tn_I`. -/
def rootNames (p : ProbDesc) : List ℕ :=
  (p.tnI.ids.filter fun x => (lblOf p.tnI x).1).map fun x => (lblOf p.tnI x).2

/-- **The reachable compound names**, computed. -/
def reachSetB (p : ProbDesc) : List ℕ :=
  (numsOf p).filter fun c => (rootNames p).any fun c₀ => (c₀ == c) || reachD (edgesOf p) c₀ c

theorem reachable_iff_root {p : ProbDesc} {c : ℕ} : p.toProblem.toPos.ReachableName c ↔
    ∃ c₀ ∈ rootNames p, Relation.ReflTransGen (DEdge p.toProblem.methods) c₀ c := by
  constructor
  · intro h
    induction h with
    | @tnI t c ht hc =>
      have ht' : t ∈ p.tnI.ids := by
        simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using ht
      have hl := label_eq_inr.1 hc
      exact ⟨c, List.mem_map.2 ⟨t, List.mem_filter.2 ⟨ht', by rw [hl]⟩, by rw [hl]⟩, .refl⟩
    | @method m t c hm hr ht hc ih =>
      obtain ⟨c₀, h₀, hrt⟩ := ih
      exact ⟨c₀, h₀, hrt.tail ⟨m, hm, rfl, t, ht, hc⟩⟩
  · rintro ⟨c₀, h₀, hrt⟩
    induction hrt with
    | refl =>
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h₀
      obtain ⟨ht, hb⟩ := List.mem_filter.1 ht
      exact HTN.Problem.ReachableName.tnI (P := p.toProblem.toPos)
        (by simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using ht)
        (label_eq_inr.2 (Prod.ext hb rfl))
    | tail _ he ih =>
      obtain ⟨m, hm, rfl, t, ht, hc⟩ := he
      exact HTN.Problem.ReachableName.method hm ih ht hc

theorem mem_reachSetB {p : ProbDesc} (hp : p.Valid) {c : ℕ} :
    c ∈ reachSetB p ↔ p.toProblem.toPos.ReachableName c := by
  unfold reachSetB
  rw [List.mem_filter, reachable_iff_root]
  simp only [List.any_eq_true, Bool.or_eq_true, beq_iff_eq, reachD_iff, listRelOf_edgesOf]
  constructor
  · rintro ⟨-, c₀, h₀, h | h⟩
    · exact ⟨c₀, h₀, h ▸ .refl⟩
    · exact ⟨c₀, h₀, h.to_reflTransGen⟩
  · rintro ⟨c₀, h₀, h⟩
    refine ⟨reach_numsOf hp (reachable_iff_root.2 ⟨c₀, h₀, h⟩), c₀, h₀, ?_⟩
    rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h

/-- **The check of the class `TO`.** -/
def classTOB (p : ProbDesc) : Bool := toB p.tnI && methodsRB toB p (reachSetB p)

theorem classTOB_iff {p : ProbDesc} (hp : p.Valid) : classTOB p = true ↔ p.toProblem.IsTO := by
  unfold classTOB
  rw [Bool.and_eq_true, toB_iff hp.tnI]
  exact and_congr Iff.rfl ⟨methodsRB_sound hp (fun c hc => (mem_reachSetB hp).2 hc)
    (fun ht => toB_iff ht), methodsRB_complete hp (fun c hc => (mem_reachSetB hp).1 hc)
      (fun ht => toB_iff ht)⟩

/-- **The decider of Thm. 4.2.1**, on a description and the padding. -/
def toDec (x : ProbDesc × List Bool) : Bool :=
  validB x.1 && classTOB x.1 &&
    (chainSet (allVecs (pfacts x.1) x.2) (dpTab x.1 (allVecs (pfacts x.1) x.2)) x.1.tnI
      [vecOf (pfacts x.1) x.1.init]).any fun w => goalB x.1 (sv (pfacts x.1) w)

theorem toDec_iff (p : ProbDesc) :
    toDec (p, List.replicate (2 ^ sz p) true) = true ↔
      p.Valid ∧ p.toProblem.IsTO ∧ p.toProblem.Solvable := by
  unfold toDec
  simp only [Bool.and_eq_true]
  rw [validB_iff]
  constructor
  · rintro ⟨⟨hp, hc⟩, hd⟩
    have hto := (classTOB_iff hp).1 hc
    refine ⟨hp, hto, ?_⟩
    have hall : ∀ v, v ∈ allVecs (pfacts p) (List.replicate (2 ^ sz p) true) ↔
        v.length = (pfacts p).length := fun v => mem_allVecs (by
      rw [List.length_replicate]
      exact Nat.pow_le_pow_right (by norm_num) (length_pfacts_le p))
    have hTO : ∀ e ∈ p.methods, p.toProblem.toPos.ReachableName e.1 →
        e.2.toTaskNetwork.IsTotallyOrdered := fun e he hr =>
      hto.2 _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hr⟩
    exact (dp_iff hp hall hTO hto.1).2 hd
  · rintro ⟨hp, hto, hs⟩
    have hall : ∀ v, v ∈ allVecs (pfacts p) (List.replicate (2 ^ sz p) true) ↔
        v.length = (pfacts p).length := fun v => mem_allVecs (by
      rw [List.length_replicate]
      exact Nat.pow_le_pow_right (by norm_num) (length_pfacts_le p))
    have hTO : ∀ e ∈ p.methods, p.toProblem.toPos.ReachableName e.1 →
        e.2.toTaskNetwork.IsTotallyOrdered := fun e he hr =>
      hto.2 _ ⟨(⟨e, he, rfl⟩ : ∃ e' ∈ p.methods, e'.toMethod = e.toMethod), hr⟩
    exact ⟨⟨hp, (classTOB_iff hp).2 hto⟩, (dp_iff hp hall hTO hto.1).1 hs⟩

theorem pt_rootNames : PT rootNames := by
  unfold rootNames
  have htn : PT fun p : ProbDesc => p.tnI := PT.fst.comp (PT.snd.comp PT.snd)
  exact PT.map (g := fun (p : ProbDesc) (x : ℕ) => (lblOf p.tnI x).2)
    (PT.filter (p := fun (p : ProbDesc) (x : ℕ) => (lblOf p.tnI x).1) (PT.fst.comp htn)
      (PT.fst.comp (pt_lblOf (htn.comp PT.fst) PT.snd))) (PT.snd.comp (pt_lblOf (htn.comp PT.fst) PT.snd))

theorem pt_reachSetB : PT reachSetB := by
  unfold reachSetB
  exact PT.filter pt_numsOf (PT.any (pt_rootNames.comp PT.fst) (PT.or (PT.beq PT.snd
    (PT.snd.comp PT.fst)) (pt_reachD.comp (PT.pair (pt_edgesOf.comp (PT.fst.comp PT.fst))
      (PT.pair PT.snd (PT.snd.comp PT.fst))))))

theorem pt_toDec : PT toDec := by
  have hP : PT fun x : ProbDesc × List Bool => x.1 := PT.fst
  have hV := pt_pfacts.comp hP
  have hA := pt_allVecs hV (PT.snd (α := ProbDesc) (β := List Bool))
  have hD := pt_dpTab hP hA
  have hc : PT fun x : ProbDesc × List Bool => classTOB x.1 :=
    (PT.and (pt_toB.comp (PT.fst.comp (PT.snd.comp (PT.snd.comp hP))))
      (pt_methodsRB pt_toB hP (pt_reachSetB.comp hP))).of_eq fun _ => rfl
  have hch := pt_chainSet hA hD (PT.fst.comp (PT.snd.comp (PT.snd.comp hP)))
    (PT.single (pt_vecOf hV (PT.fst.comp (PT.snd.comp hP))))
  have hany := PT.any (p := fun (x : ProbDesc × List Bool) (w : List Bool) =>
      goalB x.1 (sv (pfacts x.1) w)) hch
    (pt_goalB.comp (PT.pair (PT.fst.comp PT.fst) (pt_sv (hV.comp PT.fst) PT.snd)))
  exact (PT.and (PT.and (pt_validB.comp hP) hc) hany).of_eq fun _ => rfl

/-- **Theorem 4.2.1.** `PlanEx^{UNRES ∩ TO}_htn ∈ EXPTIME`. -/
theorem thm_4_2_1 : Cx.EXPTIME (PlanEx fun P => P.IsTO) := by
  have h := inExpTime_codeLang (α := ProbDesc)
    (Q := fun p => p.Valid ∧ p.toProblem.IsTO ∧ p.toProblem.Solvable) pt_toDec Polynomial.X
    fun p => by simp only [Polynomial.eval_X]; exact (toDec_iff p).symm
  exact h

end Article

end HTN
