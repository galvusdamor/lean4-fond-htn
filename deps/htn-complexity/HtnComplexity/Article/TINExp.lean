import HtnComplexity.Article.AcycNExp
import HtnComplexity.Article.ShortRun
import HtnComplexity.Article.StripsTI
/-!
# TIHTN planning is in NEXPTIME (Thm. 4.2.6, Cor. 4.2.7)

With task insertion, cyclic decompositions can be avoided
(`HTN.Article.Problem.solvableTI_iff_acyc_trees`): a solvable problem has decomposition trees in
which no compound name repeats on a path, hence of height at most the number of names and with
exponentially many nodes (`HTN.Article.size_le_of_pathAcyc`).  The executed plan contains their
yield as a subsequence; by the gap lemma (`HTN.Article.exists_short_gaps`) the inserted actions
between two actions of the yield can be cut down to fewer than `2 ^ |V|`, and undeclared inserted
actions (no-ops) can be dropped.

The certificate is a tree certificate and the plan; the check `HTN.Article.tiB` verifies the
trees, that their yield is a subsequence of the plan (`HTN.Article.subB`, greedy matching), and
the execution of the plan.

* **`HTN.Article.thm_4_2_6`** — `PlanEx^ACYC_tihtn ∈ NEXPTIME`;
* **`HTN.Article.cor_4_2_7`** — `PlanEx^UNRES_tihtn ∈ NEXPTIME`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### The subsequence check -/

/-- One step of greedy matching: drop the head of the remaining pattern if it is `b`. -/
def subStep (r : List ℕ) (b : ℕ) : List ℕ := bif (r.headI == b) && !r.isEmpty then r.tail else r

/-- **The subsequence check.** -/
def subB (as π : List ℕ) : Bool := (π.foldl subStep as).isEmpty

theorem subStep_sublist_iff (as π : List ℕ) (b : ℕ) :
    (subStep as b).Sublist π ↔ as.Sublist (b :: π) := by
  cases as with
  | nil => simp [subStep]
  | cons a as =>
    by_cases hab : a = b
    · subst hab; simp [subStep]
    · have : (a == b) = false := by simpa using hab
      simp only [subStep, List.headI_cons, this, Bool.false_and, cond_false]
      constructor
      · exact fun h => h.cons _
      · intro h
        cases h with
        | cons _ h => exact h
        | cons₂ _ _ => exact absurd rfl hab

theorem subB_iff : ∀ (π as : List ℕ), subB as π = true ↔ as.Sublist π := by
  intro π
  induction π with
  | nil => intro as; simp [subB]
  | cons b π ih =>
    intro as
    unfold subB at ih ⊢
    rw [List.foldl_cons, ih, subStep_sublist_iff]

theorem pt_subB : PT fun x : List ℕ × List ℕ => subB x.1 x.2 := by
  unfold subB
  have hs : PT fun q : (List ℕ × List ℕ) × List ℕ × ℕ => subStep q.2.1 q.2.2 := by
    unfold subStep
    exact PT.cond (PT.and (PT.beqL (PT.headI (PT.fst.comp PT.snd)) (PT.snd.comp PT.snd))
      (PT.not (PT.isEmpty (PT.fst.comp PT.snd)))) (PT.tail (PT.fst.comp PT.snd)) (PT.fst.comp PT.snd)
  refine PT.isEmpty (PT.foldl (α := List ℕ × List ℕ) (β := ℕ) (σ := List ℕ)
    (g := fun _ r b => subStep r b) PT.snd PT.fst hs (c := 0) (d := 0) fun x r b _ => ?_)
  simp only [mul_zero, add_zero, subStep]
  cases (r.headI == b) && !r.isEmpty
  · exact le_rfl
  · show sz r.tail ≤ sz r
    rw [← List.drop_one]; exact sz_drop_le r 1

/-! ### Small path-acyclic trees -/

theorem occurs_numsOf {p : ProbDesc} (hp : p.Valid) : ∀ (dt : DTree ℕ ℕ ℕ) (s : ℕ ⊕ ℕ),
    dt.Valid p.toProblem.methods s → (∀ c, s = Sum.inr c → c ∈ numsOf p) →
    ∀ c, dt.Occurs c → c ∈ numsOf p := by
  intro dt
  induction dt with
  | leaf a => intro s _ _ c hc; cases hc
  | node c m ch ih =>
    intro s hv hs c' hc'
    obtain ⟨rfl, ⟨e, he, rfl⟩, -, hch⟩ := hv.node_inv
    cases hc' with
    | root => exact hs _ rfl
    | @child _ _ _ t ht h =>
      refine ih _ _ (hch _ ht) (fun c'' hc'' => ?_) c' h
      have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
      have := lblOf_mem (hp.methods e he) ht'
      rw [label_eq_inr.1 hc''] at this
      exact mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _ this))

/-- **Path-acyclic trees are small**: a tree all of whose compound names lie in `F` has at most
`(B + 1) ^ (|F| + 1)` nodes. -/
theorem size_le_of_pathAcyc {p : ProbDesc} {B : ℕ} (hB : ∀ e ∈ p.methods, e.2.ids.length ≤ B) :
    ∀ (dt : DTree ℕ ℕ ℕ) (s : ℕ ⊕ ℕ), dt.Valid p.toProblem.methods s → dt.Acyc →
    ∀ F : Finset ℕ, (∀ c, dt.Occurs c → c ∈ F) → dt.size ≤ (B + 1) ^ (F.card + 1) := by
  intro dt
  induction dt with
  | leaf a => intro s _ _ F _; simp only [DTree.size]; exact Nat.one_le_pow _ _ (by omega)
  | node c m ch ih =>
    intro s hv ha F hF
    obtain ⟨-, ⟨e, he, rfl⟩, -, hch⟩ := hv.node_inv
    obtain ⟨hacyc, hno⟩ : (∀ t ∈ (MethodDesc.toMethod e).subtasks.T, (ch t).Acyc) ∧
        ∀ t ∈ (MethodDesc.toMethod e).subtasks.T, ¬ (ch t).Occurs c := by
      cases ha with | node h hn => exact ⟨h, hn⟩
    have hcF : c ∈ F := hF c .root
    have hcard : (F.erase c).card + 1 = F.card := Finset.card_erase_add_one hcF
    have hchild : ∀ t ∈ (MethodDesc.toMethod e).subtasks.T, (ch t).size ≤ (B + 1) ^ F.card := by
      intro t ht
      have := ih t _ (hch t ht) (hacyc t ht) (F.erase c) fun c' hc' =>
        Finset.mem_erase.2 ⟨fun h => hno t ht (h ▸ hc'), hF c' (.child ht hc')⟩
      rwa [hcard] at this
    have hT : (MethodDesc.toMethod e).subtasks.T.card ≤ B :=
      (List.toFinset_card_le _).trans (hB e he)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hchild
    rw [smul_eq_mul] at hsum
    have h1 : (MethodDesc.toMethod e).subtasks.T.card * (B + 1) ^ F.card ≤ B * (B + 1) ^ F.card :=
      Nat.mul_le_mul_right _ hT
    have h2 : 1 ≤ (B + 1) ^ F.card := Nat.one_le_pow _ _ (by omega)
    simp only [DTree.size]
    rw [pow_succ]
    nlinarith

/-! ### The check -/

/-- **The check of Thm. 4.2.6 and Cor. 4.2.7**: well-formedness, the trees, their yield a
subsequence of the plan, the execution of the plan. -/
def tiB (x : ProbDesc × (TCert × List ℕ)) : Bool :=
  validB x.1 && certB x.1 x.2.1 && subB x.2.1.2.2.1 x.2.2 && runB x.1 x.2.2

theorem pt_tiB : PT tiB := by
  have h1 : PT fun x : ProbDesc × (TCert × List ℕ) => validB x.1 := pt_validB.comp PT.fst
  have hc : PT fun x : ProbDesc × (TCert × List ℕ) => x.2.1 := PT.fst.comp PT.snd
  have hπ : PT fun x : ProbDesc × (TCert × List ℕ) => x.2.2 := PT.snd.comp PT.snd
  have h2 := pt_certB.comp (PT.pair PT.fst hc)
  have has : PT fun x : ProbDesc × (TCert × List ℕ) => x.2.1.2.2.1 :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp hc))
  have h3 := pt_subB.comp (PT.pair has hπ)
  have h4 := pt_runB.comp (PT.pair PT.fst hπ)
  refine (PT.and (PT.and (PT.and h1 h2) h3) h4).of_eq fun x => ?_
  rfl

theorem of_tiB {p : ProbDesc} {b : TCert × List ℕ} (h : tiB (p, b) = true) :
    p.Valid ∧ p.toProblem.SolvableTI := by
  obtain ⟨⟨⟨hv, hc⟩, hs⟩, hr⟩ := by simpa only [tiB, Bool.and_eq_true] using h
  have hp := (validB_iff p).1 hv
  refine ⟨hp, ?_⟩
  obtain ⟨trees, htr⟩ := treesYield_of_certB hp hc
  obtain ⟨s, hrun, hg⟩ := (runB_iff p _).1 hr
  exact (Problem.solvableTI_iff_trees p.toProblem (wf_toProblem p)).2
    ⟨trees, _, _, s, htr, (subB_iff _ _).1 hs, hrun, hg⟩

theorem run_filter_of (p : ProbDesc) (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ a, p.Declared a → q a) : ∀ (π : List ℕ) (s s' : Set ℕ), p.toProblem.Run π s s' →
      p.toProblem.Run (π.filter fun a => decide (q a)) s s' := by
  intro π
  induction π with
  | nil => intro s s' h; exact h
  | cons a π ih =>
    intro s s' h
    obtain ⟨happ, hr⟩ := h
    by_cases ha : q a
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      exact ⟨happ, ih _ _ hr⟩
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have hδ : p.toProblem.δ a = ⟨∅, ∅, ∅, ∅⟩ := δ_undeclared fun hd => ha (hq a hd)
      have : (p.toProblem.δ a).apply s = s := by rw [hδ]; simp [Action.apply]
      rw [this] at hr
      exact ih _ _ hr

theorem length_pfacts_le (p : ProbDesc) : (pfacts p).length ≤ sz p := by
  unfold pfacts
  refine (List.dedup_sublist _).length_le.trans ?_
  rw [List.length_append, List.length_flatMap]
  have h1 := length_le_sz p.init
  have h2 : (p.actions.map fun a => a.2.2.2.1.length).sum ≤ (p.actions.map sz).sum := by
    apply List.sum_le_sum
    intro a _
    exact (length_le_sz _).trans
      ((NoHTN.sz_fst_le _).trans ((NoHTN.sz_snd_le _).trans ((NoHTN.sz_snd_le _).trans (NoHTN.sz_snd_le _))))
  have h3 := sum_map_sz_le p.actions
  have h4 := sz_probDesc p
  have h5 : sz p.init = sz p.2.1 := rfl
  omega

theorem sz_le_of_declared {p : ProbDesc} {a : ℕ} (h : p.Declared a) : sz a ≤ sz p := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  have h1 := sz_le_of_mem hx
  have h2 : sz x.1 ≤ sz x := NoHTN.sz_fst_le x
  have h3 := sz_probDesc p
  show sz x.1 ≤ _
  omega

/-- **Completeness of the check, with the size of the certificate.** -/
theorem exists_tiB {p : ProbDesc} (hp : p.Valid) (h : p.toProblem.SolvableTI) :
    ∃ b : TCert × List ℕ, tiB (p, b) = true ∧
      sz b ≤ 1733 * ((sz p + 1) ^ (sz p + 2)) ^ 3 * 2 ^ sz p := by
  classical
  obtain ⟨trees, as, π, s, hTY, hac, hsub, hrun, hg⟩ :=
    (Problem.solvableTI_iff_acyc_trees p.toProblem (wf_toProblem p)).1 h
  obtain ⟨c, hcB, hcas, hclen, hnodes, hroots, hrl, hw, hwl, hasN⟩ := exists_certB hp hTY
  -- drop undeclared insertions, then shorten the gaps
  let q : ℕ → Prop := fun a => p.Declared a ∨ a ∈ numsOf p
  have hrun₁ := run_filter_of p q (fun a ha => Or.inl ha) π _ _ hrun
  have hsub₁ : as.Sublist (π.filter fun a => decide (q a)) := by
    have := hsub.filter (fun a => decide (q a))
    rwa [List.filter_eq_self.2 fun a ha => by simpa [q] using Or.inr (hasN a ha)] at this
  obtain ⟨π₂, hsub₂, hlen₂, hmem₂, hrun₂⟩ :=
    exists_short_gaps p as _ (init_subset_pfacts p) hsub₁ hrun₁
  refine ⟨(c, π₂), ?_, ?_⟩
  · simp only [tiB, Bool.and_eq_true]
    refine ⟨⟨⟨(validB_iff p).2 hp, hcB⟩, ?_⟩, (runB_iff p π₂).2 ⟨s, hrun₂, hg⟩⟩
    rw [hcas]; exact (subB_iff _ _).2 hsub₂
  set S := sz p with hS
  set X := (S + 1) ^ (S + 2) with hXdef
  -- the trees
  have hK : (numsOf p).length ≤ S := length_numsOf_le p
  have htree : ∀ x ∈ p.tnI.ids, (trees x).size ≤ (S + 1) ^ (S + 1) := by
    intro x hx
    have hxT : x ∈ p.toProblem.tnI.T := by
      simpa [ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    have := size_le_of_pathAcyc methods_ids_le (trees x) _ (hTY.1 x hxT) (hac x hxT)
      (numsOf p).toFinset fun c hc => List.mem_toFinset.2 (occurs_numsOf hp _ _ (hTY.1 x hxT)
        (fun c' hc' => reach_numsOf hp (HTN.Problem.ReachableName.tnI
          (P := p.toProblem.toPos) hxT hc')) c hc)
    exact this.trans (Nat.pow_le_pow_right (by omega) (by
      have := List.toFinset_card_le (numsOf p); omega))
  have hids : p.tnI.ids.length ≤ S := (ids_length_le_sz _).trans (by
    have := sz_probDesc p
    omega)
  have hN : c.1.length ≤ S * (S + 1) ^ (S + 1) := by
    rw [hclen]
    have := List.sum_le_card_nsmul (p.tnI.ids.map fun x => (trees x).size) ((S + 1) ^ (S + 1))
      (fun n hn => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
        exact htree x hx)
    rw [List.length_map, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hids)
  have hY : as.length ≤ c.1.length := by
    have := length_le_of_treesYield hTY
    rw [show p.toProblem.tnI.T = p.tnI.ids.toFinset from rfl, List.sum_toFinset _ hp.tnI.nodup]
      at this
    rw [hclen]; exact this
  have hc := sz_cert_le (Y := as.length) hnodes hroots hrl hw hwl (by rw [hcas])
    (by rw [hcas]; exact hasN)
  have hX1 : S + 1 ≤ X := Nat.le_self_pow (by omega) _
  have hNX : c.1.length ≤ X := hN.trans (by
    show S * (S + 1) ^ (S + 1) ≤ (S + 1) ^ (S + 1 + 1)
    calc S * (S + 1) ^ (S + 1) ≤ (S + 1) * (S + 1) ^ (S + 1) := Nat.mul_le_mul (by omega) le_rfl
      _ = (S + 1) ^ (S + 1 + 1) := by ring)
  have hM : c.1.length + as.length + sz p + 1 ≤ 3 * X := by rw [← hS]; omega
  have hM3 : (c.1.length + as.length + sz p + 1) ^ 3 ≤ 27 * X ^ 3 :=
    (Nat.pow_le_pow_left hM 3).trans_eq (by ring)
  -- the plan
  have hV : 2 ^ (pfacts p).length ≤ 2 ^ S := Nat.pow_le_pow_right (by omega) (length_pfacts_le p)
  have hπl : π₂.length ≤ 2 * X * 2 ^ S := by
    have : (as.length + 1) * 2 ^ (pfacts p).length ≤ (2 * X) * 2 ^ S :=
      Nat.mul_le_mul (by omega) hV
    omega
  have hπsz : sz π₂ ≤ π₂.length * (2 * S + 2) + 1 := sz_list_le fun a ha => by
    have := hmem₂ a ha
    rcases (by simpa [q] using (List.mem_filter.1 this).2 : p.Declared a ∨ a ∈ numsOf p) with h | h
    · exact sz_le_of_declared h
    · exact sz_le_of_mem_numsOf h
  have e1 : π₂.length * (2 * S + 2) ≤ (2 * X * 2 ^ S) * (2 * X) := Nat.mul_le_mul hπl (by omega)
  have hpow : 1 ≤ 2 ^ S := Nat.one_le_two_pow
  have hX3 : X * X ≤ X ^ 3 := by
    rw [show X ^ 3 = X * X * X by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
  rw [sz_prod]
  have : (2 * X * 2 ^ S) * (2 * X) = 4 * (X * X) * 2 ^ S := by ring
  have h5 : 4 * (X * X) * 2 ^ S ≤ 4 * X ^ 3 * 2 ^ S := by
    have := Nat.mul_le_mul_right (2 ^ S) (Nat.mul_le_mul_left 4 hX3); linarith
  have h6 : 1728 * X ^ 3 ≤ 1728 * X ^ 3 * 2 ^ S := Nat.le_mul_of_pos_right _ (by omega)
  have h7 : 1 ≤ X ^ 3 * 2 ^ S := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

/-- The exponent of the TIHTN certificate bound. -/
noncomputable def qTI : Polynomial ℕ := 3 * Polynomial.X ^ 2 + 10 * Polynomial.X + 19

theorem eval_qTI (n : ℕ) : qTI.eval n = 3 * n ^ 2 + 10 * n + 19 := by
  simp [qTI]

theorem bound_lt_qTI (S A : ℕ) (hA : A ≤ 2 ^ 11 * ((S + 1) ^ (S + 2)) ^ 3 * 2 ^ S) :
    A < 2 ^ qTI.eval S := by
  have hX : ((S + 1) ^ (S + 2)) ^ 3 ≤ 2 ^ (3 * ((S + 1) * (S + 2))) := by
    rw [pow_mul']
    refine Nat.pow_le_pow_left ?_ 3
    rw [pow_mul]
    exact Nat.pow_le_pow_left (lt_two_pow' (S + 1)).le _
  rw [eval_qTI, show 3 * S ^ 2 + 10 * S + 19 = 11 + 3 * ((S + 1) * (S + 2)) + S + 2 by ring,
    pow_add, pow_add, pow_add]
  have h1 : 2 ^ 11 * ((S + 1) ^ (S + 2)) ^ 3 * 2 ^ S ≤
      2 ^ 11 * 2 ^ (3 * ((S + 1) * (S + 2))) * 2 ^ S :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX)
  have hpos : 0 < 2 ^ 11 * 2 ^ (3 * ((S + 1) * (S + 2))) * 2 ^ S := by positivity
  omega

/-- **Corollary 4.2.7.** `PlanEx^UNRES_tihtn ∈ NEXPTIME`. -/
theorem cor_4_2_7 : Cx.NEXPTIME (PlanExTI UNRES) := by
  have h := inNExp_codeLang (α := ProbDesc) (β := TCert × List ℕ)
    (Q := fun p => p.Valid ∧ UNRES p.toProblem ∧ p.toProblem.SolvableTI) pt_tiB qTI
    fun p => ⟨fun ⟨hp, _, hs⟩ => by
      obtain ⟨b, hb, hsz⟩ := exists_tiB hp hs
      exact ⟨b, bound_lt_qTI _ _ (hsz.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (by norm_num)))), hb⟩,
      fun ⟨b, _, hb⟩ => ⟨(of_tiB hb).1, trivial, (of_tiB hb).2⟩⟩
  exact h

/-- **The check of Thm. 4.2.6**: acyclicity and the TIHTN check. -/
def acycTiB (x : ProbDesc × ((List ℕ × List (ℕ × ℕ)) × TCert × List ℕ)) : Bool :=
  acycB x.1 x.2.1 && tiB (x.1, x.2.2)

theorem pt_acycTiB : PT acycTiB := by
  have h1 := pt_acycB.comp (PT.pair (PT.fst (α := ProbDesc)
    (β := (List ℕ × List (ℕ × ℕ)) × TCert × List ℕ)) (PT.fst.comp PT.snd))
  have h2 := pt_tiB.comp (PT.pair (PT.fst (α := ProbDesc)
    (β := (List ℕ × List (ℕ × ℕ)) × TCert × List ℕ)) (PT.snd.comp PT.snd))
  refine (PT.and h1 h2).of_eq fun x => ?_
  rfl

/-- **Theorem 4.2.6.** `PlanEx^ACYC_tihtn ∈ NEXPTIME`. -/
theorem thm_4_2_6 : Cx.NEXPTIME (PlanExTI fun P => P.IsACYC) := by
  have h := inNExp_codeLang (α := ProbDesc) (β := (List ℕ × List (ℕ × ℕ)) × TCert × List ℕ)
    (Q := fun p => p.Valid ∧ p.toProblem.IsACYC ∧ p.toProblem.SolvableTI) pt_acycTiB qTI
    fun p => ⟨fun ⟨hp, hac, hs⟩ => by
      obtain ⟨b, hb, hsz⟩ := exists_tiB hp hs
      obtain ⟨R, rkL, hab, hRN, hRl, hrkN, hrkl⟩ := exists_acycCert hp hac
      refine ⟨((R, rkL), b), bound_lt_qTI _ _ ?_, by simp [acycTiB, hab, hb]⟩
      show sz ((R, rkL), b) ≤ 2 ^ 11 * ((sz p + 1) ^ (sz p + 2)) ^ 3 * 2 ^ sz p
      set S := sz p
      set X := (S + 1) ^ (S + 2) with hXdef
      have hK : (numsOf p).length ≤ S := length_numsOf_le p
      have hX1 : S + 1 ≤ X := Nat.le_self_pow (by omega) _
      have hR : sz R ≤ R.length * (2 * S + 2) + 1 :=
        sz_list_le fun a ha => sz_le_of_mem_numsOf (hRN a ha)
      have hrkS : sz rkL ≤ rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) + 1 :=
        sz_list_le fun q hq => by
          rw [sz_prod]
          have := sz_le_of_mem_numsOf (hrkN q hq).1
          have := sz_nat_le_of_lt' (show q.2 < S + 1 by have := (hrkN q hq).2; omega)
          omega
      have e1 : R.length * (2 * S + 2) ≤ X * (2 * X) := Nat.mul_le_mul (by omega) (by omega)
      have e2 : rkL.length * (2 * (S + (2 * (S + 1) + 1)) + 2) ≤ X * (8 * X) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hX3 : X * X ≤ X ^ 3 := by
        rw [show X ^ 3 = X * X * X by ring]; exact Nat.le_mul_of_pos_right _ (by omega)
      have hpow : 1 ≤ 2 ^ S := Nat.one_le_two_pow
      have h6 : X ^ 3 ≤ X ^ 3 * 2 ^ S := Nat.le_mul_of_pos_right _ (by omega)
      rw [sz_prod, sz_prod]
      nlinarith,
      fun ⟨b, _, hb⟩ => by
        simp only [acycTiB, Bool.and_eq_true] at hb
        obtain ⟨R, rkL⟩ := b.1
        exact ⟨(of_tiB hb.2).1, ((acycB_iff p _ _).1 hb.1).isACYC, (of_tiB hb.2).2⟩⟩
  exact h

end Article

end HTN
