import HtnComplexity.Article.ProgSpace
import HtnComplexity.Article.AcycRegNP
/-!
# Certificates of tail recursion

A description denotes a `TAIL-REC_h` problem (Defs. 3.9, 3.4) iff its reachable compound names can
be ranked below `h` so that a method of a reachable name does not increase the rank at its last
task and decreases it at every other compound task.  The certificate
(`HTN.Article.TRCert`) is a list `R` of names closed under reachability with ranks; the check
`HTN.Article.trB` is polynomial time.

* `HTN.Article.TRCert.isTailREC_h` — soundness, with the order by rank;
* `HTN.Article.exists_trCert` — completeness, with the ranks of a height function;
* `HTN.Article.isTailREC_h_of_isTailREC` — a `≤_r`-stratification of a description has height at
  most the number of its numbers (the reachable names are among them).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-- `x` is a last task of the network description `t`. -/
def lastB (t : TnDesc) (x : ℕ) : Bool := t.ids.all fun y => (y == x) || decide ((y, x) ∈ t.ordList)

theorem lastB_iff {prim : ℕ → Prop} {t : TnDesc} (ht : TnValid prim t) {x : ℕ} (hx : x ∈ t.ids) :
    lastB t x = true ↔ t.toTaskNetwork.IsLastId x := by
  unfold lastB TaskNetwork.IsLastId
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, mem_T_iff]
  constructor
  · intro h
    refine ⟨hx, fun y hy hyx => ?_⟩
    rcases h y hy with h | h
    · exact absurd h hyx
    · exact (ht.ordOf_iff).2 h
  · rintro ⟨-, h⟩ y hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr ((ht.ordOf_iff).1 (h y hy hyx))

/-- **A certificate of tail recursion of height `h`.** -/
structure TRCert (p : ProbDesc) (R : List ℕ) (rk : ℕ → ℕ) (h : ℕ) : Prop where
  init : ∀ x ∈ p.tnI.ids, ∀ c, lblOf p.tnI x = (true, c) → c ∈ R
  step : ∀ e ∈ p.methods, e.1 ∈ R → ∀ x ∈ e.2.ids, ∀ c, lblOf e.2 x = (true, c) →
    c ∈ R ∧ (lastB e.2 x = true → rk c ≤ rk e.1) ∧ (lastB e.2 x = false → rk c < rk e.1)
  bound : ∀ c ∈ R, rk c < h

/-- **The check of a certificate of tail recursion.** -/
def trB (h : ℕ) (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  x.1.tnI.ids.all (fun y => !(lblOf x.1.tnI y).1 || decide ((lblOf x.1.tnI y).2 ∈ x.2.1)) &&
    x.1.methods.all (fun e => !decide (e.1 ∈ x.2.1) || e.2.ids.all fun y => !(lblOf e.2 y).1 ||
      (decide ((lblOf e.2 y).2 ∈ x.2.1) &&
        bif lastB e.2 y then decide (kidOf x.2.2 (lblOf e.2 y).2 ≤ kidOf x.2.2 e.1)
          else decide (kidOf x.2.2 (lblOf e.2 y).2 < kidOf x.2.2 e.1))) &&
    x.2.1.all fun c => decide (kidOf x.2.2 c < h)

/-- The check without the bound on the ranks. -/
def trCore (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) : Bool :=
  x.1.tnI.ids.all (fun y => !(lblOf x.1.tnI y).1 || decide ((lblOf x.1.tnI y).2 ∈ x.2.1)) &&
    x.1.methods.all (fun e => !decide (e.1 ∈ x.2.1) || e.2.ids.all fun y => !(lblOf e.2 y).1 ||
      (decide ((lblOf e.2 y).2 ∈ x.2.1) &&
        bif lastB e.2 y then decide (kidOf x.2.2 (lblOf e.2 y).2 ≤ kidOf x.2.2 e.1)
          else decide (kidOf x.2.2 (lblOf e.2 y).2 < kidOf x.2.2 e.1)))

theorem trB_eq (h : ℕ) (x : ProbDesc × (List ℕ × List (ℕ × ℕ))) :
    trB h x = (trCore x && x.2.1.all fun c => decide (kidOf x.2.2 c < h)) := rfl

theorem trB_iff (h : ℕ) (p : ProbDesc) (R : List ℕ) (rkL : List (ℕ × ℕ)) :
    trB h (p, R, rkL) = true ↔ TRCert p R (kidOf rkL) h := by
  unfold trB
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun x hx c hc => ?_, fun e he hR x hx c hc => ?_, h3⟩
    · rcases h1 x hx with h | h
      · rw [hc] at h; cases h
      · rw [hc] at h; exact h
    · rcases h2 e he with h | h
      · exact absurd hR h
      · rcases h x hx with h' | ⟨h', h''⟩
        · rw [hc] at h'; cases h'
        · rw [hc] at h' h''
          refine ⟨h', fun hl => ?_, fun hl => ?_⟩
          · simpa [hl] using h''
          · simpa [hl] using h''
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun x hx => ?_, fun e he => ?_⟩, h3⟩
    · rcases hl : lblOf p.tnI x with ⟨_ | _, c⟩
      · exact Or.inl rfl
      · exact Or.inr (h1 x hx c hl)
    · by_cases hR : e.1 ∈ R
      · refine Or.inr fun x hx => ?_
        rcases hl : lblOf e.2 x with ⟨_ | _, c⟩
        · exact Or.inl rfl
        · obtain ⟨hc, hle, hlt⟩ := h2 e he hR x hx c hl
          refine Or.inr ⟨hc, ?_⟩
          cases hb : lastB e.2 x
          · simpa using hlt hb
          · simpa using hle hb
      · exact Or.inl hR

theorem pt_trCore : PT trCore := by
  have hp : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) => x.1 := PT.fst
  have hR : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) => x.2.1 := PT.fst.comp PT.snd
  have hrk : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) => x.2.2 := PT.snd.comp PT.snd
  have htn : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) => x.1.tnI :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp hp))
  have hA : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) =>
      x.1.tnI.ids.all (fun y => !(lblOf x.1.tnI y).1 || decide ((lblOf x.1.tnI y).2 ∈ x.2.1)) :=
    PT.all (PT.fst.comp htn) (PT.or (PT.not (PT.fst.comp (pt_lblOf (htn.comp PT.fst) PT.snd)))
      (PT.elem (hR.comp PT.fst) (PT.snd.comp (pt_lblOf (htn.comp PT.fst) PT.snd))))
  -- context `((x, e), y)`
  have hT : PT fun q : ((ProbDesc × (List ℕ × List (ℕ × ℕ))) × MethodDesc) × ℕ => q.1.2.2 :=
    PT.snd.comp (PT.snd.comp PT.fst)
  have hl := pt_lblOf hT PT.snd
  have hrk2 : PT fun q : ((ProbDesc × (List ℕ × List (ℕ × ℕ))) × MethodDesc) × ℕ => q.1.1.2.2 :=
    hrk.comp (PT.fst.comp PT.fst)
  have hlast : PT fun q : ((ProbDesc × (List ℕ × List (ℕ × ℕ))) × MethodDesc) × ℕ =>
      lastB q.1.2.2 q.2 := by
    unfold lastB
    exact PT.all (PT.fst.comp hT) (PT.or (PT.beqL PT.snd (PT.snd.comp PT.fst))
      (PT.elemL (PT.fst.comp (PT.snd.comp (hT.comp PT.fst))) (PT.pair PT.snd (PT.snd.comp PT.fst))))
  have hkc := pt_kidOf hrk2 (PT.snd.comp hl)
  have hke := pt_kidOf hrk2 (PT.fst.comp (PT.snd.comp PT.fst))
  have hin : PT fun q : ((ProbDesc × (List ℕ × List (ℕ × ℕ))) × MethodDesc) × ℕ =>
      !(lblOf q.1.2.2 q.2).1 || (decide ((lblOf q.1.2.2 q.2).2 ∈ q.1.1.2.1) &&
        bif lastB q.1.2.2 q.2 then decide (kidOf q.1.1.2.2 (lblOf q.1.2.2 q.2).2 ≤ kidOf q.1.1.2.2 q.1.2.1)
          else decide (kidOf q.1.1.2.2 (lblOf q.1.2.2 q.2).2 < kidOf q.1.1.2.2 q.1.2.1)) :=
    PT.or (PT.not (PT.fst.comp hl)) (PT.and (PT.elem (hR.comp (PT.fst.comp PT.fst)) (PT.snd.comp hl))
      (PT.cond hlast (PT.le hkc hke) (PT.lt hkc hke)))
  have hB : PT fun x : ProbDesc × (List ℕ × List (ℕ × ℕ)) =>
      x.1.methods.all (fun e => !decide (e.1 ∈ x.2.1) || e.2.ids.all fun y => !(lblOf e.2 y).1 ||
        (decide ((lblOf e.2 y).2 ∈ x.2.1) &&
          bif lastB e.2 y then decide (kidOf x.2.2 (lblOf e.2 y).2 ≤ kidOf x.2.2 e.1)
            else decide (kidOf x.2.2 (lblOf e.2 y).2 < kidOf x.2.2 e.1))) :=
    PT.all (PT.snd.comp (PT.fst.comp hp)) (PT.or (PT.not (PT.elem (hR.comp PT.fst)
      (PT.fst.comp PT.snd))) (PT.all (p := fun (r : (ProbDesc × (List ℕ × List (ℕ × ℕ))) × MethodDesc)
        (y : ℕ) => !(lblOf r.2.2 y).1 || (decide ((lblOf r.2.2 y).2 ∈ r.1.2.1) &&
          bif lastB r.2.2 y then decide (kidOf r.1.2.2 (lblOf r.2.2 y).2 ≤ kidOf r.1.2.2 r.2.1)
            else decide (kidOf r.1.2.2 (lblOf r.2.2 y).2 < kidOf r.1.2.2 r.2.1)))
        (PT.fst.comp (PT.snd.comp PT.snd)) hin))
  exact (PT.and hA hB).of_eq fun _ => rfl

/-- The check, with the height as an input. -/
theorem pt_trBH : PT fun x : (ProbDesc × (List ℕ × List (ℕ × ℕ))) × ℕ => trB x.2 x.1 := by
  have hR : PT fun x : (ProbDesc × (List ℕ × List (ℕ × ℕ))) × ℕ => x.1.2.1 :=
    PT.fst.comp (PT.snd.comp PT.fst)
  have hrk : PT fun x : (ProbDesc × (List ℕ × List (ℕ × ℕ))) × ℕ => x.1.2.2 :=
    PT.snd.comp (PT.snd.comp PT.fst)
  exact (PT.and (pt_trCore.comp PT.fst) (PT.all (p := fun (x : (ProbDesc × (List ℕ × List (ℕ × ℕ))) × ℕ)
    (c : ℕ) => decide (kidOf x.1.2.2 c < x.2)) hR (PT.lt (pt_kidOf (hrk.comp PT.fst) PT.snd)
    (PT.snd.comp PT.fst)))).of_eq fun x => (trB_eq _ _).symm

theorem pt_trB (h : ℕ) : PT (trB h) :=
  (pt_trBH.comp (PT.pair PT.id (PT.const h))).of_eq fun _ => rfl

/-! ### Soundness -/

/-- **A list closed under reachability contains the reachable names.** -/
theorem reach_mem_of_closed {p : ProbDesc} {R : List ℕ}
    (hinit : ∀ x ∈ p.tnI.ids, ∀ c, lblOf p.tnI x = (true, c) → c ∈ R)
    (hstep : ∀ e ∈ p.methods, e.1 ∈ R → ∀ x ∈ e.2.ids, ∀ c, lblOf e.2 x = (true, c) → c ∈ R)
    {c : ℕ} (hc : p.toProblem.toPos.ReachableName c) : c ∈ R := by
  induction hc with
  | @tnI t c ht hc =>
    have ht' : t ∈ p.tnI.ids := by
      simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using ht
    exact hinit _ ht' _ (label_eq_inr.1 hc)
  | @method m t c hm hr ht hc ih =>
    obtain ⟨e, he, rfl⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    exact hstep e he ih _ ht' _ (label_eq_inr.1 hc)

theorem TRCert.reach_mem {p : ProbDesc} {R : List ℕ} {rk : ℕ → ℕ} {h : ℕ} (hc : TRCert p R rk h)
    {c : ℕ} (hr : p.toProblem.toPos.ReachableName c) : c ∈ R :=
  reach_mem_of_closed hc.init (fun e he hR x hx c hl => (hc.step e he hR x hx c hl).1) hr

/-- **A certificate gives a `≤_r`-stratification of height at most `h`.** -/
theorem TRCert.isTailREC_h {p : ProbDesc} (hp : p.Valid) {R : List ℕ} {rk : ℕ → ℕ} {h : ℕ}
    (hc : TRCert p R rk h) : p.toProblem.IsTailREC_h h := by
  refine ⟨fun c c' => rk c ≤ rk c', ⟨⟨fun c _ => le_rfl, fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂,
    fun c c' _ _ => le_total _ _⟩, fun m hm t ht hlast c hα => ?_, fun m hm t ht hlast c hα => ?_⟩,
    rk, fun c hr => hc.bound c (hc.reach_mem hr), fun _ _ _ _ => Iff.rfl⟩
  · obtain ⟨⟨e, he, rfl⟩, hr⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    exact (hc.step e he (hc.reach_mem hr) t ht' c (label_eq_inr.1 hα)).2.1
      ((lastB_iff (hp.methods e he) ht').2 hlast)
  · obtain ⟨⟨e, he, rfl⟩, hr⟩ := hm
    have ht' : t ∈ e.2.ids := by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using ht
    have hb : lastB e.2 t = false := by
      cases hb : lastB e.2 t
      · rfl
      · exact absurd ((lastB_iff (hp.methods e he) ht').1 hb) hlast
    have := (hc.step e he (hc.reach_mem hr) t ht' c (label_eq_inr.1 hα)).2.2 hb
    exact ⟨this.le, by show ¬ rk e.1 ≤ rk c; omega⟩

/-! ### Completeness -/

open Classical in
/-- **Completeness of certificates of tail recursion**, with their size. -/
theorem exists_trCert {p : ProbDesc} (hp : p.Valid) {h : ℕ} (hh : p.toProblem.IsTailREC_h h) :
    ∃ (R : List ℕ) (rkL : List (ℕ × ℕ)), trB h (p, R, rkL) = true ∧ (∀ c ∈ R, c ∈ numsOf p) ∧
      R.length ≤ (numsOf p).length ∧ (∀ q ∈ rkL, q.1 ∈ numsOf p ∧ q.2 < h) ∧
      rkL.length ≤ (numsOf p).length ∧ ∀ c ∈ R, p.toProblem.toPos.ReachableName c := by
  obtain ⟨le, hle, f, hf, hfle⟩ := hh
  let Rch := p.toProblem.toPos.ReachableName
  let R := (numsOf p).dedup.filter fun c => decide (Rch c)
  have hRmem : ∀ c, Rch c → c ∈ R := fun c h1 =>
    List.mem_filter.2 ⟨List.mem_dedup.2 (reach_numsOf hp h1), by simpa using h1⟩
  have hRch : ∀ c ∈ R, Rch c := fun c hc => by simpa using (List.mem_filter.1 hc).2
  have hRlen : R.length ≤ (numsOf p).length :=
    (List.length_filter_le _ _).trans (List.dedup_sublist _).length_le
  have hk : ∀ c ∈ R, kidOf (R.map fun c => (c, f c)) c = f c := fun c hc => kidOf_map_pair _ hc
  refine ⟨R, R.map fun c => (c, f c), (trB_iff h p _ _).2 ⟨fun x hx c hc => ?_,
    fun e he hR x hx c hc => ?_, fun c hc => by rw [hk c hc]; exact hf c (hRch c hc)⟩,
    fun c hc => List.mem_dedup.1 (List.mem_filter.1 hc).1, hRlen, fun q hq => ?_,
    by rw [List.length_map]; exact hRlen, hRch⟩
  · have hxT : x ∈ p.toProblem.toPos.tnI.T := by
      simpa [Problem.toPos, ProbDesc.toProblem, TnDesc.toTaskNetwork] using hx
    exact hRmem c (HTN.Problem.ReachableName.tnI hxT (label_eq_inr.2 hc))
  · have hr : Rch e.1 := hRch _ hR
    have hα : (MethodDesc.toMethod e).subtasks.α x = Sum.inr c := label_eq_inr.2 hc
    have hxT : x ∈ (MethodDesc.toMethod e).subtasks.T := by
      simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx
    have hm : p.toProblem.toPos.ReachableMethod (MethodDesc.toMethod e) :=
      ⟨show MethodDesc.toMethod e ∈ p.toProblem.methods from ⟨e, he, rfl⟩, hr⟩
    have hrc : Rch c := HTN.Problem.ReachableName.method hm.1 hr hxT hα
    refine ⟨hRmem c hrc, fun hl => ?_, fun hl => ?_⟩
    · rw [hk c (hRmem c hrc), hk e.1 hR]
      exact (hfle c e.1 hrc hr).1 (hle.last _ hm x hxT ((lastB_iff (hp.methods e he) hx).1 hl) c hα)
    · rw [hk c (hRmem c hrc), hk e.1 hR]
      have hnl : ¬ (MethodDesc.toMethod e).subtasks.IsLastId x := fun h' => by
        have := (lastB_iff (hp.methods e he) hx).2 h'
        rw [this] at hl; cases hl
      obtain ⟨h1, h2⟩ := hle.nonlast _ hm x hxT hnl c hα
      have := (hfle c e.1 hrc hr).1 h1
      have := mt (hfle e.1 c hr hrc).2 h2
      omega
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    exact ⟨List.mem_dedup.1 (List.mem_filter.1 hc).1, hf c (hRch c hc)⟩

open Classical in
/-- **A tail-recursive description has a stratification of height at most the number of its
numbers.** -/
theorem isTailREC_h_of_isTailREC {p : ProbDesc} (hp : p.Valid) (h : p.toProblem.IsTailREC) :
    p.toProblem.IsTailREC_h (numsOf p).length := by
  obtain ⟨le, hle⟩ := h
  let Rch := p.toProblem.toPos.ReachableName
  let f : ℕ → ℕ := fun c => ((numsOf p).toFinset.filter fun c' => Rch c' ∧ le c' c ∧ ¬ le c c').card
  have hs := hle.strat
  refine ⟨le, hle, f, fun c hc => ?_, fun c c' hc hc' => ⟨fun hcc' => ?_, fun hf => ?_⟩⟩
  · refine lt_of_lt_of_le (Finset.card_lt_card ((Finset.ssubset_iff_of_subset
      (Finset.filter_subset _ _)).2 ⟨c, List.mem_toFinset.2 (reach_numsOf hp hc), fun h' => ?_⟩))
      (List.toFinset_card_le _)
    have := (Finset.mem_filter.1 h').2
    exact this.2.2 this.2.1
  · refine Finset.card_le_card fun c'' hc'' => ?_
    obtain ⟨hN, hr'', h1, h2⟩ := Finset.mem_filter.1 hc''
    exact Finset.mem_filter.2 ⟨hN, hr'', hs.trans _ _ _ hr'' hc hc' h1 hcc',
      fun h3 => h2 (hs.trans _ _ _ hc hc' hr'' hcc' h3)⟩
  · by_contra hn
    have hlt : le c' c := (hs.total c c' hc hc').resolve_left hn
    have : (((numsOf p).toFinset.filter fun c'' => Rch c'' ∧ le c'' c' ∧ ¬ le c' c'') ⊂
        ((numsOf p).toFinset.filter fun c'' => Rch c'' ∧ le c'' c ∧ ¬ le c c'')) := by
      refine (Finset.ssubset_iff_of_subset fun c'' hc'' => ?_).2
        ⟨c', Finset.mem_filter.2 ⟨List.mem_toFinset.2 (reach_numsOf hp hc'), hc', hlt, hn⟩,
          fun h' => ?_⟩
      · obtain ⟨hN, hr'', h1, h2⟩ := Finset.mem_filter.1 hc''
        exact Finset.mem_filter.2 ⟨hN, hr'', hs.trans _ _ _ hr'' hc' hc h1 hlt,
          fun h3 => h2 (hs.trans _ _ _ hc' hc hr'' hlt h3)⟩
      · have := (Finset.mem_filter.1 h').2
        exact this.2.2 this.2.1
    have h2 : f c' < f c := Finset.card_lt_card this
    change f c ≤ f c' at hf
    omega

end Article

end HTN
