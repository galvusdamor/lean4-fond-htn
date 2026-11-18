import HtnComplexity.Article.AProgDesc
/-!
# TIHTN plan existence by acyclic progression in polynomial space

* `HTN.Article.pt_asuccs` — the successors of a configuration of acyclic progression are computed
  in polynomial time;
* `HTN.Article.sz_acfg_le` — a TIHTN progression bound `n` bounds the reachable configurations by
  `60 (n + |p| + 1)³`;
* **`HTN.Article.inPSpace_planExTI`** — if a polynomial-time check of polynomial certificates
  decides the class `Y`, and its problems have polynomial TIHTN progression bounds, then
  `PlanEx^Y_tihtn ∈ PSPACE`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Polynomial time -/

theorem ancOf_eq (l : List (ℕ × List ℕ)) (x : ℕ) :
    ancOf l x = ((l.filter fun q => q.1 == x).headI).2 := by
  unfold ancOf
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k, b⟩ := q
    by_cases h : k = x
    · subst h; simp [List.lookup]
    · have h' : (x == k) = false := by simpa using Ne.symm h
      simp [List.lookup, h', h, ih]

theorem pt_ancOf {α : Type} [BEnc α] {L : α → List (ℕ × List ℕ)} {X : α → ℕ} (hL : PT L)
    (hX : PT X) : PT fun a => ancOf (L a) (X a) :=
  (PT.snd.comp (PT.headI (PT.filter (p := fun a (q : ℕ × List ℕ) => q.1 == X a) hL
    (PT.beq (PT.fst.comp PT.snd) (hX.comp PT.fst))))).of_eq fun a => (ancOf_eq _ _).symm

theorem pt_ancOK : PT fun x : MethodDesc × List ℕ => ancOK x.1 x.2 := by
  unfold ancOK
  have hl := pt_lblOf (α := (MethodDesc × List ℕ) × ℕ) (PT.snd.comp (PT.fst.comp PT.fst)) PT.snd
  exact PT.all (PT.fst.comp (PT.snd.comp PT.fst)) (PT.or (PT.not (PT.fst.comp hl))
    (PT.not (PT.elem (PT.snd.comp PT.fst) (PT.snd.comp hl))))

theorem asuccs_eq (p : ProbDesc) (c : ACfg) :
    asuccs p c = c.1.2.ids.flatMap (asuccsAt p c) ++ ainserts p c := rfl

theorem pt_asuccs : PT fun x : ProbDesc × ACfg => asuccs x.1 x.2 := by
  -- context `(x, y)` with `x = (p, c)` and `y` an id
  have hp : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.1 := PT.fst.comp PT.fst
  have hs : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.2.1.1 :=
    PT.fst.comp (PT.fst.comp (PT.snd.comp PT.fst))
  have hd : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.2.1.2 :=
    PT.snd.comp (PT.fst.comp (PT.snd.comp PT.fst))
  have han : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.2.2 := PT.snd.comp (PT.snd.comp PT.fst)
  have hy : PT fun r : (ProbDesc × ACfg) × ℕ => r.2 := PT.snd
  have hl : PT fun r : (ProbDesc × ACfg) × ℕ => lblOf r.1.2.1.2 r.2 := pt_lblOf hd hy
  have hanx : PT fun r : (ProbDesc × ACfg) × ℕ => ancOf r.1.2.2 r.2 := pt_ancOf han hy
  have hall : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.2.1.2.ordList.all fun q => q.2 != r.2 :=
    PT.all (PT.fst.comp (PT.snd.comp hd)) ((PT.not (PT.beqL (PT.snd.comp PT.snd)
      (hy.comp PT.fst))).of_eq fun _ => rfl)
  have hfil : PT fun r : (ProbDesc × ACfg) × ℕ => r.1.2.2.filter fun q => decide (q.1 ≠ r.2) :=
    PT.filter han ((PT.not (PT.eq (PT.fst.comp PT.snd) (hy.comp PT.fst))).of_eq fun _ => by simp)
  -- context `(r, e)`
  have hfr : PT fun z : ((ProbDesc × ACfg) × ℕ) × MethodDesc =>
      freshIds z.1.1.2.1.2.ids z.2.2.ids.length :=
    pt_freshIds (PT.fst.comp (hd.comp PT.fst)) (PT.fst.comp (PT.snd.comp PT.snd))
  have hnewanc : PT fun z : ((ProbDesc × ACfg) × ℕ) × MethodDesc =>
      (freshIds z.1.1.2.1.2.ids z.2.2.ids.length).map
        fun n => (n, ((lblOf z.1.1.2.1.2 z.1.2).2 :: ancOf z.1.1.2.2 z.1.2).dedup) :=
    PT.map (g := fun (z : ((ProbDesc × ACfg) × ℕ) × MethodDesc) (n : ℕ) =>
      (n, ((lblOf z.1.1.2.1.2 z.1.2).2 :: ancOf z.1.1.2.2 z.1.2).dedup)) hfr
      (PT.pair PT.snd (PT.dedup (PT.cons (PT.snd.comp (hl.comp (PT.fst.comp PT.fst)))
        (hanx.comp (PT.fst.comp PT.fst)))))
  have hmeth : PT fun r : (ProbDesc × ACfg) × ℕ =>
      (r.1.1.methods.filter fun e => e.1 == (lblOf r.1.2.1.2 r.2).2 && ancOK e (ancOf r.1.2.2 r.2)).map
        fun e => ((r.1.2.1.1, decDesc r.1.2.1.2 r.2 e), (r.1.2.2.filter fun q => decide (q.1 ≠ r.2)) ++
          (freshIds r.1.2.1.2.ids e.2.ids.length).map
            fun n => (n, ((lblOf r.1.2.1.2 r.2).2 :: ancOf r.1.2.2 r.2).dedup)) :=
    PT.map (PT.filter (p := fun r (e : MethodDesc) => e.1 == (lblOf r.1.2.1.2 r.2).2 &&
        ancOK e (ancOf r.1.2.2 r.2)) (PT.snd.comp (PT.fst.comp hp))
      (PT.and (PT.beqL (PT.fst.comp PT.snd) (PT.snd.comp (hl.comp PT.fst)))
        (pt_ancOK.comp (PT.pair PT.snd (hanx.comp PT.fst)))))
      (PT.pair (PT.pair (hs.comp PT.fst) (pt_decDesc.comp (PT.pair (hd.comp PT.fst)
        (PT.pair (hy.comp PT.fst) PT.snd)))) (PT.append (hfil.comp PT.fst) hnewanc))
  have hrun : PT fun r : (ProbDesc × ACfg) × ℕ =>
      runStep r.1.1 (true, r.1.2.1.1) (lblOf r.1.2.1.2 r.2).2 :=
    pt_runStep.comp (PT.pair (PT.pair hp (PT.const ([] : List ℕ)))
      (PT.pair (PT.pair (PT.const true) hs) (PT.snd.comp hl)))
  have hin : PT fun r : (ProbDesc × ACfg) × ℕ => asuccsAt r.1.1 r.1.2 r.2 :=
    (PT.cond hall (PT.cond (PT.fst.comp hl) hmeth (PT.cond (PT.fst.comp hrun)
      (PT.single (PT.pair (PT.pair (PT.dedup (PT.snd.comp hrun)) (pt_progDesc.comp (PT.pair hd hy)))
        hfil)) (PT.const ([] : List ACfg)))) (PT.const ([] : List ACfg))).of_eq fun r => by
        simp only [asuccsAt, cond_eq_if]
  have hA := PT.flatMap (g := fun (x : ProbDesc × ACfg) (y : ℕ) => asuccsAt x.1 x.2 y)
    (PT.fst.comp (PT.snd.comp (PT.fst.comp PT.snd))) hin
  -- insertions, context `(x, a)`
  have hrunI : PT fun r : (ProbDesc × ACfg) × ActDesc => runStep r.1.1 (true, r.1.2.1.1) r.2.1 :=
    pt_runStep.comp (PT.pair (PT.pair (PT.fst.comp PT.fst) (PT.const ([] : List ℕ)))
      (PT.pair (PT.pair (PT.const true) (PT.fst.comp (PT.fst.comp (PT.snd.comp PT.fst))))
        (PT.fst.comp PT.snd)))
  have hinsI : PT fun r : (ProbDesc × ACfg) × ActDesc =>
      if (runStep r.1.1 (true, r.1.2.1.1) r.2.1).1 then
        [(((runStep r.1.1 (true, r.1.2.1.1) r.2.1).2.dedup, r.1.2.1.2), r.1.2.2)] else [] :=
    (PT.cond (PT.fst.comp hrunI) (PT.single (PT.pair (PT.pair (PT.dedup (PT.snd.comp hrunI))
      (PT.snd.comp (PT.fst.comp (PT.snd.comp PT.fst)))) (PT.snd.comp (PT.snd.comp PT.fst))))
      (PT.const ([] : List ACfg))).of_eq fun r => by simp only [cond_eq_if]
  have hI := PT.flatMap (g := fun (x : ProbDesc × ACfg) (a : ActDesc) =>
      if (runStep x.1 (true, x.2.1.1) a.1).1 then
        [(((runStep x.1 (true, x.2.1.1) a.1).2.dedup, x.2.1.2), x.2.2)] else [])
    (PT.fst.comp (PT.fst.comp PT.fst)) hinsI
  exact (PT.append hA hI).of_eq fun x => (asuccs_eq _ _).symm

theorem pt_initACfg : PT initACfg := by
  unfold initACfg
  refine PT.pair pt_initCfg ?_
  have hl := pt_lblOf (α := ProbDesc × ℕ) (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))) PT.snd
  exact PT.map (PT.fst.comp (PT.fst.comp (PT.snd.comp PT.snd))) (PT.pair PT.snd
    ((PT.cond (PT.fst.comp hl) (PT.single (PT.snd.comp hl)) (PT.const ([] : List ℕ))).of_eq
      fun _ => by simp only [cond_eq_if]; rfl))

/-! ### Sizes -/

theorem length_ids_le_a {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsTIHTNProgBound n)
    {c : ACfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c) :
    c.1.2.ids.length ≤ n := by
  obtain ⟨hc, -, nd, hnd, -, hag, -⟩ := acfgReach_sound hp hrc
  have := hb nd hnd
  rw [hag.1] at this
  simpa [cfgNet, List.toFinset_card_of_nodup hc.ids_nodup] using this

theorem acfgReach_nums {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsTIHTNProgBound n)
    {c : ACfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c) :
    CfgNums p (n + sz p) c.1 ∧ ∀ q ∈ c.2, ∀ a ∈ q.2, a ∈ numsOf p := by
  induction hrc with
  | refl =>
    refine ⟨⟨fun x hx => Or.inl (mem_numsOf_tnI (List.mem_append_left _ hx)), fun q hq => ?_,
      fun f hf => ?_⟩, fun q hq a ha => ?_⟩
    · exact mem_numsOf_tnI (List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩))
    · simp only [initACfg, initCfg, List.mem_dedup] at hf
      simp [pfacts, hf]
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      split_ifs at ha with hlb
      · rw [List.mem_singleton] at ha
        subst ha
        exact mem_numsOf_tnI (List.mem_append_right _ (lblOf_mem hp.tnI hx))
      · simp at ha
  | @tail c₁ c₂ hr hs ih =>
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ih
    have hlen := length_ids_le_a hp hb hr
    rcases mem_asuccs.1 hs with ⟨x, hx, hu, ⟨e, he, hl, -, rfl⟩ | ⟨a, hl, hr', rfl⟩⟩ |
      ⟨a, ha, hr', rfl⟩
    · have hev := hp.methods e he
      refine ⟨⟨fun y hy => ?_, fun q hq => ?_, h3⟩, fun q hq b hb' => ?_⟩
      · rcases List.mem_append.1 hy with hy | hy
        · exact h1 y (List.mem_filter.1 hy).1
        · right
          have := lt_of_mem_freshIds hy
          have := methods_ids_le e he
          omega
      · rcases List.mem_append.1 hq with hq | hq
        · exact h2 q (List.mem_filter.1 hq).1
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
          exact mem_numsOf_method he (List.mem_cons_of_mem _ (List.mem_append_right _
            (lblOf_mem hev hy)))
      · rcases List.mem_append.1 hq with hq | hq
        · exact h4 q (List.mem_filter.1 hq).1 b hb'
        · obtain ⟨n', -, rfl⟩ := List.mem_map.1 hq
          rcases List.mem_cons.1 (List.mem_dedup.1 hb') with rfl | hb'
          · exact mem_numsOf_method he (List.mem_cons_self ..)
          · unfold ancOf at hb'
            rcases hlk : c₁.2.lookup x with _ | L
            · rw [hlk] at hb'; simp at hb'
            · rw [hlk] at hb'
              exact h4 (x, L) (mem_of_lookup_eq_some hlk) b hb'
    · refine ⟨⟨fun y hy => h1 y (List.mem_filter.1 hy).1, fun q hq => h2 q (List.mem_filter.1 hq).1,
        fun f hf => ?_⟩, fun q hq b hb' => h4 q (List.mem_filter.1 hq).1 b hb'⟩
      have : f ∈ {f | f ∈ (runStep p (true, c₁.1.1) a).2} := List.mem_dedup.1 hf
      rw [runStep_state] at this
      exact apply_subset_pfacts p a (fun g hg => h3 g hg) this
    · refine ⟨⟨h1, h2, fun f hf => ?_⟩, h4⟩
      have : f ∈ {f | f ∈ (runStep p (true, c₁.1.1) a.1).2} := List.mem_dedup.1 hf
      rw [runStep_state] at this
      exact apply_subset_pfacts p a.1 (fun g hg => h3 g hg) this

/-- **The size of a reachable configuration of acyclic progression.** -/
theorem sz_acfg_le {p : ProbDesc} (hp : p.Valid) {n : ℕ} (hb : p.toProblem.IsTIHTNProgBound n)
    {c : ACfg} (hrc : Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c) :
    sz c ≤ 60 * (n + sz p + 1) ^ 3 := by
  obtain ⟨hc, hca, -⟩ := acfgReach_sound hp hrc
  obtain ⟨hN, h4⟩ := acfgReach_nums hp hb hrc
  have hL := length_ids_le_a hp hb hrc
  have h1 := sz_cfg_le_of hc hN hL
  obtain ⟨hid0, -, -⟩ := hN
  set S := sz p with hS
  set Z := n + S + 1 with hZ
  set K := 2 * (n + S) + 1 + S with hKdef
  have hK : (numsOf p).length ≤ S := length_numsOf_le p
  have hid : ∀ x ∈ c.1.2.ids, sz x ≤ K := fun x hx => by
    rcases hid0 x hx with h | h
    · have := sz_le_of_mem_numsOf h; omega
    · have := sz_nat_le_of_lt' h; omega
  have hent : ∀ q ∈ c.2, sz q ≤ K + (S * (2 * S + 2) + 1) := fun q hq => by
    rw [sz_prod]
    have e1 := hid q.1 (hca.keys_mem q hq)
    have e2 : sz q.2 ≤ q.2.length * (2 * S + 2) + 1 :=
      sz_list_le fun a ha => sz_le_of_mem_numsOf (h4 q hq a ha)
    have e3 : q.2.length ≤ S :=
      (length_le_of_nodup_sub (hca.vals_nodup q hq) (h4 q hq)).trans hK
    have e4 : q.2.length * (2 * S + 2) ≤ S * (2 * S + 2) := Nat.mul_le_mul_right _ e3
    omega
  have hanl : c.2.length ≤ c.1.2.ids.length := by
    rw [← List.length_map (f := Prod.fst)]
    exact length_le_of_nodup_sub hca.keys_nodup fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact hca.keys_mem q hq
  have h2 : sz c.2 ≤ c.2.length * (2 * (K + (S * (2 * S + 2) + 1)) + 2) + 1 := sz_list_le hent
  have e5 : c.2.length * (2 * (K + (S * (2 * S + 2) + 1)) + 2) ≤ Z * (19 * (Z * Z)) := by
    refine Nat.mul_le_mul (by omega) ?_
    have : S * (2 * S + 2) ≤ Z * (2 * Z) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hZ1 : 1 ≤ Z := by omega
  have hZ3 : 1 ≤ Z ^ 3 := Nat.one_le_pow _ _ hZ1
  have e6 : Z * (19 * (Z * Z)) = 19 * Z ^ 3 := by ring
  rw [show sz c = sz c.1 + sz c.2 from sz_prod _ _]
  omega

/-! ### The search -/

section Gen

variable {β : Type} [BEnc β] [BDec β] [DecidableEq β]

instance decEqAncL : DecidableEq (List (ℕ × List ℕ)) := inferInstance
instance decEqACfg : DecidableEq ACfg := inferInstance

/-- The initial test. -/
def aInit (cB : ProbDesc × β → Bool) (x : ProbDesc × (β × ACfg)) : Bool :=
  validB x.1 && cB (x.1, x.2.1) && decide (x.2.2 = initACfg x.1)

/-- A step. -/
def aStep (x : ProbDesc × (β × ACfg) × (β × ACfg)) : Bool :=
  decide (x.2.2.1 = x.2.1.1) && decide (x.2.2.2 ∈ asuccs x.1 x.2.1.2)

/-- The acceptance test. -/
def aAcc (x : ProbDesc × (β × ACfg)) : Bool := x.2.2.1.2.ids.isEmpty && goalB x.1 x.2.2.1.1

theorem pt_aInit {cB : ProbDesc × β → Bool} (hcB : PT cB) : PT (aInit cB) := by
  have h1 : PT fun x : ProbDesc × (β × ACfg) => validB x.1 := pt_validB.comp PT.fst
  have h2 : PT fun x : ProbDesc × (β × ACfg) => cB (x.1, x.2.1) :=
    hcB.comp (PT.pair PT.fst (PT.fst.comp PT.snd))
  have h3 : PT fun x : ProbDesc × (β × ACfg) => decide (x.2.2 = initACfg x.1) :=
    PT.eq (PT.snd.comp PT.snd) (pt_initACfg.comp PT.fst)
  exact (PT.and (PT.and h1 h2) h3).of_eq fun _ => rfl

theorem pt_aStep : PT (aStep (β := β)) := by
  have h1 : PT fun x : ProbDesc × (β × ACfg) × (β × ACfg) => decide (x.2.2.1 = x.2.1.1) :=
    PT.eq (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.fst.comp PT.snd))
  have hs := pt_asuccs.comp (PT.pair (PT.fst (α := ProbDesc) (β := (β × ACfg) × (β × ACfg)))
    (PT.snd.comp (PT.fst.comp PT.snd)))
  have h2 := PT.elemL hs (PT.snd.comp (PT.snd.comp (PT.snd (α := ProbDesc)
    (β := (β × ACfg) × (β × ACfg)))))
  exact (PT.and h1 h2).of_eq fun _ => rfl

theorem pt_aAcc : PT (aAcc (β := β)) := by
  have h1 : PT fun x : ProbDesc × (β × ACfg) => x.2.2.1.2.ids.isEmpty :=
    PT.isEmpty (PT.fst.comp (PT.snd.comp (PT.fst.comp (PT.snd.comp PT.snd))))
  have h2 := pt_goalB.comp (PT.pair (PT.fst (α := ProbDesc) (β := β × ACfg))
    (PT.fst.comp (PT.fst.comp (PT.snd.comp PT.snd))))
  exact (PT.and h1 h2).of_eq fun _ => rfl

theorem planExTI_iff_search {Y : PClass} {cB : ProbDesc × β → Bool}
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (B : ℕ → ℕ)
    (hcomp : ∀ p : ProbDesc, p.Valid → Y p.toProblem → ∃ b, cB (p, b) = true ∧
      ∃ n, p.toProblem.IsTIHTNProgBound n ∧ sz b + 60 * (n + sz p + 1) ^ 3 ≤ B (sz p))
    (p : ProbDesc) :
    (p.Valid ∧ Y p.toProblem ∧ p.toProblem.SolvableTI) ↔ ∃ c₀ c, sz c₀ ≤ B (sz p) ∧
      aInit cB (p, c₀) = true ∧
      Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ aStep (p, c, c') = true) c₀ c ∧
      aAcc (p, c) = true := by
  constructor
  · rintro ⟨hp, hY, hsol⟩
    obtain ⟨b, hb, n, hn, hB⟩ := hcomp p hp hY
    obtain ⟨c, hrc, hids, hg⟩ := (solvableTI_iff_acfg hp).1 hsol
    have hsz : ∀ c, Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c →
        sz (b, c) ≤ B (sz p) := fun c hc => by
      rw [sz_prod]; have := sz_acfg_le hp hn hc; omega
    refine ⟨(b, initACfg p), (b, c), hsz _ .refl, ?_, ?_, ?_⟩
    · simp [aInit, (validB_iff p).2 hp, hb]
    · have key : ∀ c, Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c →
          Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ aStep (p, c, c') = true)
            (b, initACfg p) (b, c) := by
        intro c hc
        induction hc with
        | refl => exact .refl
        | @tail c₁ c₂ hr hs ih =>
          exact ih.tail ⟨hsz c₂ (hr.tail hs), by simp [aStep, hs]⟩
      exact key c hrc
    · simp [aAcc, hids, hg]
  · rintro ⟨⟨b, c₀⟩, c, -, hi, hr, ha⟩
    simp only [aInit, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hv, hb⟩, rfl⟩ := hi
    have hp := (validB_iff p).1 hv
    refine ⟨hp, hsound p b hp hb, ?_⟩
    have key : ∀ c, Relation.ReflTransGen (fun c c' => sz c' ≤ B (sz p) ∧ aStep (p, c, c') = true)
        (b, initACfg p) c →
        Relation.ReflTransGen (fun c c' => c' ∈ asuccs p c) (initACfg p) c.2 := by
      intro c hc
      induction hc with
      | refl => exact .refl
      | @tail c₁ c₂ _ hs ih =>
        simp only [aStep, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact ih.tail hs.2.2
    simp only [aAcc, Bool.and_eq_true, List.isEmpty_iff] at ha
    exact (solvableTI_iff_acfg hp).2 ⟨c.2, key c hr, ha.1, ha.2⟩

/-- **TIHTN plan existence by acyclic progression is in `PSPACE`** for classes with polynomial
certificates and polynomial TIHTN progression bounds. -/
theorem inPSpace_planExTI {Y : PClass} {cB : ProbDesc × β → Bool} (hcB : PT cB)
    (hsound : ∀ p b, p.Valid → cB (p, b) = true → Y p.toProblem) (r : Polynomial ℕ)
    (hcomp : ∀ p : ProbDesc, p.Valid → Y p.toProblem → (∃ b, cB (p, b) = true ∧
      sz b ≤ r.eval (sz p)) ∧ p.toProblem.IsTIHTNProgBound (r.eval (sz p))) :
    Cx.PSPACE (PlanExTI Y) := by
  let q : Polynomial ℕ := r + 60 * (r + Polynomial.X + 1) ^ 3
  have hq : ∀ n, q.eval n = r.eval n + 60 * (r.eval n + n + 1) ^ 3 := fun n => by simp [q]
  have h := inPSpace_codeLang_of_search (α := ProbDesc) (σ := β × ACfg)
    (Q := fun p => p.Valid ∧ Y p.toProblem ∧ p.toProblem.SolvableTI) (pt_aInit hcB) pt_aStep pt_aAcc q
    fun p => planExTI_iff_search hsound (fun n => q.eval n) (fun p hp hY => by
        obtain ⟨⟨b, hb, hbs⟩, hn⟩ := hcomp p hp hY
        exact ⟨b, hb, _, hn, by show _ ≤ q.eval (sz p); rw [hq]; omega⟩) p
  exact h

end Gen

end Article

end HTN
