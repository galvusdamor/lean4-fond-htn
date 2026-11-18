import HtnComplexity.Article.TODP
/-!
# The dynamic program of Thm. 4.2.1 is polynomial time in the padded input

Every function of `HtnComplexity/Article/TODP.lean` is a polynomial-time function of the
description and the list of vectors (`HTN.Article.pt_dpTab`, `HTN.Article.pt_chainSet`); the two
folds (the rounds, the chains) keep their accumulators inside the candidates and the vectors,
whose sizes are polynomial by `HTN.Syn.PolyDom.PT.pb`.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem sv_eq : ∀ (V : List ℕ) (v : List Bool),
    sv V v = ((List.range V.length).filter fun i => v.getI i).map V.getI
  | [], v => by simp [sv]
  | a :: V, [] => by
    simp only [sv, List.zip_nil_right, List.filterMap_nil]
    symm
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro i _; simp
  | a :: V, b :: v => by
    have ih := sv_eq V v
    have hsv : sv (a :: V) (b :: v) = (if b then [a] else []) ++ sv V v := by
      unfold sv; cases b <;> simp
    rw [hsv, ih, List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    cases b <;> simp [Function.comp_def, List.map_map]

variable {α : Type} [BEnc α]

theorem pt_sv {V : α → List ℕ} {v : α → List Bool} (hV : PT V) (hv : PT v) :
    PT fun a => sv (V a) (v a) :=
  (PT.map (g := fun a i => (V a).getI i) (PT.filter (p := fun a (i : ℕ) => (v a).getI i)
    (PT.rangeLength hV) (PT.getI (hv.comp PT.fst) PT.snd)) (PT.getI (hV.comp PT.fst) PT.snd)).of_eq
    fun a => (sv_eq _ _).symm

theorem pt_vecOf {V s : α → List ℕ} (hV : PT V) (hs : PT s) : PT fun a => vecOf (V a) (s a) :=
  PT.map hV (PT.elem (hs.comp PT.fst) PT.snd)

theorem pt_pfacts : PT pfacts := by
  unfold pfacts
  exact PT.dedup (PT.append (PT.fst.comp PT.snd) (PT.flatMap (g := fun (_ : ProbDesc) (a : ActDesc) =>
    a.2.2.2.1) (PT.fst.comp PT.fst) (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))))

theorem pt_runStepC {P : α → ProbDesc} {s : α → List ℕ} {a : α → ℕ} (hP : PT P) (hs : PT s)
    (ha : PT a) : PT fun x => runStep (P x) (true, s x) (a x) :=
  pt_runStep.comp (PT.pair (PT.pair hP (PT.const ([] : List ℕ))) (PT.pair (PT.pair (PT.const true) hs) ha))

theorem pt_okV {P : α → ProbDesc} {a : α → ℕ} {v : α → List Bool} (hP : PT P) (ha : PT a)
    (hv : PT v) : PT fun x => okV (P x) (a x) (v x) :=
  PT.fst.comp (pt_runStepC hP (pt_sv (pt_pfacts.comp hP) hv) ha)

theorem pt_apV {P : α → ProbDesc} {a : α → ℕ} {v : α → List Bool} (hP : PT P) (ha : PT a)
    (hv : PT v) : PT fun x => apV (P x) (a x) (v x) :=
  pt_vecOf (pt_pfacts.comp hP) (PT.snd.comp (pt_runStepC hP (pt_sv (pt_pfacts.comp hP) hv) ha))

theorem pt_stepSet {A : α → List (List Bool)} {X : α → List Trip} {S : α → List (List Bool)}
    {n : α → Bool × ℕ} (hA : PT A) (hX : PT X) (hS : PT S) (hn : PT n) :
    PT fun a => stepSet (A a) (X a) (S a) (n a) := by
  unfold stepSet
  refine PT.filter hA (PT.any (hS.comp PT.fst) ?_)
  exact PT.elemL (hX.comp (PT.fst.comp PT.fst)) (PT.pair PT.snd (PT.pair (hn.comp (PT.fst.comp PT.fst))
    (PT.snd.comp PT.fst)))

/-! ### The linearisation -/

theorem reachB_eq_reachD (E : List (ℕ × ℕ)) (a b : ℕ) : reachB E a b = reachD E a b := by
  rw [Bool.eq_iff_iff, reachB_iff, reachD_iff]

theorem memB_eq (l : List ℕ) (n : ℕ) : memB l n = decide (n ∈ l) := by
  rw [Bool.eq_iff_iff, memB_iff, decide_eq_true_eq]

theorem pt_ordB {t : α → TnDesc} {a b : α → ℕ} (ht : PT t) (ha : PT a) (hb : PT b) :
    PT fun x => TnDesc.ordB (t x) (a x) (b x) := by
  unfold TnDesc.ordB
  simp only [memB_eq, reachB_eq_reachD]
  have hE : PT fun x => (t x).ordList := PT.fst.comp (PT.snd.comp ht)
  exact PT.and (PT.and (PT.and (PT.elem (PT.fst.comp ht) ha) (PT.elem (PT.fst.comp ht) hb))
    (pt_reachD.comp (PT.pair hE (PT.pair ha hb))))
    (PT.not (pt_reachD.comp (PT.pair hE (PT.pair hb ha))))

theorem pt_rank {t : α → TnDesc} {i : α → ℕ} (ht : PT t) (hi : PT i) :
    PT fun x => TnDesc.rank (t x) (i x) := by
  unfold TnDesc.rank
  exact PT.length (PT.filter (PT.fst.comp ht) (pt_ordB (ht.comp PT.fst) PT.snd (hi.comp PT.fst)))

theorem linAt_eq (t : TnDesc) (k : ℕ) :
    TnDesc.linAt t k = t.ids.filter fun i => decide (TnDesc.rank t i = k) := by
  unfold TnDesc.linAt
  induction t.ids with
  | nil => rfl
  | cons i l ih => by_cases h : TnDesc.rank t i = k <;> simp [List.filterMap_cons, h, ih]

theorem lin_eq (t : TnDesc) : TnDesc.lin t =
    (List.range (t.ids.length + 1)).flatMap fun k => (TnDesc.linAt t k).take 1 := by
  unfold TnDesc.lin
  rw [List.filterMap_eq_flatMap_toList]
  refine List.flatMap_congr fun k _ => ?_
  cases TnDesc.linAt t k <;> simp

theorem pt_lin {t : α → TnDesc} (ht : PT t) : PT fun x => TnDesc.lin (t x) := by
  have hL : PT fun q : α × ℕ => TnDesc.linAt (t q.1) q.2 :=
    (PT.filter (p := fun (q : α × ℕ) (i : ℕ) => decide (TnDesc.rank (t q.1) i = q.2))
      (PT.fst.comp (ht.comp PT.fst)) (PT.eq (pt_rank (ht.comp (PT.fst.comp PT.fst)) PT.snd)
        (PT.snd.comp PT.fst))).of_eq fun q => (linAt_eq _ _).symm
  have htake : PT fun q : α × ℕ => (TnDesc.linAt (t q.1) q.2).take 1 :=
    (PT.cond (PT.isEmpty hL) (PT.const []) (PT.single (PT.headI hL))).of_eq fun q => by
      cases h : TnDesc.linAt (t q.1) q.2 <;> simp [h]
  exact (PT.flatMap (g := fun (x : α) (k : ℕ) => (TnDesc.linAt (t x) k).take 1)
    (PT.rangeLength (PT.append (PT.fst.comp ht) (PT.const [0]))) htake).of_eq fun x => by
      rw [lin_eq]; simp; rfl

/-! ### The folds -/

theorem pt_chainSet {A : α → List (List Bool)} {X : α → List Trip} {t : α → TnDesc}
    {S : α → List (List Bool)} (hA : PT A) (hX : PT X) (ht : PT t) (hS : PT S) :
    PT fun a => chainSet (A a) (X a) (t a) (S a) := by
  unfold chainSet
  obtain ⟨c, d, hcd⟩ := hA.pb
  refine PT.foldl (α := α) (β := ℕ) (σ := List (List Bool))
    (g := fun a S x => stepSet (A a) (X a) S (lblOf (t a) x)) (pt_lin ht) hS
    (pt_stepSet (hA.comp PT.fst) (hX.comp PT.fst) (PT.fst.comp PT.snd)
      (pt_lblOf (ht.comp PT.fst) (PT.snd.comp PT.snd))) (c := c) (d := d) fun a S x _ => ?_
  exact (NoHTN.sz_filter_le _ _).trans ((hcd a).trans (Nat.le_add_left _ _))

theorem pt_ruleB {P : α → ProbDesc} {A : α → List (List Bool)} {X : α → List Trip} {q : α → Trip}
    (hP : PT P) (hA : PT A) (hX : PT X) (hq : PT q) : PT fun a => ruleB (P a) (A a) (X a) (q a) := by
  unfold ruleB
  have hv := PT.fst.comp hq
  have hb := PT.fst.comp (PT.fst.comp (PT.snd.comp hq))
  have hx := PT.snd.comp (PT.fst.comp (PT.snd.comp hq))
  have hv' := PT.snd.comp (PT.snd.comp hq)
  refine PT.cond hb (PT.any (PT.snd.comp (PT.fst.comp hP)) (PT.and (PT.beq (PT.fst.comp PT.snd)
    (hx.comp PT.fst)) (PT.elemL (pt_chainSet (hA.comp PT.fst) (hX.comp PT.fst)
      (PT.snd.comp PT.snd) (PT.single (hv.comp PT.fst))) (hv'.comp PT.fst))))
    (PT.and (pt_okV hP hx hv) (PT.beqL (pt_apV hP hx hv) hv'))

theorem pt_namesB {P : α → ProbDesc} (hP : PT P) : PT fun a => namesB (P a) := by
  unfold namesB
  exact PT.flatMap (pt_numsOf.comp hP) (PT.cons (PT.pair (PT.const false) PT.snd)
    (PT.single (PT.pair (PT.const true) PT.snd)))

theorem pt_cand {P : α → ProbDesc} {A : α → List (List Bool)} (hP : PT P) (hA : PT A) :
    PT fun a => cand (P a) (A a) := by
  unfold cand
  refine PT.flatMap hA (PT.flatMap (pt_namesB (hP.comp PT.fst)) ?_)
  exact PT.map (g := fun (r : (α × List Bool) × (Bool × ℕ)) (v' : List Bool) => (r.1.2, r.2, v'))
    (hA.comp (PT.fst.comp PT.fst)) (PT.pair (PT.snd.comp (PT.fst.comp PT.fst))
      (PT.pair (PT.snd.comp PT.fst) PT.snd))

theorem pt_dpTab {P : α → ProbDesc} {A : α → List (List Bool)} (hP : PT P) (hA : PT A) :
    PT fun a => dpTab (P a) (A a) := by
  unfold dpTab
  have hc := pt_cand hP hA
  obtain ⟨c, d, hcd⟩ := hc.pb
  refine PT.foldl (α := α) (β := Trip) (σ := List Trip)
    (g := fun a X _ => dpStep (P a) (A a) X) (PT.append hc (PT.const [default])) (PT.const [])
    ?_ (c := c) (d := d) fun a X _ _ => (NoHTN.sz_filter_le _ _).trans ((hcd a).trans
      (Nat.le_add_left _ _))
  unfold dpStep
  exact PT.filter (hc.comp PT.fst) (pt_ruleB (hP.comp (PT.fst.comp PT.fst))
    (hA.comp (PT.fst.comp PT.fst)) (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd)

end Article

end HTN
