import HtnComplexity.Article.StripsTM
import HtnComplexity.PT.NP
import HtnComplexity.PT.DivMod
/-!
# STRIPS is PSPACE-hard (Bylander)

**`HTN.Article.strips_pspaceHard`**: every language of `PSPACE` reduces in polynomial time to
plan existence for STRIPS (`HTN.Article.PlanExSTRIPS`).

A language of `PSPACE` is accepted by a single-tape Turing machine `M` within a polynomial space
bound `q(|x|)` (`HTN.Mach.exists_tm_of_inPSpace`); the reduction maps `x` to the STRIPS problem
`HTN.Article.stripsTM` of the run of `M` on `x` in space `q(|x|) + 1`
(`HTN.Article.stripsTM_solvable_iff`), which is computed in polynomial time
(`HTN.Article.pt_stripsTM`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom TM

/-! ### Lists of polynomial length -/

/-- For every polynomial `q` there is a polynomial-time list of length `q(|x|)`. -/
theorem exists_pt_polyLen (q : Polynomial ℕ) :
    ∃ g : List Bool → List Unit, PT g ∧ ∀ x, (g x).length = q.eval x.length := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨g₁, h₁, e₁⟩ := hp
    obtain ⟨g₂, h₂, e₂⟩ := hr
    exact ⟨fun x => g₁ x ++ g₂ x, PT.append h₁ h₂, fun x => by simp [e₁, e₂]⟩
  | monomial n a =>
    induction n with
    | zero =>
      exact ⟨fun _ => List.replicate a (), PT.const _, fun x => by simp⟩
    | succ n ih =>
      obtain ⟨g, hg, eg⟩ := ih
      refine ⟨fun x => (g x).flatMap fun _ => x.map fun _ => (), PT.flatMap hg
        (PT.map PT.fst (PT.const ())), fun x => ?_⟩
      simp only [List.length_flatMap, List.length_map, List.map_const', List.sum_replicate,
        smul_eq_mul, eg, Polynomial.eval_monomial, List.length_replicate]
      ring

/-! ### The pieces of the encoding -/

theorem pt_mvApply {α : Type} [BEnc α] {m i : α → ℕ} (hm : PT m) (hi : PT i) :
    PT fun a => mvApply (m a) (i a) := by
  unfold mvApply
  exact PT.ite (PT.eq hm (PT.const 0)) (PT.subC hi 1)
    (PT.ite (PT.eq hm (PT.const 1)) hi (PT.succ hi))

theorem symCode_eq (a : Option Bool) :
    symCode a = if a = none then 0 else if a = some false then 1 else 2 := by
  rcases a with _ | _ | _ <;> rfl

theorem pt_symCode {α : Type} [BEnc α] {f : α → Option Bool} (hf : PT f) :
    PT fun a => symCode (f a) :=
  (PT.ite (PT.eq hf (PT.const none)) (PT.const 0)
    (PT.ite (PT.eq hf (PT.const (some false))) (PT.const 1) (PT.const 2))).of_eq
    fun a => (symCode_eq (f a)).symm

theorem pt_celF {α : Type} [BEnc α] (k : ℕ) {S i : α → ℕ} {a : α → Option Bool} (hS : PT S)
    (hi : PT i) (ha : PT a) : PT fun x => celF k (S x) (i x) (a x) :=
  PT.add (PT.add (PT.add (PT.const k) hS) (PT.affine 3 0 hi |>.of_eq fun _ => by ring)) (pt_symCode ha)

theorem pt_trAct {α : Type} [BEnc α] (k : ℕ) {S : α → ℕ} {tr : α → TTr} {i : α → ℕ} (hS : PT S)
    (htr : PT tr) (hi : PT i) : PT fun x => trAct k (S x) (tr x) (i x) := by
  have h1 : PT fun x => (tr x).1 := PT.fst' htr
  have h2 : PT fun x => (tr x).2.1 := PT.fst' (PT.snd' htr)
  have h3 : PT fun x => (tr x).2.2.1 := PT.fst' (PT.snd' (PT.snd' htr))
  have h4 : PT fun x => (tr x).2.2.2.1 := PT.fst' (PT.snd' (PT.snd' (PT.snd' htr)))
  have h5 : PT fun x => (tr x).2.2.2.2 := PT.snd' (PT.snd' (PT.snd' (PT.snd' htr)))
  have hki : PT fun x => k + i x := PT.add (PT.const k) hi
  have hpre : PT fun x => [(tr x).1, k + i x, celF k (S x) (i x) (tr x).2.1] :=
    PT.cons h1 (PT.cons hki (PT.single (pt_celF k hS hi h2)))
  unfold trAct
  exact PT.pair hpre (PT.pair PT.nil (PT.pair
    (PT.cons h3 (PT.cons (PT.add (PT.const k) (pt_mvApply h5 hi)) (PT.single (pt_celF k hS hi h4))))
    hpre))

theorem pt_accAct {α : Type} [BEnc α] (k : ℕ) {S : α → ℕ} {q : α → ℕ} (hS : PT S) (hq : PT q) :
    PT fun x => accAct k (S x) (q x) := by
  unfold accAct accF
  exact PT.pair (PT.single hq) (PT.pair PT.nil (PT.pair (PT.single
    (PT.add (PT.add (PT.const k) hS) (PT.affine 3 0 hS |>.of_eq fun _ => by ring))) PT.nil))

theorem pt_tmBodies {α : Type} [BEnc α] (k : ℕ) (trs : List TTr) (accs : List ℕ) {L : α → List Unit}
    (hL : PT L) : PT fun x => tmBodies k (L x).length trs accs := by
  have hS : PT fun x => (L x).length := PT.length hL
  have hR : PT fun x => List.range (L x).length := PT.rangeLength hL
  unfold tmBodies
  refine PT.append (PT.flatMap (PT.const trs) ?_) (PT.map (PT.const accs) (pt_accAct k (hS.comp PT.fst) PT.snd))
  -- the transitions, on pairs `(x, tr)`
  show PT fun p : α × TTr => ((List.range (L p.1).length).filter
    fun i => decide (mvApply p.2.2.2.2.2 i < (L p.1).length)).map (trAct k (L p.1).length p.2)
  refine PT.map (PT.filter (hR.comp PT.fst) ?_) (pt_trAct k (hS.comp (PT.fst.comp PT.fst))
    (PT.snd.comp PT.fst) PT.snd)
  exact PT.lt (pt_mvApply (PT.snd' (PT.snd' (PT.snd' (PT.snd' (PT.snd.comp PT.fst))))) PT.snd)
    (hS.comp (PT.fst.comp PT.fst))

theorem namedFrom_eq : ∀ (bs : List ABody) (o : ℕ),
    namedFrom o bs = (List.range bs.length).map fun j => (j + o, bs.getI j) := by
  intro bs
  induction bs with
  | nil => intro o; rfl
  | cons b bs ih =>
    intro o
    rw [namedFrom, ih, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp
    · exact List.map_congr_left fun j _ => by simp; omega

theorem pt_namedFrom {α : Type} [BEnc α] {f : α → List ABody} (hf : PT f) :
    PT fun x => namedFrom 0 (f x) :=
  (PT.map (g := fun x j => (j, (f x).getI j)) (PT.rangeLength hf)
    (PT.pair PT.snd (PT.getI (hf.comp PT.fst) PT.snd))).of_eq
    fun x => by rw [namedFrom_eq]; simp

theorem getD_map_some (x : List Bool) (i : ℕ) :
    (x.map some).getD i none = if i < x.length then some (x.getI i) else none := by
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
    simp [List.getI_eq_getElem _ h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by omega)]
    rfl

/-- **The encoding is computed in polynomial time.** -/
theorem pt_stripsTM (k : ℕ) (trs : List TTr) (accs : List ℕ) (q₀ : ℕ) {L : List Bool → List Unit}
    (hL : PT L) : PT fun x => stripsTM k (L x).length trs accs q₀ (x.map some) := by
  have hS : PT fun x => (L x).length := PT.length hL
  have hR : PT fun x => List.range (L x).length := PT.rangeLength hL
  have hcell : PT fun p : List Bool × ℕ => (p.1.map some).getD p.2 none :=
    (PT.ite (PT.lt PT.snd (PT.length PT.fst)) (PT.some (PT.getI PT.fst PT.snd)) (PT.const none)).of_eq
      fun p => (getD_map_some p.1 p.2).symm
  unfold stripsTM accF
  refine PT.pair (pt_namedFrom (pt_tmBodies k trs accs hL)) (PT.pair ?_ (PT.pair
    (PT.single (PT.add (PT.add (PT.const k) hS) (PT.affine 3 0 hS |>.of_eq fun _ => by ring)))
    PT.nil))
  exact PT.append (PT.cons (PT.const q₀) (PT.single (PT.const (k + 0))))
    (PT.map hR (pt_celF k (hS.comp PT.fst) PT.snd hcell))

/-! ### The hardness theorem -/

instance : Fintype Move where
  elems := {.left, .stay, .right}
  complete m := by cases m <;> simp

/-- The transitions of a machine with states `Fin k`, as a list. -/
noncomputable def trsOf {k : ℕ} (M : NTM (Fin k) (Option Bool)) : List TTr := by
  classical
  exact ((Finset.univ : Finset (Fin k × Option Bool × Fin k × Option Bool × Move)).filter
    (fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2) ∈ M.step t.1 t.2.1)).toList.map
    fun t => (t.1.val, t.2.1, t.2.2.1.val, t.2.2.2.1, moveCode t.2.2.2.2)

/-- The accepting states of a machine with states `Fin k`, as a list. -/
noncomputable def accsOf {k : ℕ} (M : NTM (Fin k) (Option Bool)) : List ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin k)).filter (· ∈ M.accept)).toList.map Fin.val

theorem trsOf_spec1 {k : ℕ} (M : NTM (Fin k) (Option Bool)) : ∀ tr ∈ trsOf M,
    ∃ (hq : tr.1 < k) (hq' : tr.2.2.1 < k) (m : Move), tr.2.2.2.2 = moveCode m ∧
      ((⟨tr.2.2.1, hq'⟩ : Fin k), tr.2.2.2.1, m) ∈ M.step ⟨tr.1, hq⟩ tr.2.1 := by
  classical
  intro tr htr
  simp only [trsOf, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and] at htr
  obtain ⟨⟨q, a, q', a', m⟩, hmem, rfl⟩ := htr
  exact ⟨q.2, q'.2, m, rfl, hmem⟩

theorem trsOf_spec2 {k : ℕ} (M : NTM (Fin k) (Option Bool)) : ∀ (q : Fin k) a (q' : Fin k) a' m,
    (q', a', m) ∈ M.step q a → (q.val, a, q'.val, a', moveCode m) ∈ trsOf M := by
  classical
  intro q a q' a' m h
  simp only [trsOf, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(q, a, q', a', m), h, rfl⟩

theorem accsOf_spec1 {k : ℕ} (M : NTM (Fin k) (Option Bool)) :
    ∀ q ∈ accsOf M, ∃ h : q < k, (⟨q, h⟩ : Fin k) ∈ M.accept := by
  classical
  intro q hq
  simp only [accsOf, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact ⟨q'.2, hq'⟩

theorem accsOf_spec2 {k : ℕ} (M : NTM (Fin k) (Option Bool)) : ∀ q ∈ M.accept, q.val ∈ accsOf M := by
  classical
  intro q hq
  simp only [accsOf, List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨q, hq, rfl⟩

/-- **STRIPS plan existence is PSPACE-hard** (Bylander). -/
theorem strips_pspaceHard : Cx.Hard Cx.PSPACE PlanExSTRIPS := by
  intro L hL
  obtain ⟨k, M, q, hblank, hM⟩ := Mach.exists_tm_of_inPSpace hL
  obtain ⟨g, hg, hglen⟩ := exists_pt_polyLen (q + 1)
  have hconv : UC fun x => (enc (stripsTM k (g x).length (trsOf M) (accsOf M) M.init.val
      (x.map some)) : List Bool) :=
    uc_of_pt_list (BDec.pt_encL.comp (pt_stripsTM k (trsOf M) (accsOf M) M.init.val hg))
  refine ⟨_, polyTimeFun_of_uc hconv, fun x => ?_⟩
  show L x ↔ codeLang StripsDesc (fun d => d.Valid ∧ d.Solvable) (enc _)
  have hvalid : (stripsTM k (g x).length (trsOf M) (accsOf M) M.init.val (x.map some)).Valid := by
    unfold StripsDesc.Valid StripsDesc.actions stripsTM
    rw [map_name_namedFrom]
    simpa using List.nodup_range
  rw [codeLang_enc, and_iff_right hvalid, stripsTM_solvable_iff M (trsOf_spec1 M) (trsOf_spec2 M) (accsOf_spec1 M)
    (accsOf_spec2 M) (by rw [hglen]; simp) hblank, hglen]
  rw [(hM x).1]
  simp only [Polynomial.eval_add, Polynomial.eval_one]
  constructor
  · rintro ⟨n, c, hr, hc⟩; exact ⟨n, c, hr.mono M (by omega), hc⟩
  · rintro ⟨n, c, hr, hc⟩; exact (hM x).1.1 ((hM x).2 ⟨n, c, hr.reaches M, hc⟩)

end Article

end HTN
