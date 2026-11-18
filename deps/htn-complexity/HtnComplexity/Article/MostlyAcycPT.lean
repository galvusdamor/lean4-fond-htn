import HtnComplexity.Article.TIUnres
import HtnPlanning.Article.MostlyAcyc
import HtnPlanning.Computable.Reach
/-!
# Lem. 4.2.2 in polynomial time

`HTN.Article.lem_4_2_2_pt`: the collapsed problem of Lem. 4.2.2 is computed from the description
in polynomial time.  The decomposition graph of a description (`HTN.Article.edgesOf`) has its
transitive closure computed by saturation (`HTN.Syn.reachB`, here with duplicates removed after
every round, `HTN.Article.rIt`); the representative of a name (`HTN.Article.rhoD`) is the first
number of the description in its strongly connected component.  The collapsed description
(`HTN.Article.mergeDesc`) relabels the names and drops the methods that become self-loops; it
denotes `P.mergeSCC ρ` (`HTN.Article.toProblem_mergeDesc`), the problem of Lem. 4.2.2.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

/-! ### Size helpers -/

theorem sz_le_of_sublist {β : Type} [BEnc β] {l l' : List β} (h : l.Sublist l') : sz l ≤ sz l' := by
  induction h with
  | slnil => exact le_rfl
  | cons a _ ih => rw [sz_cons]; omega
  | cons₂ a _ ih => rw [sz_cons, sz_cons]; omega

theorem sz_map_snd_le {β γ : Type} [BEnc β] [BEnc γ] (l : List (β × γ)) :
    sz (l.map Prod.snd) ≤ sz l := by
  induction l with
  | nil => simp [sz_nil]
  | cons q l ih =>
    rw [List.map_cons, sz_cons, sz_cons, show sz q = sz q.1 + sz q.2 from sz_prod _ _]
    omega

/-! ### The closure, in polynomial time -/

theorem succsOfList_eq (E : List (ℕ × ℕ)) (S : List ℕ) :
    succsOfList E S = (E.filter fun q => decide (q.1 ∈ S)).map Prod.snd := by
  unfold succsOfList
  have : (fun q : ℕ × ℕ => if memB S q.1 = true then some q.2 else none) =
      fun q => if q.1 ∈ S then some q.2 else none := by
    funext q; simp only [memB_iff]
  rw [this]
  induction E with
  | nil => rfl
  | cons q E ih => by_cases h : q.1 ∈ S <;> simp [List.filterMap_cons, h, ih]

theorem succsOfNode_eq (E : List (ℕ × ℕ)) (a : ℕ) :
    succsOfNode E a = (E.filter fun q => decide (q.1 = a)).map Prod.snd := by
  unfold succsOfNode
  induction E with
  | nil => rfl
  | cons q E ih =>
    by_cases h : q.1 = a <;> simp [List.filterMap_cons, h, ih]

/-- One round of saturation, duplicates removed. -/
def rStepD (E : List (ℕ × ℕ)) (S : List ℕ) : List ℕ := (S ++ succsOfList E S).dedup

/-- Saturation with duplicates removed. -/
def rIt (E : List (ℕ × ℕ)) (a : ℕ) (n : ℕ) : List ℕ := (rStepD E)^[n] (succsOfNode E a).dedup

theorem mem_rIt_iff (E : List (ℕ × ℕ)) (a : ℕ) : ∀ n b, b ∈ rIt E a n ↔ b ∈ reachIter E a n := by
  intro n
  induction n with
  | zero => intro b; simp [rIt]
  | succ n ih =>
    intro b
    rw [rIt, Function.iterate_succ_apply']
    simp only [rStepD, reachIter_succ, List.mem_dedup, List.mem_append, mem_succsOfList]
    simp only [rIt] at ih
    rw [ih]
    exact or_congr Iff.rfl (exists_congr fun x => and_congr (ih x) Iff.rfl)

/-- Reachability, by the saturation with duplicates removed. -/
def reachD (E : List (ℕ × ℕ)) (a b : ℕ) : Bool := decide (b ∈ rIt E a (E.length + 1))

theorem reachD_iff (E : List (ℕ × ℕ)) (a b : ℕ) :
    reachD E a b = true ↔ Relation.TransGen (listRelOf E) a b := by
  rw [← reachB_iff, reachB, memB_iff, reachList, reachD, decide_eq_true_eq, mem_rIt_iff]

theorem foldl_const_iterate {β σ : Type} (f : σ → σ) : ∀ (l : List β) (s : σ),
    l.foldl (fun S _ => f S) s = f^[l.length] s
  | [], _ => rfl
  | _ :: l, s => by
    rw [List.foldl_cons, foldl_const_iterate f l, List.length_cons, Function.iterate_succ_apply]

theorem sz_rStepD_le (E : List (ℕ × ℕ)) (S : List ℕ) : sz (rStepD E S) ≤ sz S + sz E := by
  unfold rStepD
  refine (sz_le_of_sublist (List.dedup_sublist _)).trans ?_
  have h1 := NoHTN.sz_append_le S (succsOfList E S)
  rw [succsOfList_eq] at h1 ⊢
  have h2 := sz_map_snd_le (E.filter fun q => decide (q.1 ∈ S))
  have h3 := NoHTN.sz_filter_le E (fun q => decide (q.1 ∈ S))
  omega

theorem pt_reachD : PT fun x : List (ℕ × ℕ) × ℕ × ℕ => reachD x.1 x.2.1 x.2.2 := by
  have hst : PT fun q : (List (ℕ × ℕ) × ℕ × ℕ) × List ℕ × ℕ => rStepD q.1.1 q.2.1 := by
    unfold rStepD
    refine PT.dedup (PT.append (PT.fst.comp PT.snd) ?_)
    refine (PT.map (g := fun (_ : (List (ℕ × ℕ) × ℕ × ℕ) × List ℕ × ℕ) (q : ℕ × ℕ) => q.2)
      (PT.filter (p := fun (r : (List (ℕ × ℕ) × ℕ × ℕ) × List ℕ × ℕ) (q : ℕ × ℕ) => decide (q.1 ∈ r.2.1))
        (PT.fst.comp PT.fst) (PT.elem (PT.fst.comp (PT.snd.comp PT.fst)) (PT.fst.comp PT.snd)))
      (PT.snd.comp PT.snd)).of_eq fun r => (succsOfList_eq _ _).symm
  have hinit : PT fun x : List (ℕ × ℕ) × ℕ × ℕ => (succsOfNode x.1 x.2.1).dedup :=
    (PT.dedup (PT.map (g := fun (_ : List (ℕ × ℕ) × ℕ × ℕ) (q : ℕ × ℕ) => q.2)
      (PT.filter (p := fun (x : List (ℕ × ℕ) × ℕ × ℕ) (q : ℕ × ℕ) => decide (q.1 = x.2.1)) PT.fst
        (PT.eq (PT.fst.comp PT.snd) (PT.fst.comp (PT.snd.comp PT.fst)))) (PT.snd.comp PT.snd))).of_eq
      fun x => by rw [succsOfNode_eq]
  have hf : PT fun x : List (ℕ × ℕ) × ℕ × ℕ =>
      (List.range (x.1 ++ [(0, 0)]).length).foldl (fun S _ => rStepD x.1 S)
        (succsOfNode x.1 x.2.1).dedup :=
    PT.foldl (α := List (ℕ × ℕ) × ℕ × ℕ) (β := ℕ) (σ := List ℕ)
      (g := fun x S _ => rStepD x.1 S) (PT.rangeLength (PT.append PT.fst (PT.const [(0, 0)])))
      hinit hst (c := 1) (d := 1) fun x S b _ => by
        have := sz_rStepD_le x.1 S
        have : sz x.1 ≤ sz x := NoHTN.sz_fst_le x
        nlinarith
  refine (PT.elem hf (PT.snd.comp PT.snd)).of_eq fun x => ?_
  unfold reachD rIt
  rw [foldl_const_iterate]
  simp

/-! ### The decomposition graph of a description -/

/-- The edges of the decomposition graph: a method's name to its compound task names. -/
def edgesOf (p : ProbDesc) : List (ℕ × ℕ) :=
  p.methods.flatMap fun e => (e.2.ids.filter fun x => (lblOf e.2 x).1).map fun x => (e.1, (lblOf e.2 x).2)

theorem mem_edgesOf {p : ProbDesc} {a b : ℕ} :
    (a, b) ∈ edgesOf p ↔ DEdge p.toProblem.methods a b := by
  simp only [edgesOf, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨e, he, x, ⟨hx, hc⟩, rfl, rfl⟩
    refine ⟨e.toMethod, ⟨e, he, rfl⟩, rfl, x, by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork]
      using hx, label_eq_inr.2 (Prod.ext hc rfl)⟩
  · rintro ⟨m, ⟨e, he, rfl⟩, rfl, x, hx, hα⟩
    have hl := label_eq_inr.1 hα
    refine ⟨e, he, x, ⟨by simpa [MethodDesc.toMethod, TnDesc.toTaskNetwork] using hx, by rw [hl]⟩,
      rfl, by rw [hl]⟩

theorem listRelOf_edgesOf (p : ProbDesc) : listRelOf (edgesOf p) = DEdge p.toProblem.methods := by
  funext a b; exact propext mem_edgesOf

/-- Same strongly connected component, decided. -/
def sccB (p : ProbDesc) (a b : ℕ) : Bool :=
  decide (a = b) || (reachD (edgesOf p) a b && reachD (edgesOf p) b a)

theorem sccB_iff {p : ProbDesc} {a b : ℕ} : sccB p a b = true ↔ SameSCC p.toProblem.methods a b := by
  unfold sccB SameSCC
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, reachD_iff, listRelOf_edgesOf]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨.refl, .refl⟩
    · exact ⟨h1.to_reflTransGen, h2.to_reflTransGen⟩
  · rintro ⟨h1, h2⟩
    by_cases hab : a = b
    · exact Or.inl hab
    · right
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 h1 with h | h
      · exact absurd h.symm hab
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 h2 with h' | h'
      · exact absurd h' hab
      exact ⟨h, h'⟩

/-- **The representative of a name**: the first number of the description in its component. -/
def rhoD (p : ProbDesc) (c : ℕ) : ℕ :=
  if ((numsOf p).filter (sccB p c)).isEmpty then c else ((numsOf p).filter (sccB p c)).headI

theorem dedge_head_mem {p : ProbDesc} {a b : ℕ} (h : DEdge p.toProblem.methods a b) :
    a ∈ numsOf p := by
  obtain ⟨m, ⟨e, he, rfl⟩, rfl, -⟩ := h
  exact mem_numsOf_method he (List.mem_cons_self ..)

theorem sccRep_rhoD (p : ProbDesc) : SCCRep p.toProblem.methods (rhoD p) := by
  have hcong : ∀ c c', SameSCC p.toProblem.methods c c' →
      (numsOf p).filter (sccB p c) = (numsOf p).filter (sccB p c') := by
    intro c c' h
    refine List.filter_congr fun x _ => ?_
    rw [Bool.eq_iff_iff, sccB_iff, sccB_iff]
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
  refine ⟨fun c => ?_, fun c c' h => ?_⟩
  · unfold rhoD
    split_ifs with he
    · exact ⟨.refl, .refl⟩
    · have hne : (numsOf p).filter (sccB p c) ≠ [] := by simpa using he
      obtain ⟨y, l, hy⟩ := List.exists_cons_of_ne_nil hne
      rw [hy, List.headI_cons]
      have : y ∈ (numsOf p).filter (sccB p c) := by rw [hy]; exact List.mem_cons_self ..
      exact sccB_iff.1 (List.mem_filter.1 this).2
  · unfold rhoD
    rw [hcong c c' h]
    split_ifs with he
    · by_contra hcc
      have h1 := h.1
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 h1 with h1 | h1
      · exact hcc h1.symm
      obtain ⟨d, hcd, -⟩ := Relation.TransGen.head'_iff.1 h1
      have hc : c ∈ numsOf p := dedge_head_mem hcd
      rw [← hcong c c' h] at he
      have : c ∈ (numsOf p).filter (sccB p c) :=
        List.mem_filter.2 ⟨hc, sccB_iff.2 ⟨.refl, .refl⟩⟩
      simp [List.isEmpty_iff.1 he] at this
    · rfl

/-! ### The collapsed description -/

/-- A network description with its compound names replaced by representatives. -/
def mapTn (p : ProbDesc) (t : TnDesc) : TnDesc :=
  (t.ids, t.ordList, t.lbl.map fun q => (q.1, q.2.1, if q.2.1 then rhoD p q.2.2 else q.2.2))

/-- A method description, relabelled. -/
def mapMeth (p : ProbDesc) (e : MethodDesc) : MethodDesc := (rhoD p e.1, mapTn p e.2)

/-- The method becomes a self-loop. -/
def loopB (p : ProbDesc) (e : MethodDesc) : Bool :=
  (e.2.ids.length == 1) && (lblOf e.2 e.2.ids.headI).1 &&
    (rhoD p (lblOf e.2 e.2.ids.headI).2 == rhoD p e.1)

/-- **The collapsed description** of Lem. 4.2.2. -/
def mergeDesc (p : ProbDesc) : ProbDesc :=
  ((p.actions, (p.methods.filter fun e => !loopB p e).map (mapMeth p)),
    (p.init, mapTn p p.tnI, p.goalPos, p.goalNeg))

theorem lookup_map_val {β γ : Type} (h : β → γ) (l : List (ℕ × β)) (x : ℕ) :
    (l.map fun q => (q.1, h q.2)).lookup x = (l.lookup x).map h := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨k, b⟩ := q
    by_cases hk : x = k
    · subst hk; simp [List.lookup]
    · have : (x == k) = false := by simpa using hk
      simp [List.lookup, this, ih]

theorem toTaskNetwork_mapTn (p : ProbDesc) (t : TnDesc) :
    (mapTn p t).toTaskNetwork = t.toTaskNetwork.mapC (rhoD p) := by
  apply TaskNetwork.ext'
  · rfl
  · rfl
  funext x
  simp only [TnDesc.toTaskNetwork, TaskNetwork.mapC, TnDesc.label, mapTn, TnDesc.lbl]
  rw [lookup_map_val (fun v : Bool × ℕ => (v.1, if v.1 then rhoD p v.2 else v.2))]
  rcases t.2.2.lookup x with _ | ⟨_ | _, n⟩ <;> rfl

theorem toMethod_mapMeth (p : ProbDesc) (e : MethodDesc) :
    (mapMeth p e).toMethod = e.toMethod.mapC (rhoD p) := by
  show Method.mk _ _ = Method.mk _ _
  rw [show (mapMeth p e).2 = mapTn p e.2 from rfl, toTaskNetwork_mapTn]; rfl

theorem loopB_iff {p : ProbDesc} {e : MethodDesc} {prim : ℕ → Prop} (he : TnValid prim e.2) :
    loopB p e = true ↔ e.toMethod.IsLoop (rhoD p) := by
  unfold loopB Method.IsLoop
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 h1
    rw [ht] at h2 h3
    simp only [List.headI_cons] at h2 h3
    refine ⟨t, (lblOf e.2 t).2, ?_, label_eq_inr.2 (Prod.ext h2 rfl), h3⟩
    show e.2.1.toFinset = {t}
    rw [show e.2.1 = [t] from ht]; simp
  · rintro ⟨t, c, hT, hα, hρ⟩
    have hT' : e.2.ids.toFinset = {t} := hT
    have hlen : e.2.ids.length = 1 := by
      rw [← List.toFinset_card_of_nodup he.nodup, hT', Finset.card_singleton]
    obtain ⟨t', ht'⟩ := List.length_eq_one_iff.1 hlen
    have htt : t' = t := by
      have : t' ∈ e.2.ids.toFinset := by rw [ht']; simp
      rw [hT'] at this; simpa using this
    subst htt
    have hl := label_eq_inr.1 hα
    refine ⟨⟨hlen, ?_⟩, ?_⟩ <;> rw [ht'] <;> simp only [List.headI_cons, hl]
    exact hρ

/-- **The collapsed description denotes the problem of Lem. 4.2.2.** -/
theorem toProblem_mergeDesc {p : ProbDesc} (hp : p.Valid) :
    (mergeDesc p).toProblem = p.toProblem.mergeSCC (rhoD p) := by
  have hm : (mergeDesc p).toProblem.methods = mergeMethods (rhoD p) p.toProblem.methods := by
    ext m
    simp only [ProbDesc.toProblem, mergeDesc, ProbDesc.methods, mergeMethods, Set.mem_setOf_eq,
      Set.mem_image, List.mem_map, List.mem_filter, Bool.not_eq_true']
    constructor
    · rintro ⟨e', ⟨e, ⟨he, hl⟩, rfl⟩, rfl⟩
      refine ⟨e.toMethod, ⟨⟨e, he, rfl⟩, fun h => ?_⟩, (toMethod_mapMeth p e).symm⟩
      rw [← loopB_iff (hp.methods e he)] at h
      rw [h] at hl; cases hl
    · rintro ⟨m, ⟨⟨e, he, rfl⟩, hnl⟩, rfl⟩
      refine ⟨mapMeth p e, ⟨e, ⟨he, ?_⟩, rfl⟩, toMethod_mapMeth p e⟩
      cases hb : loopB p e
      · rfl
      · exact absurd ((loopB_iff (hp.methods e he)).1 hb) hnl
  have ht : (mergeDesc p).toProblem.tnI = p.toProblem.tnI.mapC (rhoD p) :=
    toTaskNetwork_mapTn p p.tnI
  rw [Problem.mergeSCC]
  rw [← hm, ← ht]
  rfl

/-! ### Polynomial time -/

theorem pt_numsOf : PT numsOf := by
  have htn : ∀ {β : Type} [BEnc β] {t : β → TnDesc}, PT t → PT fun b => tnNums (t b) :=
    fun {β} _ {t} ht => PT.append (PT.fst.comp ht) (PT.map (g := fun (_ : β) (q : ℕ × Bool × ℕ) => q.2.2)
      (PT.snd.comp (PT.snd.comp ht)) (PT.snd.comp (PT.snd.comp PT.snd)))
  exact PT.append (htn (PT.fst.comp (PT.snd.comp PT.snd)))
    (PT.flatMap (g := fun (_ : ProbDesc) (m : MethodDesc) => m.1 :: tnNums m.2)
      (PT.snd.comp (PT.fst.comp PT.id)) (PT.cons (PT.fst.comp PT.snd) (htn (PT.snd.comp PT.snd))))

theorem pt_edgesOf : PT edgesOf := by
  unfold edgesOf
  have hl := pt_lblOf (α := (ProbDesc × MethodDesc) × ℕ) (PT.snd.comp (PT.snd.comp PT.fst)) PT.snd
  exact PT.flatMap (PT.snd.comp PT.fst) (PT.map (g := fun (r : ProbDesc × MethodDesc) (x : ℕ) =>
    (r.2.1, (lblOf r.2.2 x).2)) (PT.filter (p := fun (r : ProbDesc × MethodDesc) (x : ℕ) =>
      (lblOf r.2.2 x).1) (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp hl))
    (PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) (PT.snd.comp hl)))

theorem pt_sccB {α : Type} [BEnc α] {P : α → ProbDesc} {a b : α → ℕ} (hP : PT P) (ha : PT a)
    (hb : PT b) : PT fun x => sccB (P x) (a x) (b x) := by
  unfold sccB
  have hE := pt_edgesOf.comp hP
  exact PT.or (PT.eq ha hb) (PT.and (pt_reachD.comp (PT.pair hE (PT.pair ha hb)))
    (pt_reachD.comp (PT.pair hE (PT.pair hb ha))))

theorem pt_rhoD {α : Type} [BEnc α] {P : α → ProbDesc} {c : α → ℕ} (hP : PT P) (hc : PT c) :
    PT fun x => rhoD (P x) (c x) := by
  unfold rhoD
  have hL : PT fun x => (numsOf (P x)).filter (sccB (P x) (c x)) :=
    PT.filter (pt_numsOf.comp hP) (pt_sccB (hP.comp PT.fst) (hc.comp PT.fst) PT.snd)
  exact (PT.cond (PT.isEmpty hL) hc (PT.headI hL)).of_eq fun x => by simp only [Bool.cond_eq_ite]

theorem pt_mapTn {α : Type} [BEnc α] {P : α → ProbDesc} {t : α → TnDesc} (hP : PT P) (ht : PT t) :
    PT fun x => mapTn (P x) (t x) := by
  unfold mapTn
  refine PT.pair (PT.fst.comp ht) (PT.pair (PT.fst.comp (PT.snd.comp ht)) ?_)
  refine PT.map (g := fun x (q : ℕ × Bool × ℕ) => (q.1, q.2.1, if q.2.1 then rhoD (P x) q.2.2 else q.2.2))
    (PT.snd.comp (PT.snd.comp ht)) (PT.pair (PT.fst.comp PT.snd) (PT.pair (PT.fst.comp
      (PT.snd.comp PT.snd)) ?_))
  exact (PT.cond (PT.fst.comp (PT.snd.comp PT.snd)) (pt_rhoD (hP.comp PT.fst)
    (PT.snd.comp (PT.snd.comp PT.snd))) (PT.snd.comp (PT.snd.comp PT.snd))).of_eq fun _ => by
      simp only [Bool.cond_eq_ite]

theorem pt_mergeDesc : PT mergeDesc := by
  unfold mergeDesc
  have hloop : PT fun r : ProbDesc × MethodDesc => loopB r.1 r.2 := by
    unfold loopB
    have hl := pt_lblOf (α := ProbDesc × MethodDesc) (PT.snd.comp PT.snd)
      (PT.headI (PT.fst.comp (PT.snd.comp PT.snd)))
    exact PT.and (PT.and (PT.beq (PT.length (PT.fst.comp (PT.snd.comp PT.snd))) (PT.const 1))
      (PT.fst.comp hl)) (PT.beqL (pt_rhoD PT.fst (PT.snd.comp hl)) (pt_rhoD PT.fst
        (PT.fst.comp PT.snd)))
  refine PT.pair (PT.pair (PT.fst.comp PT.fst) ?_) (PT.pair (PT.fst.comp PT.snd)
    (PT.pair (pt_mapTn PT.id (PT.fst.comp (PT.snd.comp PT.snd)))
      (PT.snd.comp (PT.snd.comp PT.snd))))
  exact PT.map (g := fun (p : ProbDesc) (e : MethodDesc) => mapMeth p e)
    (PT.filter (p := fun (p : ProbDesc) (e : MethodDesc) => !loopB p e) (PT.snd.comp PT.fst)
      (PT.not hloop)) (PT.pair (pt_rhoD PT.fst (PT.fst.comp PT.snd))
        (pt_mapTn PT.fst (PT.snd.comp PT.snd)))

/-- **Lemma 4.2.2, the polynomial-time part.**  A polynomial-time function computes, from a
well-formed description, a description of the collapsed problem `P.mergeSCC ρ` of
`HTN.Article.Problem.lem_4_2_2`, for a choice `ρ` of representatives of the strongly connected
components. -/
theorem lem_4_2_2_pt : ∃ f : ProbDesc → ProbDesc, PT f ∧ ∀ p : ProbDesc, p.Valid →
    ∃ ρ, SCCRep p.toProblem.methods ρ ∧ (f p).toProblem = p.toProblem.mergeSCC ρ :=
  ⟨mergeDesc, pt_mergeDesc, fun p hp => ⟨rhoD p, sccRep_rhoD p, toProblem_mergeDesc hp⟩⟩

end Article

end HTN
