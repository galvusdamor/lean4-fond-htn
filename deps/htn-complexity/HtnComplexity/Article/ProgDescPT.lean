import HtnComplexity.Article.ProgDescSim
/-!
# Progression on descriptions is polynomial time

`HTN.Article.pt_succs`: the list of the progressions of a configuration is computed in polynomial
time; so are the initial configuration and the goal test.  Fresh ids and the renaming are
rewritten with indices (`HTN.Article.freshIds_eq`, `HTN.Article.renOf_eq`), which the calculus
handles.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem take_eq_map_getI (L : List ℕ) {k : ℕ} (hk : k ≤ L.length) :
    L.take k = (List.range k).map L.getI := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [List.getI_eq_getElem]

theorem freshIds_eq (l ids : List ℕ) : freshIds l ids.length = (List.range ids.length).map
    ((List.range (l ++ ids).length).filter fun x => decide (x ∉ l)).getI := by
  have hlen := length_freshIds l ids.length
  unfold freshIds at hlen ⊢
  rw [List.length_append]
  rw [List.length_take] at hlen
  exact take_eq_map_getI _ (by omega)

theorem zip_eq (src dst : List ℕ) (h : dst.length = src.length) :
    src.zip dst = (List.range src.length).map fun i => (src.getI i, dst.getI i) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range]
    rw [List.getI_eq_getElem, List.getI_eq_getElem]

theorem renOf_eq : ∀ (src dst : List ℕ), dst.length = src.length → ∀ x,
    renOf src dst x = kidOf (src.zip dst) x
  | [], [], _, x => rfl
  | a :: src, b :: dst, h, x => by
    have h' : dst.length = src.length := by simpa using h
    unfold renOf kidOf
    rw [List.idxOf_cons, List.zip_cons_cons, List.lookup]
    by_cases hax : a = x
    · subst hax; simp
    · have h1 : (a == x) = false := by simpa using hax
      have h2 : (x == a) = false := by simpa using Ne.symm hax
      rw [h1, h2]
      simp only [cond_false, List.getI_cons_succ]
      exact renOf_eq src dst h' x
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

variable {α : Type} [BEnc α]

theorem pt_freshIds {l k : α → List ℕ} (hl : PT l) (hk : PT k) :
    PT fun a => freshIds (l a) (k a).length := by
  have hL : PT fun a => (List.range (l a ++ k a).length).filter fun x => decide (x ∉ l a) :=
    (PT.filter (p := fun a x => !decide (x ∈ l a)) (PT.rangeLength (PT.append hl hk))
      (PT.not (PT.elem (hl.comp PT.fst) PT.snd))).of_eq fun a => by
        congr 1; funext x; simp
  exact (PT.map (g := fun a i => ((List.range (l a ++ k a).length).filter
    fun x => decide (x ∉ l a)).getI i) (PT.rangeLength hk) (PT.getI (hL.comp PT.fst) PT.snd)).of_eq
    fun a => (freshIds_eq _ _).symm

theorem pt_copyDesc {t : α → TnDesc} {dst : α → List ℕ} (ht : PT t) (hd : PT dst)
    (hlen : ∀ a, (dst a).length = (t a).ids.length) : PT fun a => copyDesc (t a) (dst a) := by
  have hids : PT fun a => (t a).ids := PT.fst.comp ht
  have hZ : PT fun a => (t a).ids.zip (dst a) :=
    (PT.map (g := fun a i => ((t a).ids.getI i, (dst a).getI i)) (PT.rangeLength hids)
      (PT.pair (PT.getI (hids.comp PT.fst) PT.snd) (PT.getI (hd.comp PT.fst) PT.snd))).of_eq
      fun a => (zip_eq _ _ (hlen a)).symm
  have hren : ∀ {β : Type} [BEnc β] {g : β → α} {y : β → ℕ}, PT g → PT y →
      PT fun b => renOf (t (g b)).ids (dst (g b)) (y b) := fun hg hy =>
    (pt_kidOf (hZ.comp hg) hy).of_eq fun b => (renOf_eq _ _ (hlen _) _).symm
  unfold copyDesc
  refine PT.pair hd (PT.pair ?_ ?_)
  · exact PT.map (g := fun a q => (renOf (t a).ids (dst a) q.1, renOf (t a).ids (dst a) q.2))
      (PT.fst.comp (PT.snd.comp ht)) (PT.pair (hren PT.fst (PT.fst.comp PT.snd))
        (hren PT.fst (PT.snd.comp PT.snd)))
  · exact PT.map (g := fun a y => (renOf (t a).ids (dst a) y, lblOf (t a) y)) hids
      (PT.pair (hren PT.fst PT.snd) (pt_lblOf (ht.comp PT.fst) PT.snd))

theorem pt_progDesc : PT fun x : TnDesc × ℕ => progDesc x.1 x.2 := by
  unfold progDesc
  have hd : PT fun x : TnDesc × ℕ => x.1 := PT.fst
  refine PT.pair (PT.filter (p := fun x y => decide (y ≠ x.2)) (PT.fst.comp hd)
    ((PT.not (PT.eq PT.snd (PT.snd.comp PT.fst))).of_eq fun _ => by simp))
    (PT.pair (PT.filter (p := fun x q => decide (q.1 ≠ x.2 ∧ q.2 ≠ x.2))
      (PT.fst.comp (PT.snd.comp hd)) ((PT.and (PT.not (PT.eq (PT.fst.comp PT.snd)
        (PT.snd.comp PT.fst))) (PT.not (PT.eq (PT.snd.comp PT.snd) (PT.snd.comp PT.fst)))).of_eq
          fun _ => by simp))
      (PT.filter (p := fun x q => decide (q.1 ≠ x.2)) (PT.snd.comp (PT.snd.comp hd))
        ((PT.not (PT.eq (PT.fst.comp PT.snd) (PT.snd.comp PT.fst))).of_eq fun _ => by simp)))

theorem pt_decDesc : PT fun x : TnDesc × ℕ × MethodDesc => decDesc x.1 x.2.1 x.2.2 := by
  have hd : PT fun x : TnDesc × ℕ × MethodDesc => x.1 := PT.fst
  have hx : PT fun x : TnDesc × ℕ × MethodDesc => x.2.1 := PT.fst.comp PT.snd
  have he : PT fun x : TnDesc × ℕ × MethodDesc => x.2.2.2 := PT.snd.comp (PT.snd.comp PT.snd)
  have hfr : PT fun x : TnDesc × ℕ × MethodDesc => freshIds x.1.ids x.2.2.2.ids.length :=
    pt_freshIds (PT.fst.comp hd) (PT.fst.comp he)
  have hcp : PT fun x : TnDesc × ℕ × MethodDesc =>
      copyDesc x.2.2.2 (freshIds x.1.ids x.2.2.2.ids.length) :=
    pt_copyDesc he hfr fun _ => length_freshIds _ _
  have hord : PT fun x : TnDesc × ℕ × MethodDesc => x.1.ordList := PT.fst.comp (PT.snd.comp hd)
  have hlbl : PT fun x : TnDesc × ℕ × MethodDesc => x.1.lbl := PT.snd.comp (PT.snd.comp hd)
  have hfil : ∀ (P : ℕ × ℕ → ℕ → Prop) [∀ q y, Decidable (P q y)],
      PT (fun r : (TnDesc × ℕ × MethodDesc) × (ℕ × ℕ) => decide (P r.2 r.1.2.1)) →
      PT fun x : TnDesc × ℕ × MethodDesc => x.1.ordList.filter fun q => decide (P q x.2.1) :=
    fun P _ hP => PT.filter hord hP
  have h1 := hfil (fun q y => q.2 = y) (PT.eq (PT.snd.comp PT.snd) (hx.comp PT.fst))
  have h2 := hfil (fun q y => q.1 = y) (PT.eq (PT.fst.comp PT.snd) (hx.comp PT.fst))
  have h3 := hfil (fun q y => q.1 ≠ y ∧ q.2 ≠ y) ((PT.and (PT.not (PT.eq (PT.fst.comp PT.snd)
    (hx.comp PT.fst))) (PT.not (PT.eq (PT.snd.comp PT.snd) (hx.comp PT.fst)))).of_eq
      fun _ => by simp)
  have hA := PT.flatMap (g := fun (x : TnDesc × ℕ × MethodDesc) (q : ℕ × ℕ) =>
      (freshIds x.1.ids x.2.2.2.ids.length).map fun n => (q.1, n))
    h1 (PT.map (g := fun (r : (TnDesc × ℕ × MethodDesc) × (ℕ × ℕ)) (n : ℕ) => (r.2.1, n))
      (hfr.comp PT.fst) (PT.pair (PT.fst.comp (PT.snd.comp PT.fst)) PT.snd))
  have hB := PT.flatMap (g := fun (x : TnDesc × ℕ × MethodDesc) (q : ℕ × ℕ) =>
      (freshIds x.1.ids x.2.2.2.ids.length).map fun n => (n, q.2))
    h2 (PT.map (g := fun (r : (TnDesc × ℕ × MethodDesc) × (ℕ × ℕ)) (n : ℕ) => (n, r.2.2))
      (hfr.comp PT.fst) (PT.pair PT.snd (PT.snd.comp (PT.snd.comp PT.fst))))
  have hids : PT fun x : TnDesc × ℕ × MethodDesc => x.1.ids.filter fun y => decide (y ≠ x.2.1) :=
    PT.filter (PT.fst.comp hd) ((PT.not (PT.eq PT.snd (hx.comp PT.fst))).of_eq fun _ => by simp)
  have hl2 : PT fun x : TnDesc × ℕ × MethodDesc => x.1.lbl.filter fun q => decide (q.1 ≠ x.2.1) :=
    PT.filter hlbl ((PT.not (PT.eq (PT.fst.comp PT.snd) (hx.comp PT.fst))).of_eq fun _ => by simp)
  refine (PT.pair (PT.append hids hfr) (PT.pair (PT.dedup (PT.append (PT.append (PT.append
    (PT.fst.comp (PT.snd.comp hcp)) hA) hB) h3)) (PT.append hl2 (PT.snd.comp (PT.snd.comp hcp))))).of_eq
    fun x => ?_
  rfl

/-- The progressions of a configuration at the task `x`. -/
def succsAt (p : ProbDesc) (c : PCfg) (x : ℕ) : List PCfg :=
  if c.2.ordList.all (fun q => q.2 != x) then
    if (lblOf c.2 x).1 then
      (p.methods.filter fun e => e.1 == (lblOf c.2 x).2).map fun e => (c.1, decDesc c.2 x e)
    else if (runStep p (true, c.1) (lblOf c.2 x).2).1 then
      [((runStep p (true, c.1) (lblOf c.2 x).2).2.dedup, progDesc c.2 x)]
    else []
  else []

theorem succs_eq (p : ProbDesc) (c : PCfg) : succs p c = c.2.ids.flatMap (succsAt p c) := rfl

theorem pt_succs : PT fun x : ProbDesc × PCfg => succs x.1 x.2 := by
  -- context `(x, y)` with `x = (p, c)` and `y` an id
  have hp : PT fun r : (ProbDesc × PCfg) × ℕ => r.1.1 := PT.fst.comp PT.fst
  have hs : PT fun r : (ProbDesc × PCfg) × ℕ => r.1.2.1 := PT.fst.comp (PT.snd.comp PT.fst)
  have hd : PT fun r : (ProbDesc × PCfg) × ℕ => r.1.2.2 := PT.snd.comp (PT.snd.comp PT.fst)
  have hy : PT fun r : (ProbDesc × PCfg) × ℕ => r.2 := PT.snd
  have hl : PT fun r : (ProbDesc × PCfg) × ℕ => lblOf r.1.2.2 r.2 := pt_lblOf hd hy
  have hall : PT fun r : (ProbDesc × PCfg) × ℕ => r.1.2.2.ordList.all fun q => q.2 != r.2 :=
    PT.all (PT.fst.comp (PT.snd.comp hd)) ((PT.not (PT.beqL (PT.snd.comp PT.snd)
      (hy.comp PT.fst))).of_eq fun _ => rfl)
  have hmeth : PT fun r : (ProbDesc × PCfg) × ℕ =>
      (r.1.1.methods.filter fun e => e.1 == (lblOf r.1.2.2 r.2).2).map
        fun e => (r.1.2.1, decDesc r.1.2.2 r.2 e) :=
    PT.map (PT.filter (p := fun r (e : MethodDesc) => e.1 == (lblOf r.1.2.2 r.2).2)
      (PT.snd.comp (PT.fst.comp hp)) (PT.beqL (PT.fst.comp PT.snd) (PT.snd.comp (hl.comp PT.fst))))
      (PT.pair (hs.comp PT.fst) (pt_decDesc.comp (PT.pair (hd.comp PT.fst)
        (PT.pair (hy.comp PT.fst) PT.snd))))
  have hrun : PT fun r : (ProbDesc × PCfg) × ℕ => runStep r.1.1 (true, r.1.2.1) (lblOf r.1.2.2 r.2).2 :=
    pt_runStep.comp (PT.pair (PT.pair hp (PT.const ([] : List ℕ)))
      (PT.pair (PT.pair (PT.const true) hs) (PT.snd.comp hl)))
  have hin : PT fun r : (ProbDesc × PCfg) × ℕ => succsAt r.1.1 r.1.2 r.2 :=
    (PT.cond hall (PT.cond (PT.fst.comp hl) hmeth (PT.cond (PT.fst.comp hrun)
      (PT.single (PT.pair (PT.dedup (PT.snd.comp hrun)) (pt_progDesc.comp (PT.pair hd hy))))
      (PT.const ([] : List PCfg)))) (PT.const ([] : List PCfg))).of_eq fun r => by
        simp only [succsAt, cond_eq_if]
  exact (PT.flatMap (g := fun (x : ProbDesc × PCfg) (y : ℕ) => succsAt x.1 x.2 y)
    (PT.fst.comp (PT.snd.comp PT.snd)) hin).of_eq fun x => (succs_eq _ _).symm

theorem pt_initCfg : PT initCfg := by
  unfold initCfg
  exact PT.pair (PT.dedup (PT.fst.comp PT.snd)) (PT.pair (PT.fst.comp (PT.fst.comp (PT.snd.comp
    PT.snd))) (PT.pair (PT.dedup (PT.fst.comp (PT.snd.comp (PT.fst.comp (PT.snd.comp PT.snd)))))
      (PT.snd.comp (PT.snd.comp (PT.fst.comp (PT.snd.comp PT.snd))))))

theorem pt_goalB : PT fun x : ProbDesc × List ℕ => goalB x.1 x.2 := by
  unfold goalB
  exact PT.and (PT.all (PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))))
    (PT.elem (PT.snd.comp PT.fst) PT.snd))
    (PT.all (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.fst))))
      (PT.not (PT.elem (PT.snd.comp PT.fst) PT.snd)))

end Article

end HTN
