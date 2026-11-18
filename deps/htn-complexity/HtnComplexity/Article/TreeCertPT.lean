import HtnComplexity.Article.TreeCert
/-!
# The check of tree certificates is polynomial time

`HTN.Article.pt_certB`: the check `HTN.Article.certB` of a tree certificate against a problem
description is a polynomial-time function in the typed calculus.  Lookups are written as the
head of a filter (`HTN.Article.kidOf_eq`, `HTN.Article.lblOf_eq`), the pairwise check runs over
the decompositions of the list (`HTN.Article.pt_pairwiseB`).
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom Syn.PolyInst PTime

theorem kidOf_eq (l : List (ℕ × ℕ)) (x : ℕ) : kidOf l x = ((l.filter fun e => e.1 == x).headI).2 := by
  unfold kidOf
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, b⟩ := e
    by_cases h : k = x
    · subst h; simp [List.lookup]
    · have h' : (x == k) = false := by simpa using Ne.symm h
      simp [List.lookup, h', h, ih]

theorem lblOf_eq (t : TnDesc) (x : ℕ) : lblOf t x = ((t.lbl.filter fun q => q.1 == x).headI).2 := by
  unfold lblOf
  induction t.lbl with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k, b⟩ := e
    by_cases h : k = x
    · subst h; simp [List.lookup]
    · have h' : (x == k) = false := by simpa using Ne.symm h
      simp [List.lookup, h', h, ih]

variable {α : Type} [BEnc α]

/-- `PT.beq` for any lawful `BEq` instance. -/
theorem PT.beqL {β : Type} [BEnc β] [DecidableEq β] [BEq β] [LawfulBEq β] {f g : α → β} (hf : PT f)
    (hg : PT g) : PT fun a => f a == g a :=
  (PT.eq hf hg).of_eq fun a => by by_cases h : f a = g a <;> simp [h]

/-- `PT.elem` for any decision procedure of membership. -/
theorem PT.elemL {β : Type} [BEnc β] [DecidableEq β] {f : α → List β} {g : α → β}
    [I : ∀ a, Decidable (g a ∈ f a)] (hf : PT f) (hg : PT g) : PT fun a => @decide _ (I a) :=
  (PT.elem hf hg).of_eq fun a => by by_cases h : g a ∈ f a <;> simp [h]

theorem pt_pairwiseB {β : Type} [BEnc β] {f : α → List β} {R : α → β → β → Bool} (hf : PT f)
    (hR : PT fun q : α × β × β => R q.1 q.2.1 q.2.2) : PT fun a => pairwiseB (R a) (f a) := by
  have h := PT.flatMapSplits (g := fun a _ b l₂ => [l₂.all (R a b)]) hf
    (PT.single (PT.all (PT.snd.comp (PT.snd.comp PT.snd))
      (hR.comp (PT.pair (PT.fst.comp PT.fst)
        (PT.pair (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.fst))) PT.snd)))))
  refine (PT.all (p := fun _ (b : Bool) => b) h PT.snd).of_eq fun a => ?_
  unfold pairwiseB
  simp [List.all_flatMap]

theorem pt_lblOf {T : α → TnDesc} {X : α → ℕ} (hT : PT T) (hX : PT X) :
    PT fun a => lblOf (T a) (X a) :=
  (PT.snd.comp (PT.headI (PT.filter (p := fun a (q : ℕ × Bool × ℕ) => q.1 == X a)
    (PT.snd.comp (PT.snd.comp hT)) (PT.beq (PT.fst.comp PT.snd) (hX.comp PT.fst))))).of_eq
    fun a => (lblOf_eq _ _).symm

theorem pt_kidOf {K : α → List (ℕ × ℕ)} {X : α → ℕ} (hK : PT K) (hX : PT X) :
    PT fun a => kidOf (K a) (X a) :=
  (PT.snd.comp (PT.headI (PT.filter (p := fun a (e : ℕ × ℕ) => e.1 == X a)
    hK (PT.beq (PT.fst.comp PT.snd) (hX.comp PT.fst))))).of_eq
    fun a => (kidOf_eq _ _).symm

theorem pt_kidsB {N : α → List NodeC} {J : α → ℕ} {T : α → TnDesc} {K : α → List (ℕ × ℕ)}
    (hN : PT N) (hJ : PT J) (hT : PT T) (hK : PT K) :
    PT fun a => kidsB (N a) (J a) (T a) (K a) := by
  unfold kidsB
  refine PT.and (PT.all (PT.fst.comp hT) (PT.elem (PT.map (g := fun _ (e : ℕ × ℕ) => e.1)
    (hK.comp PT.fst) (PT.fst.comp PT.snd)) PT.snd)) (PT.all hK (PT.and
      (PT.lt (PT.snd.comp PT.snd) (hJ.comp PT.fst)) ?_))
  exact PT.eq (PT.fst.comp (PT.getI (hN.comp PT.fst) (PT.snd.comp PT.snd)))
    (pt_lblOf (hT.comp PT.fst) (PT.fst.comp PT.snd))

theorem pt_mergeB {T : α → TnDesc} {Y : α → ℕ → List ℕ} {ys : α → List ℕ} {w : α → List (ℕ × ℕ)}
    (hT : PT T) (hY : PT fun q : α × ℕ => Y q.1 q.2) (hys : PT ys) (hw : PT w) :
    PT fun a => mergeB (T a) (Y a) (ys a) (w a) := by
  unfold mergeB
  refine PT.and (PT.and (PT.and (PT.beqL (PT.map (g := fun _ (e : ℕ × ℕ) => e.2) hw
    (PT.snd.comp PT.snd)) hys) (PT.all hw (PT.elem (PT.fst.comp (hT.comp PT.fst))
      (PT.fst.comp PT.snd)))) (PT.all (PT.fst.comp hT) (PT.beqL (PT.map (g := fun _ (e : ℕ × ℕ) => e.2)
        (PT.filter (p := fun (q : α × ℕ) (e : ℕ × ℕ) => e.1 == q.2) (hw.comp PT.fst)
          (PT.beq (PT.fst.comp PT.snd) (PT.snd.comp PT.fst))) (PT.snd.comp PT.snd)) hY)))
    (pt_pairwiseB hw ?_)
  exact PT.not (PT.elemL (PT.fst.comp (PT.snd.comp (hT.comp PT.fst)))
    (PT.pair (PT.fst.comp (PT.snd.comp PT.snd)) (PT.fst.comp (PT.fst.comp PT.snd))))

theorem pt_nodeB : PT fun x : ProbDesc × List NodeC × ℕ => nodeB x.1 x.2.1 x.2.2 := by
  have hv : PT fun x : ProbDesc × List NodeC × ℕ => x.2.1.getI x.2.2 :=
    PT.getI (PT.fst.comp PT.snd) (PT.snd.comp PT.snd)
  have hmi : PT fun x : ProbDesc × List NodeC × ℕ => (x.2.1.getI x.2.2).mi := PT.fst.comp (PT.snd.comp hv)
  have hm : PT fun x : ProbDesc × List NodeC × ℕ => x.1.methods.getI (x.2.1.getI x.2.2).mi :=
    PT.getI (PT.snd.comp (PT.fst.comp PT.fst)) hmi
  have hkids : PT fun x : ProbDesc × List NodeC × ℕ => (x.2.1.getI x.2.2).kids :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp hv))
  have hys : PT fun x : ProbDesc × List NodeC × ℕ => (x.2.1.getI x.2.2).ys :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hv)))
  have hw : PT fun x : ProbDesc × List NodeC × ℕ => (x.2.1.getI x.2.2).w :=
    PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp hv)))
  have hY : PT fun q : (ProbDesc × List NodeC × ℕ) × ℕ =>
      (q.1.2.1.getI (kidOf (q.1.2.1.getI q.1.2.2).kids q.2)).ys :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.getI (PT.fst.comp (PT.snd.comp PT.fst))
      (pt_kidOf (hkids.comp PT.fst) PT.snd)))))
  have hA := PT.and (PT.and (PT.and (PT.lt hmi (PT.length (PT.snd.comp (PT.fst.comp PT.fst))))
    (PT.beqL (PT.fst.comp hm) (PT.snd.comp (PT.fst.comp hv))))
    (pt_kidsB (PT.fst.comp PT.snd) (PT.snd.comp PT.snd) (PT.snd.comp hm) hkids))
    (pt_mergeB (Y := fun x y => (x.2.1.getI (kidOf (x.2.1.getI x.2.2).kids y)).ys)
      (PT.snd.comp hm) hY hys hw)
  have hB := PT.beqL hys (PT.single (PT.snd.comp (PT.fst.comp hv)))
  refine (PT.ite (p := fun x : ProbDesc × List NodeC × ℕ => (x.2.1.getI x.2.2).lbl.1 = true)
    ((PT.fst.comp (PT.fst.comp hv)).of_eq fun x => by simp [NodeC.lbl]) hA hB).of_eq fun x => ?_
  rfl

theorem pt_certB : PT fun x : ProbDesc × TCert => certB x.1 x.2 := by
  have hp : PT fun x : ProbDesc × TCert => x.1 := PT.fst
  have hn : PT fun x : ProbDesc × TCert => x.2.1 := PT.fst.comp PT.snd
  have hr : PT fun x : ProbDesc × TCert => x.2.2.1 := PT.fst.comp (PT.snd.comp PT.snd)
  have htn : PT fun x : ProbDesc × TCert => x.1.tnI := PT.fst.comp (PT.snd.comp (PT.snd.comp hp))
  have hY : PT fun q : (ProbDesc × TCert) × ℕ => (q.1.2.1.getI (kidOf q.1.2.2.1 q.2)).ys :=
    PT.fst.comp (PT.snd.comp (PT.snd.comp (PT.snd.comp (PT.getI (hn.comp PT.fst)
      (pt_kidOf (hr.comp PT.fst) PT.snd)))))
  unfold certB
  exact PT.and (PT.and (PT.all (PT.rangeLength hn)
    (pt_nodeB.comp (PT.pair (hp.comp PT.fst) (PT.pair (hn.comp PT.fst) PT.snd))))
    (pt_kidsB hn (PT.length hn) htn hr))
    (pt_mergeB (Y := fun x y => (x.2.1.getI (kidOf x.2.2.1 y)).ys) htn hY (PT.fst.comp (PT.snd.comp (PT.snd.comp PT.snd)))
      (PT.snd.comp (PT.snd.comp (PT.snd.comp PT.snd))))

end Article

end HTN
