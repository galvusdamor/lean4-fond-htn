import HtnComplexity.Article.SynBridge
import HtnComplexity.Computable.GridDesc
/-!
# Domains given by method bodies with the actions written out

A list of method bodies whose cells are either full action descriptions or compound task
numbers (`HTN.Article.NBody`) determines a domain description (`HTN.Article.nDom`): the actions
are the (deduplicated) actions of the cells, the methods the grids of the bodies.  This is the
form in which polynomial-time constructions are written down:

* `HTN.Article.pt_nDom`, `HTN.Article.pt_gridDesc` — polynomial time;
* `HTN.Article.valid_artOf_nDom` — the normal form (`HTN.Article.artOf`) of such a domain with a
  grid instance is well formed, provided actions of the same name are equal.
-/

namespace HTN

namespace Article

open Syn Syn.PolyDom PTime

/-- A method body with the actions written out. -/
abbrev NBody : Type := ℕ × List (List (ActionDesc ⊕ ℕ))

/-- The label of a cell. -/
def nLab : ActionDesc ⊕ ℕ → Bool × ℕ
  | Sum.inl a => (false, a.1)
  | Sum.inr c => (true, c)

/-- The actions of the cells of a body. -/
def bodyActs (b : NBody) : List ActionDesc := b.2.flatten.flatMap fun x => x.elim (fun a => [a]) fun _ => []

/-- **The domain of a list of bodies.** -/
def nDom (bs : List NBody) : DomDesc :=
  ((bs.flatMap bodyActs).dedup, bs.map fun b => (b.1, gridDesc (b.2.map (·.map nLab))))

theorem mem_bodyActs {b : NBody} {a : ActionDesc} : a ∈ bodyActs b ↔ Sum.inl a ∈ b.2.flatten := by
  simp only [bodyActs, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, ha⟩
    rcases x with a' | c
    · simp at ha; subst ha; exact hx
    · simp at ha
  · intro h; exact ⟨_, h, by simp⟩

/-! ### Well-formedness -/

theorem mem_cellLbl {ls : List (List (Bool × ℕ))} {r : ℕ × Bool × ℕ} (h : r ∈ cellLbl ls) :
    r.2 ∈ ls.flatten := by
  simp only [cellLbl, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  rw [List.mem_flatten]
  refine ⟨gridRow ls i, ?_, ?_⟩
  · unfold gridRow; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  · rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- **The normal form of a domain of bodies is well formed.** -/
theorem valid_artOf_nDom {bs : List NBody} {q : InstDesc}
    (hfun : ∀ a ∈ bs.flatMap bodyActs, ∀ a' ∈ bs.flatMap bodyActs, a.1 = a'.1 → a = a')
    (hq : q.tnI.ids.Nodup ∧ (q.tnI.lbl.map Prod.fst).Perm q.tnI.ids ∧
      ∀ r ∈ q.tnI.lbl, r.2.1 = false → r.2.2 ∈ (nDom bs).actions.map Prod.fst) :
    (artOf (nDom bs) q).Valid := by
  refine valid_artOf ?_ hq ?_
  · show ((bs.flatMap bodyActs).dedup.map Prod.fst).Nodup
    refine List.Nodup.map_on ?_ (List.nodup_dedup _)
    intro a ha a' ha' h
    exact hfun a (List.mem_dedup.1 ha) a' (List.mem_dedup.1 ha') h
  · intro m hm
    simp only [nDom, DomDesc.methods, List.mem_map] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    refine ⟨nodup_cellIds, by rw [gridDesc_lbl, map_fst_cellLbl]; exact List.Perm.refl _,
      fun r hr hf => ?_⟩
    have h := mem_cellLbl hr
    simp only [List.mem_flatten, List.mem_map] at h
    obtain ⟨_, ⟨row, hrow, rfl⟩, hx⟩ := h
    obtain ⟨x, hx', hxl⟩ := List.mem_map.1 hx
    rcases x with a | c
    · simp only [nLab] at hxl
      rw [← hxl]
      show a.1 ∈ (bs.flatMap bodyActs).dedup.map Prod.fst
      refine List.mem_map.2 ⟨a, List.mem_dedup.2 (List.mem_flatMap.2 ⟨b, hb, ?_⟩), rfl⟩
      exact mem_bodyActs.2 (List.mem_flatten.2 ⟨row, hrow, hx'⟩)
    · simp only [nLab] at hxl
      rw [← hxl] at hf; simp at hf

/-! ### Polynomial time -/

variable {α : Type} [BEnc α]

theorem getD_eq_getI_list {β : Type} (l : List (List β)) (i : ℕ) : l.getD i [] = l.getI i := by
  rw [← List.getD_default_eq_getI]; rfl

theorem pt_gridDesc {ls : α → List (List (Bool × ℕ))} (h : PT ls) : PT fun a => gridDesc (ls a) := by
  have hR := PT.rangeLength h
  have hrow : PT fun q : α × ℕ => gridRow (ls q.1) q.2 :=
    (PT.getI (h.comp PT.fst) PT.snd).of_eq fun q => (getD_eq_getI_list _ _).symm
  unfold gridDesc cellIds cellOrd cellLbl
  refine PT.pair ?_ (PT.pair ?_ ?_)
  · exact PT.flatMap hR (PT.map (PT.rangeLength hrow) (PT.natPair (PT.snd.comp PT.fst) PT.snd))
  · refine PT.flatMap hR (PT.map ((PT.rangeLength (PT.tail hrow)).of_eq fun q => by simp)
      (PT.pair (PT.natPair (PT.snd.comp PT.fst) PT.snd) (PT.natPair (PT.snd.comp PT.fst)
        (PT.succ PT.snd))))
  · refine PT.flatMap hR (PT.map (PT.rangeLength hrow) (PT.pair (PT.natPair (PT.snd.comp PT.fst)
      PT.snd) ((PT.getI (hrow.comp PT.fst) PT.snd).of_eq fun q => ?_)))
    rw [← List.getD_default_eq_getI]; rfl

theorem pt_nLab : PT nLab :=
  (PT.sumElim (f := fun x : ActionDesc ⊕ ℕ => x) (g := fun _ (a : ActionDesc) => (false, a.1))
    (h := fun _ (c : ℕ) => (true, c)) PT.id
    (PT.pair (PT.const false) (PT.fst.comp PT.snd)) (PT.pair (PT.const true) PT.snd)).of_eq
    fun x => by rcases x with a | c <;> rfl

theorem pt_bodyActs {b : α → NBody} (hb : PT b) : PT fun a => bodyActs (b a) := by
  unfold bodyActs
  have hfl : PT fun a => (b a).2.flatten :=
    (PT.flatMap (g := fun _ l => l) (PT.snd.comp hb) PT.snd).of_eq fun a => by simp
  exact PT.flatMap hfl (PT.sumElim (f := fun q : α × (ActionDesc ⊕ ℕ) => q.2)
    (g := fun _ (a : ActionDesc) => [a]) (h := fun _ (_ : ℕ) => ([] : List ActionDesc)) PT.snd
    (PT.single PT.snd) (PT.const []))

theorem pt_nDom {bs : α → List NBody} (h : PT bs) : PT fun a => nDom (bs a) := by
  unfold nDom
  exact PT.pair (PT.dedup (PT.flatMap h (pt_bodyActs PT.snd)))
    (PT.map h (PT.pair (PT.fst.comp PT.snd) (pt_gridDesc (PT.map (PT.snd.comp PT.snd)
      (PT.map PT.snd (pt_nLab.comp PT.snd))))))

end Article

end HTN
