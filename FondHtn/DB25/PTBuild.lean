import FondHtn.DB25.PTOps
/-!
# Polynomial time: descriptions from phase programs

`FOND.DB.pt_mkDesc`: `mkDesc` is computed in polynomial time.  The definitions use `Nat.unpair`
(phases of ids); they are rewritten into enumerations first (`FOND.DB.ordList_eq`,
`FOND.DB.mkActs_eq`).
-/

namespace FOND

namespace DB

open HTN HTN.Syn HTN.Syn.PolyDom PTime

/-! ## Unpair-free forms -/

/-- The ids with their phases. -/
def phasedIds (phs : List (List FActDesc)) (loop : Bool) : List (ℕ × ℕ) :=
  (List.range phs.length).flatMap (fun p => (List.range (phs.getI p).length).map
    fun i => (p, Nat.pair p i)) ++ (if loop then [(phs.length, Nat.pair phs.length 0)] else [])

theorem phasedIds_eq (phs : List (List FActDesc)) (loop : Bool) :
    phasedIds phs loop = (allIds phs loop).map fun x => (phOf x, x) := by
  cases loop <;>
  simp [phasedIds, allIds, primIds, List.map_flatMap, List.map_map, Function.comp_def, phOf, topId]

theorem ordList_eq (k : ℕ) (phs : List (List FActDesc)) (loop : Bool) :
    (progTn k phs loop).ordList = (phasedIds phs loop).flatMap fun a =>
      ((phasedIds phs loop).filter fun b => decide (a.1 < b.1)).map fun b => (a.2, b.2) := by
  rw [phasedIds_eq]
  simp only [progTn, TnDesc.ordList, List.flatMap_map, List.filter_map, List.map_map]
  rfl

theorem mkActs_eq (ml : List (List (List FActDesc) × Bool)) :
    mkActs ml = (List.range ml.length).flatMap fun k =>
      (List.range (ml.getI k).1.length).flatMap fun p =>
        (List.range (((ml.getI k).1).getI p).length).map fun i =>
          (Nat.pair k (Nat.pair p i), ((((ml.getI k).1).getI p).getI i).2) := by
  simp only [mkActs, primIds, List.map_flatMap, List.map_map]
  congr 1; funext k; congr 1; funext p; congr 1; funext i
  simp [actAt, phOf]

/-! ## Polynomial time -/

section

variable {α : Type} [BEnc α]

theorem pt_phasedIds {phs : α → List (List FActDesc)} {loop : α → Bool} (hphs : PT phs)
    (hloop : PT loop) : PT fun a => phasedIds (phs a) (loop a) := by
  unfold phasedIds
  refine PT.append (PT.flatMap (PT.rangeLength hphs) (PT.map (PT.rangeLength
    (PT.getI (hphs.comp PT.fst) PT.snd)) (PT.pair (PT.snd.comp PT.fst)
      (PT.natPair (PT.snd.comp PT.fst) PT.snd)))) ?_
  exact PT.ite (PT.eq hloop (PT.const true)) (PT.single (PT.pair (PT.length hphs)
    (PT.natPair (PT.length hphs) (PT.const 0)))) PT.nil

theorem pt_primIds {phs : α → List (List FActDesc)} (hphs : PT phs) :
    PT fun a => primIds (phs a) := by
  unfold primIds
  exact PT.flatMap (PT.rangeLength hphs) (PT.map (PT.rangeLength
    (PT.getI (hphs.comp PT.fst) PT.snd)) (PT.natPair (PT.snd.comp PT.fst) PT.snd))

theorem pt_allIds {phs : α → List (List FActDesc)} {loop : α → Bool} (hphs : PT phs)
    (hloop : PT loop) : PT fun a => allIds (phs a) (loop a) := by
  unfold allIds topId
  exact PT.append (pt_primIds hphs) (PT.ite (PT.eq hloop (PT.const true))
    (PT.single (PT.natPair (PT.length hphs) (PT.const 0))) PT.nil)

theorem pt_progTn {k : α → ℕ} {phs : α → List (List FActDesc)} {loop : α → Bool} (hk : PT k)
    (hphs : PT phs) (hloop : PT loop) : PT fun a => progTn (k a) (phs a) (loop a) := by
  have hord : PT fun a => (progTn (k a) (phs a) (loop a)).ordList := by
    have hP := pt_phasedIds hphs hloop
    have hflt : PT fun z : α × (ℕ × ℕ) => (phasedIds (phs z.1) (loop z.1)).filter
        fun b => decide (z.2.1 < b.1) :=
      PT.filter (p := fun (z : α × (ℕ × ℕ)) (b : ℕ × ℕ) => decide (z.2.1 < b.1)) (hP.comp PT.fst)
        (PT.lt (PT.fst.comp (PT.snd.comp PT.fst)) (PT.fst.comp PT.snd))
    have hin : PT fun z : α × (ℕ × ℕ) => ((phasedIds (phs z.1) (loop z.1)).filter
        fun b => decide (z.2.1 < b.1)).map fun b => (z.2.2, b.2) :=
      PT.map (g := fun (z : α × (ℕ × ℕ)) (b : ℕ × ℕ) => (z.2.2, b.2)) hflt
        (PT.pair (PT.snd.comp (PT.snd.comp PT.fst)) (PT.snd.comp PT.snd))
    refine (PT.flatMap (g := fun (a : α) (x : ℕ × ℕ) => ((phasedIds (phs a) (loop a)).filter
      fun (b : ℕ × ℕ) => decide (x.1 < b.1)).map fun (b : ℕ × ℕ) => (x.2, b.2)) hP hin).of_eq fun a =>
        (ordList_eq _ _ _).symm
  have hlbl : PT fun a => (progTn (k a) (phs a) (loop a)).lbl := by
    unfold progTn TnDesc.lbl topId
    exact PT.append (PT.map (pt_primIds hphs) (PT.pair PT.snd (PT.pair (PT.const false)
      (PT.natPair (hk.comp PT.fst) PT.snd))))
      (PT.ite (PT.eq hloop (PT.const true)) (PT.single (PT.pair (PT.natPair (PT.length hphs)
        (PT.const 0)) (PT.const (true, 0)))) PT.nil)
  exact (PT.pair (pt_allIds hphs hloop) (PT.pair hord hlbl)).of_eq fun a => rfl

theorem pt_mkActs {ml : α → List (List (List FActDesc) × Bool)} (hml : PT ml) :
    PT fun a => mkActs (ml a) := by
  refine (PT.flatMap (PT.rangeLength hml) ?_).of_eq fun a => (mkActs_eq _).symm
  -- on `(a, k)`
  have hphs : PT fun z : α × ℕ => ((ml z.1).getI z.2).1 :=
    PT.fst.comp (PT.getI (hml.comp PT.fst) PT.snd)
  refine PT.flatMap (PT.rangeLength hphs) ?_
  -- on `((a, k), p)`
  have hph : PT fun z : (α × ℕ) × ℕ => ((ml z.1.1).getI z.1.2).1.getI z.2 :=
    PT.getI (hphs.comp PT.fst) PT.snd
  refine PT.map (PT.rangeLength hph) ?_
  -- on `(((a, k), p), i)`
  exact PT.pair (PT.natPair (PT.snd.comp (PT.fst.comp PT.fst))
    (PT.natPair (PT.snd.comp PT.fst) PT.snd)) (PT.snd.comp (PT.getI (hph.comp PT.fst) PT.snd))

theorem pt_mlist {pre : α → List (List FActDesc)} {loops finals : α → List (List (List FActDesc))}
    (hpre : PT pre) (hl : PT loops) (hf : PT finals) :
    PT fun a => mlist (pre a) (loops a) (finals a) := by
  unfold mlist
  exact PT.cons (PT.pair hpre (PT.const true)) (PT.append (PT.map hl (PT.pair PT.snd
    (PT.const true))) (PT.map hf (PT.pair PT.snd (PT.const false))))

/-- **`mkDesc` is computed in polynomial time.** -/
theorem pt_mkDesc {init : α → List ℕ} {pre : α → List (List FActDesc)}
    {loops finals : α → List (List (List FActDesc))} (hi : PT init) (hpre : PT pre)
    (hl : PT loops) (hf : PT finals) :
    PT fun a => mkDesc (init a) (pre a) (loops a) (finals a) := by
  have hml := pt_mlist hpre hl hf
  have hR : PT fun a => List.range ((mlist (pre a) (loops a) (finals a)).length - 1) :=
    (PT.rangeLength (PT.tail hml)).of_eq fun a => by simp
  have hm : PT fun z : α × ℕ => (0, progTn (z.2 + 1) ((mlist (pre z.1) (loops z.1)
      (finals z.1)).getI (z.2 + 1)).1 ((mlist (pre z.1) (loops z.1) (finals z.1)).getI
        (z.2 + 1)).2) := by
    have hg : PT fun z : α × ℕ => (mlist (pre z.1) (loops z.1) (finals z.1)).getI (z.2 + 1) :=
      PT.getI (hml.comp PT.fst) (PT.succ PT.snd)
    exact PT.pair (PT.const 0) (pt_progTn (PT.succ PT.snd) (PT.fst.comp hg) (PT.snd.comp hg))
  unfold mkDesc
  exact PT.pair (PT.pair (pt_mkActs hml) (PT.map hR hm))
    (PT.pair hi (pt_progTn (PT.const 0) hpre (PT.const true)))

end

end DB

end FOND
