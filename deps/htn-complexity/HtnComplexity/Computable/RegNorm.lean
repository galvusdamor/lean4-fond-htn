import HtnComplexity.Computable.RegInv
import HtnPlanning.Core.ListsUpTo
/-!
# Normal forms of search configurations

A search configuration carries arbitrarily large identifiers — every decomposition inserts a
fresh copy of a method's subtask network above the identifiers used so far — so the search space
of `HtnComplexity/Computable/PoSearch.lean` is infinite even when, as for a regular domain
description, the configurations stay *small*.

This file supplies the **normal form** of a configuration:

* the state is replaced by the sublist of `HTN.Syn.allFacts d q` it contains, and
* the search network by `HTN.Syn.normNet`, which keeps only the tasks still to be processed and
  renames every identifier to its **index** among them.

Two configurations with the same normal form denote the same situation
(`HTN.Syn.toTN_normNet_iso`: a search network is isomorphic to its normal form), and — this is
the point — for a configuration satisfying the invariant `HTN.Syn.RegInv` the normal form
belongs to the explicit finite list `HTN.Syn.allCfgs d q` (`HTN.Syn.mem_allCfgs`).  That list is
what bounds the length of a shortest solution path in
`HtnComplexity/Computable/RegDecide.lean`.
-/

namespace HTN

namespace Syn

/-! ### The normal form of a search network -/

namespace PNet

/-- The label of an identifier, as a pair — `HTN.Syn.PNet.label` before the decoding. -/
def lblPair (p : PNet) (i : ℕ) : Bool × ℕ :=
  p.foldr (fun x r => if x.1 = i then x.2.1 else r) (false, 0)

theorem ofPair_lblPair (p : PNet) (i : ℕ) : TnDesc.ofPair (p.lblPair i) = p.label i := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.1 = i
    · simp [lblPair, label, h]
    · simp only [lblPair, label, List.foldr_cons, if_neg h]
      exact ih

theorem lblPair_eq_of_mem {p : PNet} {x : PItem} (hx : x ∈ p) (hnd : p.allIds.Nodup) :
    p.lblPair x.1 = x.2.1 := foldr_eq_of_mem (fun y => y.2.1) _ hx hnd

end PNet

/-- **The normal form of a search network**: the tasks still to be processed, each identifier
replaced by its index in the list of those tasks. -/
def normNet (p : PNet) : PNet :=
  p.ids.map (fun i =>
    (p.ids.idxOf i, p.lblPair i, true, ((p.deps i).map (fun j => p.ids.idxOf j)).dedup))

/-- **The normal form of a search configuration.** -/
def normCfg (d : DomDesc) (q : InstDesc) (c : PConfig) : PConfig :=
  ((allFacts d q).filter (fun f => memB c.1 f), normNet c.2)

theorem mem_normNet_of_mem_ids {p : PNet} {i : ℕ} (hi : i ∈ p.ids) :
    (p.ids.idxOf i, p.lblPair i, true, ((p.deps i).map (fun j => p.ids.idxOf j)).dedup)
      ∈ normNet p := List.mem_map_of_mem hi

theorem allIds_normNet (p : PNet) :
    (normNet p).allIds = p.ids.map (fun i => p.ids.idxOf i) := by
  simp [normNet, PNet.allIds, List.map_map, Function.comp_def]

theorem nodup_allIds_normNet {p : PNet} (h : PNet.Ok p) : (normNet p).allIds.Nodup := by
  rw [allIds_normNet]
  refine List.Nodup.map_on ?_ h.nodup_ids
  intro a ha b _ hab
  exact (List.idxOf_inj ha).1 hab

theorem ids_normNet (p : PNet) : (normNet p).ids = p.ids.map (fun i => p.ids.idxOf i) := by
  have hfil : (normNet p).filter (fun x => x.2.2.1) = normNet p := by
    refine List.filter_eq_self.2 fun x hx => ?_
    simp only [normNet, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rfl
  rw [PNet.ids, hfil, ← PNet.allIds, allIds_normNet]

theorem mem_ids_normNet {p : PNet} {i : ℕ} (hi : i ∈ p.ids) :
    p.ids.idxOf i ∈ (normNet p).ids := by
  rw [ids_normNet]
  exact List.mem_map_of_mem hi

theorem deps_normNet {p : PNet} (h : PNet.Ok p) {i : ℕ} (hi : i ∈ p.ids) :
    (normNet p).deps (p.ids.idxOf i) = ((p.deps i).map (fun j => p.ids.idxOf j)).dedup :=
  PNet.deps_eq_of_mem (mem_normNet_of_mem_ids hi) (nodup_allIds_normNet h)

theorem label_normNet {p : PNet} (h : PNet.Ok p) {i : ℕ} (hi : i ∈ p.ids) :
    (normNet p).label (p.ids.idxOf i) = p.label i := by
  rw [PNet.label_eq_of_head (mem_normNet_of_mem_ids hi) rfl (nodup_allIds_normNet h)]
  exact PNet.ofPair_lblPair p i

/-- Membership in the renamed predecessor list, for identifiers still to be processed. -/
theorem mem_deps_normNet_iff {p : PNet} (h : PNet.Ok p) {a b : ℕ} (hb : b ∈ p.ids) :
    p.ids.idxOf a ∈ (normNet p).deps (p.ids.idxOf b) ↔ a ∈ p.deps b := by
  rw [deps_normNet h hb]
  simp only [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyids : y ∈ p.ids := PNet.mem_ids_of_mem_deps h hy
    rwa [(List.idxOf_inj hyids).1 hyx] at hy
  · intro hab
    exact ⟨a, hab, rfl⟩

/-- The normal form is a well-formed search network. -/
theorem normNet_ok {p : PNet} (h : PNet.Ok p) : PNet.Ok (normNet p) := by
  have hwf := PNet.toTN_wf h
  refine ⟨nodup_allIds_normNet h, ?_, ?_, ?_, ?_⟩
  · intro z hz hfalse
    simp only [normNet, List.mem_map] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact absurd hfalse (by simp)
  · intro z hz j hj
    simp only [normNet, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    simp only [List.mem_dedup, List.mem_map] at hj
    obtain ⟨y, hy, rfl⟩ := hj
    exact mem_ids_normNet (PNet.mem_ids_of_mem_deps h hy)
  · intro z hz
    simp only [normNet, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    simp only [List.mem_dedup, List.mem_map]
    rintro ⟨y, hy, hyx⟩
    have hyids : y ∈ p.ids := PNet.mem_ids_of_mem_deps h hy
    have : y = i := (List.idxOf_inj hyids).1 hyx
    subst this
    exact hwf.irrefl y hy
  · intro z hz j hj k hk
    simp only [normNet, List.mem_map] at hz
    obtain ⟨i, hi, rfl⟩ := hz
    simp only [List.mem_dedup, List.mem_map] at hj ⊢
    obtain ⟨y, hy, rfl⟩ := hj
    have hyids : y ∈ p.ids := PNet.mem_ids_of_mem_deps h hy
    rw [deps_normNet h hyids] at hk
    simp only [List.mem_dedup, List.mem_map] at hk
    obtain ⟨w, hw, rfl⟩ := hk
    exact ⟨w, hwf.trans hw hy, rfl⟩

/-- **A search network is isomorphic to its normal form.** -/
theorem toTN_normNet_iso {p : PNet} (h : PNet.Ok p) :
    (PNet.toTN p).Iso (PNet.toTN (normNet p)) := by
  refine ⟨fun i => p.ids.idxOf i, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    simp only [PNet.toTN_T, Finset.mem_coe, List.mem_toFinset] at ha ⊢
    exact mem_ids_normNet ha
  · intro a ha b hb hab
    simp only [PNet.toTN_T, Finset.mem_coe, List.mem_toFinset] at ha hb
    exact (List.idxOf_inj ha).1 hab
  · intro j hj
    simp only [PNet.toTN_T, Finset.mem_coe, List.mem_toFinset, ids_normNet,
      List.mem_map] at hj
    obtain ⟨a, ha, rfl⟩ := hj
    exact ⟨a, by simpa using ha, rfl⟩
  · intro a ha b hb
    simp only [PNet.toTN_T, List.mem_toFinset] at ha hb
    simp only [PNet.toTN_ord]
    exact (mem_deps_normNet_iff h hb).symm
  · intro a ha
    simp only [PNet.toTN_T, List.mem_toFinset] at ha
    simp only [PNet.toTN_α]
    exact (label_normNet h ha).symm

/-- Normalising the state does not change it, as a set of facts. -/
theorem state_normCfg {d : DomDesc} {q : InstDesc} {c : PConfig}
    (h : ∀ f ∈ c.1, f ∈ allFacts d q) :
    {f | f ∈ (normCfg d q c).1} = {f | f ∈ c.1} := by
  ext f
  simp only [normCfg, Set.mem_setOf_eq, List.mem_filter, memB_iff]
  exact ⟨fun hf => hf.2, fun hf => ⟨h f hf, hf⟩⟩

/-! ### The finitely many normal forms -/

/-- Every item a normal form can contain. -/
def allItems (d : DomDesc) (q : InstDesc) (B : ℕ) : List PItem :=
  (List.range B).flatMap (fun i =>
    (allLbls d q).flatMap (fun l =>
      (listsUpTo B (List.range B)).map (fun ds => (i, l, true, ds))))

/-- **Every normal form of a configuration satisfying the invariant.** -/
def allCfgs (d : DomDesc) (q : InstDesc) (B : ℕ) : List PConfig :=
  (allFacts d q).sublists.flatMap (fun st =>
    (listsUpTo B (allItems d q B)).map (fun p => (st, p)))

/-! ### An arithmetic bound on the number of normal forms

The decision procedure needs a *number* of search rounds, and it has to compute it — so it does
not use the length of `HTN.Syn.allCfgs`, which is defined through `List.sublists`, but the
closed arithmetic expression `HTN.Syn.regBound`, which bounds it. -/

theorem length_allItems_le (d : DomDesc) (q : InstDesc) (B : ℕ) :
    (allItems d q B).length ≤ B * ((allLbls d q).length * (B + 1) ^ B) := by
  have hinner : ∀ i ∈ List.range B,
      ((allLbls d q).flatMap (fun l =>
        (listsUpTo B (List.range B)).map
          (fun ds => ((i, l, true, ds) : PItem)))).length
        ≤ (allLbls d q).length * (B + 1) ^ B := by
    intro i _
    refine length_flatMap_le _ _ ((B + 1) ^ B) fun l _ => ?_
    rw [List.length_map]
    simpa using length_listsUpTo_le (List.range B) B
  have h := length_flatMap_le (List.range B)
    (fun i => (allLbls d q).flatMap (fun l =>
      (listsUpTo B (List.range B)).map (fun ds => ((i, l, true, ds) : PItem))))
    ((allLbls d q).length * (B + 1) ^ B) hinner
  simpa [allItems] using h

/-- **A computable bound on the number of normal forms.** -/
def cfgBound (d : DomDesc) (q : InstDesc) (B : ℕ) : ℕ :=
  2 ^ (allFacts d q).length * (B * ((allLbls d q).length * (B + 1) ^ B) + 1) ^ B

theorem length_allCfgs_le (d : DomDesc) (q : InstDesc) (B : ℕ) :
    (allCfgs d q B).length ≤ cfgBound d q B := by
  have hinner : ∀ st ∈ (allFacts d q).sublists,
      ((listsUpTo B (allItems d q B)).map (fun p => ((st, p) : PConfig))).length
        ≤ (B * ((allLbls d q).length * (B + 1) ^ B) + 1) ^ B := by
    intro st _
    rw [List.length_map]
    refine le_trans (length_listsUpTo_le _ _) (Nat.pow_le_pow_left ?_ _)
    have := length_allItems_le d q B
    omega
  have h := length_flatMap_le (allFacts d q).sublists
    (fun st => (listsUpTo B (allItems d q B)).map (fun p => ((st, p) : PConfig)))
    ((B * ((allLbls d q).length * (B + 1) ^ B) + 1) ^ B) hinner
  rw [List.length_sublists] at h
  exact h

/-- **The normal form of a configuration satisfying the invariant is one of the finitely many
listed configurations.** -/
theorem mem_allCfgs {d : DomDesc} {q : InstDesc} {B : ℕ} {c : PConfig} (h : CfgInv d q B c) :
    normCfg d q c ∈ allCfgs d q B := by
  have hlen : c.2.ids.length ≤ B := h.small
  have hidx : ∀ i ∈ c.2.ids, c.2.ids.idxOf i < B := fun i hi =>
    lt_of_lt_of_le (List.idxOf_lt_length_of_mem hi) hlen
  refine List.mem_flatMap.2 ⟨(allFacts d q).filter (fun f => memB c.1 f), ?_, ?_⟩
  · exact List.mem_sublists.2 (List.filter_sublist)
  · refine List.mem_map.2 ⟨normNet c.2, ?_, rfl⟩
    refine mem_listsUpTo ?_ ?_
    · simpa [normNet] using hlen
    · intro z hz
      simp only [normNet, List.mem_map] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      obtain ⟨x, hxm, hx1, hflag⟩ := PNet.mem_ids.1 hi
      have hlbl : c.2.lblPair i = x.2.1 := by
        rw [← hx1]
        exact PNet.lblPair_eq_of_mem hxm h.ok.nodup
      have hdeps : ∀ j ∈ ((c.2.deps i).map (fun j => c.2.ids.idxOf j)).dedup,
          j ∈ List.range B := by
        intro j hj
        simp only [List.mem_dedup, List.mem_map] at hj
        obtain ⟨y, hy, rfl⟩ := hj
        exact List.mem_range.2 (hidx y (PNet.mem_ids_of_mem_deps h.ok hy))
      refine List.mem_flatMap.2 ⟨c.2.ids.idxOf i, List.mem_range.2 (hidx i hi), ?_⟩
      refine List.mem_flatMap.2 ⟨c.2.lblPair i, ?_, ?_⟩
      · rw [hlbl]
        exact h.lbls x hxm hflag
      · refine List.mem_map.2 ⟨_, mem_listsUpTo ?_ hdeps, rfl⟩
        have := nodup_length_le (List.nodup_dedup
          ((c.2.deps i).map (fun j => c.2.ids.idxOf j))) hdeps
        simpa using this

end Syn

end HTN
