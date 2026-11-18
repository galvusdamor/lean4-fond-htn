import FondHtn.HardTR.TDescL
/-!
# CB22 Thm 5, P1: the refinements of the description are words of the grammar

**`FOND.HardTR.TD.netYield_gen`**: every refinement of the initial network of the description is
the image under `nmA` of a word of `TL.Gen X.mach .main` consisting of declared actions.
-/

set_option linter.unusedSectionVars false

namespace FOND

namespace HardTR

open TL TT TE HardMP HTN HTN.Syn HTN.Article AcycHard.Sav

/-! ## Generic destructuring -/

section Gen

variable {A C : Type} {Y : A ⊕ C → List A → Prop}

theorem seqY_nil_iff {as : List A} : SeqY Y [] as ↔ as = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem seqY_cons_iff {x : A ⊕ C} {xs : List (A ⊕ C)} {as : List A} :
    SeqY Y (x :: xs) as ↔ ∃ u v, as = u ++ v ∧ Y x u ∧ SeqY Y xs v := by
  constructor
  · intro h; cases h with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
  · rintro ⟨u, v, rfl, h1, h2⟩; exact .cons h1 h2

theorem setY_nil_iff {as : List A} : SetY Y [] as ↔ as = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem setY_cons_iff {x : A ⊕ C} {xs : List (A ⊕ C)} {as : List A} :
    SetY Y (x :: xs) as ↔ ∃ u v, Y x u ∧ SetY Y xs v ∧ Interleave u v as := by
  constructor
  · intro h; cases h with | cons h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩
  · rintro ⟨u, v, h1, h2, h3⟩; exact .cons h1 h2 h3

/-- Interleavings of images are images of interleavings. -/
theorem interleave_map {B : Type} (f : B → A) :
    ∀ {u' v' z : List A}, Interleave u' v' z → ∀ {u v : List B}, u' = u.map f → v' = v.map f →
      ∃ w, z = w.map f ∧ Interleave u v w := by
  intro u' v' z h
  induction h with
  | nil =>
    intro u v hu hv
    obtain rfl : u = [] := List.map_eq_nil_iff.1 hu.symm
    obtain rfl : v = [] := List.map_eq_nil_iff.1 hv.symm
    exact ⟨[], rfl, .nil⟩
  | left a h ih =>
    intro u v hu hv
    obtain ⟨b, u, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hu.symm
    obtain ⟨w, rfl, hw⟩ := ih rfl hv
    exact ⟨b :: w, rfl, .left b hw⟩
  | right a h ih =>
    intro u v hu hv
    obtain ⟨b, v, rfl, rfl, rfl⟩ := List.map_eq_cons_iff.1 hv.symm
    obtain ⟨w, rfl, hw⟩ := ih hu rfl
    exact ⟨b :: w, rfl, .right b hw⟩

end Gen

namespace TD

variable {S : Type} {cS : S → ℕ} {X : Spec S} {allS : List S} {ops : List Op} {ens : List (En S)}

/-- The words of a task (as action names). -/
def GW (cS : S → ℕ) (X : Spec S) (ops : List Op) (ens : List (En S)) (y : Nt) (as : List ℕ) : Prop :=
  ∃ u, Gen X.mach y u ∧ as = u.map (nmA cS) ∧ ∀ a ∈ u, a ∈ acts X ops ens

variable {F : Type} {D : HTN.Domain F ℕ ℕ ℕ}

theorem yl_lA {n : ℕ} {a : Act Op (En S)} {u : List ℕ} (h : YL D n (toLab (lA cS a)) u) :
    u = [nmA cS a] := by
  rcases h with ⟨b, hb, rfl⟩ | ⟨c, k, m, hc, -⟩
  · simp only [lA, toLab, Bool.false_eq_true, ↓reduceIte, Sum.inl.injEq] at hb; rw [hb]
  · simp [lA, toLab] at hc

/-- The claim for refinements within `n` steps. -/
def Q (cS : S → ℕ) (X : Spec S) (ops : List Op) (ens : List (En S)) (D : HTN.Domain F ℕ ℕ ℕ) (n : ℕ) :
    Prop :=
  ∀ m ∈ D.methods, ∀ as, D.NetYieldN n m.subtasks as → ∃ y, m.abstractTask = nmN y ∧ GW cS X ops ens y as

theorem yl_lN (IH : ∀ k < n, Q cS X ops ens D k) {y : Nt} {u : List ℕ} (h : YL D n (toLab (lN y)) u) :
    GW cS X ops ens y u := by
  rcases h with ⟨b, hb, -⟩ | ⟨c, k, m, hc, hk, hm, hmc, hy⟩
  · simp [lN, toLab] at hb
  · simp only [lN, toLab, ↓reduceIte, Sum.inr.injEq] at hc
    obtain ⟨y', hy', hgw⟩ := IH k hk m hm _ hy
    rw [hmc, ← hc] at hy'
    rw [nmN_inj hy']; exact hgw

/-- The claim for one method description. -/
def PM (cS : S → ℕ) (X : Spec S) (ops : List Op) (ens : List (En S)) (D : HTN.Domain F ℕ ℕ ℕ) (n : ℕ)
    (e : MethodDesc) : Prop :=
  ∀ as, D.NetYieldN n e.2.toTaskNetwork as → ∃ y, e.1 = nmN y ∧ GW cS X ops ens y as

variable (hmwf : ∀ m ∈ D.methods, m.subtasks.WF)
include hmwf

theorem seqY_desc {ls : List (Bool × ℕ)} {n : ℕ} {as : List ℕ}
    (h : D.NetYieldN n (seqTn ls).toTaskNetwork as) : SeqY (YL D n) (ls.map toLab) as :=
  seqY_of_netYieldN hmwf (HardMP.isSeqNet_seqTn ls) h

theorem setY_desc {ls : List (Bool × ℕ)} {n : ℕ} {as : List ℕ}
    (h : D.NetYieldN n (setTn ls).toTaskNetwork as) : SetY (YL D n) (ls.map toLab) as :=
  setY_of_netYieldN hmwf (setNet_setTn ls) h

theorem pm_nil {n : ℕ} {y : Nt} (hg : Gen X.mach y []) : PM cS X ops ens D n (nmN y, seqTn []) := by
  intro as h
  have := seqY_desc hmwf h
  rw [List.map_nil, seqY_nil_iff] at this
  exact ⟨y, rfl, [], hg, by simp [this], by simp⟩

theorem pm_A {n : ℕ} {y : Nt} {a : Act Op (En S)} (ha : a ∈ acts X ops ens) (hg : Gen X.mach y [a]) :
    PM cS X ops ens D n (nmN y, seqTn [lA cS a]) := by
  intro as h
  have := seqY_desc hmwf h
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, rfl⟩ := this
  rw [yl_lA hu]
  exact ⟨y, rfl, [a], hg, by simp, by simpa using ha⟩

theorem pm_N {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) {y y₁ : Nt}
    (hg : ∀ u, Gen X.mach y₁ u → Gen X.mach y u) : PM cS X ops ens D n (nmN y, seqTn [lN y₁]) := by
  intro as h
  have := seqY_desc hmwf h
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, rfl⟩ := this
  obtain ⟨u', hu', rfl, hd⟩ := yl_lN IH hu
  exact ⟨y, rfl, u', hg _ hu', by simp, hd⟩

theorem pm_NN {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) {y y₁ y₂ : Nt}
    (hg : ∀ u v, Gen X.mach y₁ u → Gen X.mach y₂ v → Gen X.mach y (u ++ v)) :
    PM cS X ops ens D n (nmN y, seqTn [lN y₁, lN y₂]) := by
  intro as h
  have := seqY_desc hmwf h
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, w, z, rfl, hw, rfl⟩ := this
  obtain ⟨u', hu', rfl, hd⟩ := yl_lN IH hu
  obtain ⟨w', hw', rfl, hd'⟩ := yl_lN IH hw
  refine ⟨y, rfl, u' ++ w', hg _ _ hu' hw', by simp, ?_⟩
  intro a ha; rcases List.mem_append.1 ha with h | h
  · exact hd a h
  · exact hd' a h

theorem pm_ANN {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) {y y₁ y₂ : Nt} {a : Act Op (En S)}
    (ha : a ∈ acts X ops ens)
    (hg : ∀ u v, Gen X.mach y₁ u → Gen X.mach y₂ v → Gen X.mach y (a :: (u ++ v))) :
    PM cS X ops ens D n (nmN y, seqTn [lA cS a, lN y₁, lN y₂]) := by
  intro as h
  have := seqY_desc hmwf h
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, w, z, rfl, hw, x, t, rfl, hx, rfl⟩ := this
  rw [yl_lA hu]
  obtain ⟨w', hw', rfl, hd⟩ := yl_lN IH hw
  obtain ⟨x', hx', rfl, hd'⟩ := yl_lN IH hx
  refine ⟨y, rfl, a :: (w' ++ x'), hg _ _ hw' hx', by simp, ?_⟩
  intro b hb
  simp only [List.mem_cons, List.mem_append] at hb
  rcases hb with rfl | h | h
  · exact ha
  · exact hd b h
  · exact hd' b h

theorem pm_AANN {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) {y y₁ y₂ : Nt} {a a' : Act Op (En S)}
    (ha : a ∈ acts X ops ens) (ha' : a' ∈ acts X ops ens)
    (hg : ∀ u v, Gen X.mach y₁ u → Gen X.mach y₂ v → Gen X.mach y (a :: a' :: (u ++ v))) :
    PM cS X ops ens D n (nmN y, seqTn [lA cS a, lA cS a', lN y₁, lN y₂]) := by
  intro as h
  have := seqY_desc hmwf h
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, u₂, v₂, rfl, hu₂, w, z, rfl, hw, x, t, rfl, hx, rfl⟩ := this
  rw [yl_lA hu, yl_lA hu₂]
  obtain ⟨w', hw', rfl, hd⟩ := yl_lN IH hw
  obtain ⟨x', hx', rfl, hd'⟩ := yl_lN IH hx
  refine ⟨y, rfl, a :: a' :: (w' ++ x'), hg _ _ hw' hx', by simp, ?_⟩
  intro b hb
  simp only [List.mem_cons, List.mem_append] at hb
  rcases hb with rfl | rfl | h | h
  · exact ha
  · exact ha'
  · exact hd b h
  · exact hd' b h

theorem pm_setNN {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) {y y₁ y₂ : Nt}
    (hg : ∀ u v z, Gen X.mach y₁ u → Gen X.mach y₂ v → Interleave u v z → Gen X.mach y z) :
    PM cS X ops ens D n (nmN y, setTn [lN y₁, lN y₂]) := by
  intro as h
  have := setY_desc hmwf h
  simp only [List.map_cons, List.map_nil, setY_cons_iff, setY_nil_iff] at this
  obtain ⟨u, v, hu, ⟨w, z, hw, rfl, hi2⟩, hi⟩ := this
  obtain rfl := hi2.eq_of_nil_right
  obtain ⟨u', hu', rfl, hd⟩ := yl_lN IH hu
  obtain ⟨w', hw', rfl, hd'⟩ := yl_lN IH hw
  obtain ⟨z', rfl, hz⟩ := interleave_map (nmA cS) hi rfl rfl
  refine ⟨y, rfl, z', hg _ _ _ hu' hw' hz, rfl, fun a ha => ?_⟩
  rcases hz.mem_iff.1 ha with h | h
  · exact hd a h
  · exact hd' a h

theorem pm_main {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) :
    PM cS X ops ens D n (nmN .main, setTn [lN (.loop true), lN (.loop false), lN .finT]) := by
  intro as h
  have := setY_desc hmwf h
  simp only [List.map_cons, List.map_nil, setY_cons_iff, setY_nil_iff] at this
  obtain ⟨u, v, hu, ⟨w, z, hw, ⟨x, t, hx, rfl, hi3⟩, hi2⟩, hi⟩ := this
  obtain rfl := hi3.eq_of_nil_right
  obtain ⟨u', hu', rfl, hd⟩ := yl_lN IH hu
  obtain ⟨w', hw', rfl, hd'⟩ := yl_lN IH hw
  obtain ⟨x', hx', rfl, hd''⟩ := yl_lN IH hx
  have hfin : x' = [.fin] := by cases hx'; rfl
  subst hfin
  obtain ⟨y₁, hy₁, hy₂⟩ := Interleave.assoc' hi2 hi
  obtain ⟨uv, rfl, huv⟩ := interleave_map (nmA cS) hy₁ rfl rfl
  obtain ⟨z', rfl, hz⟩ := interleave_map (nmA cS) hy₂ rfl rfl
  refine ⟨.main, rfl, z', Gen.main hu' hw' huv hz, rfl, fun a ha => ?_⟩
  rcases hz.mem_iff.1 ha with h | h
  · rcases huv.mem_iff.1 h with h | h
    · exact hd a h
    · exact hd' a h
  · exact hd'' a h

set_option maxHeartbeats 4000000 in
attribute [local irreducible] PM in
/-- **Every method body refines into words of its task.** -/
theorem pm_all {n : ℕ} (IH : ∀ k < n, Q cS X ops ens D k) :
    ∀ e ∈ meths cS X ops ens, PM cS X ops ens D n e := by
  simp only [meths, methsP, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_flatMap,
    List.forall_mem_map, List.mem_range, List.forall_mem_nil, and_true, implies_true]
  repeat' (first | apply And.intro | intro)
  all_goals first
    | (exfalso; simp_all; done)
    | exact pm_main hmwf IH
    | (refine pm_A hmwf ?_ Gen.fin; simp [mem_acts_iff])
    | exact pm_nil hmwf (Gen.loopNil _)
    | exact pm_NN hmwf IH (fun _ _ h1 h2 => Gen.loopCons h1 h2)
    | exact pm_setNN hmwf IH (fun _ _ _ h1 h2 hi => Gen.block h1 h2 hi)
    | exact pm_setNN hmwf IH (fun _ _ _ h1 h2 hi => Gen.treeS h1 h2 hi)
    | exact pm_N hmwf IH (fun _ h => Gen.tree0 h)
    | exact pm_N hmwf IH (fun _ h => Gen.bitM h)
    | (refine pm_A hmwf ?_ (Gen.wrap _); simp [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.inc _ _); simp_all [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.rv _ _); simp [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.rvD _ _); simp [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.rb _ _ _); simp_all [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.rbD _ _ _); simp [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.re _ _); simp_all [mem_acts_iff])
    | (refine pm_A hmwf ?_ (Gen.reD _); simp [mem_acts_iff])
    | (refine pm_ANN hmwf IH ?_ (fun _ _ h1 h2 => Gen.bitS _ ‹_ < mm X› h1 h2); simp_all [mem_acts_iff])
    | (refine pm_ANN hmwf IH ?_ (fun _ _ h1 h2 => Gen.core _ h1 h2); simp_all [mem_acts_iff])
    | (refine pm_AANN hmwf IH ?_ ?_ (fun _ _ h1 h2 => Gen.coreN _ h1 h2) <;> simp_all [mem_acts_iff])

/-- **The claim for all step counts.** -/
theorem q_all (hD : D.methods = {m | ∃ e ∈ meths cS X ops ens, e.toMethod = m}) :
    ∀ n, Q cS X ops ens D n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro m hm as hy
    rw [hD] at hm
    obtain ⟨e, he, rfl⟩ := hm
    exact pm_all hmwf IH e he as hy

/-- **The refinements of the initial network are words of `main`.** -/
theorem netYield_gen (hD : D.methods = {m | ∃ e ∈ meths cS X ops ens, e.toMethod = m}) {as : List ℕ}
    (h : D.NetYield (seqTn [lN .main]).toTaskNetwork as) : GW cS X ops ens .main as := by
  obtain ⟨n, hn⟩ := h
  have := seqY_desc hmwf hn
  simp only [List.map_cons, List.map_nil, seqY_cons_iff, seqY_nil_iff] at this
  obtain ⟨u, v, rfl, hu, rfl⟩ := this
  rw [List.append_nil]
  rcases hu with ⟨b, hb, -⟩ | ⟨c, k, m, hc, -, hm, hmc, hy⟩
  · simp [lN, toLab] at hb
  · simp only [lN, toLab, ↓reduceIte, Sum.inr.injEq] at hc
    obtain ⟨y', hy', hgw⟩ := q_all hmwf hD k m hm _ hy
    rw [hmc, ← hc] at hy'
    rw [nmN_inj hy']; exact hgw

end TD

end HardTR

end FOND
