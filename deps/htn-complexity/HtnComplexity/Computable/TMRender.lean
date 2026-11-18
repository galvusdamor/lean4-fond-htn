import HtnComplexity.Computable.TMLists
import HtnComplexity.Computable.Render
import HtnComplexity.Computable.GuardShape
import HtnComplexity.Guard.TMFamilyCorrect
/-!
# The family construction, written down as a description

This file instantiates the generic bridge `HTN.Syn.Rendering`
(`HtnComplexity/Computable/Render.lean`) for the re-split construction of Theorem 4.3.7
(`HtnComplexity/Guard/TMFamily.lean`), for a machine with finitely many states and symbols
and injective numberings `q`, `g` of them.

* `HTN.TMEnc.Fam.famBodies N n K` — the listed methods: for every compound task of
  `HTN.TMEnc.Fam.taskFinsetFam` and every body of it (`HTN.TMEnc.Fam.bodyFinsetFam`), the grid
  body with its guard row appended (`HTN.TMEnc.Fam.guardShape`), and the body of the fresh
  initial task `sI`, three chains followed by `done`, with its guard row
  (`HTN.TMEnc.Fam.sIShape`);
* `HTN.TMEnc.Fam.famRendering` — the rendering of the family problem;
* `HTN.TMEnc.Fam.famDomDesc N q g n K`, `HTN.TMEnc.Fam.famInstDesc N q g w` — the two
  descriptions.  The domain description is a function of the machine, the input *length* and
  the time bound; the instance description of the machine and the word;
* `HTN.TMEnc.Fam.solvable_famDesc_iff` — **the described family problem is solvable exactly when
  the original encoding `HTN.TMEnc.problemFix N w K` is**, and
  `HTN.TMEnc.solvable_famDesc_homingMachine_iff` — for the normalised machine it decides
  acceptance within the time bound.
-/

namespace HTN

namespace TMEnc

namespace Fam

open scoped Classical

open TM TaskNetwork GuardTask Syn

variable {Q Γ : Type}

/-! ### The listed shapes -/

/-- The guarded body of a grid method, as a shape: the grid rows with the guard row appended. -/
noncomputable def guardShape (n : ℕ) (t : TMTask Q Γ) (ls : List (List (GAct Q Γ ⊕ TMTask Q Γ))) :
    Shape (GAct Q Γ) (TMTask Q Γ) :=
  ⟨ls ++ [[Sum.inl (gact n ⟨t, grid ls⟩)]], 0⟩

/-- The guarded body of the method of `sI`: the three chains, the task `done` after them, and
the trivial guard as a free row. -/
def sIShape (K : ℕ) : Shape (GAct Q Γ) (TMTask Q Γ) :=
  ⟨liftBody (initChainsFix K) ++ [[Sum.inr TMTask.done]] ++ [[Sum.inl (Sum.inl none)]],
    (liftBody (initChainsFix (Q := Q) (Γ := Γ) K)).length⟩

/-- **The listed methods of the family domain.** -/
noncomputable def famBodies [Fintype Q] [Fintype Γ] (N : NTM Q Γ) (n K : ℕ) :
    List (TMTask Q Γ × Shape (GAct Q Γ) (TMTask Q Γ)) :=
  ((taskFinsetFam N n K).toList.flatMap fun t =>
    (bodyFinsetFam N n K t).toList.map fun ls => (t, guardShape n t ls)) ++
  [(TMTask.sI, sIShape K)]

/-- A guarded grid method is its listed shape, up to isomorphism. -/
lemma iso_guardShape (n : ℕ) (t : TMTask Q Γ) (ls : List (List (GAct Q Γ ⊕ TMTask Q Γ))) :
    (guardMethod gid (gact n) (⟨t, grid ls⟩ : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ))).subtasks.Iso
      (guardShape n t ls).net := by
  set m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ) := ⟨t, grid ls⟩
  have hk : ((gid m).1, 0) ∉ (Shape.mk ls 0 : Shape (GAct Q Γ) (TMTask Q Γ)).net.T := by
    rw [Shape.net_zero]
    exact gid_not_mem m
  have h := Shape.iso_addTask (Shape.mk ls 0) (gid m).1 (gact n m) hk (Or.inl rfl)
  rw [Shape.net_zero] at h
  exact h

/-- The guarded method of `sI` is its listed shape, up to isomorphism. -/
lemma iso_sIShape (n K : ℕ) :
    (guardMethod gid (gact n)
      (⟨TMTask.sI, initNetG K⟩ : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ))).subtasks.Iso
      (sIShape (Q := Q) (Γ := Γ) K).net := by
  set m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ) := ⟨TMTask.sI, initNetG K⟩
  set s : Shape (GAct Q Γ) (TMTask Q Γ) :=
    ⟨liftBody (initChainsFix K) ++ [[Sum.inr TMTask.done]],
      (liftBody (initChainsFix (Q := Q) (Γ := Γ) K)).length⟩
  have hs : s.net = initNetG K := rfl
  have hk : ((gid m).1, 0) ∉ s.net.T := by
    rw [hs]
    exact gid_not_mem m
  have hg : gact n m = Sum.inl none := by
    simp only [gact, gsel_of_not_produceWord (m := m) (by rintro i ⟨⟩)]
  have h := Shape.iso_addTask s (gid m).1 (gact n m) hk (Or.inr (by simp [s]))
  rw [hs, hg] at h
  exact h

/-! ### The rendering -/

/-- The initial state of the family instance, as a list. -/
def famInitL (N : NTM Q Γ) (w : List Γ) : List (GFact Q Γ) :=
  Sum.inr (TMFact.st N.init) :: (List.range w.length).map fun i => Sum.inl (i, w.getD i N.blank)

lemma famInitL_eq (N : NTM Q Γ) (w : List Γ) :
    {v | v ∈ famInitL N w} = (famInstance N w).init := by
  ext v
  simp only [famInitL, Set.mem_setOf_eq, List.mem_cons, List.mem_map, List.mem_range,
    famInstance, specInstance, inpOf, Set.mem_union, Set.mem_singleton_iff, Set.mem_image]

variable [Fintype Q] [Fintype Γ]

/-- **The rendering of the family problem** of a machine with finitely many states and symbols,
numbered injectively by `q` and `g`. -/
noncomputable def famRendering (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) (K : ℕ) :
    Rendering ((famDomain N w.length K).mkProblem (famInstance N w)) where
  eF := encGFact q g
  eA := encGAct q g
  eC := encTMTask g
  eF_inj := encGFact_injective hq hg
  eA_inj := encGAct_injective hq hg
  eC_inj := encTMTask_injective hg
  acts := famActs w.length
  precL := gPrecL
  addL := gAddL
  delL := gDelL
  bodies := famBodies N w.length K
  tnIshape := ⟨[[Sum.inr TMTask.sI]], 0⟩
  initL := famInitL N w
  goalL := []
  used_mem := fun _ h => mem_famActs_of_usedAction h
  precL_eq := fun o _ => gPrecL_eq o
  addL_eq := fun o _ => gAddL_eq o
  delL_eq := fun o _ => gDelL_eq o
  init_eq := famInitL_eq N w
  goal_eq := by
    ext v
    simp [Domain.mkProblem, famInstance]
  tnI_wf := TaskNetwork.seq_wf
  tnI_iso := by
    rw [Shape.net_zero]
    exact TaskNetwork.Iso.refl _
  bodies_sub := by
    intro p hp
    simp only [famBodies, List.mem_append, List.mem_flatMap, List.mem_map, Finset.mem_toList,
      List.mem_singleton] at hp
    rcases hp with ⟨t, -, ls, hls, rfl⟩ | rfl
    · refine ⟨guardMethod gid (gact w.length) ⟨t, grid ls⟩,
        ⟨⟨t, grid ls⟩, Or.inl ⟨ls, ?_, rfl⟩, rfl⟩, rfl, iso_guardShape _ t ls⟩
      rw [← coe_bodyFinsetFam]
      exact hls
    · exact ⟨guardMethod gid (gact w.length) ⟨TMTask.sI, initNetG K⟩,
        ⟨⟨TMTask.sI, initNetG K⟩, Or.inr rfl, rfl⟩, rfl, iso_sIShape _ K⟩
  bodies_all := by
    refine bodies_all_of_names (names := (taskFinsetFam N w.length K).toList)
      (fun t ht => Finset.mem_toList.2 (mem_taskFinsetFam_of_reachableName_famDomain w ht)) ?_
    rintro mg ⟨m, hm, rfl⟩ hnm
    rw [guardMethod_abstractTask, Finset.mem_toList] at hnm
    rcases hm with ⟨ls, hls, hsub⟩ | hsI
    · obtain ⟨t, sub⟩ := m
      simp only at hsub hls hnm
      subst hsub
      refine ⟨(t, guardShape w.length t ls), ?_, rfl, iso_guardShape _ t ls⟩
      simp only [famBodies, List.mem_append, List.mem_flatMap, List.mem_map, Finset.mem_toList]
      refine Or.inl ⟨t, hnm, ls, ?_, rfl⟩
      rw [← Finset.mem_coe, coe_bodyFinsetFam]
      exact hls
    · have hsI' : m = ⟨TMTask.sI, initNetG K⟩ := hsI
      subst hsI'
      exact ⟨(TMTask.sI, sIShape K), by simp [famBodies], rfl, iso_sIShape _ K⟩

/-! ### The two descriptions -/

/-- **The description of the family domain**: a function of the machine, the numberings, the
input length `n` and the time bound `K`. -/
noncomputable def famDomDesc (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (n K : ℕ) : DomDesc :=
  ((famActs n).map fun o =>
      (encGAct q g o, ((gPrecL o).map (encGFact q g), (gAddL o).map (encGFact q g),
        (gDelL o).map (encGFact q g))),
    (famBodies N n K).map fun p => (encTMTask g p.1, p.2.desc (encGAct q g) (encTMTask g)))

/-- **The description of the family instance**: a function of the machine, the numberings and
the input word. -/
def famInstDesc (N : NTM Q Γ) (q : Q → ℕ) (g : Γ → ℕ) (w : List Γ) : InstDesc :=
  ((famInitL N w).map (encGFact q g), [],
    (Shape.mk [[(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]] 0).desc (encGAct q g)
      (encTMTask g))

lemma domDesc_famRendering (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) (K : ℕ) :
    (famRendering N hq hg w K).domDesc = famDomDesc N q g w.length K := rfl

lemma instDesc_famRendering (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) (K : ℕ) :
    (famRendering N hq hg w K).instDesc = famInstDesc N q g w := rfl

/-- **The described family problem is the encoding of Theorem 4.3.7.**  The domain description
depends on the word only through its length, the instance description carries the word, and the
pair is solvable exactly when the original encoding `HTN.TMEnc.problemFix N w K` — whose domain
carries the word — is. -/
theorem solvable_famDesc_iff (N : NTM Q Γ) {q : Q → ℕ} {g : Γ → ℕ}
    (hq : Function.Injective q) (hg : Function.Injective g) (w : List Γ) (K : ℕ) :
    Syn.Solvable (famDomDesc N q g w.length K) (famInstDesc N q g w) ↔
      (problemFix N w K).Solvable := by
  rw [← domDesc_famRendering N hq hg w K, ← instDesc_famRendering N hq hg w K,
    (famRendering N hq hg w K).solvable_iff]
  exact solvable_famDomain_iff N w K

end Fam

open TM

/-- **The described family problem of the normalised machine decides acceptance.**  For a
machine clocked at `K`, with `|w| ≤ K` and `K' ≥ 2K + 1`, the pair of descriptions — the domain
one a function of the machine, the length `|w|` and `K'` only — is solvable exactly when `N`
accepts `w` within `K` steps.  `q` and `g` are any injective numberings of the states and the
symbols of the normalised machine. -/
theorem solvable_famDesc_homingMachine_iff [Fintype Q] [Fintype Γ] (N : NTM Q Γ)
    {q : Q ⊕ Bool → ℕ} {g : Γ × Bool → ℕ} (hq : Function.Injective q)
    (hg : Function.Injective g) {w : List Γ} {K K' : ℕ} (hw : 1 ≤ w.length)
    (hwK : w.length ≤ K) (hK' : 2 * K + 1 ≤ K') (hclock : ClockedAt N w K) :
    Syn.Solvable (Fam.famDomDesc (homingMachine N) q g w.length K')
        (Fam.famInstDesc (homingMachine N) q g (markInput N w)) ↔ N.AcceptsWithin w K := by
  have h := Fam.solvable_famDesc_iff (homingMachine N) hq hg (markInput N w) K'
  rw [markInput_length] at h
  rw [h, ← solvable_famDomain_homingMachine_iff N hw hwK hK' hclock, famProblem_eq,
    Fam.solvable_famDomain_iff]

end TMEnc

end HTN
