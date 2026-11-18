import HtnComplexity.Computable.TMNum
import HtnComplexity.Guard.TMFamilyReach
import HtnComplexity.TMEnc.TMEncFixSize
/-!
# The lists of the family construction

`HTN.Syn.Rendering` (`HtnComplexity/Computable/Render.lean`) writes a semantic problem down
from *lists*: the actions with their precondition, add and delete lists, and the method bodies.
This file provides those lists for the re-split family construction of
`HtnComplexity/Guard/TMFamily.lean`, for a machine with finitely many states and symbols.

* `HTN.TMEnc.tmPrecL`, `tmAddL`, `tmDelL` — the action model of Table 4.3.1 as lists
  (`HTN.TMEnc.tmPrecL_eq`, …); the only effect that is not a fixed finite set in the source, the
  delete list of `assert_c` ("every other symbol"), becomes a finite list because the alphabet is
  finite;
* `HTN.TMEnc.Fam.gPrecL`, `gAddL`, `gDelL` — the same for the enlarged signature;
* `HTN.TMEnc.Fam.famActs n` — the actions a description of the family domain lists: the
  encoding's operators, the trivial guard and the guard of every input fact of a position
  `i < n`; `HTN.TMEnc.Fam.mem_famActs_of_usedAction` says it covers every action the family
  problem uses;
* `HTN.TMEnc.Fam.bodyFinsetFam` — the method bodies of one compound task of the unguarded family
  domain as a finite set, with `HTN.TMEnc.Fam.coe_bodyFinsetFam`: it is exactly `bodiesAll`.
-/

namespace HTN

namespace TMEnc

open scoped Classical

open TM TaskNetwork

variable {Q Γ : Type}

/-! ### The action model as lists -/

section Lists

variable [Fintype Γ]

/-- All symbols of the tape, the separator `none` included. -/
noncomputable def symList : List (Option Γ) :=
  none :: (Finset.univ : Finset Γ).toList.map some

lemma mem_symList (c : Option Γ) : c ∈ (symList : List (Option Γ)) := by
  cases c <;> simp [symList]

/-- Preconditions of the actions, as lists. -/
def tmPrecL : TMAct Q Γ → List (TMFact Q Γ)
  | .assert _ => []
  | .check f => [f]
  | .call _ => []
  | .start x => [.stepF x]
  | .respond _ => []
  | .wait x => [.steppedF x]
  | .assertHead => []
  | .retractHead => []
  | .step q c _ _ => [.head, .sym c, .st q]

/-- Add effects of the actions, as lists. -/
def tmAddL : TMAct Q Γ → List (TMFact Q Γ)
  | .assert c => [.sym c]
  | .check _ => []
  | .call x => [.stepF x]
  | .start _ => []
  | .respond x => [.steppedF x]
  | .wait _ => []
  | .assertHead => [.head]
  | .retractHead => [.noHead]
  | .step _ _ q' c' => [.sym c', .st q']

/-- Delete effects of the actions, as lists: `assert_c` deletes every other symbol. -/
noncomputable def tmDelL : TMAct Q Γ → List (TMFact Q Γ)
  | .assert c => (symList.filter fun d => d ≠ c).map TMFact.sym
  | .check _ => []
  | .call _ => []
  | .start x => [.stepF x]
  | .respond _ => []
  | .wait x => [.steppedF x]
  | .assertHead => [.noHead]
  | .retractHead => [.head]
  | .step q c _ _ => [.sym c, .st q]

omit [Fintype Γ] in
lemma tmPrecL_eq (a : TMAct Q Γ) : {v | v ∈ tmPrecL a} = prec a := by
  cases a <;> ext v <;> simp [tmPrecL, prec]

omit [Fintype Γ] in
lemma tmAddL_eq (a : TMAct Q Γ) : {v | v ∈ tmAddL a} = add a := by
  cases a <;> ext v <;> simp [tmAddL, add]

lemma tmDelL_eq (a : TMAct Q Γ) : {v | v ∈ tmDelL (Γ := Γ) a} = del a := by
  cases a with
  | assert c =>
      ext v
      simp only [tmDelL, Set.mem_setOf_eq, List.mem_map, List.mem_filter, decide_eq_true_eq, del]
      constructor
      · rintro ⟨d, ⟨-, hd⟩, rfl⟩
        exact ⟨d, rfl, hd⟩
      · rintro ⟨d, rfl, hd⟩
        exact ⟨d, ⟨mem_symList d, hd⟩, rfl⟩
  | _ => ext v; simp [tmDelL, del]

end Lists

/-! ### Every operator is listed -/

lemma mem_opFinset_univ [Fintype Q] [Fintype Γ] (a : TMAct Q Γ) :
    a ∈ opFinset (Finset.univ : Finset Q) (Finset.univ : Finset Γ) := by
  have hs : ∀ c : Option Γ, c ∈ symsOf (Finset.univ : Finset Γ) := by
    intro c; cases c <;> simp [symsOf]
  have hx : ∀ x : SyncKind, x ∈ syncFinset := by
    intro x; cases x <;> simp [syncFinset]
  have hf : ∀ f : TMFact Q Γ, f ∈ factFinset (Finset.univ : Finset Q) (Finset.univ : Finset Γ) := by
    intro f
    cases f <;> simp [factFinset, hs, hx]
  cases a <;> simp [opFinset, hs, hx, hf]

namespace Fam

section Lists

variable [Fintype Γ]

/-- Preconditions in the enlarged signature, as lists. -/
def gPrecL : GAct Q Γ → List (GFact Q Γ)
  | .inl none => []
  | .inl (some p) => [Sum.inl p]
  | .inr a => (tmPrecL a).map Sum.inr

/-- Add effects in the enlarged signature, as lists. -/
def gAddL : GAct Q Γ → List (GFact Q Γ)
  | .inl _ => []
  | .inr a => (tmAddL a).map Sum.inr

/-- Delete effects in the enlarged signature, as lists. -/
noncomputable def gDelL : GAct Q Γ → List (GFact Q Γ)
  | .inl _ => []
  | .inr a => (tmDelL a).map Sum.inr

omit [Fintype Γ] in
lemma gPrecL_eq (a : GAct Q Γ) : {v | v ∈ gPrecL (Γ := Γ) a} = gPrec a := by
  rcases a with (_ | p) | a
  · ext v; simp [gPrecL, gPrec]
  · ext v; simp [gPrecL, gPrec]
  · rw [gPrec, ← tmPrecL_eq]
    ext v
    simp [gPrecL]

omit [Fintype Γ] in
lemma gAddL_eq (a : GAct Q Γ) : {v | v ∈ gAddL (Γ := Γ) a} = gAdd a := by
  rcases a with p | a
  · ext v; simp [gAddL, gAdd]
  · rw [gAdd, ← tmAddL_eq]
    ext v
    simp [gAddL]

lemma gDelL_eq (a : GAct Q Γ) : {v | v ∈ gDelL (Γ := Γ) a} = gDel a := by
  rcases a with p | a
  · ext v; simp [gDelL, gDel]
  · rw [gDel, ← tmDelL_eq]
    ext v
    simp [gDelL]

end Lists

/-! ### The listed actions -/

/-- **The actions a description of the family domain lists**: the trivial guard, the guard of
every input fact of a position `i < n`, and the operators of the encoding. -/
noncomputable def famActs [Fintype Q] [Fintype Γ] (n : ℕ) : List (GAct Q Γ) :=
  Sum.inl none ::
    ((List.range n).flatMap fun i =>
      (Finset.univ : Finset Γ).toList.map fun c => Sum.inl (some (i, c))) ++
    (opFinset (Finset.univ : Finset Q) (Finset.univ : Finset Γ)).toList.map Sum.inr

lemma mem_famActs [Fintype Q] [Fintype Γ] {n : ℕ} {a : GAct Q Γ}
    (h : ∀ p : ℕ × Γ, a = Sum.inl (some p) → p.1 < n) : a ∈ famActs n := by
  rcases a with (_ | ⟨i, c⟩) | a
  · simp [famActs]
  · have hi := h (i, c) rfl
    simp [famActs, hi]
  · simp [famActs, mem_opFinset_univ]

/-- A body of the unguarded family domain mentions no guard action. -/
lemma not_guard_of_mem_allDomain {N : NTM Q Γ} {n K : ℕ}
    {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)} (hm : m ∈ (allDomain N n K).methods)
    {t : ℕ × ℕ} (ht : t ∈ m.subtasks.T) (o : Option (ℕ × Γ)) :
    m.subtasks.α t ≠ Sum.inl (Sum.inl o) := by
  intro hα
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · have hmem : m.subtasks.α t ∈ ls.flatten := by
      rw [hsub] at ht ⊢
      exact TaskNetwork.grid_α_mem_flatten ht
    rw [hα] at hmem
    have hls' : ∃ ls₀, ls = liftBody ls₀ := by
      by_cases hw : ∃ i, m.abstractTask = TMTask.produceWord i
      · obtain ⟨i, hi⟩ := hw
        rw [hi, bodiesAll_produceWord] at hls
        split_ifs at hls
        · obtain ⟨c, rfl⟩ := hls; exact ⟨_, rfl⟩
        · exact ⟨_, hls⟩
      · push_neg at hw
        rw [bodiesAll_eq_image hw] at hls
        obtain ⟨ls₀, -, rfl⟩ := hls
        exact ⟨ls₀, rfl⟩
    obtain ⟨ls₀, rfl⟩ := hls'
    simp only [liftBody, List.mem_flatten, List.mem_map] at hmem
    obtain ⟨_, ⟨l, -, rfl⟩, hx⟩ := hmem
    obtain ⟨x, -, hx⟩ := List.mem_map.1 hx
    cases x <;> simp at hx
  · have hsI' : m = ⟨TMTask.sI, initNetG K⟩ := hsI
    subst hsI'
    have hrel := relabel_initNetFix (Q := Q) (Γ := Γ) K
    have hmap : Sum.map (Sum.inr : TMAct Q Γ → GAct Q Γ) id
        ((initNetFix (Q := Q) (Γ := Γ) K).α t) = Sum.inl (Sum.inl o) := by
      rw [← hα, ← hrel]; rfl
    cases hx : (initNetFix (Q := Q) (Γ := Γ) K).α t <;> rw [hx] at hmap <;> simp at hmap

/-- **The listed actions cover every action the family problem uses.** -/
theorem mem_famActs_of_usedAction [Fintype Q] [Fintype Γ] {N : NTM Q Γ} {n K : ℕ}
    {w : List Γ} {a : GAct Q Γ}
    (h : ((famDomain N n K).mkProblem (famInstance N w)).UsedAction a) : a ∈ famActs n := by
  refine mem_famActs fun p hp => ?_
  subst hp
  rcases h with ⟨t, ht, hα⟩ | ⟨mg, hmg, t, ht, hα⟩
  · -- the initial task network is the single compound task `sI`
    have hmem : (seq [(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]).α t ∈
        [[(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]].flatten :=
      TaskNetwork.grid_α_mem_flatten ht
    change (seq [(Sum.inr TMTask.sI : GAct Q Γ ⊕ TMTask Q Γ)]).α t = _ at hα
    rw [hα] at hmem
    simp at hmem
  · obtain ⟨m, hm, rfl⟩ := hmg
    simp only [GuardTask.guardMethod_subtasks, GuardTask.addTask_T, Finset.mem_insert] at ht
    by_cases hg : t = gid m
    · subst hg
      rw [GuardTask.guardMethod_subtasks, GuardTask.addTask_α_self] at hα
      have hs : gsel n m = some p := by
        simpa [gact] using hα
      unfold gsel at hs
      split at hs
      · split_ifs at hs with hi
        split at hs
        · simp only [Option.some.injEq] at hs
          subst hs
          exact hi
        · exact absurd hs (by simp)
      · exact absurd hs (by simp)
    · have ht' : t ∈ m.subtasks.T := ht.resolve_left hg
      have hα' : m.subtasks.α t = Sum.inl (Sum.inl (some p)) := by
        rw [GuardTask.guardMethod_subtasks] at hα
        simpa [GuardTask.addTask, Function.update, hg] using hα
      exact absurd hα' (not_guard_of_mem_allDomain hm ht' _)

/-! ### The bodies as a finite set -/

/-- **The bodies of one compound task of the unguarded family domain**, as a finite set. -/
noncomputable def bodyFinsetFam [Fintype Q] [Fintype Γ] (N : NTM Q Γ) (n K : ℕ) :
    TMTask Q Γ → Finset (List (List (GAct Q Γ ⊕ TMTask Q Γ)))
  | .produceWord i =>
      if i < n then Finset.univ.image fun c => liftBody (bodyWord n i c)
      else {liftBody (bodyWord n i N.blank)}
  | t => (bodyFinsetFix N Finset.univ Finset.univ (wpad N n) K t).image liftBody

/-- **The finite set is exactly the set of bodies.** -/
theorem coe_bodyFinsetFam [Fintype Q] [Fintype Γ] (N : NTM Q Γ) (n K : ℕ) (t : TMTask Q Γ) :
    (↑(bodyFinsetFam N n K t) : Set _) = bodiesAll N n K t := by
  by_cases hw : ∃ i, t = TMTask.produceWord i
  · obtain ⟨i, rfl⟩ := hw
    rw [bodiesAll_produceWord]
    by_cases hi : i < n
    · simp only [bodyFinsetFam, if_pos hi, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      ext ls
      simp [eq_comm]
    · simp [bodyFinsetFam, hi]
  · push_neg at hw
    rw [bodiesAll_eq_image hw]
    have h1 : bodyFinsetFam N n K t =
        (bodyFinsetFix N Finset.univ Finset.univ (wpad N n) K t).image liftBody := by
      cases t with
      | produceWord i => exact absurd rfl (hw i)
      | _ => rfl
    rw [h1, Finset.coe_image]
    congr 1
    exact Set.Subset.antisymm (bodyFinsetFix_subset_bodiesFix t)
      (bodiesFix_subset_bodyFinsetFix (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _) t)

end Fam

end TMEnc

end HTN
