import HtnComplexity.Guard.MethodGuard
import HtnComplexity.Guard.GridRelabel
import HtnComplexity.Guard.TaskClass
import HtnComplexity.TMEnc.TMEncFix
import HtnPlanning.Core.Transfer
/-!
# The re-split of the Theorem 4.3.7 encoding: the word out of the domain, into the instance

`HtnComplexity/TMEnc/TMEncFix.lean` builds, from a machine `N`, an input word `w` and a time
bound `K`, an acyclic, totally ordered HTN problem `HTN.TMEnc.problemFix N w K` whose solutions
are the accepting runs of `N` on `w`.  The word sits in the **domain**: the methods
`produceWord i` write the letters of `w` onto the tape.

A hardness *family* in the sense of `HTN.Syn.Coded.HardFamilyPT` needs the opposite split — one
domain per input **length**, the word carried by the instance.  This file performs that re-split,
using the generic method-guard tool of `HtnComplexity/Guard/MethodGuard.lean`.

## The construction

The signature is enlarged: one extra fact `inp i c` ("the instance's input has the letter `c` at
position `i`") for each position and letter, and one extra action per fact, a no-op whose only
precondition is that fact, plus a trivial no-op with no precondition at all.

* `HTN.TMEnc.Fam.GFact`, `HTN.TMEnc.Fam.GAct`, `HTN.TMEnc.Fam.gModel` — the enlarged signature
  and its action model; the original facts and actions are the right summands, so that the
  `Inhabited` instance of the enlarged action type is the original default and the dummy label
  of a grid network is preserved by the inclusion.
* `HTN.TMEnc.Fam.bodiesAll N n K` — the bodies of the **family** construction: those of
  `HTN.TMEnc.bodiesFix`, except that at each position `i < n` the task `produceWord i` gets *one
  method per letter* of the alphabet.  The definition mentions the length `n` and not the word.
* `HTN.TMEnc.Fam.famDomain N n K` — the family domain: every method of `bodiesAll` with a guard
  task added (`HTN.GuardTask.guardMethod`), the guard action of a `produceWord i` method being
  the one whose precondition is `inp i c` for the letter `c` the method writes.
* `HTN.TMEnc.Fam.famInstance N w` — the instance: the original initial state together with the
  facts `inp i (wᵢ)`, `i < |w|`.

## Main results

* `HTN.TMEnc.Fam.solvable_famDomain_iff` — **the re-split**: the family problem, whose domain
  depends on `w` only through its length, is solvable exactly when `HTN.TMEnc.problemFix N w K`
  is;
* `HTN.TMEnc.Fam.solvable_spec_iff` — the auxiliary half: the enlarged signature changes nothing.
-/

namespace HTN

namespace TMEnc

namespace Fam

open TM TaskNetwork GuardTask

universe uq ug

variable {Q Γ : Type}

/-! ### The enlarged signature -/

/-- The facts of the family construction: the facts of the encoding, together with one fact
`inp i c` per position `i` and letter `c`, saying that the instance's input word has the letter
`c` at position `i`. -/
abbrev GFact (Q Γ : Type) := (ℕ × Γ) ⊕ TMFact Q Γ

/-- The actions of the family construction: the actions of the encoding, together with one no-op
`guard (i, c)` per input fact and one no-op `guard none` with no precondition at all.  The
original actions are the *right* summand so that the default action of the enlarged type is the
default action of the original one. -/
abbrev GAct (Q Γ : Type) := Option (ℕ × Γ) ⊕ TMAct Q Γ

instance instInhabitedGAct : Inhabited (GAct Q Γ) := ⟨Sum.inr default⟩

/-- The inclusion of the original actions into the enlarged ones preserves the dummy label. -/
lemma gact_default : (Sum.inr : TMAct Q Γ → GAct Q Γ) default = default := rfl

/-- Preconditions in the enlarged signature: the guard actions test their input fact. -/
def gPrec : GAct Q Γ → Set (GFact Q Γ)
  | .inl none => ∅
  | .inl (some p) => {Sum.inl p}
  | .inr a => Sum.inr '' prec a

/-- Add effects in the enlarged signature: the guard actions are no-ops. -/
def gAdd : GAct Q Γ → Set (GFact Q Γ)
  | .inl _ => ∅
  | .inr a => Sum.inr '' add a

/-- Delete effects in the enlarged signature: the guard actions are no-ops. -/
def gDel : GAct Q Γ → Set (GFact Q Γ)
  | .inl _ => ∅
  | .inr a => Sum.inr '' del a

/-- The action model of the family construction. -/
def gModel : ActionModel (GFact Q Γ) (GAct Q Γ) where
  prec := gPrec
  add := gAdd
  del := gDel

@[simp] lemma gModel_prec (a : GAct Q Γ) : gModel.prec a = gPrec a := rfl
@[simp] lemma gModel_add (a : GAct Q Γ) : gModel.add a = gAdd a := rfl
@[simp] lemma gModel_del (a : GAct Q Γ) : gModel.del a = gDel a := rfl

/-- The input facts. -/
def inpFacts : Set (GFact Q Γ) := Set.range (Sum.inl : ℕ × Γ → GFact Q Γ)

lemma not_mem_inpFacts (f : TMFact Q Γ) : (Sum.inr f : GFact Q Γ) ∉ inpFacts := by
  rintro ⟨p, ⟨⟩⟩

/-! ### Lifting a body of the original construction -/

/-- The image of a method body under the inclusion of the signature. -/
def liftBody (ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) :
    List (List (GAct Q Γ ⊕ TMTask Q Γ)) :=
  ls.map (List.map (Sum.map Sum.inr id))

lemma relabel_grid_lift (ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))) :
    relabel (Sum.inr : TMAct Q Γ → GAct Q Γ) (id : TMTask Q Γ → TMTask Q Γ)
        (Equiv.refl (ℕ × ℕ)) (grid ls) = grid (liftBody ls) :=
  relabel_grid _ _ gact_default ls

/-! ### The bodies of the family construction -/

/-- The body of the task `produceWord i` that writes the letter `c`, in a construction whose
input word has length `n`. -/
def bodyWord (n i : ℕ) (c : Γ) : List (List (TMAct Q Γ ⊕ TMTask Q Γ)) :=
  if i + 1 < n then
    [[Sum.inr (TMTask.produceSym (some c)), Sum.inr (TMTask.produceWord (i + 1))]]
  else [[Sum.inr (TMTask.produceSym (some c))]]

/-- The bodies of `produceWord i` in the original construction are the single body writing the
`i`-th letter of the word. -/
lemma bodiesFix_produceWord (N : NTM Q Γ) (w : List Γ) (K i : ℕ) :
    bodiesFix N w K (TMTask.produceWord i) = {bodyWord w.length i (w.getD i N.blank)} := by
  show bodies N w K (TMTask.produceWord i) = _
  by_cases h : i + 1 < w.length <;> simp [bodies, bodyWord, h]

/-- A canonical word of the given length, used to name the part of the construction that depends
on the length of the input alone. -/
def wpad (N : NTM Q Γ) (n : ℕ) : List Γ := List.replicate n N.blank

@[simp] lemma length_wpad (N : NTM Q Γ) (n : ℕ) : (wpad N n).length = n := by
  simp [wpad]

/-- Away from the tasks `produceWord i`, the bodies of the construction depend on the input word
only through its length. -/
lemma bodiesFix_eq_wpad {N : NTM Q Γ} {w : List Γ} {n K : ℕ} (hw : w.length = n)
    {t : TMTask Q Γ} (ht : ∀ i, t ≠ TMTask.produceWord i) :
    bodiesFix N w K t = bodiesFix N (wpad N n) K t := by
  cases t with
  | produceWord i => exact absurd rfl (ht i)
  | produceInit =>
      show bodies N w K TMTask.produceInit = bodies N (wpad N n) K TMTask.produceInit
      simp [bodies, hw]
  | _ => rfl

/-- **The bodies of the family construction.**  At each position `i < n` the task
`produceWord i` has one method per letter of the alphabet; everything else is as in the original
construction, which away from those tasks depends on the length of the input alone. -/
def bodiesAll (N : NTM Q Γ) (n K : ℕ) (t : TMTask Q Γ) :
    Set (List (List (GAct Q Γ ⊕ TMTask Q Γ))) :=
  match t with
  | .produceWord i =>
      if i < n then {ls | ∃ c : Γ, ls = liftBody (bodyWord n i c)}
      else {liftBody (bodyWord n i N.blank)}
  | _ => liftBody '' bodiesFix N (wpad N n) K t

@[simp] lemma bodiesAll_produceWord (N : NTM Q Γ) (n K i : ℕ) :
    bodiesAll N n K (TMTask.produceWord i) =
      if i < n then {ls | ∃ c : Γ, ls = liftBody (bodyWord n i c)}
      else {liftBody (bodyWord n i N.blank)} := rfl

lemma bodiesAll_eq_image {N : NTM Q Γ} {n K : ℕ} {t : TMTask Q Γ}
    (ht : ∀ i, t ≠ TMTask.produceWord i) :
    bodiesAll N n K t = liftBody '' bodiesFix N (wpad N n) K t := by
  cases t with
  | produceWord i => exact absurd rfl (ht i)
  | _ => rfl

/-- The bodies of the original construction, in the enlarged signature. -/
def bodiesSpec (N : NTM Q Γ) (w : List Γ) (K : ℕ) (t : TMTask Q Γ) :
    Set (List (List (GAct Q Γ ⊕ TMTask Q Γ))) := liftBody '' bodiesFix N w K t

lemma bodiesSpec_subset_bodiesAll {N : NTM Q Γ} {w : List Γ} {n K : ℕ} (hw : w.length = n)
    (t : TMTask Q Γ) : bodiesSpec N w K t ⊆ bodiesAll N n K t := by
  cases t with
  | produceWord i =>
      rintro ls hls
      simp only [bodiesSpec, bodiesFix_produceWord, Set.image_singleton,
        Set.mem_singleton_iff] at hls
      subst hls
      rw [bodiesAll_produceWord]
      by_cases hi : i < n
      · rw [if_pos hi]
        exact ⟨w.getD i N.blank, by rw [hw]⟩
      · have hge : w.length ≤ i := by omega
        have hb : w.getD i N.blank = N.blank := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        rw [if_neg hi, hb, hw]
        rfl
  | _ =>
      intro ls hls
      rw [bodiesAll_eq_image (by rintro i ⟨⟩), ← bodiesFix_eq_wpad hw (by rintro i ⟨⟩)]
      exact hls

/-! ### The domains -/

/-- The initial task network of the construction, in the enlarged signature. -/
def initNetG (K : ℕ) : TaskNetwork (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ) :=
  gridTail (liftBody (initChainsFix K)) [Sum.inr TMTask.done]

lemma relabel_initNetFix (K : ℕ) :
    relabel (Sum.inr : TMAct Q Γ → GAct Q Γ) (id : TMTask Q Γ → TMTask Q Γ)
        (Equiv.refl (ℕ × ℕ)) (initNetFix K) = initNetG K := by
  show relabel _ _ _ (gridTail (initChainsFix K) [Sum.inr TMTask.done]) = _
  rw [relabel_gridTail _ _ gact_default]
  simp [initNetG, liftBody]

/-- The methods generated by a family of bodies, together with the single method of the fresh
initial task `sI`. -/
def methodsOf (b : TMTask Q Γ → Set (List (List (GAct Q Γ ⊕ TMTask Q Γ)))) (K : ℕ) :
    Set (Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)) :=
  {m | ∃ ls ∈ b m.abstractTask, m.subtasks = grid ls} ∪ {⟨TMTask.sI, initNetG K⟩}

/-- The domain of the original construction, in the enlarged signature. -/
def specDomain (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    Domain (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  toActionModel := gModel
  methods := methodsOf (bodiesSpec N w K) K

/-- The domain offering one method per letter at each position of the input. -/
def allDomain (N : NTM Q Γ) (n K : ℕ) :
    Domain (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  toActionModel := gModel
  methods := methodsOf (bodiesAll N n K) K

/-! ### The guard data -/

/-- The identifier of the guard task of a method: one more than the largest first component of
its identifiers, so it is fresh. -/
def gid (m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)) : ℕ × ℕ :=
  (m.subtasks.T.sup Prod.fst + 1, 0)

lemma gid_not_mem (m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)) : gid m ∉ m.subtasks.T := by
  intro h
  have := Finset.le_sup (f := Prod.fst) h
  simp only [gid] at this
  omega

/-- The input fact a method is guarded by, if any: a method of `produceWord i` with `i < n`
writing the letter `c` is guarded by `inp i c`, every other method by nothing. -/
def gsel (n : ℕ) (m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)) : Option (ℕ × Γ) :=
  match m.abstractTask with
  | .produceWord i =>
      if i < n then
        match m.subtasks.α (0, 0) with
        | Sum.inr (.produceSym (some c)) => some (i, c)
        | _ => none
      else none
  | _ => none

/-- The guard action of a method: the no-op whose precondition is the method's input fact. -/
def gact (n : ℕ) (m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)) : GAct Q Γ := Sum.inl (gsel n m)

lemma gsel_of_not_produceWord {n : ℕ} {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)}
    (h : ∀ i, m.abstractTask ≠ TMTask.produceWord i) : gsel n m = none := by
  rw [gsel]
  split
  · next i heq => exact absurd heq (h i)
  · rfl

lemma gsel_produceWord_of_not_lt {n i : ℕ} {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)}
    (hm : m.abstractTask = TMTask.produceWord i) (hi : ¬ i < n) : gsel n m = none := by
  rw [gsel, hm]
  simp [hi]

lemma gsel_produceWord {n i : ℕ} {c : Γ} {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)}
    (hm : m.abstractTask = TMTask.produceWord i) (hi : i < n)
    (hα : m.subtasks.α (0, 0) = Sum.inr (TMTask.produceSym (some c))) :
    gsel n m = some (i, c) := by
  rw [gsel, hm]
  simp [hi, hα]

/-- The family domain: every method of `allDomain` with its guard task. -/
def famDomain (N : NTM Q Γ) (n K : ℕ) :
    Domain (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  toActionModel := gModel
  methods := guardMethod gid (gact n) '' (allDomain N n K).methods

/-- The guard facts the instance carries: the letters of the word, position by position. -/
def inpOf (N : NTM Q Γ) (w : List Γ) : Set (GFact Q Γ) :=
  (fun i => (Sum.inl (i, w.getD i N.blank) : GFact Q Γ)) '' {i | i < w.length}

/-- The instance of the original construction, in the enlarged signature. -/
def specInstance (N : NTM Q Γ) : Instance (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  init := {Sum.inr (TMFact.st N.init)}
  goal := ∅
  tnI := seq [Sum.inr TMTask.sI]

/-- **The instance of the family construction**: the original one, enlarged by the facts that
spell out the input word. -/
def famInstance (N : NTM Q Γ) (w : List Γ) :
    Instance (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ) where
  init := (specInstance N).init ∪ inpOf N w
  goal := ∅
  tnI := seq [Sum.inr TMTask.sI]

/-! ### The enlarged signature changes nothing -/

/-- The methods of the original construction, read in the enlarged signature, are the images of
the methods of `HTN.TMEnc.domainFix`. -/
lemma methods_specDomain (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    (specDomain N w K).methods =
      Method.relabel (Sum.inr : TMAct Q Γ → GAct Q Γ) (id : TMTask Q Γ → TMTask Q Γ)
        (Equiv.refl (ℕ × ℕ)) '' (domainFix N w K).methods := by
  ext m'
  constructor
  · rintro (⟨ls', hls', hsub⟩ | hsI)
    · obtain ⟨ls, hls, rfl⟩ := hls'
      refine ⟨⟨m'.abstractTask, grid ls⟩, Or.inl ⟨ls, hls, rfl⟩, ?_⟩
      rw [Method.relabel_grid _ _ gact_default]
      cases m'
      simp_all [liftBody]
    · simp only [Set.mem_singleton_iff] at hsI
      refine ⟨⟨TMTask.sI, initNetFix K⟩, Or.inr rfl, ?_⟩
      rw [hsI]
      simp [Method.relabel, relabel_initNetFix]
  · rintro ⟨m, (⟨ls, hls, hsub⟩ | hsI), rfl⟩
    · refine Or.inl ⟨liftBody ls, ⟨ls, hls, rfl⟩, ?_⟩
      rw [Method.relabel_subtasks, hsub, relabel_grid_lift]
    · simp only [Set.mem_singleton_iff] at hsI
      subst hsI
      refine Or.inr ?_
      simp [Method.relabel, relabel_initNetFix]

/-- **The enlarged signature changes nothing**: the construction read over the enlarged facts and
actions is solvable exactly when the original one is. -/
theorem solvable_spec_iff (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    ((specDomain N w K).mkProblem (specInstance N)).Solvable ↔ (problemFix N w K).Solvable := by
  refine Problem.solvable_relabel_iff (eF := (Sum.inr : TMFact Q Γ → GFact Q Γ))
    (eA := (Sum.inr : TMAct Q Γ → GAct Q Γ)) (eC := (id : TMTask Q Γ → TMTask Q Γ))
    (eI := Equiv.refl (ℕ × ℕ)) Sum.inr_injective Sum.inr_injective Function.injective_id
    (fun o _ => rfl) (fun o _ => rfl) (fun o _ => rfl) ?_ ?_ TaskNetwork.seq_wf ?_ ?_
  · show ({Sum.inr (TMFact.st N.init)} : Set (GFact Q Γ)) = Sum.inr '' {TMFact.st N.init}
    simp
  · show (∅ : Set (GFact Q Γ)) = Sum.inr '' ∅
    simp
  · show seq [Sum.inr TMTask.sI] = relabel _ _ _ (seq [Sum.inr TMTask.sI])
    rw [relabel_seq _ _ gact_default]
    rfl
  · exact methods_specDomain N w K

/-! ### The hypotheses of the method-guard re-split -/

lemma mem_methodsOf {b : TMTask Q Γ → Set (List (List (GAct Q Γ ⊕ TMTask Q Γ)))} {K : ℕ}
    {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)} :
    m ∈ methodsOf b K ↔
      (∃ ls ∈ b m.abstractTask, m.subtasks = grid ls) ∨ m = ⟨TMTask.sI, initNetG K⟩ :=
  Iff.rfl

lemma methodsOf_mono {b b' : TMTask Q Γ → Set (List (List (GAct Q Γ ⊕ TMTask Q Γ)))}
    (h : ∀ t, b t ⊆ b' t) (K : ℕ) : methodsOf b K ⊆ methodsOf b' K := by
  rintro m (⟨ls, hls, hsub⟩ | hsI)
  · exact Or.inl ⟨ls, h _ hls, hsub⟩
  · exact Or.inr hsI

lemma wf_of_mem_methodsOf {b : TMTask Q Γ → Set (List (List (GAct Q Γ ⊕ TMTask Q Γ)))} {K : ℕ}
    {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)} (h : m ∈ methodsOf b K) : m.subtasks.WF := by
  rcases h with ⟨ls, -, hsub⟩ | hsI
  · rw [hsub]; exact grid_wf
  · subst hsI; exact gridTail_wf

/-- The first task of the body writing the letter `c` is the production of that letter. -/
lemma grid_α_zero_bodyWord (n i : ℕ) (c : Γ) :
    (grid (liftBody (bodyWord (Q := Q) n i c))).α (0, 0)
      = Sum.inr (TMTask.produceSym (some c)) := by
  by_cases h : i + 1 < n <;> simp [bodyWord, liftBody, h]

/-- Two bodies writing different letters are different networks. -/
lemma bodyWord_inj {n i : ℕ} {c c' : Γ}
    (h : grid (liftBody (bodyWord (Q := Q) n i c)) = grid (liftBody (bodyWord (Q := Q) n i c'))) :
    c = c' := by
  have h0 : (grid (liftBody (bodyWord (Q := Q) n i c))).α (0, 0)
      = (grid (liftBody (bodyWord (Q := Q) n i c'))).α (0, 0) := by rw [h]
  rw [grid_α_zero_bodyWord, grid_α_zero_bodyWord] at h0
  simpa using h0

lemma mem_inpOf_iff {N : NTM Q Γ} {w : List Γ} {i : ℕ} {c : Γ} (hi : i < w.length) :
    (Sum.inl (i, c) : GFact Q Γ) ∈ inpOf N w ↔ c = w.getD i N.blank := by
  constructor
  · rintro ⟨j, -, hEq⟩
    simp only [Sum.inl.injEq, Prod.mk.injEq] at hEq
    obtain ⟨rfl, hc⟩ := hEq
    exact hc.symm
  · rintro rfl
    exact ⟨i, hi, rfl⟩

lemma inpOf_subset (N : NTM Q Γ) (w : List Γ) : inpOf N w ⊆ inpFacts := by
  rintro f ⟨i, -, rfl⟩
  exact ⟨_, rfl⟩

/-- **The instance admits exactly the methods of the word.** -/
lemma granted_iff (N : NTM Q Γ) (w : List Γ) (K : ℕ)
    {m : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ)} (hm : m ∈ (allDomain N w.length K).methods) :
    m ∈ (specDomain N w K).methods ↔ gPrec (gact w.length m) ⊆ inpOf N w := by
  set n := w.length with hn
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · -- a method coming from a body
    by_cases hw : ∃ i, m.abstractTask = TMTask.produceWord i
    · obtain ⟨i, hi⟩ := hw
      rw [hi] at hls
      rw [bodiesAll_produceWord] at hls
      by_cases hlt : i < n
      · -- one method per letter
        rw [if_pos hlt] at hls
        obtain ⟨c, rfl⟩ := hls
        have hα : m.subtasks.α (0, 0) = Sum.inr (TMTask.produceSym (some c)) := by
          rw [hsub]; exact grid_α_zero_bodyWord n i c
        have hg : gact n m = Sum.inl (some (i, c)) := by
          rw [gact, gsel_produceWord hi hlt hα]
        rw [hg]
        show _ ↔ ({Sum.inl (i, c)} : Set (GFact Q Γ)) ⊆ inpOf N w
        rw [Set.singleton_subset_iff, mem_inpOf_iff (by omega)]
        constructor
        · rintro (⟨ls', hls', hsub'⟩ | hsI)
          · rw [hi] at hls'
            simp only [bodiesSpec, bodiesFix_produceWord, Set.image_singleton,
              Set.mem_singleton_iff] at hls'
            subst hls'
            rw [hsub] at hsub'
            exact bodyWord_inj hsub'
          · rw [hsI] at hi
            exact absurd hi (by rintro ⟨⟩)
        · intro hc
          refine Or.inl ⟨liftBody (bodyWord n i c), ?_, hsub⟩
          rw [hi]
          simp only [bodiesSpec, bodiesFix_produceWord, Set.image_singleton,
            Set.mem_singleton_iff, ← hn, ← hc]
      · -- beyond the word: a single method, and no guard
        rw [if_neg hlt] at hls
        simp only [Set.mem_singleton_iff] at hls
        have hg : gact n m = Sum.inl none := by
          rw [gact, gsel_produceWord_of_not_lt hi hlt]
        rw [hg]
        have hb : w.getD i N.blank = N.blank := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i)]
        constructor
        · intro _
          show (∅ : Set (GFact Q Γ)) ⊆ _
          exact Set.empty_subset _
        · intro _
          refine Or.inl ⟨ls, ?_, hsub⟩
          rw [hi]
          simp only [bodiesSpec, bodiesFix_produceWord, Set.image_singleton,
            Set.mem_singleton_iff, hls, hb, ← hn]
    · -- every other task: the bodies of the two domains agree
      push_neg at hw
      have hg : gact n m = Sum.inl none := by rw [gact, gsel_of_not_produceWord hw]
      rw [hg, bodiesAll_eq_image hw] at *
      constructor
      · intro _
        show (∅ : Set (GFact Q Γ)) ⊆ _
        exact Set.empty_subset _
      · intro _
        refine Or.inl ⟨ls, ?_, hsub⟩
        rwa [bodiesSpec, bodiesFix_eq_wpad hn.symm hw]
  · -- the method of the fresh initial task
    subst hsI
    have hg : gact n (⟨TMTask.sI, initNetG K⟩ : Method (ℕ × ℕ) (GAct Q Γ) (TMTask Q Γ))
        = Sum.inl none := by
      rw [gact, gsel_of_not_produceWord (by rintro i ⟨⟩)]
    rw [hg]
    constructor
    · intro _
      show (∅ : Set (GFact Q Γ)) ⊆ _
      exact Set.empty_subset _
    · intro _
      exact Or.inr rfl

/-- Only the actions of the original signature are used by the original construction. -/
lemma usedAction_spec {N : NTM Q Γ} {w : List Γ} {K : ℕ} {a : GAct Q Γ}
    (ha : ((specDomain N w K).mkProblem (specInstance N)).UsedAction a) :
    ∃ a₀ : TMAct Q Γ, a = Sum.inr a₀ := by
  have key : ∀ (tn : TaskNetwork (ℕ × ℕ) (TMAct Q Γ) (TMTask Q Γ)) (t : ℕ × ℕ),
      (relabel (Sum.inr : TMAct Q Γ → GAct Q Γ) (id : TMTask Q Γ → TMTask Q Γ)
        (Equiv.refl (ℕ × ℕ)) tn).α t = Sum.inl a → ∃ a₀, a = Sum.inr a₀ := by
    intro tn t h
    have h' : Sum.map (Sum.inr : TMAct Q Γ → GAct Q Γ) id (tn.α t) = Sum.inl a := h
    cases hx : tn.α t with
    | inl a₀ => rw [hx] at h'; exact ⟨a₀, by simpa using h'.symm⟩
    | inr c => rw [hx] at h'; exact absurd h' (by simp)
  rcases ha with ⟨t, -, hα⟩ | ⟨m, hm, t, -, hα⟩
  · have htn : ((specDomain N w K).mkProblem (specInstance N)).tnI
        = relabel (Sum.inr : TMAct Q Γ → GAct Q Γ) (id : TMTask Q Γ → TMTask Q Γ)
          (Equiv.refl (ℕ × ℕ)) (seq [Sum.inr TMTask.sI]) := by
      rw [relabel_seq _ _ gact_default]
      rfl
    rw [htn] at hα
    exact key _ t hα
  · have hm' : m ∈ Method.relabel (Sum.inr : TMAct Q Γ → GAct Q Γ)
        (id : TMTask Q Γ → TMTask Q Γ) (Equiv.refl (ℕ × ℕ)) '' (domainFix N w K).methods := by
      rw [← methods_specDomain N w K]; exact hm
    obtain ⟨m₀, -, rfl⟩ := hm'
    exact key _ t hα

/-! ### The re-split -/

/-- **The re-split of the Theorem 4.3.7 encoding.**

The domain `HTN.TMEnc.Fam.famDomain N n K` depends on the input only through its *length* `n`:
at each position `i < n` it offers one method per letter of the alphabet, each guarded by the
input fact for that position and letter.  The instance
`HTN.TMEnc.Fam.famInstance N w` carries the word, as the input facts of its initial state.

The two are solvable exactly when the original problem `HTN.TMEnc.problemFix N w K`, which
carries the word in its domain, is. -/
theorem solvable_famDomain_iff (N : NTM Q Γ) (w : List Γ) (K : ℕ) :
    ((famDomain N w.length K).mkProblem (famInstance N w)).Solvable ↔
      (problemFix N w K).Solvable := by
  have hmain :
      ((famDomain N w.length K).mkProblem (famInstance N w)).Solvable ↔
        ((specDomain N w K).mkProblem (specInstance N)).Solvable := by
    refine GuardTask.solvable_methodGuard_resplit_iff
      (Dall := allDomain N w.length K) (Dspec := specDomain N w K)
      (Dfam := famDomain N w.length K) (Q := specInstance N)
      (G := inpFacts) (Gw := inpOf N w) (gid := gid) (gact := gact w.length)
      rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ (inpOf_subset N w) ?_ ?_ ?_ ?_ ?_ TaskNetwork.seq_wf
    · exact methodsOf_mono (fun t => bodiesSpec_subset_bodiesAll rfl t) K
    · exact fun m hm => ⟨m, hm, rfl⟩
    · rintro mg ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · exact fun m hm => wf_of_mem_methodsOf hm
    · exact fun m _ => gid_not_mem m
    · refine fun m _ => ⟨?_, rfl, rfl⟩
      show gPrec (gact w.length m) ⊆ inpFacts
      rw [gact]
      cases gsel w.length m with
      | none => exact Set.empty_subset _
      | some p => exact Set.singleton_subset_iff.2 ⟨p, rfl⟩
    · exact fun m hm => granted_iff N w K hm
    · rintro a f hf
      have hf' : f ∈ gAdd a := hf
      show f ∉ inpFacts
      cases a with
      | inl x => simp [gAdd] at hf'
      | inr a₀ =>
          obtain ⟨g, -, rfl⟩ := hf'
          exact not_mem_inpFacts g
    · rintro a f hf
      have hf' : f ∈ gDel a := hf
      show f ∉ inpFacts
      cases a with
      | inl x => simp [gDel] at hf'
      | inr a₀ =>
          obtain ⟨g, -, rfl⟩ := hf'
          exact not_mem_inpFacts g
    · rintro a ha f hf
      obtain ⟨a₀, rfl⟩ := usedAction_spec ha
      have hf' : f ∈ gPrec (Sum.inr a₀ : GAct Q Γ) := hf
      obtain ⟨g, -, rfl⟩ := hf'
      exact not_mem_inpFacts g
    · rintro f hf
      have : f = Sum.inr (TMFact.st N.init) := hf
      subst this
      exact not_mem_inpFacts _
    · rintro f ⟨⟩
  exact hmain.trans (solvable_spec_iff N w K)

/-! ### The family construction is well formed, acyclic and totally ordered

The class conditions of the source classes of the open cells of Table 3 are established for the
family construction: its initial task network is a single chain and it is acyclic, hence also
tail-recursive.  Acyclicity uses the rank function of the original construction — the rank of
`produceSym c` does not depend on the letter `c`, which is why the letter-indexed family of
methods is still stratified — and the generic transfer
`HTN.GuardTask.isAcyclic_guard_iff` for the guard tasks. -/

/-- A compound task occurs in a lifted body exactly when it occurs in the body. -/
lemma mem_flatten_liftBody {ls : List (List (TMAct Q Γ ⊕ TMTask Q Γ))} {c : TMTask Q Γ} :
    (Sum.inr c : GAct Q Γ ⊕ TMTask Q Γ) ∈ (liftBody ls).flatten ↔
      (Sum.inr c : TMAct Q Γ ⊕ TMTask Q Γ) ∈ ls.flatten := by
  rw [liftBody, ← List.map_flatten]
  constructor
  · intro h
    obtain ⟨y, hy, hyc⟩ := List.mem_map.1 h
    cases y with
    | inl a => exact absurd hyc (by simp)
    | inr d =>
        have hd : d = c := by simpa using hyc
        subst hd
        exact hy
  · intro h
    exact List.mem_map.2 ⟨Sum.inr c, h, rfl⟩

/-- **The rank function of the original construction stratifies the family construction.** -/
lemma rank_lt_of_mem_bodiesAll {N : NTM Q Γ} {n K : ℕ} {t : TMTask Q Γ}
    {ls : List (List (GAct Q Γ ⊕ TMTask Q Γ))} (hls : ls ∈ bodiesAll N n K t)
    {c : TMTask Q Γ} (hc : Sum.inr c ∈ ls.flatten) :
    rank K n c < rank K n t := by
  by_cases hw : ∃ i, t = TMTask.produceWord i
  · obtain ⟨i, rfl⟩ := hw
    rw [bodiesAll_produceWord] at hls
    have hex : ∃ c', ls = liftBody (bodyWord n i c') := by
      by_cases hlt : i < n
      · rw [if_pos hlt] at hls; exact hls
      · rw [if_neg hlt] at hls; exact ⟨N.blank, hls⟩
    obtain ⟨c', rfl⟩ := hex
    rw [mem_flatten_liftBody] at hc
    by_cases hlt : i + 1 < n
    · simp only [bodyWord, if_pos hlt, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      rcases hc with rfl | rfl <;> simp only [rank] <;> omega
    · simp only [bodyWord, if_neg hlt, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false, Sum.inr.injEq] at hc
      subst hc
      simp only [rank]
      omega
  · push_neg at hw
    rw [bodiesAll_eq_image hw] at hls
    obtain ⟨ls₀, hls₀, rfl⟩ := hls
    rw [mem_flatten_liftBody] at hc
    have h := rank_lt_of_mem_bodiesFix (N := N) (w := wpad N n) (K := K) hls₀ hc
    simpa using h

/-- The compound tasks of the initial task network, in the enlarged signature. -/
lemma rank_lt_of_mem_initNetG {w : List Γ} {K : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ (initNetG (Q := Q) (Γ := Γ) K).T) {c : TMTask Q Γ}
    (hc : (initNetG (Q := Q) (Γ := Γ) K).α p = Sum.inr c) :
    rank K w.length c < rank K w.length (TMTask.sI (Q := Q) (Γ := Γ)) := by
  have hrel := relabel_initNetFix (Q := Q) (Γ := Γ) K
  have hT : p ∈ (initNetFix (Q := Q) (Γ := Γ) K).T := by
    have : (initNetG (Q := Q) (Γ := Γ) K).T
        = (initNetFix (Q := Q) (Γ := Γ) K).T.image (Equiv.refl (ℕ × ℕ)) := by
      rw [← hrel]; rfl
    rw [this] at hp
    simpa using hp
  have hα : (initNetFix (Q := Q) (Γ := Γ) K).α p = Sum.inr c := by
    have hmap : Sum.map (Sum.inr : TMAct Q Γ → GAct Q Γ) id
        ((initNetFix (Q := Q) (Γ := Γ) K).α p) = Sum.inr c := by
      rw [← hc, ← hrel]; rfl
    cases hx : (initNetFix (Q := Q) (Γ := Γ) K).α p with
    | inl a => rw [hx] at hmap; exact absurd hmap (by simp)
    | inr d => rw [hx] at hmap; simpa using hmap
  exact rank_lt_of_mem_initNetFix (w := w) hT hα

/-- **The family domain, before the guard tasks are added, is acyclic.** -/
theorem isAcyclic_allDomain (N : NTM Q Γ) (n K : ℕ)
    (Qi : Instance (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)) :
    ((allDomain N n K).mkProblem Qi).IsAcyclic := by
  refine Problem.isAcyclic_of_rank _ (rank K n) ?_
  rintro ⟨ct, tn⟩ ⟨hm, -⟩ t ht c hc
  rcases hm with ⟨ls, hls, hsub⟩ | hsI
  · subst hsub
    refine rank_lt_of_mem_bodiesAll hls ?_
    have hmem := TaskNetwork.grid_α_mem_flatten (ls := ls) ht
    rwa [hc] at hmem
  · simp only [Set.mem_singleton_iff, Method.mk.injEq] at hsI
    obtain ⟨rfl, rfl⟩ := hsI
    have h := rank_lt_of_mem_initNetG (w := wpad N n) (K := K) ht hc
    simpa using h

/-- **The family problem is acyclic.** -/
theorem isAcyclic_famDomain (N : NTM Q Γ) (n K : ℕ)
    (Qi : Instance (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)) :
    ((famDomain N n K).mkProblem Qi).IsAcyclic :=
  (GuardTask.isAcyclic_guard_iff (D := allDomain N n K) (Dg := famDomain N n K) (Q := Qi)
      (fun m hm => ⟨m, hm, rfl⟩) (by rintro mg ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩)
      (fun m _ => gid_not_mem m)).2 (isAcyclic_allDomain N n K Qi)

/-- **The family problem is tail-recursive**, so the same construction serves in `HTN-AC` and in
`HTN-TR`. -/
theorem isTailRecursive_famDomain (N : NTM Q Γ) (n K : ℕ)
    (Qi : Instance (GFact Q Γ) (GAct Q Γ) (TMTask Q Γ) (ℕ × ℕ)) :
    ((famDomain N n K).mkProblem Qi).IsTailRecursive :=
  (isAcyclic_famDomain N n K Qi).isTailRecursive

/-- **The initial task network of the family problem is totally ordered.** -/
theorem isTO_tnI_famDomain (N : NTM Q Γ) (n K : ℕ) (w : List Γ) :
    ((famDomain N n K).mkProblem (famInstance N w)).IsTO_tnI :=
  TaskNetwork.seq_isTotallyOrdered

/-- **The family problem is well formed.** -/
theorem wf_famDomain (N : NTM Q Γ) (n K : ℕ) (w : List Γ) :
    ((famDomain N n K).mkProblem (famInstance N w)).WF where
  tnI := TaskNetwork.seq_wf
  methods := by
    rintro mg ⟨m, hm, rfl⟩
    exact GuardTask.addTask_wf (wf_of_mem_methodsOf hm) _ _

end Fam

end TMEnc

end HTN
