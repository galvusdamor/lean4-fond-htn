import FondHtn.DB25.Chain
import FondHtn.DB25.OpsSem
import FondHtn.Prim.WeakHard
/-!
# Regular problems built from phase programs

A **phase program** is a list of phases, each a list of action descriptions (their names are
ignored).  `FOND.DB.mkDesc init pre loops finals` is the FOND description with

* the initial network: the phases of `pre`, then the compound task `0`;
* for every `phs ∈ loops` a method `0 → phs · 0` (the phases, then `0` again);
* for every `phs ∈ finals` a method `0 → phs`;

where the tasks of a phase are unordered and every phase precedes the next (ids `⟨p, i⟩`, the
compound task `⟨|phs|, 0⟩`), and every task carries its own action, named `⟨k, ⟨p, i⟩⟩` for the
`k`-th network.

`FOND.DB.mkDesc_strongOD_iff`: strong OD plan existence is the chain of phase games
`∃ w f, phasesWin pre (phasesWin loops[w₁] (… phasesWin finals[f] ⊤)) s_I`.
-/

namespace FOND

namespace DB

open HTN HTN.Syn HTN.Article Problem FOND.TaskNetwork

/-! ## Networks of phase programs -/

/-- The ids of the primitive tasks. -/
def primIds (phs : List (List FActDesc)) : List ℕ :=
  (List.range phs.length).flatMap fun p => (List.range (phs.getI p).length).map (Nat.pair p)

/-- The id of the compound task. -/
def topId (phs : List (List FActDesc)) : ℕ := Nat.pair phs.length 0

/-- The phase of an id. -/
def phOf (x : ℕ) : ℕ := (Nat.unpair x).1

/-- All ids. -/
def allIds (phs : List (List FActDesc)) (loop : Bool) : List ℕ :=
  primIds phs ++ (if loop then [topId phs] else [])

/-- The network of a phase program (the `k`-th one). -/
def progTn (k : ℕ) (phs : List (List FActDesc)) (loop : Bool) : TnDesc :=
  (allIds phs loop,
    (allIds phs loop).flatMap (fun a => ((allIds phs loop).filter fun b =>
      decide (phOf a < phOf b)).map (a, ·)),
    (primIds phs).map (fun x => (x, false, Nat.pair k x)) ++
      (if loop then [(topId phs, true, 0)] else []))

theorem mem_primIds {phs : List (List FActDesc)} {x : ℕ} :
    x ∈ primIds phs ↔ phOf x < phs.length ∧ (Nat.unpair x).2 < (phs.getI (phOf x)).length := by
  simp only [primIds, List.mem_flatMap, List.mem_range, List.mem_map, phOf]
  constructor
  · rintro ⟨p, hp, i, hi, rfl⟩; simp [hp, hi]
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, _, h2, Nat.pair_unpair x⟩

theorem nodup_primIds (phs : List (List FActDesc)) : (primIds phs).Nodup := by
  unfold primIds
  rw [List.nodup_flatMap]
  refine ⟨fun p _ => (List.nodup_range).map fun a b h => (Nat.pair_eq_pair.1 h).2, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun p _ q _ hpq => ?_
  rw [Function.onFun, List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_range] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, h⟩ := hy
  exact hpq (Nat.pair_eq_pair.1 h).1.symm

theorem topId_not_mem (phs : List (List FActDesc)) : topId phs ∉ primIds phs := by
  rw [mem_primIds]; simp [topId, phOf]

theorem phOf_topId (phs : List (List FActDesc)) : phOf (topId phs) = phs.length := by
  simp [topId, phOf]

theorem mem_allIds {phs : List (List FActDesc)} {loop : Bool} {x : ℕ} :
    x ∈ allIds phs loop ↔ x ∈ primIds phs ∨ (loop = true ∧ x = topId phs) := by
  cases loop <;> simp [allIds]

theorem nodup_allIds (phs : List (List FActDesc)) (loop : Bool) : (allIds phs loop).Nodup := by
  cases loop
  · simpa [allIds] using nodup_primIds phs
  · simp only [allIds, if_true]
    exact List.nodup_append.2 ⟨nodup_primIds phs, List.nodup_singleton _, by
      intro x hx y hy; simp at hy; subst hy; exact fun e => topId_not_mem phs (e ▸ hx)⟩

theorem mem_ordL {k : ℕ} {phs : List (List FActDesc)} {loop : Bool} {a b : ℕ} :
    (a, b) ∈ (progTn k phs loop).ordList ↔
      a ∈ allIds phs loop ∧ b ∈ allIds phs loop ∧ phOf a < phOf b := by
  simp only [progTn, TnDesc.ordList, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', ⟨hb', hlt⟩, rfl, rfl⟩; exact ⟨ha', hb', hlt⟩
  · rintro ⟨ha, hb, hlt⟩; exact ⟨a, ha, b, ⟨hb, hlt⟩, rfl, rfl⟩

theorem tnValid_progTn {prim : ℕ → Prop} (k : ℕ) (phs : List (List FActDesc)) (loop : Bool)
    (hprim : ∀ x ∈ primIds phs, prim (Nat.pair k x)) : TnValid prim (progTn k phs loop) where
  nodup := nodup_allIds phs loop
  ord_mem := by
    rintro ⟨a, b⟩ h
    have := mem_ordL.1 h
    exact ⟨this.1, this.2.1⟩
  irrefl := fun a h => by have := (mem_ordL.1 h).2.2; omega
  trans := fun a b c h1 h2 => by
    have h1' := mem_ordL.1 h1; have h2' := mem_ordL.1 h2
    exact mem_ordL.2 ⟨h1'.1, h2'.2.1, by omega⟩
  lbl_perm := by
    cases loop <;> simp [progTn, TnDesc.lbl, TnDesc.ids, allIds, List.map_map, Function.comp_def]
  prim_ok := by
    intro q hq hf
    simp only [progTn, TnDesc.lbl, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨x, hx, rfl⟩ | hq
    · exact hprim x hx
    · cases loop <;> simp at hq; subst hq; simp at hf

/-! ## The described networks -/

section Net

variable {k : ℕ} {phs : List (List FActDesc)} {loop : Bool}

theorem tnValid_progTn_true (k : ℕ) (phs : List (List FActDesc)) (loop : Bool) :
    TnValid (fun _ => True) (progTn k phs loop) := tnValid_progTn k phs loop fun _ _ => trivial

theorem progTn_T {x : ℕ} : x ∈ (progTn k phs loop).toTaskNetwork.T ↔ x ∈ allIds phs loop := by
  simp [TnDesc.toTaskNetwork, progTn, TnDesc.ids]

theorem progTn_ord {a b : ℕ} : (progTn k phs loop).toTaskNetwork.ord a b ↔
    a ∈ allIds phs loop ∧ b ∈ allIds phs loop ∧ phOf a < phOf b := by
  show (progTn k phs loop).ordOf a b ↔ _
  rw [(tnValid_progTn_true k phs loop).ordOf_iff]; exact mem_ordL

theorem progTn_α_prim {x : ℕ} (hx : x ∈ primIds phs) :
    (progTn k phs loop).toTaskNetwork.α x = Sum.inl (Nat.pair k x) := by
  show (progTn k phs loop).label x = _
  unfold TnDesc.label
  simp only [progTn, TnDesc.lbl]
  rw [lookup_append, Undec.lookup_map_self (fun x => (false, Nat.pair k x)) _ hx]
  rfl

theorem progTn_α_top : (progTn k phs true).toTaskNetwork.α (topId phs) = Sum.inr 0 := by
  show (progTn k phs true).label (topId phs) = _
  unfold TnDesc.label
  simp only [progTn, TnDesc.lbl, if_true]
  rw [lookup_append, Undec.lookup_map_self_none (fun x => (false, Nat.pair k x)) _
    (topId_not_mem phs)]
  simp [List.lookup]

theorem progTn_wf : (progTn k phs loop).toTaskNetwork.WF := TnDesc.toTaskNetwork_wf _

theorem isLoop_progTn : IsLoop (progTn k phs true).toTaskNetwork 0 := by
  refine ⟨progTn_wf, topId phs, progTn_T.2 (mem_allIds.2 (Or.inr ⟨rfl, rfl⟩)), progTn_α_top,
    fun t ht hne => ?_⟩
  have htp : t ∈ primIds phs := by
    rcases mem_allIds.1 (progTn_T.1 ht) with h | ⟨-, h⟩
    · exact h
    · exact absurd h hne
  refine ⟨⟨_, progTn_α_prim htp⟩, progTn_ord.2 ⟨progTn_T.1 ht,
    mem_allIds.2 (Or.inr ⟨rfl, rfl⟩), ?_⟩⟩
  rw [phOf_topId]; exact (mem_primIds.1 htp).1

theorem isFinal_progTn : IsFinal (progTn k phs false).toTaskNetwork := by
  refine ⟨progTn_wf, fun t ht => ?_⟩
  have htp : t ∈ primIds phs := by simpa [mem_allIds] using progTn_T.1 ht
  exact ⟨_, progTn_α_prim htp⟩

/-- The `p`-th phase of the primitive part. -/
theorem winK_phase {P : Problem ℕ ℕ ℕ ℕ}
    (hδ : ∀ x ∈ primIds phs, P.δ (Nat.pair k x) =
      ((phs.getI (phOf x)).getI (Nat.unpair x).2).toAction)
    {p : ℕ} (hp : p < phs.length) (K : Set ℕ → Prop) (s : Set ℕ) :
    P.WinK K (restr (primPart (progTn k phs loop).toTaskNetwork) fun x => phOf x = p) s ↔
      setWin K ((phs.getI p).map FActDesc.toAction) s := by
  classical
  refine winK_iff_setWin _ _ ((List.range (phs.getI p).length).map (Nat.pair p)) _ s rfl
    (fun a b h => ?_) ((List.nodup_range).map fun a b h => (Nat.pair_eq_pair.1 h).2) ?_
    (by simp) (fun i hi => ?_)
  · obtain ⟨⟨hab, -, -⟩, ha, hb⟩ := h
    have := (progTn_ord.1 hab).2.2; omega
  · ext x
    simp only [mem_restr_T, primPart, progTn_T, List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨⟨hx, hprim⟩, rfl⟩
      have htp : x ∈ primIds phs := by
        rcases mem_allIds.1 hx with h | ⟨rfl, h⟩
        · exact h
        · subst h; rw [progTn_α_top] at hprim; simp at hprim
      exact ⟨_, (mem_primIds.1 htp).2, by simp [phOf]⟩
    · rintro ⟨i, hi, rfl⟩
      have htp : Nat.pair (phOf (Nat.pair p i)) i ∈ primIds phs := by
        rw [mem_primIds]; simp [phOf, hp, hi]
      have htp' : Nat.pair p i ∈ primIds phs := by simpa [phOf] using htp
      exact ⟨⟨mem_allIds.2 (Or.inl htp'), _, progTn_α_prim htp'⟩, by simp [phOf]⟩
  · simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hi ⊢
    have htp : Nat.pair p i ∈ primIds phs := by
      rw [mem_primIds]; simp [phOf, hp, hi]
    refine ⟨_, progTn_α_prim htp, ?_⟩
    rw [hδ _ htp]
    simp [phOf, List.getI_eq_getElem _ hi]

theorem primPart_phaseOrd :
    PhaseOrd (primPart (progTn k phs loop).toTaskNetwork) phOf := by
  classical
  intro a ha b hb
  simp only [primPart, mem_restr_T, progTn_T] at ha hb
  simp only [primPart, restr, progTn_ord]
  constructor
  · rintro ⟨⟨-, -, h⟩, -, -⟩; exact h
  · intro h; exact ⟨⟨ha.1, hb.1, h⟩, ha.2, hb.2⟩

theorem primPart_ph_lt {x : ℕ} (hx : x ∈ (primPart (progTn k phs loop).toTaskNetwork).T) :
    phOf x < phs.length := by
  classical
  simp only [primPart, mem_restr_T, progTn_T] at hx
  rcases mem_allIds.1 hx.1 with h | ⟨rfl, h⟩
  · exact (mem_primIds.1 h).1
  · subst h; have := hx.2; rw [progTn_α_top] at this; simp at this

/-- **The primitive part of a phase program network is the sequence of its phase games.** -/
theorem winK_primPart_progTn {P : Problem ℕ ℕ ℕ ℕ}
    (hδ : ∀ x ∈ primIds phs, P.δ (Nat.pair k x) =
      ((phs.getI (phOf x)).getI (Nat.unpair x).2).toAction) (K : Set ℕ → Prop) (s : Set ℕ) :
    P.WinK K (primPart (progTn k phs loop).toTaskNetwork) s ↔ phasesWin phs K s := by
  rw [winK_phases primPart_phaseOrd (fun x hx => primPart_ph_lt hx) K s]
  suffices h : ∀ c i, i + c = phs.length → ∀ K s,
      P.nestW (primPart (progTn k phs loop).toTaskNetwork) phOf i c K s ↔
        phasesWin (phs.drop i) K s by
    simpa using h phs.length 0 (by simp) K s
  intro c
  induction c with
  | zero =>
    intro i hi K s
    have : phs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]; rfl
  | succ c ih =>
    intro i hi K s
    have hlt : i < phs.length := by omega
    rw [List.drop_eq_getElem_cons hlt, phasesWin_cons, nestW, ← List.getI_eq_getElem _ hlt]
    have hK : P.nestW (primPart (progTn k phs loop).toTaskNetwork) phOf (i + 1) c K =
        phasesWin (phs.drop (i + 1)) K := funext fun s' => propext (ih (i + 1) (by omega) K s')
    rw [hK]
    exact winK_phase hδ hlt _ s

end Net

/-! ## The description -/

/-- The networks: `tn_I`, the loops, the finals. -/
def mlist (pre : List (List FActDesc)) (loops finals : List (List (List FActDesc))) :
    List (List (List FActDesc) × Bool) :=
  (pre, true) :: (loops.map (·, true) ++ finals.map (·, false))

/-- The action at the id `x` of a phase program. -/
def actAt (phs : List (List FActDesc)) (x : ℕ) : FActDesc :=
  (phs.getI (phOf x)).getI (Nat.unpair x).2

/-- The actions of all networks, named `⟨k, x⟩`. -/
def mkActs (ml : List (List (List FActDesc) × Bool)) : List FActDesc :=
  (List.range ml.length).flatMap fun k =>
    (primIds (ml.getI k).1).map fun x => (Nat.pair k x, (actAt (ml.getI k).1 x).2)

/-- **The description of a regular problem from phase programs.** -/
def mkDesc (init : List ℕ) (pre : List (List FActDesc))
    (loops finals : List (List (List FActDesc))) : FProbDesc :=
  ((mkActs (mlist pre loops finals),
    (List.range ((mlist pre loops finals).length - 1)).map fun j =>
      (0, progTn (j + 1) ((mlist pre loops finals).getI (j + 1)).1
        ((mlist pre loops finals).getI (j + 1)).2)),
    (init, progTn 0 pre true))

section Desc

variable {init : List ℕ} {pre : List (List FActDesc)} {loops finals : List (List (List FActDesc))}

theorem names_mkActs (ml : List (List (List FActDesc) × Bool)) :
    (mkActs ml).map FActDesc.name =
      (List.range ml.length).flatMap fun k => (primIds (ml.getI k).1).map (Nat.pair k) := by
  simp only [mkActs, List.map_flatMap, List.map_map]
  rfl

theorem nodup_names (ml : List (List (List FActDesc) × Bool)) :
    ((mkActs ml).map FActDesc.name).Nodup := by
  rw [names_mkActs, List.nodup_flatMap]
  refine ⟨fun k _ => (nodup_primIds _).map fun a b h => (Nat.pair_eq_pair.1 h).2, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun p _ q _ hpq => ?_
  rw [Function.onFun, List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map] at hx hy
  obtain ⟨i, -, rfl⟩ := hx
  obtain ⟨j, -, h⟩ := hy
  exact hpq (Nat.pair_eq_pair.1 h).1.symm

theorem mem_names {ml : List (List (List FActDesc) × Bool)} {k x : ℕ} (hk : k < ml.length)
    (hx : x ∈ primIds (ml.getI k).1) : Nat.pair k x ∈ (mkActs ml).map FActDesc.name := by
  rw [names_mkActs]
  exact List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, List.mem_map.2 ⟨x, hx, rfl⟩⟩

theorem actAt_mem {phs : List (List FActDesc)} {x : ℕ} (hx : x ∈ primIds phs) :
    ∃ ph ∈ phs, actAt phs x ∈ ph := by
  obtain ⟨h1, h2⟩ := mem_primIds.1 hx
  refine ⟨phs.getI (phOf x), ?_, ?_⟩
  · rw [List.getI_eq_getElem _ h1]; exact List.getElem_mem h1
  · unfold actAt; rw [List.getI_eq_getElem _ h2]; exact List.getElem_mem h2

/-- Every action has an effect. -/
def EffsNe (ml : List (List (List FActDesc) × Bool)) : Prop :=
  ∀ e ∈ ml, ∀ ph ∈ e.1, ∀ a ∈ ph, a.2.2.2 ≠ []

theorem mlist_length : (mlist pre loops finals).length = loops.length + finals.length + 1 := by
  simp [mlist]

theorem mkDesc_valid (hE : EffsNe (mlist pre loops finals)) :
    (mkDesc init pre loops finals).Valid where
  names_nodup := nodup_names _
  effs_ne := by
    intro a ha
    simp only [mkDesc, FProbDesc.actions, mkActs, List.mem_flatMap, List.mem_range,
      List.mem_map] at ha
    obtain ⟨k, hk, x, hx, rfl⟩ := ha
    obtain ⟨ph, hph, ha⟩ := actAt_mem hx
    show (actAt _ x).2.2.2 ≠ []
    exact hE _ (by rw [List.getI_eq_getElem _ hk]; exact List.getElem_mem hk) ph hph (actAt _ x) ha
  tnI := by
    refine tnValid_progTn 0 pre true fun x hx => ?_
    unfold FProbDesc.Declared
    exact mem_names (ml := mlist pre loops finals) (by simp [mlist]) (by simpa [mlist] using hx)
  methods := by
    intro m hm
    simp only [mkDesc, FProbDesc.methods, List.mem_map, List.mem_range] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    refine tnValid_progTn _ _ _ fun x hx => ?_
    unfold FProbDesc.Declared
    exact mem_names (by omega) hx

theorem mkDesc_δ (hE : EffsNe (mlist pre loops finals)) {k x : ℕ}
    (hk : k < (mlist pre loops finals).length) (hx : x ∈ primIds ((mlist pre loops finals).getI k).1) :
    (mkDesc init pre loops finals).toProblem.δ (Nat.pair k x) =
      (actAt ((mlist pre loops finals).getI k).1 x).toAction := by
  have hm : (Nat.pair k x, (actAt ((mlist pre loops finals).getI k).1 x).2) ∈
      (mkDesc init pre loops finals).actions := by
    simp only [mkDesc, FProbDesc.actions, mkActs, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨k, hk, x, hx, rfl⟩
  exact FProbDesc.δ_of_mem (mkDesc_valid hE) hm

theorem mlist_getI_zero : (mlist pre loops finals).getI 0 = (pre, true) := rfl

theorem mlist_getI_loop {w : ℕ} (hw : w < loops.length) :
    (mlist pre loops finals).getI (w + 1) = (loops.getI w, true) := by
  simp only [mlist, List.getI_cons_succ]
  rw [List.getI_append _ _ _ (by simpa using hw)]
  rw [List.getI_eq_getElem _ (by simpa using hw), List.getI_eq_getElem _ hw]
  simp

theorem mlist_getI_final {f : ℕ} (hf : f < finals.length) :
    (mlist pre loops finals).getI (loops.length + 1 + f) = (finals.getI f, false) := by
  rw [show loops.length + 1 + f = (loops.length + f) + 1 by omega]
  simp only [mlist, List.getI_cons_succ]
  rw [List.getI_append_right _ _ _ (by simp), List.getI_eq_getElem _ (by simpa using hf),
    List.getI_eq_getElem _ hf]
  simp

/-- The loop method `w`. -/
noncomputable def loopM (pre : List (List FActDesc)) (loops : List (List (List FActDesc))) (w : ℕ) :
    Method ℕ ℕ ℕ := MethodDesc.toMethod (0, progTn (w + 1) (loops.getI w) true)

/-- The final method `f`. -/
noncomputable def finalM (loops finals : List (List (List FActDesc))) (f : ℕ) : Method ℕ ℕ ℕ :=
  MethodDesc.toMethod (0, progTn (loops.length + 1 + f) (finals.getI f) false)

theorem mem_methods_iff {m : Method ℕ ℕ ℕ} : m ∈ (mkDesc init pre loops finals).toProblem.methods ↔
    ∃ j < loops.length + finals.length, m = MethodDesc.toMethod (0, progTn (j + 1)
      ((mlist pre loops finals).getI (j + 1)).1 ((mlist pre loops finals).getI (j + 1)).2) := by
  simp only [FProbDesc.toProblem, mkDesc, FProbDesc.methods, Set.mem_setOf_eq, List.mem_map,
    List.mem_range, mlist_length]
  constructor
  · rintro ⟨e, ⟨j, hj, rfl⟩, rfl⟩; exact ⟨j, by omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨_, ⟨j, by omega, rfl⟩, rfl⟩

theorem loopM_mem {w : ℕ} (hw : w < loops.length) :
    loopM pre loops w ∈ (mkDesc init pre loops finals).toProblem.methods :=
  mem_methods_iff.2 ⟨w, by omega, by rw [mlist_getI_loop hw]; rfl⟩

theorem finalM_mem {f : ℕ} (hf : f < finals.length) :
    finalM loops finals f ∈ (mkDesc init pre loops finals).toProblem.methods := by
  refine mem_methods_iff.2 ⟨loops.length + f, by omega, ?_⟩
  rw [show loops.length + f + 1 = loops.length + 1 + f by omega, mlist_getI_final hf]; rfl

theorem method_cases {m : Method ℕ ℕ ℕ} (hm : m ∈ (mkDesc init pre loops finals).toProblem.methods) :
    (∃ w < loops.length, m = loopM pre loops w) ∨ (∃ f < finals.length, m = finalM loops finals f) := by
  obtain ⟨j, hj, rfl⟩ := mem_methods_iff.1 hm
  rcases Nat.lt_or_ge j loops.length with h | h
  · left; refine ⟨j, h, ?_⟩; rw [mlist_getI_loop h]; rfl
  · right
    refine ⟨j - loops.length, by omega, ?_⟩
    have := mlist_getI_final (pre := pre) (loops := loops) (finals := finals)
      (f := j - loops.length) (by omega)
    rw [show loops.length + 1 + (j - loops.length) = j + 1 by omega] at this
    rw [this]; unfold finalM; congr 3; omega

theorem regChain_mkDesc : (mkDesc init pre loops finals).toProblem.RegChain 0 := by
  refine ⟨isLoop_progTn, fun m hm => ?_⟩
  rcases method_cases hm with ⟨w, -, rfl⟩ | ⟨f, -, rfl⟩
  · exact ⟨rfl, Or.inl isLoop_progTn⟩
  · exact ⟨rfl, Or.inr isFinal_progTn⟩

/-- Chains of phase games. -/
def chainP : List (List (List FActDesc)) → (Set ℕ → Prop) → Set ℕ → Prop
  | [], K => K
  | phs :: L, K => phasesWin phs (chainP L K)

theorem hδ_of (hE : EffsNe (mlist pre loops finals)) {k : ℕ}
    (hk : k < (mlist pre loops finals).length) {phs : List (List FActDesc)}
    (hphs : ((mlist pre loops finals).getI k).1 = phs) :
    ∀ x ∈ primIds phs, (mkDesc init pre loops finals).toProblem.δ (Nat.pair k x) =
      ((phs.getI (phOf x)).getI (Nat.unpair x).2).toAction := by
  subst hphs
  intro x hx
  exact mkDesc_δ hE hk hx

theorem chainWin_mkDesc (hE : EffsNe (mlist pre loops finals)) {f : ℕ} (hf : f < finals.length) :
    ∀ (ws : List ℕ), (∀ w ∈ ws, w < loops.length) → ∀ s,
      (mkDesc init pre loops finals).toProblem.chainWin
        (blocks (ws.map (loopM pre loops)) ++ [(finalM loops finals f).subtasks]) s ↔
      chainP (ws.map loops.getI ++ [finals.getI f]) (fun _ => True) s := by
  intro ws
  induction ws with
  | nil =>
    intro _ s
    simp only [List.map_nil, blocks, List.nil_append, chainP]
    show (mkDesc init pre loops finals).toProblem.WinK (fun _ => True)
      (progTn (loops.length + 1 + f) (finals.getI f) false).toTaskNetwork s ↔ _
    have hX := primPart_final (isFinal_progTn (k := loops.length + 1 + f) (phs := finals.getI f))
    rw [← winK_primPart_progTn (hδ_of (init := init) (pre := pre) (loops := loops)
      (finals := finals) hE (k := loops.length + 1 + f) (by rw [mlist_length]; omega)
      (by rw [mlist_getI_final hf])) _ s]
    exact ⟨fun h => h.iso hX.symm, fun h => h.iso hX⟩
  | cons w ws ih =>
    intro hws s
    have hw := hws w (by simp)
    simp only [List.map_cons, blocks, List.cons_append, chainP]
    show (mkDesc init pre loops finals).toProblem.WinK _
      (primPart (progTn (w + 1) (loops.getI w) true).toTaskNetwork) s ↔ _
    have hK : (mkDesc init pre loops finals).toProblem.chainWin
        (blocks (ws.map (loopM pre loops)) ++ [(finalM loops finals f).subtasks]) =
        chainP (ws.map loops.getI ++ [finals.getI f]) (fun _ => True) :=
      funext fun s' => propext (ih (fun w' hw' => hws w' (by simp [hw'])) s')
    simp only [blocks] at hK
    rw [hK]
    exact winK_primPart_progTn (hδ_of (init := init) (pre := pre) (loops := loops)
      (finals := finals) hE (k := w + 1) (by rw [mlist_length]; omega)
      (by rw [mlist_getI_loop hw])) _ s

/-- **Strong OD plan existence of a problem built from phase programs.** -/
theorem mkDesc_strongOD_iff (hE : EffsNe (mlist pre loops finals)) :
    (mkDesc init pre loops finals).toProblem.StrongODSolvable ↔
      ∃ (ws : List ℕ) (f : ℕ), (∀ w ∈ ws, w < loops.length) ∧ f < finals.length ∧
        chainP (pre :: (ws.map loops.getI ++ [finals.getI f])) (fun _ => True) {x | x ∈ init} := by
  rw [strongOD_iff_chain regChain_mkDesc]
  have hpre := hδ_of (init := init) hE (k := 0) (by simp [mlist]) (phs := pre) rfl
  have key : ∀ (ws : List ℕ) (f : ℕ), (∀ w ∈ ws, w < loops.length) → f < finals.length →
      ((mkDesc init pre loops finals).toProblem.chainWin
        (primPart (mkDesc init pre loops finals).toProblem.tnI ::
          blocks (ws.map (loopM pre loops)) ++ [(finalM loops finals f).subtasks])
        (mkDesc init pre loops finals).toProblem.init ↔
      chainP (pre :: (ws.map loops.getI ++ [finals.getI f])) (fun _ => True) {x | x ∈ init}) := by
    intro ws f hws hf
    show (mkDesc init pre loops finals).toProblem.WinK _
      (primPart (progTn 0 pre true).toTaskNetwork) {x | x ∈ init} ↔ _
    have hK := funext fun s => propext (chainWin_mkDesc (init := init) hE hf ws hws s)
    show (mkDesc init pre loops finals).toProblem.WinK ((mkDesc init pre loops finals).toProblem.chainWin
      (blocks (ws.map (loopM pre loops)) ++ [(finalM loops finals f).subtasks]))
      (primPart (progTn 0 pre true).toTaskNetwork) {x | x ∈ init} ↔ _
    rw [hK]
    exact winK_primPart_progTn hpre _ _
  constructor
  · rintro ⟨ms, mf, hms, hmf, hfin, hw⟩
    -- the final method
    obtain ⟨f, hf, rfl⟩ : ∃ f < finals.length, mf = finalM loops finals f := by
      rcases method_cases hmf with ⟨w, -, rfl⟩ | h
      · exact absurd isLoop_progTn (fun h => loop_not_final h hfin)
      · exact h
    -- the loop methods
    have : ∀ ms : List (Method ℕ ℕ ℕ), (∀ m ∈ ms, m ∈ (mkDesc init pre loops finals).toProblem.methods ∧
        IsLoop m.subtasks 0) → ∃ ws : List ℕ, (∀ w ∈ ws, w < loops.length) ∧
          ms = ws.map (loopM pre loops) := by
      intro ms
      induction ms with
      | nil => exact fun _ => ⟨[], by simp, rfl⟩
      | cons m ms ih =>
        intro h
        obtain ⟨ws, hws, rfl⟩ := ih fun m' hm' => h m' (by simp [hm'])
        rcases method_cases (h m List.mem_cons_self).1 with ⟨w, hw, rfl⟩ | ⟨g, -, rfl⟩
        · refine ⟨w :: ws, fun w' hw' => ?_, rfl⟩
          rcases List.mem_cons.1 hw' with rfl | h
          · exact hw
          · exact hws w' h
        · have h1 := (h (finalM loops finals g) List.mem_cons_self).2
          exact absurd (isFinal_progTn (k := loops.length + 1 + g) (phs := finals.getI g))
            (loop_not_final h1)
    obtain ⟨ws, hws, rfl⟩ := this ms hms
    exact ⟨ws, f, hws, hf, (key ws f hws hf).1 hw⟩
  · rintro ⟨ws, f, hws, hf, h⟩
    refine ⟨ws.map (loopM pre loops), finalM loops finals f, fun m hm => ?_, finalM_mem hf,
      isFinal_progTn, (key ws f hws hf).2 h⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
    exact ⟨loopM_mem (hws w hw), isLoop_progTn⟩

end Desc


end DB



end FOND
