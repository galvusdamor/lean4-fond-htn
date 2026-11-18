import HtnComplexity.Space.AltTbl
import HtnComplexity.Space.RegRename
import HtnPlanning.Computable.Bodies
import HtnPlanning.Core.ToStateReach
/-!
# Totally ordered HTN plan existence as reachability with calls

This is the mathematical half of the target side of cells 3 and 5 of Table 3: plan existence for
a totally ordered domain description `d` and a rooted instance description `q` is
reachability with calls (`HTN.Space.CReach`) in a table computed from `d` alone, from an initial
state and to a goal read off `q` exactly as in the regular and the tail-recursive case
(`HTN.Space.regInitR`, `HTN.Space.regGoalR`):

    HTN.Space.solvable_to_iff_cReach :
      Solvable d q ↔ ∃ s', CReach (toPlain d) (toCalls d) {f | f ∈ regInitR q} s' ∧
        {f | f ∈ regGoalR q} ⊆ s'

## The facts

| fact | number | meaning |
| --- | --- | --- |
| `toF v` | `4v + 2` | the fact `v` of the source problem holds |
| `toCall c` | `4c + 3` | the compound task `c` is to be refined next |
| `0` | `0` | the current refinement is complete |
| `toCur m j` | `4⟨m, j⟩ + 4` | the refinement is at position `j` of the body of method `m` |

A state of the table is a world state (a set of source facts, encoded) together with exactly one
*control* fact.  Unlike Alford's stack machine for the tail-recursive case, there is no stack:
the control fact describes the innermost frame only, and a call of a compound task in the middle
of a body is a call pair — push `toCur m j ↦ toCall c`, return `0 ↦ toCur m (j + 1)` — whose
callee runs in a branch of its own (`HTN.Space.CReach.call`).

## The rows

| kind | precondition | add | delete |
| --- | --- | --- | --- |
| `begRow m` | `toCall (hd m)` | `toCur m 0` | `toCall (hd m)` |
| `finRow m` | `toCur m |bd m|` | `0` | `toCur m |bd m|` |
| `execRow m j a` | `toCur m j`, `prec a` | `toCur m (j+1)`, `add a` | `toCur m j`, `del a` |
| `pushRow m j c` | `toCur m j` | `toCall c` | `toCur m j` |
| `retRow m j` | `0` | `toCur m (j+1)` | `0` |
-/

namespace HTN

namespace Space

open Syn

/-! ### The facts -/

/-- A fact of the source problem. -/
def toF (v : ℕ) : ℕ := 4 * v + 2

/-- A compound task, to be refined next. -/
def toCall (c : ℕ) : ℕ := 4 * c + 3

/-- The control fact of position `j` of the body of method `m`. -/
def toCur (m j : ℕ) : ℕ := 4 * Nat.pair m j + 4

theorem toF_injective : Function.Injective toF := fun a b h => by
  simp only [toF] at h; omega

theorem toCall_injective : Function.Injective toCall := fun a b h => by
  simp only [toCall] at h; omega

theorem toCur_inj {m j m' j' : ℕ} (h : toCur m j = toCur m' j') : m = m' ∧ j = j' := by
  simp only [toCur] at h
  have : Nat.pair m j = Nat.pair m' j' := by omega
  exact Prod.mk.inj (Nat.pair_eq_pair.1 this |> fun h => by rw [h.1, h.2])

@[simp] theorem toF_mod (v : ℕ) : toF v % 4 = 2 := by simp only [toF]; omega
@[simp] theorem toCall_mod (c : ℕ) : toCall c % 4 = 3 := by simp only [toCall]; omega
@[simp] theorem toCur_mod (m j : ℕ) : toCur m j % 4 = 0 := by simp only [toCur]; omega
theorem toCur_ne_zero (m j : ℕ) : toCur m j ≠ 0 := by simp only [toCur]; omega

/-- A control fact: anything that is not a source fact. -/
def IsCtl (k : ℕ) : Prop := k % 4 ≠ 2

/-- The encoded world state `W` with the control fact `k`. -/
def st (W : Set ℕ) (k : ℕ) : Set ℕ := toF '' W ∪ {k}

theorem ctl_not_mem_image {k : ℕ} (hk : IsCtl k) (W : Set ℕ) : k ∉ toF '' W := by
  rintro ⟨v, -, hv⟩
  apply hk
  rw [← hv]
  exact toF_mod v

theorem mem_st_ctl {W : Set ℕ} {k k' : ℕ} (hk' : IsCtl k') : k' ∈ st W k ↔ k' = k := by
  constructor
  · rintro (h | h)
    · exact absurd h (ctl_not_mem_image hk' W)
    · exact h
  · rintro rfl; exact Or.inr rfl

theorem toF_mem_st {W : Set ℕ} {k v : ℕ} (hk : IsCtl k) : toF v ∈ st W k ↔ v ∈ W := by
  constructor
  · rintro (⟨w, hw, hwv⟩ | h)
    · rwa [← toF_injective hwv]
    · exact absurd (h ▸ toF_mod v) hk
  · intro h; exact Or.inl ⟨v, h, rfl⟩

theorem st_inj {W W' : Set ℕ} {k k' : ℕ} (hk : IsCtl k) (hk' : IsCtl k')
    (h : st W k = st W' k') : W = W' ∧ k = k' := by
  refine ⟨?_, ?_⟩
  · ext v
    rw [← toF_mem_st hk (W := W), ← toF_mem_st hk' (W := W'), h]
  · have : k ∈ st W' k' := h ▸ Or.inr rfl
    exact (mem_st_ctl hk).1 this

theorem isCtl_zero : IsCtl 0 := by simp [IsCtl]
theorem isCtl_toCall (c : ℕ) : IsCtl (toCall c) := by simp [IsCtl]
theorem isCtl_toCur (m j : ℕ) : IsCtl (toCur m j) := by simp [IsCtl]

/-! ### The rows -/

section Rows

variable (d : DomDesc)

/-- Start the body of method `m`. -/
def begRow (m : ℕ) : Row := ([toCall (d.hd m)], [toCur m 0], [toCall (d.hd m)])

/-- Finish the body of method `m`. -/
def finRow (m : ℕ) : Row :=
  ([toCur m (d.bd m).length], [0], [toCur m (d.bd m).length])

/-- Execute the action `a` at position `j` of the body of method `m`. -/
def execRow (m j a : ℕ) : Row :=
  (toCur m j :: (actOf d a).1.map toF, toCur m (j + 1) :: (actOf d a).2.1.map toF,
    toCur m j :: (actOf d a).2.2.map toF)

/-- Call the compound task `c` at position `j` of the body of method `m`. -/
def pushRow (m j c : ℕ) : Row := ([toCur m j], [toCall c], [toCur m j])

/-- Return from the call at position `j` of the body of method `m`. -/
def retRow (m j : ℕ) : Row := ([0], [toCur m (j + 1)], [0])

/-- The plain rows at position `j` of the body of method `m`. -/
def execRows (m j : ℕ) : List Row :=
  match (d.bd m).getD j (Sum.inl 0) with
  | Sum.inl a => [execRow d m j a]
  | Sum.inr _ => []

/-- The call pairs at position `j` of the body of method `m`. -/
def callRows (m j : ℕ) : List (Row × Row) :=
  match (d.bd m).getD j (Sum.inl 0) with
  | Sum.inl _ => []
  | Sum.inr c => [(pushRow m j c, retRow m j)]

/-- **The plain rows** of a totally ordered domain description. -/
def toPlain : List Row :=
  (List.range d.methods.length).flatMap fun m =>
    begRow d m :: finRow d m :: (List.range (d.bd m).length).flatMap (execRows d m)

/-- **The call pairs** of a totally ordered domain description. -/
def toCalls : List (Row × Row) :=
  (List.range d.methods.length).flatMap fun m =>
    (List.range (d.bd m).length).flatMap (callRows d m)

theorem mem_toPlain {r : Row} :
    r ∈ toPlain d ↔ ∃ m < d.methods.length, r = begRow d m ∨ r = finRow d m ∨
      ∃ j < (d.bd m).length, ∃ a, (d.bd m)[j]? = some (Sum.inl a) ∧ r = execRow d m j a := by
  simp only [toPlain, List.mem_flatMap, List.mem_range, List.mem_cons]
  refine exists_congr fun m => and_congr_right fun _ => or_congr Iff.rfl (or_congr Iff.rfl ?_)
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [execRows, List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
  rcases (d.bd m)[j] with a | c
  · simp
  · simp

theorem mem_toCalls {p r : Row} :
    (p, r) ∈ toCalls d ↔ ∃ m < d.methods.length, ∃ j < (d.bd m).length, ∃ c,
      (d.bd m)[j]? = some (Sum.inr c) ∧ p = pushRow m j c ∧ r = retRow m j := by
  simp only [toCalls, List.mem_flatMap, List.mem_range]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [callRows, List.getD_eq_getElem _ _ hj, List.getElem?_eq_getElem hj]
  rcases (d.bd m)[j] with a | c
  · simp
  · simp [Prod.ext_iff]

end Rows

/-! ### Applying the rows to encoded states -/

theorem ctl_of_rowOk {W : Set ℕ} {k k' : ℕ} (hk' : IsCtl k') {r : Row} (hr : k' ∈ r.1)
    (h : RowOk r (st W k)) : k' = k :=
  (mem_st_ctl hk').1 (h k' hr)

/-- A row that replaces the control fact `k` by `k'` and leaves the world alone. -/
theorem rowApp_ctl {W : Set ℕ} {k k' : ℕ} (hk : IsCtl k) :
    rowApp ([k], [k'], [k]) (st W k) = st W k' := by
  ext f
  simp only [mem_rowApp, st, List.mem_singleton, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨h1 | h1, h2⟩)
    · exact Or.inr h
    · exact Or.inl h1
    · exact absurd h1 h2
  · rintro (h | h)
    · refine Or.inr ⟨Or.inl h, ?_⟩
      rintro rfl
      exact ctl_not_mem_image hk W h
    · exact Or.inl h

theorem rowApp_execRow (d : DomDesc) {W : Set ℕ} {m j a : ℕ} :
    rowApp (execRow d m j a) (st W (toCur m j)) =
      st (d.toDomain.transition a W) (toCur m (j + 1)) := by
  ext f
  simp only [mem_rowApp, execRow, st, List.mem_cons, List.mem_map, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_image]
  have hne : toCur m (j + 1) ≠ toCur m j := fun h => by
    have := (toCur_inj h).2; omega
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · rcases h with h | ⟨v, hv, rfl⟩
      · exact Or.inr h
      · refine Or.inl ⟨v, ?_, rfl⟩
        simp only [ActionModel.transition, DomDesc.toDomain_add, add_eq_actOf]
        exact Or.inr hv
    · push_neg at h2
      rcases h1 with ⟨v, hv, rfl⟩ | h1
      · refine Or.inl ⟨v, ?_, rfl⟩
        simp only [ActionModel.transition, DomDesc.toDomain_del, del_eq_actOf]
        exact Or.inl ⟨hv, fun hd => h2.2 v hd rfl⟩
      · exact absurd h1 h2.1
  · rintro (⟨v, hv, rfl⟩ | h)
    · simp only [ActionModel.transition, DomDesc.toDomain_del, del_eq_actOf,
        DomDesc.toDomain_add, add_eq_actOf] at hv
      rcases hv with ⟨hv, hnd⟩ | hv
      · refine Or.inr ⟨Or.inl ⟨v, hv, rfl⟩, ?_⟩
        rintro (h | ⟨w, hw, hwv⟩)
        · exact absurd (h ▸ toF_mod v) (by simp)
        · exact hnd (toF_injective hwv ▸ hw)
      · exact Or.inl (Or.inr ⟨v, hv, rfl⟩)
    · exact Or.inl (Or.inl h)

theorem rowApp_retRow {W : Set ℕ} {m j : ℕ} :
    rowApp (retRow m j) (st W 0) = st W (toCur m (j + 1)) := rowApp_ctl isCtl_zero

theorem rowApp_pushRow {W : Set ℕ} {m j c : ℕ} :
    rowApp (pushRow m j c) (st W (toCur m j)) = st W (toCall c) := rowApp_ctl (isCtl_toCur m j)

theorem rowApp_begRow (d : DomDesc) {W : Set ℕ} {m : ℕ} :
    rowApp (begRow d m) (st W (toCall (d.hd m))) = st W (toCur m 0) :=
  rowApp_ctl (isCtl_toCall _)

theorem rowApp_finRow (d : DomDesc) {W : Set ℕ} {m : ℕ} :
    rowApp (finRow d m) (st W (toCur m (d.bd m).length)) = st W 0 :=
  rowApp_ctl (isCtl_toCur _ _)

/-! ### What a control fact still has to do -/

/-- The task sequence a control fact still has to refine. -/
def rest (d : DomDesc) (k : ℕ) : List (ℕ ⊕ ℕ) :=
  if k = 0 then []
  else if k % 4 = 3 then [Sum.inr (k / 4)]
  else if k % 4 = 0 then (d.bd (Nat.unpair (k / 4 - 1)).1).drop (Nat.unpair (k / 4 - 1)).2
  else []

@[simp] theorem rest_zero (d : DomDesc) : rest d 0 = [] := by simp [rest]

@[simp] theorem rest_toCall (d : DomDesc) (c : ℕ) : rest d (toCall c) = [Sum.inr c] := by
  have h1 : toCall c ≠ 0 := by simp [toCall]
  rw [rest, if_neg h1, if_pos (toCall_mod c)]
  congr 2
  simp only [toCall]; omega

@[simp] theorem rest_toCur (d : DomDesc) (m j : ℕ) : rest d (toCur m j) = (d.bd m).drop j := by
  have h1 : toCur m j ≠ 0 := toCur_ne_zero m j
  have h2 : ¬ toCur m j % 4 = 3 := by simp
  rw [rest, if_neg h1, if_neg h2, if_pos (toCur_mod m j)]
  have : toCur m j / 4 - 1 = Nat.pair m j := by simp only [toCur]; omega
  rw [this, Nat.unpair_pair]

/-! ### Soundness -/

section Correct

variable {d : DomDesc}

/-- `Sem d k W k' W'`: reaching the control fact `k'` with the world `W'` from `k` with `W` is
consistent with the refinement semantics — whatever `k'` still has to do from `W'`, `k` could
have done from `W`. -/
def Sem (d : DomDesc) (k : ℕ) (W : Set ℕ) (k' : ℕ) (W' : Set ℕ) : Prop :=
  ∀ W'', d.toDomain.SeqReach (rest d k') W' W'' → d.toDomain.SeqReach (rest d k) W W''

theorem drop_eq_cons_of_getElem? {l : List (ℕ ⊕ ℕ)} {j : ℕ} {x : ℕ ⊕ ℕ} (h : l[j]? = some x) :
    l.drop j = x :: l.drop (j + 1) := by
  obtain ⟨hj, hx⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.drop_eq_getElem_cons hj, hx]

theorem cReach_sound (hTO : d.MethodsTO) {s s' : Set ℕ} (h : CReach (toPlain d) (toCalls d) s s') :
    ∀ W k, IsCtl k → s = st W k →
      ∃ W' k', IsCtl k' ∧ s' = st W' k' ∧ Sem d k W k' W' := by
  induction h with
  | refl s =>
    intro W k hk hs
    exact ⟨W, k, hk, hs, fun _ h => h⟩
  | @plain r s s' hr hok _ ih =>
    intro W k hk hs
    subst hs
    obtain ⟨m, hm, hcase⟩ := (mem_toPlain d).1 hr
    rcases hcase with rfl | rfl | ⟨j, hj, a, hja, rfl⟩
    · have hk' : toCall (d.hd m) = k :=
        ctl_of_rowOk (isCtl_toCall _) (List.mem_singleton_self _) hok
      subst hk'
      obtain ⟨W', k', hk', rfl, hsem⟩ := ih W (toCur m 0) (isCtl_toCur m 0)
        (rowApp_begRow d)
      refine ⟨W', k', hk', rfl, fun W'' h => ?_⟩
      have hb := hsem W'' h
      rw [rest_toCur, List.drop_zero] at hb
      rw [rest_toCall]
      exact Domain.SeqReach.comp ((DomDesc.seqBody_iff hTO).2 ⟨m, hm, rfl, rfl⟩) hb
        Domain.SeqReach.nil
    · have hk' : toCur m (d.bd m).length = k :=
        ctl_of_rowOk (isCtl_toCur _ _) (List.mem_singleton_self _) hok
      subst hk'
      obtain ⟨W', k', hk', rfl, hsem⟩ := ih W 0 isCtl_zero (rowApp_finRow d)
      refine ⟨W', k', hk', rfl, fun W'' h => ?_⟩
      have := hsem W'' h
      rw [rest_zero] at this
      rw [rest_toCur, List.drop_length]
      exact this
    · have hk' : toCur m j = k :=
        ctl_of_rowOk (isCtl_toCur _ _) (List.mem_cons_self) hok
      subst hk'
      have happ : d.toDomain.toActionModel.Applicable a W := by
        intro f hf
        simp only [DomDesc.toDomain_prec, prec_eq_actOf, Set.mem_setOf_eq] at hf
        have := hok (toF f) (List.mem_cons_of_mem _ (List.mem_map_of_mem hf))
        exact (toF_mem_st (isCtl_toCur m j)).1 this
      obtain ⟨W', k', hk', rfl, hsem⟩ := ih _ (toCur m (j + 1)) (isCtl_toCur _ _)
        (rowApp_execRow d)
      refine ⟨W', k', hk', rfl, fun W'' h => ?_⟩
      have := hsem W'' h
      rw [rest_toCur] at this ⊢
      rw [drop_eq_cons_of_getElem? hja]
      exact Domain.SeqReach.prim happ this
  | @call p r s t s' hpr hok1 _ hok2 _ ih1 ih2 =>
    intro W k hk hs
    subst hs
    obtain ⟨m, hm, j, hj, c, hjc, rfl, rfl⟩ := (mem_toCalls d).1 hpr
    have hk' : toCur m j = k :=
      ctl_of_rowOk (isCtl_toCur _ _) (List.mem_singleton_self _) hok1
    subst hk'
    obtain ⟨W₁, k₁, hk₁, rfl, hsem1⟩ := ih1 W (toCall c) (isCtl_toCall c) rowApp_pushRow
    have hk₁0 : 0 = k₁ := ctl_of_rowOk isCtl_zero (List.mem_singleton_self _) hok2
    subst hk₁0
    obtain ⟨W', k', hk', rfl, hsem2⟩ := ih2 W₁ (toCur m (j + 1)) (isCtl_toCur _ _)
      rowApp_retRow
    refine ⟨W', k', hk', rfl, fun W'' h => ?_⟩
    have h2 := hsem2 W'' h
    have h1 := hsem1 W₁ (by rw [rest_zero]; exact Domain.SeqReach.nil)
    rw [rest_toCall] at h1
    rw [rest_toCur] at h2 ⊢
    rw [drop_eq_cons_of_getElem? hjc, show Sum.inr c :: (d.bd m).drop (j + 1)
      = [Sum.inr c] ++ (d.bd m).drop (j + 1) from rfl]
    exact h1.append h2

/-! ### Completeness -/

theorem cReach_complete (hTO : d.MethodsTO) {xs : List (ℕ ⊕ ℕ)} {W W' : Set ℕ}
    (h : d.toDomain.SeqReach xs W W') :
    ∀ m j, m < d.methods.length → j ≤ (d.bd m).length → xs = (d.bd m).drop j →
      CReach (toPlain d) (toCalls d) (st W (toCur m j)) (st W' 0) := by
  induction h with
  | @nil s =>
    intro m j hm hj hxs
    have hjl : j = (d.bd m).length := by
      have := congrArg List.length hxs
      simp only [List.length_nil, List.length_drop] at this
      omega
    subst hjl
    refine CReach.plain ((mem_toPlain d).2 ⟨m, hm, Or.inr (Or.inl rfl)⟩) ?_ ?_
    · intro f hf
      simp only [finRow, List.mem_singleton] at hf
      subst hf
      exact Or.inr rfl
    · rw [rowApp_finRow d]
      exact CReach.refl _
  | @prim a xs s u happ _ ih =>
    intro m j hm hj hxs
    have hjl : j < (d.bd m).length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega)] at hxs
      simp at hxs
    have hja : (d.bd m)[j]? = some (Sum.inl a) := by
      rw [List.drop_eq_getElem_cons hjl] at hxs
      rw [List.getElem?_eq_getElem hjl, (List.cons.inj hxs).1]
    have hxs' : xs = (d.bd m).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl] at hxs
      exact (List.cons.inj hxs).2
    refine CReach.plain ((mem_toPlain d).2 ⟨m, hm, Or.inr (Or.inr ⟨j, hjl, a, hja, rfl⟩)⟩)
      ?_ ?_
    · intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact Or.inr rfl
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
        refine (toF_mem_st (isCtl_toCur m j)).2 (happ ?_)
        simp only [DomDesc.toDomain_prec, prec_eq_actOf, Set.mem_setOf_eq]
        exact hv
    · rw [rowApp_execRow d]
      exact ih m (j + 1) hm (by omega) hxs'
  | @comp c bs xs s t u hbody _ _ ih1 ih2 =>
    intro m j hm hj hxs
    have hjl : j < (d.bd m).length := by
      by_contra hcon
      rw [List.drop_eq_nil_of_le (by omega)] at hxs
      simp at hxs
    have hjc : (d.bd m)[j]? = some (Sum.inr c) := by
      rw [List.drop_eq_getElem_cons hjl] at hxs
      rw [List.getElem?_eq_getElem hjl, (List.cons.inj hxs).1]
    have hxs' : xs = (d.bd m).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl] at hxs
      exact (List.cons.inj hxs).2
    obtain ⟨m', hm', hc, hbs⟩ := (DomDesc.seqBody_iff hTO).1 hbody
    have hcallee : CReach (toPlain d) (toCalls d) (st s (toCall c)) (st t 0) := by
      subst hc
      refine CReach.plain ((mem_toPlain d).2 ⟨m', hm', Or.inl rfl⟩) ?_ ?_
      · intro f hf
        simp only [begRow, List.mem_singleton] at hf
        subst hf
        exact Or.inr rfl
      · rw [rowApp_begRow d]
        exact ih1 m' 0 hm' (Nat.zero_le _) (by rw [List.drop_zero, hbs])
    refine CReach.call (t := st t 0) ((mem_toCalls d).2 ⟨m, hm, j, hjl, c, hjc, rfl, rfl⟩) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [pushRow, List.mem_singleton] at hf
      subst hf
      exact Or.inr rfl
    · rw [rowApp_pushRow]; exact hcallee
    · intro f hf
      simp only [retRow, List.mem_singleton] at hf
      subst hf
      exact Or.inr rfl
    · rw [rowApp_retRow]
      exact ih2 m (j + 1) hm (by omega) hxs'

/-! ### Plan existence -/

variable {q : InstDesc}

theorem isSeqNet_rooted (hq : q.IsRooted) :
    ∃ t, (problem d q).tnI.IsSeqNet [t] [Sum.inr (rootName q)] := by
  obtain ⟨t, hT, hα⟩ := InstDesc.rootName_spec hq
  refine ⟨t, ⟨List.nodup_singleton t, fun x => ?_, ?_, fun x y => ?_⟩⟩
  · show x ∈ q.tnI.toTaskNetwork.T ↔ x ∈ [t]
    rw [hT]; simp
  · show [t].map q.tnI.toTaskNetwork.α = _
    rw [List.map_singleton, hα]
  · show q.tnI.toTaskNetwork.ord x y ↔ _
    constructor
    · intro hxy
      have hwf := q.tnI.toTaskNetwork_wf
      have hx : x ∈ q.tnI.toTaskNetwork.T := hwf.mem_left hxy
      have hy : y ∈ q.tnI.toTaskNetwork.T := hwf.mem_right hxy
      rw [hT, Finset.mem_singleton] at hx hy
      subst hx; subst hy
      exact absurd hxy (hwf.irrefl _)
    · rintro ⟨hx, hy, hlt⟩
      simp at hx hy
      subst hx; subst hy
      simp at hlt

/-- **Plan existence for a rooted totally ordered problem is reachability along the root task.** -/
theorem solvable_iff_seqReach_root (hTO : d.MethodsTO) (hq : q.IsRooted) :
    Solvable d q ↔ ∃ W', d.toDomain.SeqReach [Sum.inr (rootName q)] {f | f ∈ q.initList} W' ∧
      {f | f ∈ q.goalList} ⊆ W' := by
  obtain ⟨t, ht⟩ := isSeqNet_rooted (d := d) hq
  exact Problem.solvable_iff_seqReach (problem_wf d q) (isTO_problem hTO hq.isTO).2 ht

theorem regInitR_eq_st (q : InstDesc) :
    {f | f ∈ regInitR q} = st {f | f ∈ q.initList} (toCall (rootName q)) := by
  ext f
  simp only [regInitR, st, toF, toCall, Set.mem_setOf_eq, List.mem_append, List.mem_map,
    List.mem_singleton, Set.mem_union, Set.mem_image, Set.mem_singleton_iff]

theorem regGoalR_subset_iff {W : Set ℕ} {k : ℕ} (hk : IsCtl k) :
    {f | f ∈ regGoalR q} ⊆ st W k ↔ {f | f ∈ q.goalList} ⊆ W ∧ k = 0 := by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, ?_⟩
    · have : toF v ∈ st W k := h (show toF v ∈ {f | f ∈ regGoalR q} by
        simp only [Set.mem_setOf_eq, regGoalR, List.mem_append, List.mem_map, toF]
        exact Or.inl ⟨v, hv, rfl⟩)
      exact (toF_mem_st hk).1 this
    · have : (0 : ℕ) ∈ st W k := h (by simp [regGoalR])
      exact ((mem_st_ctl isCtl_zero).1 this).symm
  · rintro ⟨hg, rfl⟩ f hf
    simp only [regGoalR, List.mem_append, List.mem_map, List.mem_singleton,
      Set.mem_setOf_eq] at hf
    rcases hf with ⟨v, hv, rfl⟩ | rfl
    · exact (toF_mem_st isCtl_zero).2 (hg hv)
    · exact Or.inr rfl

/-- **Plan existence for a totally ordered HTN description with a rooted instance is
reachability with calls** in the table of `d`, from and to the lists of the regular case. -/
theorem solvable_to_iff_cReach (hTO : d.MethodsTO) (hq : q.IsRooted) :
    Solvable d q ↔ ∃ s', CReach (toPlain d) (toCalls d) {f | f ∈ regInitR q} s' ∧
      {f | f ∈ regGoalR q} ⊆ s' := by
  rw [solvable_iff_seqReach_root hTO hq, regInitR_eq_st]
  constructor
  · rintro ⟨W', hreach, hgoal⟩
    refine ⟨st W' 0, ?_, (regGoalR_subset_iff isCtl_zero).2 ⟨hgoal, rfl⟩⟩
    cases hreach with
    | comp hbody hb hrest =>
      cases hrest
      obtain ⟨m', hm', hc, hbs⟩ := (DomDesc.seqBody_iff hTO).1 hbody
      rw [← hc]
      refine CReach.plain ((mem_toPlain d).2 ⟨m', hm', Or.inl rfl⟩) ?_ ?_
      · intro f hf
        simp only [begRow, List.mem_singleton] at hf
        subst hf
        exact Or.inr rfl
      · rw [rowApp_begRow d]
        exact cReach_complete hTO hb m' 0 hm' (Nat.zero_le _) (by rw [List.drop_zero, hbs])
  · rintro ⟨s', hreach, hgoal⟩
    obtain ⟨W', k', hk', rfl, hsem⟩ := cReach_sound hTO hreach _ _ (isCtl_toCall _) rfl
    obtain ⟨hg, rfl⟩ := (regGoalR_subset_iff hk').1 hgoal
    refine ⟨W', ?_, hg⟩
    have := hsem W' (by rw [rest_zero]; exact Domain.SeqReach.nil)
    rwa [rest_toCall] at this

end Correct

end Space

end HTN
