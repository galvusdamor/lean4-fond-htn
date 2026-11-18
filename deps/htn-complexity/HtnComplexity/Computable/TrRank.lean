import HtnComplexity.Computable.RegInv
/-!
# A computable rank for a tail-recursive domain description

`HTN.Syn.DomDesc.IsTailRec` only *asserts* that some rank function `rk : ℕ → ℕ` witnesses tail
recursion: a compound *last* subtask of a listed method may keep the rank of the task the
method decomposes, every other compound subtask must decrease it.  A decision procedure needs
a rank it can compute, and this file supplies one, in the way
`HtnComplexity/Computable/PoRank.lean` supplies `HTN.Syn.rkD` for an acyclic description:

* `HTN.Syn.isLastIdB` — a `Bool` deciding `TaskNetwork.IsLastId` for a described network;
* `HTN.Syn.strictEdges d` — the edges `(c, c')` of the dependency graph
  (`HTN.Syn.compEdges`) that come from a subtask which is *not* last;
* `HTN.Syn.WReach d a b` — reachability in the full dependency graph, reflexively;
* `HTN.Syn.rkT d c` — the number of names `z` such that some path from `c` to `z` uses a strict
  edge.  It strictly decreases along a strict edge and never increases along any edge, so
  `HTN.Syn.tailRecBy_rkT`: a tail-recursive description is tail-recursive *by* `rkT`.

The only mathematical content is that no such path can lead from a name back to itself: along a
path the rank asserted to exist never increases, and a strict edge makes it drop.
-/

namespace HTN

namespace Syn

/-! ### Deciding whether a subtask is last -/

/-- **A `Bool` deciding `TaskNetwork.IsLastId`** for a described task network. -/
def isLastIdB (t : TnDesc) (x : ℕ) : Bool :=
  memB t.ids x && t.ids.all fun y => (y == x) || TnDesc.ordB t y x

theorem isLastIdB_iff {t : TnDesc} {x : ℕ} :
    isLastIdB t x = true ↔ t.toTaskNetwork.IsLastId x := by
  simp only [isLastIdB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    memB_iff, TaskNetwork.IsLastId, TnDesc.toTaskNetwork_T, List.mem_toFinset]
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy hne => ?_⟩
    rcases hall y hy with h | h
    · exact absurd h hne
    · exact TnDesc.ordB_iff.1 h
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy => ?_⟩
    by_cases hne : y = x
    · exact Or.inl hne
    · exact Or.inr (TnDesc.ordB_iff.2 (hall y hy hne))

/-! ### The strict edges of the dependency graph -/

/-- The edges of the dependency graph that a **non-last** subtask contributes. -/
def strictEdges (d : DomDesc) : List (ℕ × ℕ) :=
  d.methods.flatMap fun e =>
    e.2.ids.dedup.filterMap fun x =>
      if isLastIdB e.2 x then none
      else
        match e.2.label x with
        | Sum.inr c' => some (e.1, c')
        | Sum.inl _ => none

theorem mem_strictEdges {d : DomDesc} {a b : ℕ} :
    (a, b) ∈ strictEdges d ↔
      ∃ e ∈ d.methods, e.1 = a ∧ ∃ x ∈ e.2.ids,
        ¬ e.2.toTaskNetwork.IsLastId x ∧ e.2.label x = Sum.inr b := by
  simp only [strictEdges, List.mem_flatMap, List.mem_filterMap, List.mem_dedup]
  constructor
  · rintro ⟨e, he, x, hx, hval⟩
    by_cases hlast : isLastIdB e.2 x = true
    · rw [if_pos hlast] at hval
      simp at hval
    · rw [if_neg hlast] at hval
      rcases hlab : e.2.label x with c' | c'
      · rw [hlab] at hval
        simp at hval
      · rw [hlab] at hval
        simp only [Option.some.injEq, Prod.ext_iff] at hval
        refine ⟨e, he, hval.1, x, hx, fun hc => hlast (isLastIdB_iff.2 hc), ?_⟩
        rw [hlab, hval.2]
  · rintro ⟨e, he, rfl, x, hx, hlast, hlab⟩
    have hlastB : ¬ isLastIdB e.2 x = true := fun hc => hlast (isLastIdB_iff.1 hc)
    exact ⟨e, he, x, hx, by rw [if_neg hlastB, hlab]⟩

theorem mem_compEdges_of_mem_strictEdges {d : DomDesc} {a b : ℕ} (h : (a, b) ∈ strictEdges d) :
    (a, b) ∈ compEdges d := by
  obtain ⟨e, he, hea, x, hx, -, hlab⟩ := mem_strictEdges.1 h
  exact mem_compEdges.2 ⟨e, he, hea, x, hx, hlab⟩

/-! ### Reachability in the dependency graph -/

/-- Reflexive reachability in the dependency graph. -/
def WReach (d : DomDesc) (a b : ℕ) : Prop :=
  a = b ∨ Relation.TransGen (listRelOf (compEdges d)) a b

/-- Reflexive reachability in the dependency graph, as a `Bool`. -/
def wReachB (d : DomDesc) (a b : ℕ) : Bool := (a == b) || reachB (compEdges d) a b

theorem wReachB_iff {d : DomDesc} {a b : ℕ} : wReachB d a b = true ↔ WReach d a b := by
  simp only [wReachB, WReach, Bool.or_eq_true, beq_iff_eq]
  exact or_congr Iff.rfl reachB_iff

theorem WReach.refl (d : DomDesc) (a : ℕ) : WReach d a a := Or.inl rfl

theorem WReach.head {d : DomDesc} {a b c : ℕ} (hab : (a, b) ∈ compEdges d) (hbc : WReach d b c) :
    WReach d a c := by
  rcases hbc with rfl | h
  · exact Or.inr (Relation.TransGen.single hab)
  · exact Or.inr (Relation.TransGen.head hab h)

/-- Along an edge of the dependency graph a tail-recursion rank does not increase. -/
theorem rk_le_of_mem_compEdges {d : DomDesc} {rk : ℕ → ℕ} (hrk : d.TailRecBy rk) {a b : ℕ}
    (h : (a, b) ∈ compEdges d) : rk b ≤ rk a := by
  classical
  obtain ⟨e, he, rfl, x, hx, hlab⟩ := mem_compEdges.1 h
  have hxT : x ∈ e.2.toTaskNetwork.T := by simpa using hx
  have := hrk e he x hxT b hlab
  by_cases hlast : e.2.toTaskNetwork.IsLastId x
  · exact this.1 hlast
  · exact le_of_lt (this.2 hlast)

/-- Along a *strict* edge a tail-recursion rank strictly decreases. -/
theorem rk_lt_of_mem_strictEdges {d : DomDesc} {rk : ℕ → ℕ} (hrk : d.TailRecBy rk) {a b : ℕ}
    (h : (a, b) ∈ strictEdges d) : rk b < rk a := by
  obtain ⟨e, he, rfl, x, hx, hlast, hlab⟩ := mem_strictEdges.1 h
  have hxT : x ∈ e.2.toTaskNetwork.T := by simpa using hx
  exact (hrk e he x hxT b hlab).2 hlast

theorem rk_le_of_wReach {d : DomDesc} {rk : ℕ → ℕ} (hrk : d.TailRecBy rk) {a b : ℕ}
    (h : WReach d a b) : rk b ≤ rk a := by
  rcases h with rfl | h
  · exact le_rfl
  · induction h with
    | single hst => exact rk_le_of_mem_compEdges hrk hst
    | tail _ hst ih => exact le_trans (rk_le_of_mem_compEdges hrk hst) ih

/-! ### The rank -/

/-- The names an edge of the dependency graph points at. -/
def compTargets (d : DomDesc) : List ℕ := (compEdges d).map Prod.snd

theorem mem_compTargets {d : DomDesc} {b : ℕ} :
    b ∈ compTargets d ↔ ∃ a, (a, b) ∈ compEdges d := by
  simp only [compTargets, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, by simpa using hp⟩
  · rintro ⟨a, ha⟩
    exact ⟨(a, b), ha, rfl⟩

/-- `z` lies strictly below `a` iff some path from `a` to `z` uses a strict edge. -/
def sBelowB (d : DomDesc) (a z : ℕ) : Bool :=
  (strictEdges d).any fun p => wReachB d a p.1 && wReachB d p.2 z

theorem sBelowB_iff {d : DomDesc} {a z : ℕ} :
    sBelowB d a z = true ↔ ∃ p ∈ strictEdges d, WReach d a p.1 ∧ WReach d p.2 z := by
  simp only [sBelowB, List.any_eq_true, Bool.and_eq_true, wReachB_iff]

/-- A tail-recursion rank strictly decreases from `a` to anything strictly below it. -/
theorem rk_lt_of_sBelowB {d : DomDesc} {rk : ℕ → ℕ} (hrk : d.TailRecBy rk) {a z : ℕ}
    (h : sBelowB d a z = true) : rk z < rk a := by
  obtain ⟨p, hp, h1, h2⟩ := sBelowB_iff.1 h
  have hp1 : rk p.1 ≤ rk a := rk_le_of_wReach hrk h1
  have hp2 : rk p.2 < rk p.1 := rk_lt_of_mem_strictEdges hrk (by simpa using hp)
  have hz : rk z ≤ rk p.2 := rk_le_of_wReach hrk h2
  omega

/-- Nothing lies strictly below itself. -/
theorem sBelowB_self {d : DomDesc} (hd : d.IsTailRec) (a : ℕ) : sBelowB d a a = false := by
  obtain ⟨rk, hrk⟩ := hd
  rcases h : sBelowB d a a with _ | _
  · rfl
  · exact absurd (rk_lt_of_sBelowB hrk h) (lt_irrefl _)

/-- **The computed rank of a compound name**: the number of names strictly below it. -/
def rkT (d : DomDesc) (c : ℕ) : ℕ :=
  ((compTargets d).dedup.filter fun z => sBelowB d c z).length

theorem sBelowB_of_mem_compEdges {d : DomDesc} {a b z : ℕ} (hab : (a, b) ∈ compEdges d)
    (h : sBelowB d b z = true) : sBelowB d a z = true := by
  obtain ⟨p, hp, h1, h2⟩ := sBelowB_iff.1 h
  exact sBelowB_iff.2 ⟨p, hp, WReach.head hab h1, h2⟩

/-- **The computed rank does not increase along an edge** of the dependency graph. -/
theorem rkT_le_of_mem_compEdges {d : DomDesc} {a b : ℕ} (h : (a, b) ∈ compEdges d) :
    rkT d b ≤ rkT d a := by
  exact length_filter_le_of_imp fun z _ hz => sBelowB_of_mem_compEdges h hz

/-- **The computed rank strictly decreases along a strict edge.** -/
theorem rkT_lt_of_mem_strictEdges {d : DomDesc} (hd : d.IsTailRec) {a b : ℕ}
    (h : (a, b) ∈ strictEdges d) : rkT d b < rkT d a := by
  have hab : (a, b) ∈ compEdges d := mem_compEdges_of_mem_strictEdges h
  refine length_filter_lt (x := b) ?_ ?_ ?_ (sBelowB_self hd b)
  · exact fun z _ hz => sBelowB_of_mem_compEdges hab hz
  · exact List.mem_dedup.2 (mem_compTargets.2 ⟨a, hab⟩)
  · exact sBelowB_iff.2 ⟨(a, b), h, WReach.refl d a, WReach.refl d b⟩

/-- **A tail-recursive description is tail-recursive by the computed rank.** -/
theorem tailRecBy_rkT {d : DomDesc} (hd : d.IsTailRec) : d.TailRecBy (rkT d) := by
  intro e he t ht c hc
  have htids : t ∈ e.2.ids := by simpa using ht
  refine ⟨fun _ => ?_, fun hlast => ?_⟩
  · exact rkT_le_of_mem_compEdges (mem_compEdges.2 ⟨e, he, rfl, t, htids, hc⟩)
  · exact rkT_lt_of_mem_strictEdges hd (mem_strictEdges.2 ⟨e, he, rfl, t, htids, hlast, hc⟩)

end Syn

end HTN
