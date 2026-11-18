import HtnComplexity.Space.StripsSystem
/-!
# Renaming the facts of an action table

Solvability of an action table (`HtnComplexity/Space/StripsSystem.lean`) only depends on the
facts through their *identity*, so it survives any renaming that is injective on the facts that
actually occur:

    HTN.Space.solvableTbl_map :
      SolvableTbl (tbl.map (mapRow ρ)) (s₀.map ρ) (g.map ρ) ↔ SolvableTbl tbl s₀ g

on the hypothesis that `ρ` is injective on `HTN.Space.relFacts tbl s₀ g`, the facts of the table,
of the initial state and of the goal.

The point of the lemma is arithmetical.  The compiled `STRIPS` problem of a regular HTN
description (`HtnComplexity/Space/RegTable.lean`) carries the facts of the instance as
`12 v` and its initial compound task as `8 c + 1`; a machine reading the *code* of the instance
would have to multiply a binary numeral by `3`, which is a carry-propagating computation.  After
the renaming

    ρ (12 v) = 4 v + 2,   ρ (8 c + 1) = 4 c + 3,   ρ 2 = 0,   ρ 3 = 1

— which `HTN.Space.regRho` realises by an injection of `ℕ` into itself — the instance side is
`v ↦ 4 v + 2` and `c ↦ 4 c + 3`, that is, two constant bits prefixed to the numeral, which is a
string surgery a machine can do.  The residues `2` and `3` modulo `4` are chosen rather than `0`
and `1` because the numeral of `0` is *empty*: `v ↦ 4 v` is a bit prefixing at every `v` except
`v = 0`, while `v ↦ 4 v + 2` is one everywhere.

The proof of the lemma is a transport of runs in both directions, through the two canonical
translations of a state: `HTN.Space.pushSt` keeps the relevant facts of a state and renames them,
`HTN.Space.pullSt` collects the relevant facts whose renaming the state carries.
-/

namespace HTN

namespace Space

/-- A row with its facts renamed. -/
def mapRow (ρ : ℕ → ℕ) (r : Row) : Row := (r.1.map ρ, r.2.1.map ρ, r.2.2.map ρ)

/-- The facts occurring in an action table. -/
def tblFacts (tbl : List Row) : List ℕ := tbl.flatMap fun r => r.1 ++ r.2.1 ++ r.2.2

/-- The facts a table, an initial state and a goal mention. -/
def relFacts (tbl : List Row) (s₀ g : List ℕ) : List ℕ := tblFacts tbl ++ s₀ ++ g

theorem mem_tblFacts_of_prec {tbl : List Row} {r : Row} (hr : r ∈ tbl) {f : ℕ} (hf : f ∈ r.1) :
    f ∈ tblFacts tbl :=
  List.mem_flatMap.2 ⟨r, hr, by simp [hf]⟩

theorem mem_tblFacts_of_add {tbl : List Row} {r : Row} (hr : r ∈ tbl) {f : ℕ} (hf : f ∈ r.2.1) :
    f ∈ tblFacts tbl :=
  List.mem_flatMap.2 ⟨r, hr, by simp [hf]⟩

theorem mem_tblFacts_of_del {tbl : List Row} {r : Row} (hr : r ∈ tbl) {f : ℕ} (hf : f ∈ r.2.2) :
    f ∈ tblFacts tbl :=
  List.mem_flatMap.2 ⟨r, hr, by simp [hf]⟩

/-- The relevant facts of a state, renamed. -/
def pushSt (ρ : ℕ → ℕ) (R u : List ℕ) : List ℕ := (R.filter fun a => decide (a ∈ u)).map ρ

/-- The relevant facts whose renaming a state carries. -/
def pullSt (ρ : ℕ → ℕ) (R v : List ℕ) : List ℕ := R.filter fun a => decide (ρ a ∈ v)

@[simp] theorem mem_pushSt {ρ : ℕ → ℕ} {R u : List ℕ} {y : ℕ} :
    y ∈ pushSt ρ R u ↔ ∃ a, (a ∈ R ∧ a ∈ u) ∧ ρ a = y := by
  simp [pushSt, List.mem_filter, and_assoc]

@[simp] theorem mem_pullSt {ρ : ℕ → ℕ} {R v : List ℕ} {a : ℕ} :
    a ∈ pullSt ρ R v ↔ a ∈ R ∧ ρ a ∈ v := by
  simp [pullSt, List.mem_filter]

variable {ρ : ℕ → ℕ} {tbl : List Row} {s₀ g : List ℕ}

/-- The renaming is injective where it matters. -/
def InjOnRel (ρ : ℕ → ℕ) (tbl : List Row) (s₀ g : List ℕ) : Prop :=
  ∀ a ∈ relFacts tbl s₀ g, ∀ b ∈ relFacts tbl s₀ g, ρ a = ρ b → a = b

/-! ### Transporting a run forwards -/

theorem reachTbl_pushSt (hinj : InjOnRel ρ tbl s₀ g) {u v : List ℕ} (h : ReachTbl tbl u v) :
    ReachTbl (tbl.map (mapRow ρ)) (pushSt ρ (relFacts tbl s₀ g) u)
      (pushSt ρ (relFacts tbl s₀ g) v) := by
  set R := relFacts tbl s₀ g with hR
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w v _ hstep ih =>
    obtain ⟨row, hrow, hprec, hpost⟩ := hstep
    refine ih.tail ⟨mapRow ρ row, List.mem_map_of_mem hrow, ?_, ?_⟩
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      exact mem_pushSt.2 ⟨a, ⟨List.mem_append_left _
        (List.mem_append_left _ (mem_tblFacts_of_prec hrow ha)), hprec a ha⟩, rfl⟩
    · intro y
      constructor
      · intro hy
        obtain ⟨a, ⟨haR, hav⟩, rfl⟩ := mem_pushSt.1 hy
        rcases (hpost a).1 hav with hadd | ⟨hw, hdel⟩
        · exact Or.inl (List.mem_map_of_mem hadd)
        · refine Or.inr ⟨mem_pushSt.2 ⟨a, ⟨haR, hw⟩, rfl⟩, fun hc => ?_⟩
          obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hc
          have hbR : b ∈ R := List.mem_append_left _
            (List.mem_append_left _ (mem_tblFacts_of_del hrow hb))
          exact hdel (hinj b hbR a haR hbe ▸ hb)
      · rintro (hy | ⟨hy, hdel⟩)
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
          exact mem_pushSt.2 ⟨a, ⟨List.mem_append_left _
            (List.mem_append_left _ (mem_tblFacts_of_add hrow ha)),
            (hpost a).2 (Or.inl ha)⟩, rfl⟩
        · obtain ⟨a, ⟨haR, haw⟩, rfl⟩ := mem_pushSt.1 hy
          refine mem_pushSt.2 ⟨a, ⟨haR, (hpost a).2 (Or.inr ⟨haw, fun hc => ?_⟩)⟩, rfl⟩
          exact hdel (List.mem_map_of_mem hc)

/-! ### Transporting a run backwards -/

theorem reachTbl_pullSt (hinj : InjOnRel ρ tbl s₀ g) {u v : List ℕ}
    (h : ReachTbl (tbl.map (mapRow ρ)) u v) :
    ReachTbl tbl (pullSt ρ (relFacts tbl s₀ g) u) (pullSt ρ (relFacts tbl s₀ g) v) := by
  set R := relFacts tbl s₀ g with hR
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w v _ hstep ih =>
    obtain ⟨row', hrow', hprec, hpost⟩ := hstep
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hrow'
    refine ih.tail ⟨row, hrow, ?_, ?_⟩
    · intro a ha
      refine mem_pullSt.2 ⟨List.mem_append_left _
        (List.mem_append_left _ (mem_tblFacts_of_prec hrow ha)), ?_⟩
      exact hprec (ρ a) (List.mem_map_of_mem ha)
    · intro a
      constructor
      · intro ha
        obtain ⟨haR, hav⟩ := mem_pullSt.1 ha
        rcases (hpost (ρ a)).1 hav with hadd | ⟨hw, hdel⟩
        · obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hadd
          have hbR : b ∈ R := List.mem_append_left _
            (List.mem_append_left _ (mem_tblFacts_of_add hrow hb))
          exact Or.inl (hinj b hbR a haR hbe ▸ hb)
        · exact Or.inr ⟨mem_pullSt.2 ⟨haR, hw⟩, fun hc => hdel (List.mem_map_of_mem hc)⟩
      · rintro (ha | ⟨ha, hdel⟩)
        · refine mem_pullSt.2 ⟨List.mem_append_left _
            (List.mem_append_left _ (mem_tblFacts_of_add hrow ha)), ?_⟩
          exact (hpost (ρ a)).2 (Or.inl (List.mem_map_of_mem ha))
        · obtain ⟨haR, haw⟩ := mem_pullSt.1 ha
          refine mem_pullSt.2 ⟨haR, (hpost (ρ a)).2 (Or.inr ⟨haw, fun hc => ?_⟩)⟩
          obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hc
          have hbR : b ∈ R := List.mem_append_left _
            (List.mem_append_left _ (mem_tblFacts_of_del hrow hb))
          exact hdel (hinj b hbR a haR hbe ▸ hb)

/-! ### Solvability is invariant -/

theorem mem_relFacts_of_mem_init {f : ℕ} (hf : f ∈ s₀) : f ∈ relFacts tbl s₀ g :=
  List.mem_append_left _ (List.mem_append_right _ hf)

theorem mem_relFacts_of_mem_goal {f : ℕ} (hf : f ∈ g) : f ∈ relFacts tbl s₀ g :=
  List.mem_append_right _ hf

/-- **Solvability of an action table is invariant under a renaming of the facts that is injective
where it matters.** -/
theorem solvableTbl_map (hinj : InjOnRel ρ tbl s₀ g) :
    SolvableTbl (tbl.map (mapRow ρ)) (s₀.map ρ) (g.map ρ) ↔ SolvableTbl tbl s₀ g := by
  set R := relFacts tbl s₀ g with hR
  have hpull : ∀ f : ℕ, f ∈ s₀ ↔ f ∈ pullSt ρ R (s₀.map ρ) := by
    intro f
    rw [mem_pullSt]
    constructor
    · intro hf
      exact ⟨mem_relFacts_of_mem_init hf, List.mem_map_of_mem hf⟩
    · rintro ⟨hfR, hf⟩
      obtain ⟨b, hb, hbe⟩ := List.mem_map.1 hf
      exact hinj b (mem_relFacts_of_mem_init hb) f hfR hbe ▸ hb
  have hpush : ∀ y : ℕ, y ∈ s₀.map ρ ↔ y ∈ pushSt ρ R s₀ := by
    intro y
    rw [mem_pushSt]
    constructor
    · intro hy
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
      exact ⟨f, ⟨mem_relFacts_of_mem_init hf, hf⟩, rfl⟩
    · rintro ⟨a, ⟨-, ha⟩, rfl⟩
      exact List.mem_map_of_mem ha
  constructor
  · rintro ⟨v, hreach, hgoal⟩
    obtain ⟨t, hreach', hmem⟩ :=
      exists_run_of_congr (reachTbl_pullSt (g := g) (s₀ := s₀) hinj hreach) (u' := s₀) hpull
    refine ⟨t, hreach', fun f hf => (hmem f).2 (mem_pullSt.2 ⟨mem_relFacts_of_mem_goal hf, ?_⟩)⟩
    exact hgoal (ρ f) (List.mem_map_of_mem hf)
  · rintro ⟨v, hreach, hgoal⟩
    obtain ⟨t, hreach', hmem⟩ :=
      exists_run_of_congr (reachTbl_pushSt (g := g) hinj hreach) (u' := s₀.map ρ) hpush
    refine ⟨t, hreach', fun y hy => ?_⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
    exact (hmem (ρ f)).2 (mem_pushSt.2 ⟨f, ⟨mem_relFacts_of_mem_goal hf, hgoal f hf⟩, rfl⟩)

/-! ### The renaming the compiled regular problem calls for

The facts of the compiled `STRIPS` problem of a regular HTN description
(`HtnComplexity/Space/RegTable.lean`) are `12 v` (a fact `v` of the source instance),
`8 c + 1` ("the compound task `c` of the source description is pending"), `2` ("done") and `3`
(the unsatisfiable fact), together with the facts `4 w` and `4 c' + 1` the token gadget
introduces.  The renaming `HTN.Space.regRho` divides the first family by `3` and the second by
`2`, turning them into `4 v + 2` and `4 c + 3`, and moves everything else out of the way into the
residue class `0` modulo `4`.  It is injective **everywhere**, so no vocabulary lemma about the
table is needed: `HTN.Space.solvableTbl_regRho` applies to any table at all. -/

/-- **The renaming of the facts of a compiled regular problem**: `12 v ↦ 4 v + 2`,
`8 c + 1 ↦ 4 c + 3`, `2 ↦ 0`, `3 ↦ 1`, and `n ↦ 4 n + 4` on everything else.

The two residues `2` and `3` modulo `4` are chosen because the numeral of `4 v + 2` is the
numeral of `v` with two constant bits in front **at every argument, `v = 0` included**
(`HTN.PTime.bitsOfNat_four_add_two`), which the residues `0` and `1` would not give: the numeral
of `0` is empty. -/
def regRho (n : ℕ) : ℕ :=
  if n % 12 = 0 then n / 3 + 2
  else if n % 8 = 1 then n / 2 + 3
  else if n = 2 then 0
  else if n = 3 then 1
  else 4 * n + 4

@[simp] theorem regRho_state (v : ℕ) : regRho (12 * v) = 4 * v + 2 := by
  rw [regRho, if_pos (by omega)]; omega

@[simp] theorem regRho_pending (c : ℕ) : regRho (8 * c + 1) = 4 * c + 3 := by
  rw [regRho, if_neg (by omega), if_pos (by omega)]; omega

@[simp] theorem regRho_done : regRho 2 = 0 := by decide

@[simp] theorem regRho_bot : regRho 3 = 1 := by decide

/-- **The renaming is injective.** -/
theorem regRho_injective : Function.Injective regRho := by
  intro a b h
  simp only [regRho] at h
  split_ifs at h <;> omega

/-- An injective renaming is in particular injective where it matters. -/
theorem injOnRel_of_injective (h : Function.Injective ρ) : InjOnRel ρ tbl s₀ g :=
  fun _ _ _ _ hab => h hab

/-- **Solvability of an action table is invariant under `HTN.Space.regRho`.** -/
theorem solvableTbl_regRho :
    SolvableTbl (tbl.map (mapRow regRho)) (s₀.map regRho) (g.map regRho) ↔
      SolvableTbl tbl s₀ g :=
  solvableTbl_map (injOnRel_of_injective regRho_injective)

end Space

end HTN
