import HtnComplexity.Space.SeqTable
/-!
# The initial configuration of the gadget machine, characterised locally

Step A3 of `TABLE4-PLAN.md`, semantic half.  The machine for unrooted totally ordered instances
guesses the compiled initial state of the gadget instance
`regInitR (seqInst (code d) d q xs ws)`, witness facts included, and has to check the guess
against the code of `q` with a test of Cobham's class.  This file fixes *what* that test decides:
`HTN.Space.SeqM.InitOk d q S`, a conjunction of conditions each of which mentions a bounded
number of entries of the configuration `S` and of the code of `q` (the shape of the entries,
the facts of the instance, the root entry, `cur`/`fin`, the rank-witness conditions of
`HTN.Syn.SeqG.WitOk` on the entries `wit p i`, and the agreement of the entries `lab`, `nop`,
`len` with the witnesses).

* `HTN.Space.SeqM.initOk_iff` — `InitOk d q S` holds exactly when `S` carries (as a set) the
  compiled initial state of a gadget instance for some checked witness;
* `HTN.Space.SeqM.solvable_iff_exists_initOk` — hence a totally ordered instance over a totally
  ordered tail-recursive domain is solvable iff the table problem of the gadget domain is
  solvable from **some** configuration passing `InitOk`, towards the compiled goal
  `HTN.Space.SeqM.seqGoal d q`, which does not depend on the guess.

What is left for A3 is the Cobham programming of `InitOk` on encoded entries (the bit-level
shapes are `HTN.Space.SeqM.bits_cfact_inst` / `bits_cfact_gad` of `SeqCode.lean`).
-/

namespace HTN

namespace Space

namespace SeqM

open Syn SeqG PTime

/-! ### The compiled numerals -/

/-- The compiled numeral of a fact `v` of the instance. -/
def cfI (v : ℕ) : ℕ := 4 * (2 * v + 1) + 2

/-- The compiled numeral of a gadget fact. -/
def cfG (g : GF) : ℕ := 4 * gfNum g + 2

/-- The compiled numeral of the root task of the gadget instance. -/
def cRoot (d : DomDesc) : ℕ := 4 * leastFresh (vocC d) + 3

theorem cfI_injective : Function.Injective cfI := fun a b h => by
  simp only [cfI] at h; omega

theorem cfG_injective : Function.Injective cfG := fun a b h =>
  gfNum_injective (by simp only [cfG] at h; omega)

theorem cfI_ne_cfG (v : ℕ) (g : GF) : cfI v ≠ cfG g := by
  simp only [cfI, cfG, gfNum]; omega

theorem cfI_ne_cRoot (v : ℕ) (d : DomDesc) : cfI v ≠ cRoot d := by
  simp only [cfI, cRoot]; omega

theorem cfG_ne_cRoot (g : GF) (d : DomDesc) : cfG g ≠ cRoot d := by
  simp only [cfG, cRoot]; omega

/-- The compiled goal of the gadget instance; it does not depend on the sequence or witness. -/
def seqGoal (d : DomDesc) (q : InstDesc) : List ℕ :=
  (q.goalList.map (code d).ρ ++ [(code d).gf .fin]).map (fun v => 4 * v + 2) ++ [0]

theorem regGoalR_seqInst (d : DomDesc) (q : InstDesc) (xs : List (ℕ ⊕ ℕ))
    (ws : List (ℕ × ℕ)) : regGoalR (seqInst (code d) d q xs ws) = seqGoal d q := rfl

/-- **Membership in the compiled initial state of a gadget instance.** -/
theorem mem_regInitR_seqInst {d : DomDesc} {q : InstDesc} {xs : List (ℕ ⊕ ℕ)}
    {ws : List (ℕ × ℕ)} {f : ℕ} :
    f ∈ regInitR (seqInst (code d) d q xs ws) ↔
      (∃ v ∈ q.initList, f = cfI v) ∨
      (∃ g, (g = .cur 0 ∨ (code d).gf g ∈ stat (code d) d xs ws) ∧ f = cfG g) ∨
      f = cRoot d := by
  have hstat : ∀ y ∈ gadStatic (code d) d xs ws, ∃ g, y = (code d).gf g := by
    intro y hy
    simp only [gadStatic, List.mem_cons, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨w, -, rfl⟩ | rfl | ⟨p, -, rfl⟩ | ⟨p, -, rfl⟩ <;> exact ⟨_, rfl⟩
  have hroot : rootName (seqInst (code d) d q xs ws) = leastFresh (vocC d) := rfl
  rw [regInitR, hroot]
  simp only [seqInst, InstDesc.initList, gadInit, List.mem_append, List.mem_map,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ((⟨y, (⟨v, hv, rfl⟩ | rfl | hy), rfl⟩) | rfl)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr (Or.inl ⟨.cur 0, Or.inl rfl, rfl⟩)
    · obtain ⟨g, rfl⟩ := hstat _ hy
      exact Or.inr (Or.inl ⟨g, Or.inr hy, rfl⟩)
    · exact Or.inr (Or.inr rfl)
  · rintro (⟨v, hv, rfl⟩ | ⟨g, (rfl | hg), rfl⟩ | rfl)
    · exact Or.inl ⟨_, Or.inl ⟨v, hv, rfl⟩, rfl⟩
    · exact Or.inl ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact Or.inl ⟨_, Or.inr (Or.inr hg), rfl⟩
    · exact Or.inr rfl

/-! ### Witnesses read off a configuration -/

theorem injOn_wit (s : Set ℕ) :
    Set.InjOn (fun w : ℕ × ℕ => cfG (.wit w.1 w.2)) ((fun w : ℕ × ℕ => cfG (.wit w.1 w.2)) ⁻¹' s) :=
  fun a _ b _ h => by
    have := cfG_injective h
    simp only [GF.wit.injEq] at this
    exact Prod.ext this.1 this.2

/-- The witness pairs a configuration carries. -/
noncomputable def witList (S : List ℕ) : List (ℕ × ℕ) :=
  (S.toFinset.preimage (fun w : ℕ × ℕ => cfG (.wit w.1 w.2)) (injOn_wit _)).toList

theorem mem_witList {S : List ℕ} {p a : ℕ} : (p, a) ∈ witList S ↔ cfG (.wit p a) ∈ S := by
  simp [witList]

/-! ### The local conditions -/

/-- **The conditions the initial test checks** on a configuration `S` (a list of numerals), for
the domain description `d` (through its vocabulary) and the instance `q`. -/
structure InitOk (d : DomDesc) (q : InstDesc) (S : List ℕ) : Prop where
  shape : ∀ f ∈ S, (∃ v, f = cfI v) ∨ (∃ g, f = cfG g) ∨ f = cRoot d
  root : cRoot d ∈ S
  inst : ∀ v, cfI v ∈ S ↔ v ∈ q.initList
  cur : ∀ p, cfG (.cur p) ∈ S ↔ p = 0
  fin : cfG .fin ∉ S
  wit : WitOk q.tnI (witList S)
  lab : ∀ p x, cfG (.lab p x) ∈ S ↔
    ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ S ∧ q.tnI.label i = x
  nop : ∀ p, cfG (.nop p) ∈ S ↔
    ∃ i ∈ q.tnI.ids, cfG (.wit p i) ∈ S ∧ unknownPrimB d (q.tnI.label i) = true
  len : ∀ k, cfG (.len k) ∈ S ↔
    (∀ i ∈ q.tnI.ids, cfG (.wit k i) ∉ S) ∧ (k = 0 ∨ ∃ i ∈ q.tnI.ids, cfG (.wit (k - 1) i) ∈ S)

/-! ### The static facts of a checked witness -/

section Static

variable {d : DomDesc} {t : TnDesc} {ws : List (ℕ × ℕ)} {xs : List (ℕ ⊕ ℕ)}

theorem _root_.HTN.Syn.SeqG.WitOk.exists_id_iff (h : WitOk t ws) {p : ℕ} :
    (∃ i ∈ t.ids, (p, i) ∈ ws) ↔ p < t.ids.toFinset.card := by
  constructor
  · rintro ⟨i, hi, hp⟩
    rw [(h.mem_iff hi).1 hp]
    exact h.wpos_lt hi
  · intro hp
    obtain ⟨h1, h2⟩ := h.wnode_spec hp
    exact ⟨_, h1, (h.mem_iff h1).2 h2.symm⟩

theorem getElem_of_witSeq (hx : WitSeq t ws xs) {p i : ℕ} (hi : i ∈ t.ids) (hw : (p, i) ∈ ws)
    (hp : p < xs.length) : xs[p] = t.label i := by
  have := hx.2 p i hi hw
  rwa [List.getElem?_eq_getElem hp, Option.some.injEq] at this

theorem lab_mem_stat_iff (h : WitOk t ws) (hx : WitSeq t ws xs) {p : ℕ} {x : ℕ ⊕ ℕ} :
    (code d).gf (.lab p x) ∈ stat (code d) d xs ws ↔ ∃ i ∈ t.ids, (p, i) ∈ ws ∧ t.label i = x := by
  rw [lab_mem_stat]
  constructor
  · rintro ⟨hp, rfl⟩
    obtain ⟨i, hi, hw⟩ := h.exists_id_iff.2 (hx.1 ▸ hp)
    exact ⟨i, hi, hw, (getElem_of_witSeq hx hi hw hp).symm⟩
  · rintro ⟨i, hi, hw, rfl⟩
    have hp : p < xs.length := hx.1 ▸ h.exists_id_iff.1 ⟨i, hi, hw⟩
    exact ⟨hp, getElem_of_witSeq hx hi hw hp⟩

theorem nop_mem_stat_iff (h : WitOk t ws) (hx : WitSeq t ws xs) {p : ℕ} :
    (code d).gf (.nop p) ∈ stat (code d) d xs ws ↔
      ∃ i ∈ t.ids, (p, i) ∈ ws ∧ unknownPrimB d (t.label i) = true := by
  rw [nop_mem_stat]
  constructor
  · rintro ⟨hp, hu⟩
    obtain ⟨i, hi, hw⟩ := h.exists_id_iff.2 (hx.1 ▸ hp)
    exact ⟨i, hi, hw, getElem_of_witSeq hx hi hw hp ▸ hu⟩
  · rintro ⟨i, hi, hw, hu⟩
    have hp : p < xs.length := hx.1 ▸ h.exists_id_iff.1 ⟨i, hi, hw⟩
    exact ⟨hp, (getElem_of_witSeq hx hi hw hp).symm ▸ hu⟩

theorem len_mem_stat_iff (h : WitOk t ws) (hx : WitSeq t ws xs) {k : ℕ} :
    (code d).gf (.len k) ∈ stat (code d) d xs ws ↔
      (∀ i ∈ t.ids, (k, i) ∉ ws) ∧ (k = 0 ∨ ∃ i ∈ t.ids, (k - 1, i) ∈ ws) := by
  rw [len_mem_stat, hx.1]
  have h1 : (∀ i ∈ t.ids, (k, i) ∉ ws) ↔ ¬ k < t.ids.toFinset.card := by
    rw [← h.exists_id_iff]
    simp
  rw [h1, h.exists_id_iff]
  omega

theorem wit_mem_stat_iff {p a : ℕ} :
    (code d).gf (.wit p a) ∈ stat (code d) d xs ws ↔ (p, a) ∈ ws := by
  rw [mem_stat]
  simp only [GF.wit.injEq, reduceCtorEq, and_false, exists_false, or_false]
  constructor
  · rintro ⟨w, hw, rfl, rfl⟩
    exact hw
  · intro hw
    exact ⟨_, hw, rfl, rfl⟩

end Static

/-! ### The characterisation -/

theorem _root_.HTN.Syn.SeqG.WitOk.congr {t : TnDesc} {ws ws' : List (ℕ × ℕ)} (h : WitOk t ws)
    (hw : ∀ w, w ∈ ws' ↔ w ∈ ws) : WitOk t ws' where
  total i hi := by simpa only [hw] using h.total i hi
  endp e he := by simpa only [hw] using h.endp e he
  func p p' a := by simpa only [hw] using h.func p p' a
  inj p i j := by simpa only [hw] using h.inj p i j
  down p i := by simpa only [hw] using h.down p i
  mono e he p p' := by simpa only [hw] using h.mono e he p p'

section Mem

variable {d : DomDesc} {q : InstDesc} {xs : List (ℕ ⊕ ℕ)} {ws : List (ℕ × ℕ)}

theorem cfI_mem_regInitR {v : ℕ} :
    cfI v ∈ regInitR (seqInst (code d) d q xs ws) ↔ v ∈ q.initList := by
  rw [mem_regInitR_seqInst]
  constructor
  · rintro (⟨w, hw, h⟩ | ⟨g, -, h⟩ | h)
    · rwa [cfI_injective h]
    · exact absurd h (cfI_ne_cfG _ _)
    · exact absurd h (cfI_ne_cRoot _ _)
  · exact fun hv => Or.inl ⟨v, hv, rfl⟩

theorem cfG_mem_regInitR {g : GF} :
    cfG g ∈ regInitR (seqInst (code d) d q xs ws) ↔
      g = .cur 0 ∨ (code d).gf g ∈ stat (code d) d xs ws := by
  rw [mem_regInitR_seqInst]
  constructor
  · rintro (⟨w, -, h⟩ | ⟨g', hg', h⟩ | h)
    · exact absurd h.symm (cfI_ne_cfG _ _)
    · rwa [cfG_injective h]
    · exact absurd h (cfG_ne_cRoot _ _)
  · exact fun hg => Or.inr (Or.inl ⟨g, hg, rfl⟩)

theorem cRoot_mem_regInitR : cRoot d ∈ regInitR (seqInst (code d) d q xs ws) :=
  mem_regInitR_seqInst.2 (Or.inr (Or.inr rfl))

theorem shape_of_mem_regInitR {f : ℕ} (hf : f ∈ regInitR (seqInst (code d) d q xs ws)) :
    (∃ v, f = cfI v) ∨ (∃ g, f = cfG g) ∨ f = cRoot d := by
  rcases mem_regInitR_seqInst.1 hf with ⟨v, -, rfl⟩ | ⟨g, -, rfl⟩ | rfl
  · exact Or.inl ⟨v, rfl⟩
  · exact Or.inr (Or.inl ⟨g, rfl⟩)
  · exact Or.inr (Or.inr rfl)

end Mem

/-- A configuration with the same facts as the compiled initial state of a gadget instance for a
checked witness passes the local checks. -/
theorem initOk_of_eqv {d : DomDesc} {q : InstDesc} {S : List ℕ} {ws : List (ℕ × ℕ)}
    {xs : List (ℕ ⊕ ℕ)} (hw : WitOk q.tnI ws) (hx : WitSeq q.tnI ws xs)
    (hS : ∀ f, f ∈ S ↔ f ∈ regInitR (seqInst (code d) d q xs ws)) : InitOk d q S := by
  have hW : ∀ p a, cfG (.wit p a) ∈ S ↔ (p, a) ∈ ws := fun p a => by
    rw [hS, cfG_mem_regInitR, wit_mem_stat_iff]
    simp
  refine ⟨fun f hf => shape_of_mem_regInitR ((hS f).1 hf), (hS _).2 cRoot_mem_regInitR,
    fun v => by rw [hS, cfI_mem_regInitR], fun p => ?_, ?_, ?_,
    fun p x => ?_, fun p => ?_, fun k => ?_⟩
  · rw [hS, cfG_mem_regInitR]
    simp only [GF.cur.injEq, cur_nmem_stat, or_false]
  · rw [hS, cfG_mem_regInitR]
    simp only [reduceCtorEq, fin_nmem_stat, or_self, not_false_eq_true]
  · exact hw.congr fun w => by rw [mem_witList, hW]
  · rw [hS, cfG_mem_regInitR, lab_mem_stat_iff hw hx]
    simp [hW]
  · rw [hS, cfG_mem_regInitR, nop_mem_stat_iff hw hx]
    simp [hW]
  · rw [hS, cfG_mem_regInitR, len_mem_stat_iff hw hx]
    simp [hW]

/-- **The local conditions characterise the compiled initial states of the gadget instances.** -/
theorem initOk_iff {d : DomDesc} {q : InstDesc} (hq : q.IsTO) {S : List ℕ} :
    InitOk d q S ↔ ∃ ws xs, WitOk q.tnI ws ∧ WitSeq q.tnI ws xs ∧
      ∀ f, f ∈ S ↔ f ∈ regInitR (seqInst (code d) d q xs ws) := by
  constructor
  · intro hS
    have hw := hS.wit
    obtain ⟨xs, hx⟩ := exists_witSeq hq hw
    have hW : ∀ p a, (p, a) ∈ witList S ↔ cfG (.wit p a) ∈ S := fun p a => mem_witList
    have hG : ∀ g, cfG g ∈ S ↔ cfG g ∈ regInitR (seqInst (code d) d q xs (witList S)) := by
      intro g
      rw [cfG_mem_regInitR]
      cases g with
      | cur p => rw [hS.cur]; simp only [GF.cur.injEq, cur_nmem_stat, or_false]
      | fin => simp only [hS.fin, reduceCtorEq, fin_nmem_stat, or_self]
      | len k => rw [hS.len, len_mem_stat_iff hw hx]; simp [hW]
      | lab p x => rw [hS.lab, lab_mem_stat_iff hw hx]; simp [hW]
      | nop p => rw [hS.nop, nop_mem_stat_iff hw hx]; simp [hW]
      | wit p a => rw [wit_mem_stat_iff, hW]; simp
    refine ⟨witList S, xs, hw, hx, fun f => ?_⟩
    constructor
    · intro hf
      rcases hS.shape f hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | rfl
      · exact cfI_mem_regInitR.2 ((hS.inst v).1 hf)
      · exact (hG g).1 hf
      · exact cRoot_mem_regInitR
    · intro hf
      rcases shape_of_mem_regInitR hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | rfl
      · exact (hS.inst v).2 (cfI_mem_regInitR.1 hf)
      · exact (hG g).2 hf
      · exact hS.root
  · rintro ⟨ws, xs, hw, hx, hS⟩
    exact initOk_of_eqv hw hx hS

theorem solvableTbl_congr {tbl : List Row} {u u' g : List ℕ} (hu : ∀ f, f ∈ u' ↔ f ∈ u) :
    SolvableTbl tbl u g → SolvableTbl tbl u' g := by
  rintro ⟨s, hs, hg⟩
  obtain ⟨t, ht, hts⟩ := exists_run_of_congr hs hu
  exact ⟨t, ht, fun f hf => (hts f).2 (hg f hf)⟩

/-- **Solvability through a guessed, locally checked initial configuration.**  A totally ordered
instance `q` with at most `N` initial tasks over a totally ordered tail-recursive domain `d` is
solvable exactly when the compiled table of the gadget domain reaches the compiled goal from some
configuration that passes the local checks `InitOk d q`. -/
theorem solvable_iff_exists_initOk {d : DomDesc} {q : InstDesc} {N : ℕ} (hTO : d.MethodsTO)
    (hTR : d.IsTailRec) (hq : q.IsTO) (hN : q.tnI.ids.length ≤ N) :
    Solvable d q ↔ (trDom (seqDom (code d) d N)).HasEmptyMethod ∧
      ∃ S, InitOk d q S ∧ SolvableTbl (trTableR (seqDom (code d) d N)) S (seqGoal d q) := by
  constructor
  · intro hs
    obtain ⟨ws, xs, hw, hx, -, he, ht⟩ := (solvable_iff_exists_wit hTO hTR hq hN).1 hs
    exact ⟨he, _, (initOk_iff hq).2 ⟨ws, xs, hw, hx, fun f => Iff.rfl⟩, ht⟩
  · rintro ⟨he, S, hS, hs⟩
    obtain ⟨ws, xs, hw, hx, hSR⟩ := (initOk_iff hq).1 hS
    exact (solvable_iff_tbl_of_wit hTO hTR hq hN hw hx).2
      ⟨he, solvableTbl_congr (fun f => (hSR f).symm) hs⟩

end SeqM

end Space

end HTN
