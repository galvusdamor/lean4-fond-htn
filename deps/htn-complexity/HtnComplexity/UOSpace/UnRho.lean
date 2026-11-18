import HtnComplexity.UOSpace.UnSim
import HtnComplexity.Space.ThrSpace
/-!
# Renaming the unrooted table into the vocabulary of the thread machine

The machine of `HtnComplexity/Space/ThrMachine.lean` reads off the code of the instance a
configuration `S` with `HTN.Space.Thr.ThrInitOk d q S`: the facts `cfI v` of the initial state,
the slot facts `cfG (.lab p x)`, `cfG (.nop p)`, `cfG (.len n)`, `cfG (.cur 0)`, and a lot of
facts (witnesses, edges, closure) that our table does not need.  We rename the facts of
`HTN.UOTbl.unTbl d W N` by the injection `HTN.UOTbl.unRho`, which sends

* `fSt v ↦ cfI v`, `fRoot (cLab p l) ↦ cfG (.lab p l)`, `fRoot (cNop p) ↦ cfG (.nop p)`,
  `fRoot (cLen p) ↦ cfG (.len p)`, `fRoot (cCur p) ↦ cfG (.cur p)`, `fDone ↦ cfG .fin`,
* and every other number (residues `0`, `1` modulo `4`) to itself — numbers that never occur
  in such a configuration.

* `HTN.UOTbl.solvableTbl_pull` — solvability in the renamed table from any configuration `S` is
  solvability in `unTbl` from the facts of `S` the table can see (`pullSt`);
* `HTN.UOTbl.pull_hyps` — for `ThrInitOk d q S`, that state satisfies the hypotheses of
  `HtnComplexity/UOSpace/UnSim.lean`, with the slots of `S`.
-/

namespace HTN

namespace UOTbl

open Syn Space SeqG SeqM Thr UOAbs

/-! ### The renaming -/

/-- The task of a label code. -/
def lsum (m : ℕ) : ℕ ⊕ ℕ := if m % 2 = 0 then Sum.inl (m / 2) else Sum.inr (m / 2)

theorem lsum_lcode (l : Bool × ℕ) : lsum (lcode l) = TnDesc.ofPair l := by
  rcases l with ⟨b, n⟩
  cases b <;> simp [lsum, lcode, TnDesc.ofPair]; omega

theorem lsum_injective : Function.Injective lsum := by
  intro a b h
  unfold lsum at h
  split_ifs at h with h1 h2 h2 <;> simp at h <;> omega

/-- The gadget fact of an input code. -/
def gdec (c : ℕ) : GF :=
  if c % 4 = 0 then .lab (c / 4).unpair.1 (lsum (c / 4).unpair.2)
  else if c % 4 = 1 then .nop (c / 4)
  else if c % 4 = 2 then .len (c / 4)
  else .cur (c / 4)

theorem gdec_injective : Function.Injective gdec := by
  intro a b h
  unfold gdec at h
  split_ifs at h <;> simp only [GF.lab.injEq, GF.nop.injEq, GF.len.injEq, GF.cur.injEq] at h
  · obtain ⟨h1, h2⟩ := h
    have h3 := lsum_injective h2
    have : (a / 4).unpair = (b / 4).unpair := Prod.ext h1 h3
    have := congrArg (fun x => Nat.pair x.1 x.2) this
    simp only [Nat.pair_unpair] at this
    omega
  all_goals omega

theorem gdec_ne_fin (c : ℕ) : gdec c ≠ .fin := by
  unfold gdec; split_ifs <;> simp

/-- **The renaming.** -/
def unRho (n : ℕ) : ℕ :=
  if n % 4 = 2 then cfI (n / 4)
  else if n % 4 = 3 then cfG (gdec (n / 4))
  else if n = 0 then cfG .fin
  else n

@[simp] theorem unRho_fSt (v : ℕ) : unRho (fSt v) = cfI v := by
  simp only [unRho, fSt]
  rw [if_pos (by omega)]
  congr 1; omega

theorem unRho_fRoot (c : ℕ) : unRho (fRoot c) = cfG (gdec c) := by
  simp only [unRho, fRoot]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 2; omega

@[simp] theorem unRho_cLab (p : ℕ) (l : Bool × ℕ) :
    unRho (fRoot (cLab p l)) = cfG (.lab p (TnDesc.ofPair l)) := by
  rw [unRho_fRoot, gdec, if_pos (by simp [cLab])]
  simp [cLab, lsum_lcode]

@[simp] theorem unRho_cNop (p : ℕ) : unRho (fRoot (cNop p)) = cfG (.nop p) := by
  rw [unRho_fRoot]
  congr 1
  unfold gdec cNop
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

@[simp] theorem unRho_cLen (p : ℕ) : unRho (fRoot (cLen p)) = cfG (.len p) := by
  rw [unRho_fRoot]
  congr 1
  unfold gdec cLen
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

@[simp] theorem unRho_cCur (p : ℕ) : unRho (fRoot (cCur p)) = cfG (.cur p) := by
  rw [unRho_fRoot]
  congr 1
  unfold gdec cCur
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1; omega

@[simp] theorem unRho_fDone : unRho fDone = cfG .fin := by simp [unRho, fDone]

theorem unRho_other {n : ℕ} (h0 : n ≠ 0) (h2 : n % 4 ≠ 2) (h3 : n % 4 ≠ 3) : unRho n = n := by
  simp [unRho, h0, h2, h3]

theorem cfG_mod4 (g : GF) : cfG g % 4 = 2 := by simp only [cfG]; omega
theorem cfI_mod4 (v : ℕ) : cfI v % 4 = 2 := by simp only [cfI]; omega

theorem unRho_injective : Function.Injective unRho := by
  intro a b h
  have key : ∀ n, (n % 4 = 2 ∧ unRho n = cfI (n / 4)) ∨ (n % 4 = 3 ∧ unRho n = cfG (gdec (n / 4)))
      ∨ (n = 0 ∧ unRho n = cfG .fin) ∨ (n ≠ 0 ∧ n % 4 ≠ 2 ∧ n % 4 ≠ 3 ∧ unRho n = n) := by
    intro n
    by_cases h2 : n % 4 = 2
    · exact Or.inl ⟨h2, by simp [unRho, h2]⟩
    by_cases h3 : n % 4 = 3
    · exact Or.inr (Or.inl ⟨h3, by simp [unRho, h3]⟩)
    by_cases h0 : n = 0
    · exact Or.inr (Or.inr (Or.inl ⟨h0, by subst h0; simp [unRho]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h0, h2, h3, unRho_other h0 h2 h3⟩))
  rcases key a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha0, ha2, ha3, ea⟩ <;>
  rcases key b with ⟨hb, eb⟩ | ⟨hb, eb⟩ | ⟨hb, eb⟩ | ⟨hb0, hb2, hb3, eb⟩ <;>
  rw [ea, eb] at h
  · have := cfI_injective h; omega
  · exact absurd h (cfI_ne_cfG _ _)
  · exact absurd h (cfI_ne_cfG _ _)
  · have := cfI_mod4 (a / 4); omega
  · exact absurd h.symm (cfI_ne_cfG _ _)
  · have := gdec_injective (cfG_injective h); omega
  · exact absurd (cfG_injective h) (gdec_ne_fin _)
  · have := cfG_mod4 (gdec (a / 4)); omega
  · exact absurd h.symm (cfI_ne_cfG _ _)
  · exact absurd (cfG_injective h).symm (gdec_ne_fin _)
  · omega
  · have := cfG_mod4 GF.fin; omega
  · have := cfI_mod4 (b / 4); omega
  · have := cfG_mod4 (gdec (b / 4)); omega
  · have := cfG_mod4 GF.fin; omega
  · exact h

/-! ### Irrelevant facts and the pull-back -/

theorem reach_extend {T : List Row} {u v X : List ℕ} (h : ReachTbl T u v)
    (hX : ∀ f ∈ X, f ∉ tblFacts T) : ReachTbl T (u ++ X) (v ++ X) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail w w' _ hst ih =>
    obtain ⟨r, hr, hpre, hpost⟩ := hst
    refine ih.tail ⟨r, hr, fun f hf => List.mem_append_left _ (hpre f hf), fun f => ?_⟩
    simp only [List.mem_append, hpost]
    constructor
    · rintro ((h1 | ⟨h1, h2⟩) | h1)
      · exact Or.inl h1
      · exact Or.inr ⟨Or.inl h1, h2⟩
      · exact Or.inr ⟨Or.inr h1, fun hd => hX f h1 (mem_tblFacts_of_del hr hd)⟩
    · rintro (h1 | ⟨h1 | h1, h2⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr h1

/-- **Solvability in a renamed table, from an arbitrary configuration.** -/
theorem solvableTbl_pull {ρ : ℕ → ℕ} (hρ : Function.Injective ρ) {T0 : List Row}
    {X g0 S : List ℕ} :
    SolvableTbl (T0.map (mapRow ρ)) S (g0.map ρ) ↔
      SolvableTbl T0 (pullSt ρ (relFacts T0 X g0) S) g0 := by
  set R := relFacts T0 X g0 with hR
  have hinj : InjOnRel ρ T0 X g0 := injOnRel_of_injective hρ
  constructor
  · rintro ⟨S', hr, hg⟩
    refine ⟨_, reachTbl_pullSt hinj hr, fun f hf => mem_pullSt.2 ⟨?_, hg _ (List.mem_map_of_mem hf)⟩⟩
    exact mem_relFacts_of_mem_goal hf
  · rintro ⟨u, hr, hg⟩
    have h1 := reachTbl_pushSt hinj hr
    set Y := S.filter (fun f => decide (f ∉ R.map ρ)) with hY
    have hYt : ∀ f ∈ Y, f ∉ tblFacts (T0.map (mapRow ρ)) := by
      intro f hf ht
      obtain ⟨a, ha, rfl⟩ := mem_tblFacts_of_mem_map ht
      have := (List.mem_filter.1 hf).2
      simp only [decide_eq_true_eq] at this
      exact this (List.mem_map_of_mem (List.mem_append_left _ (List.mem_append_left _ ha)))
    have h2 := reach_extend h1 hYt
    have hcongr : ∀ f, f ∈ S ↔ f ∈ pushSt ρ R (pullSt ρ R S) ++ Y := by
      intro f
      simp only [List.mem_append, mem_pushSt, mem_pullSt, hY, List.mem_filter,
        decide_eq_true_eq]
      constructor
      · intro hf
        by_cases hfR : f ∈ R.map ρ
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hfR
          exact Or.inl ⟨a, ⟨ha, ha, hf⟩, rfl⟩
        · exact Or.inr ⟨hf, hfR⟩
      · rintro (⟨a, ⟨-, -, ha⟩, rfl⟩ | ⟨hf, -⟩)
        · exact ha
        · exact hf
    obtain ⟨t, ht, htm⟩ := exists_run_of_congr h2 hcongr
    refine ⟨t, ht, fun f hf => (htm f).2 (List.mem_append_left _ ?_)⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hf
    exact mem_pushSt.2 ⟨a, ⟨mem_relFacts_of_mem_goal ha, hg a ha⟩, rfl⟩

/-! ### The configurations of the thread machine -/

/-- The renamed table. -/
def unT (d : DomDesc) (W N : ℕ) : List Row := (unTbl d W N).map (mapRow unRho)

/-- The facts the table may see: those of the table, of the initial state and of the goal. -/
def unRel (d : DomDesc) (q : InstDesc) (W N : ℕ) : List ℕ :=
  relFacts (unTbl d W N) (q.initList.map fSt) (goalU q)

theorem goal_map_unRho (q : InstDesc) : (goalU q).map unRho = (goalF q.goalList).map enc := by
  simp [goalU, goalF, List.map_map, Function.comp_def, enc]

/-- **Solvability of the renamed table from a configuration.** -/
theorem solvableT_iff {d : DomDesc} {q : InstDesc} {W N : ℕ} {S : List ℕ} :
    SolvableTbl (unT d W N) S ((goalF q.goalList).map enc) ↔
      SolvableTbl (unTbl d W N) (pullSt unRho (unRel d q W N) S) (goalU q) := by
  rw [← goal_map_unRho]
  exact solvableTbl_pull unRho_injective

/-! ### Slots -/

section Slots

variable {d : DomDesc} {q : InstDesc} {S : List ℕ}

theorem thr_slot_inj (h : ThrInitOk d q S) {j j' : ℕ} (hj : j < nIds q) (hj' : j' < nIds q)
    (he : slotId q S j = slotId q S j') : j = j' := by
  obtain ⟨hi, hw⟩ := h.slot_spec hj
  obtain ⟨-, hw'⟩ := h.slot_spec hj'
  rw [← he] at hw'
  have e1 := (h.wit.mem_iff hi).1 (mem_witList.2 hw)
  have e2 := (h.wit.mem_iff hi).1 (mem_witList.2 hw')
  omega

theorem thr_slot_surj (h : ThrInitOk d q S) {i : ℕ} (hi : i ∈ q.tnI.ids) :
    ∃ j < nIds q, slotId q S j = i :=
  ⟨_, h.wit.wpos_lt hi, h.wit.wnode_wpos hi⟩

theorem flagLbls_ofTnDesc (t : TnDesc) :
    flagLbls (PNet.ofTnDesc t) =
      ((((PNet.keysOf t).filter (fun x => memB t.ids x)).map t.lblPair : List _) : Multiset _) := by
  simp only [flagLbls, PNet.ofTnDesc, List.filter_map, List.map_map, Function.comp_def]

/-- **The slots list the initial tasks.** -/
theorem thr_uoAbs_init (h : ThrInitOk d q S) :
    uoAbs (initConfig q) = (q.initList.toFinset,
      (((List.range (nIds q)).map (fun p => q.tnI.lblPair (slotId q S p)) : List _) : Multiset _)) := by
  show (q.initList.toFinset, flagLbls (PNet.ofTnDesc q.tnI)) = _
  congr 1
  rw [flagLbls_ofTnDesc, Multiset.coe_eq_coe]
  have hperm : List.Perm ((List.range (nIds q)).map (slotId q S))
      ((PNet.keysOf q.tnI).filter (fun x => memB q.tnI.ids x)) := by
    refine (List.perm_ext_iff_of_nodup ?_ ((List.nodup_dedup _).filter _)).2 fun x => ?_
    · refine List.Nodup.map_on (fun a ha b hb he => ?_) List.nodup_range
      exact thr_slot_inj h (List.mem_range.1 ha) (List.mem_range.1 hb) he
    · simp only [List.mem_map, List.mem_range, List.mem_filter, memB_iff]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have := (h.slot_spec hj).1
        exact ⟨PNet.mem_keysOf_of_mem_ids this, this⟩
      · rintro ⟨-, hx⟩
        exact thr_slot_surj h hx
  have := hperm.map q.tnI.lblPair
  rw [List.map_map] at this
  exact this.symm

end Slots

/-! ### The pulled-back configuration satisfies the hypotheses of the simulation -/

section Pull

variable {d : DomDesc} {q : InstDesc} {W N : ℕ} {S : List ℕ}

theorem mem_S_mod (h : ThrInitOk d q S) {f : ℕ} (hf : f ∈ S) : f % 4 = 2 := by
  rcases h.shape f hf with ⟨v, rfl⟩ | ⟨g, rfl⟩ | ⟨e, rfl⟩
  · exact cfI_mod4 v
  · exact cfG_mod4 g
  · exact cfN_mod e

theorem mem_pull {f : ℕ} : f ∈ pullSt unRho (unRel d q W N) S ↔ f ∈ unRel d q W N ∧ unRho f ∈ S :=
  mem_pullSt

theorem fSt_mem_unRel {v : ℕ} (hv : v ∈ q.initList) : fSt v ∈ unRel d q W N :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hv))

theorem mem_unRel_of_row {r : Row} (hr : r ∈ unTbl d W N) {f : ℕ} (hf : f ∈ r.1) :
    f ∈ unRel d q W N :=
  List.mem_append_left _ (List.mem_append_left _ (mem_tblFacts_of_prec hr hf))

theorem pull_strip (h : ThrInitOk d q S) :
    ∀ f, f ∈ strip (pullSt unRho (unRel d q W N) S) ↔ StP q.initList.toFinset f := by
  intro f
  rw [mem_strip, mem_pull]
  constructor
  · rintro ⟨⟨-, hS⟩, hin⟩
    by_cases h2 : f % 4 = 2
    · obtain ⟨v, rfl⟩ : ∃ v, f = fSt v := ⟨f / 4, by simp only [fSt]; omega⟩
      rw [unRho_fSt, h.inst] at hS
      exact stP_fSt.2 (List.mem_toFinset.2 hS)
    · exfalso
      have h3 : f % 4 ≠ 3 := hin
      by_cases h0 : f = 0
      · subst h0
        exact h.fin (by simpa [unRho] using hS)
      · rw [unRho_other h0 h2 h3] at hS
        exact h2 (mem_S_mod h hS)
  · rintro ⟨v, hv, rfl⟩
    have hv' := List.mem_toFinset.1 hv
    exact ⟨⟨fSt_mem_unRel hv', by rw [unRho_fSt, h.inst]; exact hv'⟩, not_isIn_fSt v⟩

theorem lblPair_eq_of_label {t : TnDesc} {i : ℕ} {l : Bool × ℕ}
    (h : t.label i = TnDesc.ofPair l) : t.lblPair i = l := by
  rw [← TnDesc.ofPair_lblPair] at h
  rcases hl : t.lblPair i with ⟨b, n⟩
  rcases l with ⟨b', n'⟩
  rw [hl] at h
  cases b <;> cases b' <;> simp [TnDesc.ofPair] at h <;> simp [h]

theorem pull_inOK (h : ThrInitOk d q S) :
    InOK d (fun p => q.tnI.lblPair (slotId q S p)) (nIds q) (pullSt unRho (unRel d q W N) S) where
  labOK p l hc := by
    have hS := (mem_pull.1 hc).2
    rw [unRho_cLab, h.lab] at hS
    obtain ⟨i, hi, hw, hlab⟩ := hS
    obtain ⟨hp, hsl⟩ := h.slot_of_wit hi hw
    refine ⟨hp, ?_⟩
    rw [hsl]
    exact lblPair_eq_of_label hlab
  nopOK p hc := by
    have hS := (mem_pull.1 hc).2
    rw [unRho_cNop, h.nop] at hS
    obtain ⟨i, hi, hw, hunk⟩ := hS
    obtain ⟨hp, hsl⟩ := h.slot_of_wit hi hw
    refine ⟨hp, ?_⟩
    rw [hsl]
    rcases hl : q.tnI.label i with a | c
    · rw [hl] at hunk
      have : q.tnI.lblPair i = (false, a) := lblPair_eq_of_label (by rw [hl]; rfl)
      rw [this]
      exact ⟨rfl, by simpa [unknownPrimB] using hunk⟩
    · rw [hl] at hunk; simp [unknownPrimB] at hunk
  lenOK p hc := by
    have hS := (mem_pull.1 hc).2
    rw [unRho_cLen] at hS
    exact (h.len_iff p).1 hS

theorem pull_cur (h : ThrInitOk d q S) : fRoot (cCur 0) ∈ pullSt unRho (unRel d q W N) S := by
  refine mem_pull.2 ⟨mem_unRel_of_row (r := zeroRow (labsU d) W (kI d))
    (mem_unTbl.2 (Or.inl rfl)) (by simp [zeroRow]), ?_⟩
  rw [unRho_cCur]
  exact (h.cur 0).2 rfl

theorem pull_len (h : ThrInitOk d q S) (hN : nIds q ≤ N) :
    fRoot (cLen (nIds q)) ∈ pullSt unRho (unRel d q W N) S := by
  refine mem_pull.2 ⟨mem_unRel_of_row (r := doneRow (kI d) (nIds q))
    (mem_unTbl.2 (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hN, rfl⟩))))) (by simp [doneRow]), ?_⟩
  rw [unRho_cLen]
  exact (h.len_iff _).2 rfl

theorem pull_lab (h : ThrInitOk d q S) (hN : nIds q ≤ N) (hW : 0 < W) {p : ℕ} (hp : p < nIds q)
    (hl : q.tnI.lblPair (slotId q S p) ∈ labsU d) :
    fRoot (cLab p (q.tnI.lblPair (slotId q S p))) ∈ pullSt unRho (unRel d q W N) S := by
  refine mem_pull.2 ⟨mem_unRel_of_row (r := labRow (kI d) p (q.tnI.lblPair (slotId q S p)) 0)
    (mem_unTbl.2 (Or.inr (Or.inr (Or.inl ⟨p, by omega, _, hl, 0, hW, rfl⟩)))) (by simp [labRow]),
    ?_⟩
  rw [unRho_cLab, h.lab]
  obtain ⟨hi, hw⟩ := h.slot_spec hp
  exact ⟨_, hi, hw, (TnDesc.ofPair_lblPair _ _).symm⟩

theorem pull_nop (h : ThrInitOk d q S) (hN : nIds q ≤ N) {p : ℕ} (hp : p < nIds q)
    (hu : Unk d (q.tnI.lblPair (slotId q S p))) :
    fRoot (cNop p) ∈ pullSt unRho (unRel d q W N) S := by
  refine mem_pull.2 ⟨mem_unRel_of_row (r := nopRow (kI d) p)
    (mem_unTbl.2 (Or.inr (Or.inl ⟨p, by omega, rfl⟩))) (by simp [nopRow]), ?_⟩
  rw [unRho_cNop, h.nop]
  obtain ⟨hi, hw⟩ := h.slot_spec hp
  refine ⟨_, hi, hw, ?_⟩
  rw [← TnDesc.ofPair_lblPair]
  rcases hl : q.tnI.lblPair (slotId q S p) with ⟨b, a⟩
  rw [hl] at hu
  obtain ⟨hb, ha⟩ := hu
  simp only at hb ha
  subst hb
  simp [TnDesc.ofPair, unknownPrimB, ha]

end Pull

/-! ### Correctness from a checked configuration -/

/-- **Plan existence is solvability of the renamed table from any checked configuration**, and
from the canonical one. -/
theorem solvable_iff_solvableT {d : DomDesc} {q : InstDesc} {W N : ℕ} (hd : d.MethodsUO)
    (hq : q.IsUO) (hW0 : 0 < W) (hW : nIds q + uoBndP d q * maxBody d < 2 ^ W) (hN : nIds q ≤ N)
    {S : List ℕ} (h : ThrInitOk d q S) :
    Solvable d q ↔ SolvableTbl (unT d W N) S ((goalF q.goalList).map enc) := by
  rw [solvableT_iff]
  constructor
  · intro hs
    exact solvableTblU_of_solvable hd hq hW hN (thr_uoAbs_init h) (pull_strip h) (pull_cur h)
      (pull_len h hN) (fun p hp hl => pull_lab h hN hW0 hp hl) (fun p hp hu => pull_nop h hN hp hu)
      hs
  · intro hs
    exact solvable_of_solvableTblU hd hq (thr_uoAbs_init h) (pull_strip h) (pull_inOK h) hs

end UOTbl

end HTN
