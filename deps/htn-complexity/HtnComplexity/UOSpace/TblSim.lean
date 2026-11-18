import HtnComplexity.UOSpace.TblRows
import HtnComplexity.Space.RegRename
/-!
# The action table simulates the abstract unordered progression

`HTN.UOTbl.solvable_iff_solvableTbl`: for an unordered domain and a rooted instance, and counters
of `W` bits with `uoBndP d q · maxBody d + 1 < 2 ^ W`,

    Solvable d q ↔ SolvableTbl (uoTbl d W) (regInitR q) (regGoalR q).

* **Completeness** (`solvableTbl_of_solvable`): a short abstract run
  (`HTN.Syn.solvable_iff_short_uo`) never makes a counter overflow, and every abstract step is
  simulated by a sequence of rows.
* **Soundness** (`solvable_of_solvableTbl`): an invariant on the reachable table states — each one
  is the initial state, or represents an abstractly reachable configuration (possibly in the middle
  of unfolding a method), or is a final state.
-/

namespace HTN

namespace UOTbl

open Syn Space UOAbs

/-! ### The rows of the table -/

theorem mem_uoTbl {d : DomDesc} {W : ℕ} {r : Row} :
    r ∈ uoTbl d W ↔ (∃ e ∈ d.methods, r = startRow (labs d) W e.1) ∨
      (∃ l ∈ labs d, l.1 = false ∧ ∃ i < W, r = exeRow d l i) ∨
      (∃ k e, d.methods[k]? = some e ∧ ((∃ i < W, r = decRow k e i) ∨
        (∃ p l, (body e)[p]? = some l ∧ ∃ i < W, r = addRow k p l i) ∨
        r = endRow k (body e).length)) ∨
      r = finRow (labs d) W := by
  simp only [uoTbl, methRows, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_filter,
    List.mem_range, List.mem_singleton, List.mem_zipIdx_iff_getElem?, decide_eq_true_eq]
  constructor
  · rintro (((⟨e, he, rfl⟩ | ⟨l, ⟨hl, hl1⟩, i, hi, rfl⟩) |
      ⟨⟨e, k⟩, hk, ((⟨i, hi, rfl⟩ | ⟨⟨l, p⟩, hp, i, hi, rfl⟩) | rfl)⟩) | rfl)
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr (Or.inl ⟨l, hl, hl1, i, hi, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inl ⟨p, l, hp, i, hi, rfl⟩)⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (⟨e, he, rfl⟩ | ⟨l, hl, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p, l, hp, i, hi, rfl⟩ | rfl)⟩ | rfl)
    · exact Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨l, ⟨hl, hl1⟩, i, hi, rfl⟩))
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inl (Or.inl ⟨i, hi, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inl (Or.inr ⟨(l, p), hp, i, hi, rfl⟩)⟩)
    · exact Or.inl (Or.inr ⟨(e, k), hk, Or.inr rfl⟩)
    · exact Or.inr rfl

theorem head_mem_labs {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) :
    (true, e.1) ∈ labs d := by
  simp only [labs, List.mem_append, List.mem_map]
  exact Or.inl ⟨e, he, rfl⟩

theorem body_mem_labs {d : DomDesc} {e : MethodDesc} (he : e ∈ d.methods) {l : Bool × ℕ}
    (hl : l ∈ body e) : l ∈ labs d := by
  simp only [labs, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨e, he, hl⟩

/-! ### The initial configuration of a rooted instance -/

theorem uoAbs_initConfig_rooted {q : InstDesc} (hq : q.IsRooted) :
    uoAbs (initConfig q) = (q.initList.toFinset, {(true, rootName q)}) := by
  obtain ⟨t, hT, hα⟩ := InstDesc.rootName_spec hq
  have hids : ∀ x, x ∈ q.tnI.ids ↔ x = t := by
    intro x
    have : x ∈ q.tnI.toTaskNetwork.T ↔ x ∈ ({t} : Finset ℕ) := by rw [hT]
    simpa using this
  have hlbl : q.tnI.lblPair t = (true, rootName q) :=
    TnDesc.ofPair_eq_inr_iff.1 (by rw [TnDesc.ofPair_lblPair]; exact hα)
  have hkeys : t ∈ PNet.keysOf q.tnI := PNet.mem_keysOf_of_mem_ids ((hids t).2 rfl)
  have hnd : (PNet.keysOf q.tnI).Nodup := List.nodup_dedup _
  show (q.initList.toFinset, flagLbls (PNet.ofTnDesc q.tnI)) = _
  congr 1
  have hf : (PNet.keysOf q.tnI).filter (fun x => memB q.tnI.ids x) = [t] := by
    rw [← List.perm_singleton]
    refine (List.perm_ext_iff_of_nodup (hnd.filter _) (List.nodup_singleton t)).2 fun x => ?_
    simp only [List.mem_filter, memB_iff, hids, List.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hkeys, rfl⟩
  simp only [flagLbls, PNet.ofTnDesc, List.filter_map, List.map_map, Function.comp_def]
  rw [hf]
  simp [hlbl]

theorem mem_regInitR {q : InstDesc} (f : ℕ) :
    f ∈ regInitR q ↔ StP q.initList.toFinset f ∨ f = fRoot (rootName q) := by
  simp [regInitR, StP, fSt, fRoot, eq_comm]

/-! ### Completeness -/

section Complete

variable {d : DomDesc} {q : InstDesc} {W : ℕ}

theorem simA_add {k : ℕ} {e : MethodDesc} (hk : d.methods[k]? = some e) {σ : Finset ℕ}
    {M0 : Multiset (Bool × ℕ)} (hfin : ∀ l, (M0 + (body e : Multiset (Bool × ℕ))).count l < 2 ^ W) :
    ∀ n p, p + n = (body e).length → ∀ s,
      Rep (labs d) W σ (M0 + ((body e).take p : Multiset (Bool × ℕ))) (· = fI (kCtl k p)) s →
      ∃ s', ReachTbl (uoTbl d W) s s' ∧
        Rep (labs d) W σ (M0 + (body e : Multiset (Bool × ℕ)))
          (· = fI (kCtl k (body e).length)) s' := by
  have he : e ∈ d.methods := List.mem_of_getElem? hk
  intro n
  induction n with
  | zero =>
    intro p hp s hs
    have : p = (body e).length := by omega
    subst this
    exact ⟨s, Relation.ReflTransGen.refl, by simpa using hs⟩
  | succ n ih =>
    intro p hp s hs
    have hpl : p < (body e).length := by omega
    have hget : (body e)[p]? = some (body e)[p] := List.getElem?_eq_getElem hpl
    have htake : (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ)) =
        (body e)[p] ::ₘ ((body e).take p : Multiset (Bool × ℕ)) := by
      rw [List.take_add_one, hget, Option.toList_some, ← Multiset.coe_add, add_comm]
      rfl
    have hlL : (body e)[p] ∈ labs d := body_mem_labs he (List.getElem_mem hpl)
    have hcnt : ((M0 + ((body e).take p : Multiset (Bool × ℕ))).count (body e)[p]) + 1 < 2 ^ W := by
      have hle : (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ)) ≤ (body e : Multiset _) :=
        Multiset.coe_le.2 (List.take_sublist _ _).subperm
      have h1 : (M0 + (((body e).take (p + 1) : List _) : Multiset (Bool × ℕ))).count (body e)[p]
          ≤ (M0 + (body e : Multiset (Bool × ℕ))).count (body e)[p] :=
        Multiset.count_le_of_le _ (by gcongr)
      rw [htake, Multiset.add_cons, Multiset.count_cons_self] at h1
      exact lt_of_le_of_lt h1 (hfin _)
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_zero hcnt
    have hr : addRow k p (body e)[p] i ∈ uoTbl d W :=
      mem_uoTbl.2 (Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inl ⟨p, _, hget, i, hi, rfl⟩)⟩)))
    have hpre := (add_pre hs (ctlOK_ctl k p) k p (body e)[p] i).2 ⟨rfl, hlL, hi, hlow, hb⟩
    have hpost := add_post hs hlL hi hlow hb (fun f => mem_applyRow)
    rw [← Multiset.add_cons, ← htake] at hpost
    obtain ⟨s', hs', hrep⟩ := ih (p + 1) (by omega) _ hpost
    exact ⟨s', Relation.ReflTransGen.head (stepTbl_applyRow hr hpre) hs', hrep⟩

theorem simA_step {σ σ' : Finset ℕ} {M M' : Multiset (Bool × ℕ)} {s : List ℕ}
    (h : Rep (labs d) W σ M (· = fI kIdle) s) (hst : Step (uoSys d q) (σ, M) (σ', M'))
    (hcnt : ∀ l, M'.count l < 2 ^ W) :
    ∃ s', ReachTbl (uoTbl d W) s s' ∧ Rep (labs d) W σ' M' (· = fI kIdle) s' := by
  cases hst with
  | dec _ _ c β hc hm =>
    obtain ⟨e, he, rfl, rfl⟩ := hm
    obtain ⟨k, hk⟩ : ∃ k, d.methods[k]? = some e := List.mem_iff_getElem?.1 he
    have hpos : 0 < M.count (true, e.1) := Multiset.count_pos.2 hc
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_one hpos (h.2.1 _)
    have hL := head_mem_labs he
    have hr : decRow k e i ∈ uoTbl d W :=
      mem_uoTbl.2 (Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inl ⟨i, hi, rfl⟩⟩)))
    have hpre := (dec_pre h ctlOK_idle k e i).2 ⟨rfl, hL, hi, hlow, hb⟩
    have h1 := dec_post h k e hL hi hlow hb (fun f => mem_applyRow)
    have h1' : Rep (labs d) W σ (M.erase (true, e.1) + (((body e).take 0 : List _) :
        Multiset (Bool × ℕ))) (· = fI (kCtl k 0)) (applyRow (decRow k e i) s) := by
      simpa using h1
    obtain ⟨s2, hs2, hrep2⟩ := simA_add hk hcnt (body e).length 0 (by simp) _ h1'
    have hr2 : endRow k (body e).length ∈ uoTbl d W :=
      mem_uoTbl.2 (Or.inr (Or.inr (Or.inl ⟨k, e, hk, Or.inr (Or.inr rfl)⟩)))
    have hpre2 := (end_pre hrep2 k _).2 rfl
    have h3 := end_post hrep2 (fun f => mem_applyRow)
    exact ⟨_, (Relation.ReflTransGen.head (stepTbl_applyRow hr hpre) hs2).tail
      (stepTbl_applyRow hr2 hpre2), h3⟩
  | exe _ _ a ha happ =>
    have hpos : 0 < M.count (false, a) := Multiset.count_pos.2 ha
    obtain ⟨i, hi, hlow, hb⟩ := Counter.exists_low_one hpos (h.2.1 _)
    have hL := h.1 _ ha
    have hr : exeRow d (false, a) i ∈ uoTbl d W :=
      mem_uoTbl.2 (Or.inr (Or.inl ⟨_, hL, rfl, i, hi, rfl⟩))
    have hpre := (exe_pre h ctlOK_idle d (false, a) i).2 ⟨rfl, ⟨hL, hi, hlow, hb⟩, happ⟩
    exact ⟨_, Relation.ReflTransGen.single (stepTbl_applyRow hr hpre),
      exe_post h d hL hi hlow hb (fun f => mem_applyRow)⟩

theorem simA_run {m : ℕ} {x y : Cfg} (hr : ReachIn (uoSys d q) m x y) :
    ∀ s, Rep (labs d) W x.1 x.2 (· = fI kIdle) s →
      Multiset.card x.2 + m * maxBody d < 2 ^ W →
      ∃ s', ReachTbl (uoTbl d W) s s' ∧ Rep (labs d) W y.1 y.2 (· = fI kIdle) s' := by
  induction hr with
  | refl x => exact fun s hs _ => ⟨s, Relation.ReflTransGen.refl, hs⟩
  | @step n x y z hst _ ih =>
    intro s hs hb
    have hcy : Multiset.card y.2 ≤ Multiset.card x.2 + 1 * maxBody d :=
      card_le_of_reachIn (closed_uoSys d q) (ReachIn.step hst (ReachIn.refl _))
    have hcnt : ∀ l, y.2.count l < 2 ^ W := fun l =>
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by rw [Nat.succ_mul] at hb; omega)
    obtain ⟨s1, h1, r1⟩ := simA_step hs hst hcnt
    obtain ⟨s2, h2, r2⟩ := ih s1 r1 (by rw [Nat.succ_mul] at hb; omega)
    exact ⟨s2, h1.trans h2, r2⟩

theorem solvableTbl_of_solvable (hd : d.MethodsUO) (hq : q.IsRooted)
    (hW : uoBndP d q * maxBody d + 1 < 2 ^ W) (h : Solvable d q) :
    SolvableTbl (uoTbl d W) (regInitR q) (regGoalR q) := by
  have hW0 : 0 < W := by
    rcases Nat.eq_zero_or_pos W with rfl | h
    · simp at hW
    · exact h
  obtain ⟨m, hm, y, hy, hg⟩ := (solvable_iff_short_uo hd hq.isUO).1 h
  rw [uoAbs_initConfig_rooted hq] at hy
  have hroot : ∃ e ∈ d.methods, e.1 = rootName q := by
    cases hy with
    | refl => exact absurd hg.1 (by simp)
    | step hst _ =>
      cases hst with
      | dec _ _ c β hc hm' =>
        obtain ⟨e, he, hec, -⟩ := hm'
        refine ⟨e, he, ?_⟩
        rw [hec]
        simpa using hc
      | exe _ _ a ha _ => simp at ha
  obtain ⟨e, he, hec⟩ := hroot
  have hL : (true, rootName q) ∈ labs d := hec ▸ head_mem_labs he
  have hr0 : startRow (labs d) W (rootName q) ∈ uoTbl d W :=
    mem_uoTbl.2 (Or.inl ⟨e, he, by rw [hec]⟩)
  have hpre0 := (start_pre mem_regInitR (labs d) W (rootName q)).2 rfl
  have h0 := start_post mem_regInitR hL hW0 (fun f => mem_applyRow)
  have hmb : m * maxBody d ≤ uoBndP d q * maxBody d := Nat.mul_le_mul_right _ hm
  obtain ⟨s1, hs1, hrep1⟩ := simA_run hy _ h0 (by simp; omega)
  obtain ⟨hy0, hgy⟩ := hg
  have hfpre := (fin_pre hrep1 ctlOK_idle).2 ⟨rfl, fun l _ => by simp [hy0]⟩
  have hfin := fin_post hrep1 (fun f => mem_applyRow)
  refine ⟨_, (Relation.ReflTransGen.head (stepTbl_applyRow hr0 hpre0) hs1).tail
    (stepTbl_applyRow (mem_uoTbl.2 (Or.inr (Or.inr (Or.inr rfl)))) hfpre), ?_⟩
  intro f hf
  simp only [regGoalR, List.mem_append, List.mem_map, List.mem_singleton] at hf
  rcases hf with ⟨v, hv, rfl⟩ | rfl
  · exact (hfin.mem_fSt ctlOK_done v).2 (hgy v hv)
  · exact hfin.mem_done.2 rfl

end Complete

/-! ### Soundness -/

section Sound

variable {d : DomDesc} {q : InstDesc} {W : ℕ}

/-- Abstract reachability from the initial configuration of a rooted instance. -/
def AR (d : DomDesc) (q : InstDesc) (z : Cfg) : Prop :=
  Relation.ReflTransGen (Step (uoSys d q)) (q.initList.toFinset, {(true, rootName q)}) z

theorem reachIn_of_rtg {S : Sys} {x y : Cfg} (h : Relation.ReflTransGen (Step S) x y) :
    ∃ m, ReachIn S m x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, ReachIn.refl _⟩
  | head hxy _ ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, ReachIn.step hxy hm⟩

/-- **The invariant of the reachable table states.** -/
def Inv (d : DomDesc) (q : InstDesc) (W : ℕ) (s : List ℕ) : Prop :=
  (∀ f, f ∈ s ↔ StP q.initList.toFinset f ∨ f = fRoot (rootName q)) ∨
  (∃ σ M, AR d q (σ, M) ∧ Rep (labs d) W σ M (· = fI kIdle) s) ∨
  (∃ σ M k e p, d.methods[k]? = some e ∧ p ≤ (body e).length ∧
    AR d q (σ, M + ((body e).drop p : Multiset (Bool × ℕ))) ∧
    Rep (labs d) W σ M (· = fI (kCtl k p)) s) ∨
  (∃ σ, AR d q (σ, 0) ∧ Rep (labs d) W σ 0 (· = fDone) s)

theorem not_fI_mem_start {s : List ℕ} {σ : Finset ℕ} {c : ℕ}
    (hs : ∀ f, f ∈ s ↔ StP σ f ∨ f = fRoot c) (k : ℕ) : fI k ∉ s := by
  rw [hs]
  rintro (⟨v, -, hv⟩ | hv)
  · exact fI_ne_fSt _ _ hv
  · exact fI_ne_fRoot _ _ hv

theorem count_pos_of_testBit {n i : ℕ} (h : n.testBit i = true) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · exact hn

theorem inv_step (hW : 0 < W) {s s' : List ℕ} (hs : Inv d q W s) (h : StepTbl (uoTbl d W) s s') :
    Inv d q W s' := by
  obtain ⟨r, hr, hpre, hs'⟩ := h
  rcases hs with hs0 | ⟨σ, M, har, hrep⟩ | ⟨σ, M, k, e, p, hk, hp, har, hrep⟩ | ⟨σ, har, hrep⟩
  · -- the initial state: only a start row applies
    rcases mem_uoTbl.1 hr with ⟨e, he, rfl⟩ | ⟨l, hlL, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p, l, hp, i, hi, rfl⟩ | rfl)⟩ | rfl
    · have hc := (start_pre hs0 (labs d) W e.1).1 hpre
      rw [hc] at hs'
      have hL : (true, rootName q) ∈ labs d := hc ▸ head_mem_labs he
      exact Or.inr (Or.inl ⟨_, _, Relation.ReflTransGen.refl, start_post hs0 hL hW hs'⟩)
    · exact absurd (hpre (fI kIdle) (by simp [exeRow])) (not_fI_mem_start hs0 _)
    · exact absurd (hpre (fI kIdle) (by simp [decRow])) (not_fI_mem_start hs0 _)
    · exact absurd (hpre (fI (kCtl k p)) (by simp [addRow])) (not_fI_mem_start hs0 _)
    · exact absurd (hpre (fI (kCtl k (body e).length)) (by simp [endRow])) (not_fI_mem_start hs0 _)
    · exact absurd (hpre (fI kIdle) (by simp [finRow])) (not_fI_mem_start hs0 _)
  · -- idle
    rcases mem_uoTbl.1 hr with ⟨e, he, rfl⟩ | ⟨⟨b, a⟩, hlL, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p, l, hp, i, hi, rfl⟩ | rfl)⟩ | rfl
    · have := (hrep.mem_root _).1 (hpre (fRoot e.1) (by simp [startRow]))
      exact absurd this (fRoot_ne_fI _ _)
    · obtain rfl : b = false := hl1
      obtain ⟨-, ⟨hlL', hi', hlow, hb⟩, happ⟩ := (exe_pre hrep ctlOK_idle d (false, a) i).1 hpre
      have hmem : (false, a) ∈ M := Multiset.count_pos.1 (count_pos_of_testBit hb)
      exact Or.inr (Or.inl ⟨_, _, har.tail (Step.exe σ M a hmem happ),
        exe_post hrep d hlL' hi' hlow hb hs'⟩)
    · obtain ⟨-, hL, hi', hlow, hb⟩ := (dec_pre hrep ctlOK_idle k e i).1 hpre
      have hmem : (true, e.1) ∈ M := Multiset.count_pos.1 (count_pos_of_testBit hb)
      have he : e ∈ d.methods := List.mem_of_getElem? hk
      refine Or.inr (Or.inr (Or.inl ⟨σ, _, k, e, 0, hk, Nat.zero_le _, ?_,
        dec_post hrep k e hL hi' hlow hb hs'⟩))
      simpa using har.tail (Step.dec σ M e.1 _ hmem ⟨e, he, rfl, rfl⟩)
    · have := (add_pre hrep ctlOK_idle k p l i).1 hpre
      simp at this
    · have := (end_pre hrep k _).1 hpre
      simp at this
    · obtain ⟨-, hz⟩ := (fin_pre hrep ctlOK_idle).1 hpre
      have hM : M = 0 := Multiset.eq_zero_of_forall_notMem fun x hx =>
        (Multiset.count_pos.2 hx).ne' (hz x (hrep.1 x hx))
      subst hM
      exact Or.inr (Or.inr (Or.inr ⟨σ, har, fin_post hrep hs'⟩))
  · -- in the middle of unfolding method `k`
    rcases mem_uoTbl.1 hr with ⟨e', he', rfl⟩ | ⟨l, hlL, hl1, i, hi, rfl⟩ |
      ⟨k', e', hk', (⟨i, hi, rfl⟩ | ⟨p', l, hp', i, hi, rfl⟩ | rfl)⟩ | rfl
    · have := (hrep.mem_root _).1 (hpre (fRoot e'.1) (by simp [startRow]))
      exact absurd this (fRoot_ne_fI _ _)
    · have := (exe_pre hrep (ctlOK_ctl k p) d l i).1 hpre
      simp at this
    · have := (dec_pre hrep (ctlOK_ctl k p) k' e' i).1 hpre
      simp at this
    · obtain ⟨hC, hlL, hi', hlow, hb⟩ := (add_pre hrep (ctlOK_ctl k p) k' p' l i).1 hpre
      obtain ⟨rfl, rfl⟩ : k' = k ∧ p' = p := by simpa using hC
      obtain rfl : e' = e := Option.some_injective _ (hk'.symm.trans hk)
      have hpl : p' < (body e').length := by
        by_contra hcon
        rw [List.getElem?_eq_none (by omega)] at hp'
        exact absurd hp' (by simp)
      have hl : (body e')[p'] = l := by
        rw [List.getElem?_eq_getElem hpl] at hp'
        exact Option.some_injective _ hp'
      refine Or.inr (Or.inr (Or.inl ⟨σ, _, k', e', p' + 1, hk', hpl, ?_,
        add_post hrep hlL hi' hlow hb hs'⟩))
      rw [List.drop_eq_getElem_cons hpl, hl] at har
      have heq : M + ((l :: List.drop (p' + 1) (body e') : List _) : Multiset (Bool × ℕ)) =
          (l ::ₘ M) + (List.drop (p' + 1) (body e') : Multiset (Bool × ℕ)) := by
        rw [← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]
      rwa [heq] at har
    · have hC := (end_pre hrep k' _).1 hpre
      obtain ⟨rfl, hpe⟩ : k' = k ∧ (body e').length = p := by simpa using hC
      obtain rfl : e' = e := Option.some_injective _ (hk'.symm.trans hk)
      rw [← hpe, List.drop_length] at har
      exact Or.inr (Or.inl ⟨σ, M, by simpa using har, end_post (hpe ▸ hrep) hs'⟩)
    · have := (fin_pre hrep (ctlOK_ctl k p)).1 hpre
      simp at this
  · -- final state: nothing applies
    exfalso
    rcases mem_uoTbl.1 hr with ⟨e, he, rfl⟩ | ⟨l, hlL, hl1, i, hi, rfl⟩ |
      ⟨k, e, hk, (⟨i, hi, rfl⟩ | ⟨p, l, hp, i, hi, rfl⟩ | rfl)⟩ | rfl
    · have := (hrep.mem_root _).1 (hpre (fRoot e.1) (by simp [startRow]))
      exact fRoot_ne_fDone _ this
    · have := (exe_pre hrep ctlOK_done d l i).1 hpre
      exact fI_ne_fDone _ this.1
    · have := (dec_pre hrep ctlOK_done k e i).1 hpre
      exact fI_ne_fDone _ this.1
    · have := (add_pre hrep ctlOK_done k p l i).1 hpre
      exact fI_ne_fDone _ this.1
    · have := (end_pre hrep k _).1 hpre
      exact fI_ne_fDone _ this
    · have := (fin_pre hrep ctlOK_done).1 hpre
      exact fI_ne_fDone _ this.1

theorem inv_reach (hW : 0 < W) {s : List ℕ} (h : ReachTbl (uoTbl d W) (regInitR q) s) :
    Inv d q W s := by
  induction h with
  | refl => exact Or.inl mem_regInitR
  | tail _ hst ih => exact inv_step hW ih hst

theorem solvable_of_solvableTbl (hd : d.MethodsUO) (hq : q.IsRooted) (hW : 0 < W)
    (h : SolvableTbl (uoTbl d W) (regInitR q) (regGoalR q)) : Solvable d q := by
  obtain ⟨s, hr, hg⟩ := h
  have h0 : fDone ∈ s := hg 0 (by simp [regGoalR])
  rcases inv_reach hW hr with hs0 | ⟨σ, M, -, hrep⟩ | ⟨σ, M, k, e, p, -, -, -, hrep⟩ | ⟨σ, har, hrep⟩
  · rcases (hs0 fDone).1 h0 with ⟨v, -, hv⟩ | hv
    · exact absurd hv (fDone_ne_fSt _)
    · exact absurd hv (fDone_ne_fRoot _)
  · exact absurd (hrep.mem_done.1 h0) (fDone_ne_fI _)
  · exact absurd (hrep.mem_done.1 h0) (fDone_ne_fI _)
  · have hgoal : IsGoal (uoSys d q) (σ, 0) := ⟨rfl, fun f hf =>
      (hrep.mem_fSt ctlOK_done f).1 (hg (fSt f) (by simp [regGoalR, fSt, hf]))⟩
    obtain ⟨m, hm⟩ := reachIn_of_rtg har
    rw [← uoAbs_initConfig_rooted hq] at hm
    obtain ⟨cs, hcs, -, hend⟩ := ppath_of_reachIn hd hm (uoInv_initConfig hq.isUO) rfl
    exact solvable_of_pReach (pReach_of_ppath hcs) (isGoalB_iff_uo.2 (hend ▸ hgoal))

end Sound

/-- **The unordered-HTN action table decides plan existence.** -/
theorem solvable_iff_solvableTbl {d : DomDesc} {q : InstDesc} {W : ℕ} (hd : d.MethodsUO)
    (hq : q.IsRooted) (hW : uoBndP d q * maxBody d + 1 < 2 ^ W) :
    Solvable d q ↔ SolvableTbl (uoTbl d W) (regInitR q) (regGoalR q) := by
  have hW0 : 0 < W := by
    rcases Nat.eq_zero_or_pos W with rfl | h
    · simp at hW
    · exact h
  exact ⟨solvableTbl_of_solvable hd hq hW, solvable_of_solvableTbl hd hq hW0⟩

end UOTbl

end HTN
