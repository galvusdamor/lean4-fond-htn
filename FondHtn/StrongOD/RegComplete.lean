import FondHtn.StrongOD.RegSound
/-!
# Completeness of the search for regular problems

A belief-set sequence (`FOND.SOD.NW`) is replayed by the search: belief sets are restricted to
states over the facts `factsU p` of the description (`FOND.SOD.bsw_restrictU`) and written as
the list of the sublists of `factsU p` denoting them (`FOND.SOD.rep`); every block is checked
state by state, each by a depth-first evaluation of polynomial stack size
(`HTN.Syn.PolyDom.dfs_complete`).  All configurations of the run respect the bounds of
`FOND.SOD.RBounds`.
-/

namespace FOND

open HTN HTN.Syn HTN.Syn.PolyDom HTN.Article HTN.Article.NoHTN PTime FOND.Prim

namespace SOD

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

variable {p : FProbDesc}

/-! ## Restricting belief sets to the facts of the description -/

/-- The states over the facts of the description. -/
def PU (p : FProbDesc) : Set (Set ℕ) := {X | ∀ f ∈ X, f ∈ factsU p}

theorem outcomes_PU {a : ℕ} {s s' : Set ℕ} (hs : s ∈ PU p)
    (h : s' ∈ (p.toProblem.δ a).outcomes s) : s' ∈ PU p := by
  change s' ∈ (p.δ a).outcomes s at h
  rw [δ_eq_actL, Action.mem_outcomes] at h
  obtain ⟨_, ⟨e, he, rfl⟩, rfl⟩ := h
  intro f hf
  rcases hf with ⟨hf, -⟩ | hf
  · exact hs f hf
  · exact add_mem_factsU he hf

theorem bsw_restrictU {W : Set (Set ℕ)} {tn : TaskNetwork ℕ ℕ ℕ} {s : Set ℕ}
    (h : BSW p.toProblem W tn s) : s ∈ PU p → BSW p.toProblem (W ∩ PU p) tn s := by
  induction h with
  | empty h hs => exact fun hU => .empty h ⟨hs, hU⟩
  | step hu hα happ _ ih =>
    exact fun hU => .step hu hα happ fun s' hs' => ih s' hs' (outcomes_PU hU hs')

theorem nw_anti {o : List ℕ} {S : Set (Set ℕ)} (h : NW p o S) {S₀ : Set (Set ℕ)}
    (hS : S₀ ⊆ S) : NW p o S₀ := by
  cases h with
  | nil => exact .nil _
  | cons he hc hreg hblk hn => exact .cons he hc hreg (fun s hs => hblk s (hS hs)) hn

/-- **The list of a belief set over the facts of the description.** -/
noncomputable def rep (p : FProbDesc) (S : Set (Set ℕ)) : List (List ℕ) := by
  classical
  exact (factsU p).sublists.filter fun w => decide ({f | f ∈ w} ∈ S)

theorem mem_rep {S : Set (Set ℕ)} {w : List ℕ} :
    w ∈ rep p S ↔ w.Sublist (factsU p) ∧ {f | f ∈ w} ∈ S := by
  classical
  simp [rep, List.mem_sublists]

theorem setW_rep {S : Set (Set ℕ)} (hS : S ⊆ PU p) : setW (rep p S) = S := by
  classical
  ext X
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_rep.1 hw).2
  · intro hX
    refine ⟨(factsU p).filter fun f => decide (f ∈ X), mem_rep.2 ⟨List.filter_sublist, ?_⟩, ?_⟩
    · have : {f | f ∈ (factsU p).filter fun f => decide (f ∈ X)} = X := by
        ext f; simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨hS hX f h, h⟩⟩
      rw [this]; exact hX
    · ext f; simp only [Set.mem_setOf_eq, List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => ⟨hS hX f h, h⟩, fun h => h.2⟩

theorem mem_PU_of_sublist {w : List ℕ} (hw : w.Sublist (factsU p)) : {f | f ∈ w} ∈ PU p :=
  fun _ hf => hw.subset hf

/-! ## Sizes -/

/-- The bound on the stack of the depth-first evaluation of a block game. -/
def stackBound (n : ℕ) : ℕ :=
  2 * (4 * n + 1 + cfgBound n) + 3 +
    (2 * n) * dfsCost (n * (2 * cfgBound n + 2) + 1) (4 * n + 1)

theorem bgameReach_sGood {W : List (List ℕ)} : ∀ (m : ℕ) (c c' : GCfg), SGood p c →
    GameReach bsuccs (p, W) m c c' → SGood p c' := by
  intro m
  induction m with
  | zero => rintro c c' hc rfl; exact hc
  | succ m ih =>
    rintro c c' hc ⟨c₁, h₁, hr⟩
    exact ih c₁ c' (sGood_succ hc h₁) hr

theorem sz_primD_le (t : TnDesc) : sz (primD t) ≤ sz t := by
  obtain ⟨i, o, l⟩ := t
  simp only [primD, sz_prod, TnDesc.ids, TnDesc.ordList, TnDesc.lbl]
  have h1 := sz_filter_le i (primB (i, o, l))
  have h2 := sz_le_of_sublist' (List.dedup_sublist
    (o.filter fun q => primB (i, o, l) q.1 && primB (i, o, l) q.2))
  have h3 := sz_filter_le o (fun q => primB (i, o, l) q.1 && primB (i, o, l) q.2)
  have h4 := sz_filter_le l (fun q : ℕ × Bool × ℕ => !q.2.1)
  omega

theorem sz_dedup_le (l : List ℕ) : sz l.dedup ≤ sz l := sz_le_of_sublist' (List.dedup_sublist l)

/-- The root of a block game is well sized. -/
theorem sGood_root {w : List ℕ} (hw : ∀ f ∈ w, f ∈ factsU p) {B : TnDesc} (hB : sz B ≤ sz p) :
    SGood p ((0 : ℕ), (0 : ℕ), w.dedup, B) := by
  have h6 := six_le_sz p
  exact ⟨Nat.zero_le _, by simp [sz_nat]; omega, List.nodup_dedup _,
    fun f hf => hw f (List.mem_dedup.1 hf), hB⟩

theorem sz_le_two_mul (k : ℕ) : sz k ≤ 2 * k + 1 := sz_nat_le k

/-- **The depth-first evaluation of a won block game, with polynomial stacks.** -/
theorem block_dfs {W : List (List ℕ)} {w : List ℕ} (hw : ∀ f ∈ w, f ∈ factsU p) {B : TnDesc}
    (hB : sz B ≤ sz p) (hinv : ∀ s : List ℕ, s.Nodup → CfgInv (s, B))
    (hbsw : BSW p.toProblem (setW W) (cfgNet B) {f | f ∈ w}) :
    Relation.ReflTransGen (fun S S' => dfsStep bacc buni bsuccs ((p, W), S, S') = true ∧
      sz S' ≤ stackBound (sz p)) [(2 * B.ids.length, ((0 : ℕ), (0 : ℕ), w.dedup, B))] [] := by
  set n := sz p
  have hk : 2 * B.ids.length ≤ 2 * n := by
    have := (length_le_sz B.ids).trans ((sz_ids_le_d B).trans hB); omega
  have hwin := block_complete hbsw (2 * B.ids.length) 0 w.dedup B (sameOn_refl _)
    (setOf_mem_dedup _).symm (hinv _ (List.nodup_dedup _)) le_rfl
  refine dfs_complete (B := n * (2 * cfgBound n + 2) + 1) (K := 4 * n + 1) _ _ [] hwin
    (fun k' hk' => (sz_le_two_mul k').trans (by omega)) (fun m _ c' hr => ?_) ?_
  · exact sz_gsuccs_le (bgameReach_sGood m _ c' (sGood_root hw hB) hr)
  · rw [sz_nil]
    have := Nat.mul_le_mul_right (dfsCost (n * (2 * cfgBound n + 2) + 1) (4 * n + 1)) hk
    unfold stackBound
    omega

theorem sz_root_le {w : List ℕ} (hw : ∀ f ∈ w, f ∈ factsU p) {B : TnDesc} (hB : sz B ≤ sz p) :
    sz [(2 * B.ids.length, ((0 : ℕ), (0 : ℕ), w.dedup, B))] ≤ stackBound (sz p) := by
  have h1 := sz_le_of_sGood (sGood_root hw hB)
  have hk : 2 * B.ids.length ≤ 2 * sz p := by
    have := (length_le_sz B.ids).trans ((sz_ids_le_d B).trans hB); omega
  have h2 := (sz_le_two_mul (2 * B.ids.length)).trans (show 2 * (2 * B.ids.length) + 1 ≤ 4 * sz p + 1
    by omega)
  rw [sz_cons, sz_nil, sz_prod]
  unfold stackBound
  omega

/-! ## Size bounds of the fields -/

/-- The bound on the name lists. -/
def ccB (m : ℕ) : ℕ := m * (2 * (m + 1) + 2) + 1

theorem ccB_mono {a b : ℕ} (h : a ≤ b) : ccB a ≤ ccB b := by
  unfold ccB; have := Nat.mul_le_mul h (show 2 * (a + 1) + 2 ≤ 2 * (b + 1) + 2 by omega); omega

theorem sz_lbl_le (t : TnDesc) : sz t.lbl ≤ sz t := by
  have := sz_snd_le t.2
  have := sz_snd_le t
  simp only [TnDesc.lbl] at *
  omega

theorem sz_lblOf_snd_le (t : TnDesc) (x : ℕ) : sz (lblOf t x).2 ≤ sz t + 1 := by
  cases hl : t.lbl.lookup x with
  | none => rw [lblOf_none hl]; simp [sz_nat]
  | some v =>
    rw [lblOf_some hl]
    have h1 := sz_le_of_mem (mem_of_lookup_eq_some hl)
    have h2 := sz_lbl_le t
    rw [sz_prod] at h1
    have := sz_snd_le v
    omega

theorem sz_compL_le (t : TnDesc) : sz (compL t) ≤ ccB (sz t) := by
  have h := sz_list_le (compL t) (sz t + 1) fun c hc => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
    exact sz_lblOf_snd_le t x
  have hl : (compL t).length ≤ sz t := by
    simp only [compL, List.length_map]
    exact (List.length_filter_le _ _).trans ((length_le_sz _).trans (sz_ids_le_d t))
  have := Nat.mul_le_mul_right (2 * (sz t + 1) + 2) hl
  unfold ccB; omega

theorem sz_method_le {e : MethodDesc} (he : e ∈ p.methods) : sz e.2 ≤ sz p := by
  have h1 := sz_le_of_mem he
  have h2 := sz_methods_le p
  have := sz_snd_le e
  omega

theorem sz_rep_le (S : Set (Set ℕ)) : sz (rep p S) ≤ sz (factsU p).sublists := by
  classical
  exact sz_filter_le _ _

/-- The bound on the lists of states. -/
def lsB (p : FProbDesc) : ℕ := sz (factsU p).sublists + 4 * sz p + 3

/-- The bound on the configurations, given the certificate `r`. -/
def cfgB (p : FProbDesc) (r : List ℕ) : ℕ :=
  sz r + 3 + 2 * ccB (sz p) + sz p + 3 * lsB p + stackBound (sz p)

theorem sz_cfg_le {r cur : List ℕ} {ph : ℕ} {S S' R : List (List ℕ)} {B : TnDesc} {nx : List ℕ}
    {st : List (ℕ × GCfg)} (hph : ph ≤ 1) (hcur : sz cur ≤ ccB (sz p)) (hS : sz S ≤ lsB p)
    (hB : sz B ≤ sz p) (hnx : sz nx ≤ ccB (sz p)) (hS' : sz S' ≤ lsB p) (hR : sz R ≤ lsB p)
    (hst : sz st ≤ stackBound (sz p)) :
    sz ((r, (ph, cur, S, B, nx, S', R, st)) : RCfg) ≤ cfgB p r := by
  have := (sz_nat_le ph).trans (show 2 * ph + 1 ≤ 3 by omega)
  simp only [sz_prod, cfgB]
  omega

/-! ## Runs -/

/-- The bounded step relation of the search. -/
def BR (p : FProbDesc) (L : ℕ) (c c' : RCfg) : Prop := sz c' < L ∧ rstep (p, c, c') = true

section Run

variable {L : ℕ} {r : List ℕ} (hL : cfgB p r < L)
include hL

theorem lift_dfs {cur nx : List ℕ} {S LS' R : List (List ℕ)} {B : TnDesc}
    (hcur : sz cur ≤ ccB (sz p)) (hS : sz S ≤ lsB p) (hB : sz B ≤ sz p)
    (hnx : sz nx ≤ ccB (sz p)) (hS' : sz LS' ≤ lsB p) (hR : sz R ≤ lsB p)
    {st₀ st₁ : List (ℕ × GCfg)}
    (h : Relation.ReflTransGen (fun S S' => dfsStep bacc buni bsuccs ((p, LS'), S, S') = true ∧
      sz S' ≤ stackBound (sz p)) st₀ st₁) :
    Relation.ReflTransGen (BR p L) (r, (1, cur, S, B, nx, LS', R, st₀))
      (r, (1, cur, S, B, nx, LS', R, st₁)) := by
  refine Relation.ReflTransGen.lift (fun st => ((r, (1, cur, S, B, nx, LS', R, st)) : RCfg))
    (fun a b hab => ⟨lt_of_le_of_lt (sz_cfg_le le_rfl hcur hS hB hnx hS' hR hab.2) hL, ?_⟩) h
  have hne : a ≠ [] := by
    rintro rfl; simp [dfsStep_nil] at hab
  have hd : dfsB p (1, cur, S, B, nx, LS', R, a) (1, cur, S, B, nx, LS', R, b) = true := by
    simp only [dfsB, Bool.and_eq_true, hab.1, decide_true, beq_self_eq_true, and_true, true_and]
    simpa using hne
  simp [rstep, hd]

theorem block_run {cur nx : List ℕ} {S LS' : List (List ℕ)} {B : TnDesc}
    (hcur : sz cur ≤ ccB (sz p)) (hS : sz S ≤ lsB p) (hB : sz B ≤ sz p)
    (hnx : sz nx ≤ ccB (sz p)) (hS' : sz LS' ≤ lsB p)
    (hinv : ∀ s : List ℕ, s.Nodup → CfgInv (s, B)) :
    ∀ R : List (List ℕ), (∀ w ∈ R, (∀ f ∈ w, f ∈ factsU p) ∧
      BSW p.toProblem (setW LS') (cfgNet B) {f | f ∈ w}) → sz R ≤ lsB p →
      Relation.ReflTransGen (BR p L) (r, (1, cur, S, B, nx, LS', R, []))
        (r, (1, cur, S, B, nx, LS', [], [])) := by
  intro R
  induction R with
  | nil => exact fun _ _ => Relation.ReflTransGen.refl
  | cons w R ih =>
    intro hR hsz
    have hRs : sz R ≤ lsB p := by rw [sz_cons] at hsz; omega
    have hw := hR w List.mem_cons_self
    refine Relation.ReflTransGen.head (b := (r, (1, cur, S, B, nx, LS', R,
      [(2 * B.ids.length, ((0 : ℕ), (0 : ℕ), w.dedup, B))]))) ⟨?_, ?_⟩ ?_
    · exact lt_of_le_of_lt (sz_cfg_le le_rfl hcur hS hB hnx hS' hRs (sz_root_le hw.1 hB)) hL
    · simp [rstep, loadB]
    · exact (lift_dfs hL hcur hS hB hnx hS' hRs (block_dfs hw.1 hB hinv hw.2)).trans
        (ih (fun w' hw' => hR w' (List.mem_cons_of_mem _ hw')) hRs)

theorem nw_run (hp : p.Valid) {o : List ℕ} {S : Set (Set ℕ)} (hn : NW p o S) :
    ∀ S₀ ⊆ S, S₀ ⊆ PU p → ∀ B : TnDesc, sz B ≤ sz p → sz o ≤ ccB (sz p) →
      ∃ z, Relation.ReflTransGen (BR p L) (r, (0, o, rep p S₀, B, o, rep p S₀, [], [])) z ∧
        racc (p, z) = true := by
  induction hn with
  | nil S => exact fun _ _ _ _ _ _ => ⟨_, Relation.ReflTransGen.refl, rfl⟩
  | @cons c e S S' he hc hreg hblk _ ih =>
    intro S₀ hS₀ hS₀U B hB ho
    have hS₀sz : sz (rep p S₀) ≤ lsB p := (sz_rep_le S₀).trans (by unfold lsB; omega)
    set S'' := S' ∩ PU p with hS''
    have hS''sz : sz (rep p S'') ≤ lsB p := (sz_rep_le S'').trans (by unfold lsB; omega)
    have hBe : sz (primD e.2) ≤ sz p := (sz_primD_le _).trans (sz_method_le he)
    have hce : sz (compL e.2) ≤ ccB (sz p) := (sz_compL_le _).trans (ccB_mono (sz_method_le he))
    have hinv : ∀ s : List ℕ, s.Nodup → CfgInv (s, primD e.2) :=
      fun s hs => inv_primD_valid (hp.methods e he) hs
    have hS''U : S'' ⊆ PU p := Set.inter_subset_right
    obtain ⟨z, hz, hza⟩ := ih S'' Set.inter_subset_left hS''U (primD e.2) hBe hce
    have hnil : sz ([] : List (List ℕ)) ≤ lsB p := by rw [sz_nil]; unfold lsB; omega
    have hnil' : sz ([] : List (ℕ × GCfg)) ≤ stackBound (sz p) := by
      rw [sz_nil]; unfold stackBound; omega
    have hch : chooseB p (0, [c], rep p S₀, B, [c], rep p S₀, [], [])
        (1, [c], rep p S₀, primD e.2, compL e.2, rep p S'', rep p S₀, []) = true := by
      simp only [chooseB, Bool.and_eq_true, beq_self_eq_true, List.any_eq_true,
        decide_eq_true_eq, true_and]
      exact ⟨e, he, ⟨by rw [hc], hreg⟩, rfl⟩
    have hfin : finB (1, [c], rep p S₀, primD e.2, compL e.2, rep p S'', [], [])
        (0, compL e.2, rep p S'', primD e.2, compL e.2, rep p S'', [], []) = true := by
      simp [finB]
    refine ⟨z, Relation.ReflTransGen.head ⟨lt_of_le_of_lt (sz_cfg_le (Nat.le_refl 1) ho hS₀sz hBe
      hce hS''sz hS₀sz hnil') hL, by simp [rstep, hch]⟩ ?_, hza⟩
    refine (block_run hL ho hS₀sz hBe hce hS''sz hinv _ (fun w hw => ⟨fun f hf =>
      (mem_rep.1 hw).1.subset hf, ?_⟩) hS₀sz).trans ?_
    · have hX := hS₀ (mem_rep.1 hw).2
      have := bsw_restrictU (hblk _ hX) (mem_PU_of_sublist (mem_rep.1 hw).1)
      rwa [setW_rep hS''U]
    · exact Relation.ReflTransGen.head ⟨lt_of_le_of_lt (sz_cfg_le (Nat.zero_le 1) hce hS''sz hBe
        hce hS''sz hnil hnil') hL, by simp [rstep, hfin]⟩ hz

end Run

end SOD

end FOND
