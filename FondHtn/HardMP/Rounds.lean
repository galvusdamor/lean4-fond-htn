import FondHtn.HardMP.Encoding
import HtnComplexity.Article.TODPPT
/-!
# One round of the path game down a derivation tree

The reduction from totally ordered (deterministic) HTN planning simulates the dynamic program of
Thm. 4.2.1 (`HTN.Article.dpTab`): a configuration stores a *current triple* `(v, x, v')` — the
start vector `v` (slot `0`), the task name `x` (the current task; `none` is a virtual root task
whose only "method" is the initial task network), and the end vector `v'` (slot `1`).  One
*round* is a program chosen by the policy (`FOND.HardMP.rules`):

* `noop` — only if the flag `done` is set; nothing changes;
* `progM` for a method `e` of the source problem (or the root): the policy checks that the
  current task is `e.1`, guesses vectors `u₀, …, u_k` (slots `2, …, k + 2`, `k` the number of
  subtasks), the program checks `u₀ = v` and `u_k = v'`, nature picks a child `i < k`, and the
  current triple becomes `(u_i, label i, u_{i+1})`; for `k = 0` the flag `done` is set;
* `progA` for an action name `a`: the program checks (bitwise) that `a` is applicable in `v` and
  leads to `v'`, and sets `done`.

The **semantic lemmas** (`FOND.HardMP.round_sound`, `FOND.HardMP.round_complete`): if every
outcome of a round satisfies the invariant `Good` (done, or the current triple is in the table
of the dynamic program), so does the configuration before it; and conversely, a configuration
whose triple is in the `m + 1`-th iterate of the table has a round all of whose outcomes have
their triples in the `m`-th iterate (or are done).
-/

namespace FOND

namespace HardMP

open HTN HTN.Article HTN.Syn

/-! ## Fields -/

/-- The flag `done`. -/
def fDone : ℕ := 0

/-- The selector of child `i`. -/
def fSel (i : ℕ) : ℕ := 2 * i + 1

/-- Bit `j` of slot `k`. -/
def fSlot (k j : ℕ) : ℕ := 2 * Nat.pair k j + 2

@[simp] theorem fSlot_inj {k j k' j' : ℕ} : fSlot k j = fSlot k' j' ↔ k = k' ∧ j = j' := by
  unfold fSlot
  constructor
  · intro h
    have : Nat.pair k j = Nat.pair k' j' := by omega
    exact Nat.pair_eq_pair.1 this
  · rintro ⟨rfl, rfl⟩; rfl

theorem fSel_injective : Function.Injective fSel := fun a b h => by unfold fSel at h; omega

@[simp] theorem fSel_inj {i i' : ℕ} : fSel i = fSel i' ↔ i = i' := fSel_injective.eq_iff

@[simp] theorem fSlot_ne_fSel (k j i : ℕ) : fSlot k j ≠ fSel i := by unfold fSlot fSel; omega
@[simp] theorem fSel_ne_fSlot (k j i : ℕ) : fSel i ≠ fSlot k j := by unfold fSlot fSel; omega
@[simp] theorem fSlot_ne_fDone (k j : ℕ) : fSlot k j ≠ fDone := by unfold fSlot fDone; omega
@[simp] theorem fDone_ne_fSlot (k j : ℕ) : fDone ≠ fSlot k j := by unfold fSlot fDone; omega
@[simp] theorem fSel_ne_fDone (i : ℕ) : fSel i ≠ fDone := by unfold fSel fDone; omega
@[simp] theorem fDone_ne_fSel (i : ℕ) : fDone ≠ fSel i := by unfold fSel fDone; omega

/-- The vector in slot `k` (bits `0, …, n - 1`). -/
def vecC (n : ℕ) (c : Cfg) (k : ℕ) : List Bool := (List.range n).map fun j => c.val (fSlot k j)

@[simp] theorem length_vecC (n : ℕ) (c : Cfg) (k : ℕ) : (vecC n c k).length = n := by
  simp [vecC]

theorem vecC_congr {n : ℕ} {c d : Cfg} {k k' : ℕ}
    (h : ∀ j < n, c.val (fSlot k j) = d.val (fSlot k' j)) : vecC n c k = vecC n d k' :=
  List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

theorem getI_vecC {n : ℕ} {c : Cfg} {k j : ℕ} (hj : j < n) : (vecC n c k).getI j = c.val (fSlot k j) := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp [vecC]

/-- The list of the bit fields `j < n` of the slots `k`, `k ∈ ks`. -/
def slotFields (n : ℕ) (ks : List ℕ) : List ℕ := ks.flatMap fun k => (List.range n).map (fSlot k)

theorem mem_slotFields {n : ℕ} {ks : List ℕ} {x : ℕ} :
    x ∈ slotFields n ks ↔ ∃ k ∈ ks, ∃ j < n, x = fSlot k j := by
  simp [slotFields, eq_comm]

theorem slotFields_nodup (n : ℕ) {ks : List ℕ} (hks : ks.Nodup) : (slotFields n ks).Nodup := by
  unfold slotFields
  refine List.nodup_flatMap.2 ⟨fun k _ => (List.nodup_range).map fun a b h => (fSlot_inj.1 h).2,
    hks.imp fun {a b} hab => ?_⟩
  rw [Function.onFun, List.disjoint_left]
  intro x hx hx'
  simp only [List.mem_map, List.mem_range] at hx hx'
  obtain ⟨j, -, rfl⟩ := hx
  obtain ⟨j', -, h⟩ := hx'
  exact hab (fSlot_inj.1 h).1.symm

/-- The pairs `(bit j of slot src, bit j of slot dst)`, `j < n`. -/
def cpPairs (n src dst : ℕ) : List (ℕ × ℕ) := (List.range n).map fun j => (fSlot src j, fSlot dst j)

/-! ## The programs -/

/-- The copies for child `i`: slot `i + 2` to slot `0`, slot `i + 3` to slot `1`. -/
def childPairs (n i : ℕ) : List (ℕ × ℕ) := cpPairs n (i + 2) 0 ++ cpPairs n (i + 3) 1


/-- The program of a method (or of the root) with head `h` and body `bs`. -/
def progM (n : ℕ) (h : Option (Bool × ℕ)) (bs : List (Bool × ℕ)) : List (List ASpec) :=
  [chkI [] [] [h]] ++ (slotFields n ((List.range (bs.length + 1)).map (· + 2))).map guessI ++
    (cpPairs n 0 2).map (fun q => eqI q.1 q.2) ++
    (cpPairs n (bs.length + 2) 1).map (fun q => eqI q.1 q.2) ++
    bif bs.isEmpty then [setI fDone] else
      [pickI fSel bs.length] ++
        (List.range bs.length).flatMap (fun i =>
          (childPairs n i).map fun q => ccpI (fSel i) q.1 q.2) ++
        (List.range bs.length).map fun i => ccurI (fSel i) h (some (bs.getI i))

/-- The check of bit `j` of the result of the action `act` (`V` the relevant facts). -/
def bitI (V : List ℕ) (act : ActDesc) (j : ℕ) : List ASpec :=
  bif decide (V.getI j ∈ act.2.2.2.1) then chkI [fSlot 1 j] [] []
  else bif decide (V.getI j ∈ act.2.2.2.2) then chkI [] [fSlot 1 j] []
  else eqI (fSlot 0 j) (fSlot 1 j)

/-- The final check of an action: the current task, applicability, and setting `done`. -/
def chkA (V : List ℕ) (act : ActDesc) (a : ℕ) : List ASpec :=
  bif act.2.1.all (fun f => decide (f ∈ V)) then
    [(((List.range V.length).filter fun j => decide (V.getI j ∈ act.2.1)).map (fSlot 0),
      ((List.range V.length).filter fun j => decide (V.getI j ∈ act.2.2.1)).map (fSlot 0),
      [([fDone], [])], [some (false, a)], [])]
  else []

/-- The program of an action name `a`. -/
def progA (p : ProbDesc) (a : ℕ) : List (List ASpec) :=
  (List.range (pfacts p).length).map (bitI (pfacts p) (actDescOf p a)) ++
    [chkA (pfacts p) (actDescOf p a) a]

/-- The program while `done`. -/
def progNoop : List (List ASpec) := [chkI [fDone] [] []]

/-- The body of a described network: the labels along its linearisation. -/
def bodyOf (t : TnDesc) : List (Bool × ℕ) := (TnDesc.lin t).map (lblOf t)

/-- **The programs of one round.** -/
def rules (p : ProbDesc) : List (List (List ASpec)) :=
  [progNoop, progM (pfacts p).length none (bodyOf p.tnI)] ++
    p.methods.map (fun e => progM (pfacts p).length (some (true, e.1)) (bodyOf e.2)) ++
    (numsOf p).map (progA p)

/-- The goal check of the initial program. -/
def goalI (p : ProbDesc) : List ASpec :=
  bif p.goalPos.all (fun f => decide (f ∈ pfacts p)) then
    chkI (((List.range (pfacts p).length).filter fun j => decide ((pfacts p).getI j ∈ p.goalPos)).map
        (fSlot 1))
      (((List.range (pfacts p).length).filter fun j => decide ((pfacts p).getI j ∈ p.goalNeg)).map
        (fSlot 1)) []
  else []

/-- **The initial program**: guess the final state, check the goal. -/
def progInit (p : ProbDesc) : List (List ASpec) :=
  ((List.range (pfacts p).length).map (fSlot 1)).map guessI ++ [goalI p]

/-- **The initial configuration**: the root task, slot `0` holds the initial state. -/
def cfgInit (p : ProbDesc) : Cfg :=
  ⟨fun f => decide (∃ j < (pfacts p).length, f = fSlot 0 j ∧ (pfacts p).getI j ∈ p.init), none⟩

/-! ## Semantics of the method programs -/

theorem cps_val_sel (c : Cfg) {ps : List (ℕ × ℕ)} (hps : ∀ q ∈ ps, ∃ k j, q.2 = fSlot k j) (i : ℕ) :
    (c.cps ps).val (fSel i) = c.val (fSel i) := by
  refine Cfg.cps_val_not _ _ fun hm => ?_
  obtain ⟨q, hq, he⟩ := List.mem_map.1 hm
  obtain ⟨k, j, hk⟩ := hps q hq
  exact fSlot_ne_fSel k j i (hk ▸ he)

theorem mem_cpPairs {n src dst : ℕ} {q : ℕ × ℕ} :
    q ∈ cpPairs n src dst ↔ ∃ j < n, q = (fSlot src j, fSlot dst j) := by
  simp [cpPairs, eq_comm]

/-- The blocks of conditional copies when exactly the selector `i` is set. -/
theorem mem_wpP_ccpBlocks {P : ℕ → List (ℕ × ℕ)} (hP : ∀ i q, q ∈ P i → ∃ k j, q.2 = fSlot k j)
    {i : ℕ} : ∀ {ks : List ℕ}, ks.Nodup → ∀ {c : Cfg} {Ψ : Set Cfg},
      (∀ i' ∈ ks, c.val (fSel i') = decide (i' = i)) →
      (c ∈ wpP (ks.flatMap fun i' => (P i').map fun q => ccpI (fSel i') q.1 q.2) Ψ ↔
        (if i ∈ ks then c.cps (P i) else c) ∈ Ψ)
  | [], _, c, Ψ, _ => by simp
  | i' :: ks, hnd, c, Ψ, hsel => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, wpP_append]
    by_cases hi : i' = i
    · subst hi
      have hs : c.val (fSel i') = true := by simpa using hsel i' (by simp)
      have hno : fSel i' ∉ (P i').map Prod.snd := fun hm => by
        obtain ⟨q, hq, he⟩ := List.mem_map.1 hm
        obtain ⟨k, j, hk⟩ := hP i' q hq
        exact fSlot_ne_fSel k j i' (hk ▸ he)
      rw [mem_wpP_ccp_on hno hs, mem_wpP_ccpBlocks hP hnd.2 (fun i'' hi'' => by
        rw [cps_val_sel _ (hP i') i'']; exact hsel i'' (by simp [hi'']))]
      simp [hnd.1]
    · have hs : c.val (fSel i') = false := by simpa [hi] using hsel i' (by simp)
      rw [mem_wpP_ccp_off hs, mem_wpP_ccpBlocks hP hnd.2 (fun i'' hi'' => hsel i'' (by simp [hi'']))]
      simp [Ne.symm hi]

/-- The blocks of conditional changes of the current task when exactly the selector `i` is set. -/
theorem mem_wpP_ccurBlocks {h : Option (Bool × ℕ)} {y : ℕ → Option (Bool × ℕ)} {i : ℕ} :
    ∀ {ks : List ℕ}, ks.Nodup → ∀ {c : Cfg} {Ψ : Set Cfg},
      (∀ i' ∈ ks, c.val (fSel i') = decide (i' = i)) →
      (c ∈ wpP (ks.map fun i' => ccurI (fSel i') h (y i')) Ψ ↔
        if i ∈ ks then c.cur = h ∧ (⟨c.val, y i⟩ : Cfg) ∈ Ψ else c ∈ Ψ)
  | [], _, c, Ψ, _ => by simp
  | i' :: ks, hnd, c, Ψ, hsel => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, wpP_cons, mem_wpI_ccur]
    by_cases hi : i' = i
    · subst hi
      have hs : c.val (fSel i') = true := by simpa using hsel i' (by simp)
      rw [if_pos hs, if_pos (by simp)]
      refine and_congr Iff.rfl ?_
      have : ∀ c' : Cfg, c'.val = c.val → (c' ∈ wpP (ks.map fun i'' => ccurI (fSel i'') h (y i''))
          Ψ ↔ c' ∈ Ψ) := by
        intro c' hc'
        rw [mem_wpP_ccurBlocks hnd.2 (fun i'' hi'' => by rw [hc']; exact hsel i'' (by simp [hi'']))]
        simp [hnd.1]
      exact this ⟨c.val, y i'⟩ rfl
    · have hs : c.val (fSel i') = false := by simpa [hi] using hsel i' (by simp)
      rw [if_neg (by simp [hs]), mem_wpP_ccurBlocks hnd.2 (fun i'' hi'' => hsel i'' (by simp [hi'']))]
      simp [Ne.symm hi]

theorem childPairs_tgt (n i : ℕ) : ∀ q ∈ childPairs n i, ∃ k j, q.2 = fSlot k j := by
  intro q hq
  rcases List.mem_append.1 hq with hq | hq <;> obtain ⟨j, -, rfl⟩ := mem_cpPairs.1 hq <;>
    exact ⟨_, _, rfl⟩

/-- The outcome of the round for child `i`. -/
def childCfg (n : ℕ) (bs : List (Bool × ℕ)) (c : Cfg) (i : ℕ) : Cfg :=
  ⟨((c.pick fSel bs.length i).cps (childPairs n i)).val, some (bs.getI i)⟩

theorem childPairs_src (n i : ℕ) : ∀ q ∈ childPairs n i, q.1 ∉ (childPairs n i).map Prod.snd := by
  intro q hq' hm
  obtain ⟨r, hr, he⟩ := List.mem_map.1 hm
  unfold childPairs at hq' hr
  rcases List.mem_append.1 hq' with h1 | h1 <;> rcases List.mem_append.1 hr with h2 | h2 <;>
    obtain ⟨j1, -, rfl⟩ := mem_cpPairs.1 h1 <;> obtain ⟨j2, -, rfl⟩ := mem_cpPairs.1 h2 <;>
    simp at he

theorem childPairs_nodup (n i : ℕ) : ((childPairs n i).map Prod.snd).Nodup := by
  unfold childPairs cpPairs
  rw [List.map_append, List.map_map, List.map_map]
  refine List.Nodup.append ((List.nodup_range).map fun a b h => (fSlot_inj.1 h).2)
    ((List.nodup_range).map fun a b h => (fSlot_inj.1 h).2) ?_
  rw [List.disjoint_left]
  intro x hx hx'
  simp only [List.mem_map, List.mem_range, Function.comp] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, h⟩ := hx'
  simp at h

theorem childCfg_val_tgt {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {i src dst j : ℕ}
    (hq : (fSlot src j, fSlot dst j) ∈ childPairs n i) :
    (childCfg n bs c i).val (fSlot dst j) = c.val (fSlot src j) := by
  have := Cfg.cps_val_mem (c.pick fSel bs.length i) (childPairs n i) (childPairs_src n i)
    (childPairs_nodup n i) hq
  simp only [childCfg]
  rw [this, Cfg.pick_val_ne (fun i' => fSlot_ne_fSel _ _ _)]

theorem childCfg_vecC0 {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {i : ℕ} :
    vecC n (childCfg n bs c i) 0 = vecC n c (i + 2) :=
  vecC_congr fun j hj => childCfg_val_tgt (List.mem_append_left _ (mem_cpPairs.2 ⟨j, hj, rfl⟩))

theorem childCfg_vecC1 {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {i : ℕ} :
    vecC n (childCfg n bs c i) 1 = vecC n c (i + 3) :=
  vecC_congr fun j hj => childCfg_val_tgt (List.mem_append_right _ (mem_cpPairs.2 ⟨j, hj, rfl⟩))

theorem childCfg_done {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {i : ℕ} :
    (childCfg n bs c i).val fDone = c.val fDone := by
  simp only [childCfg]
  rw [Cfg.cps_val_not, Cfg.pick_val_ne (fun i' => fDone_ne_fSel _)]
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.1 hm
  obtain ⟨k, j, hk⟩ := childPairs_tgt n i q hq
  exact fSlot_ne_fDone k j (hk ▸ he)

@[simp] theorem childCfg_cur {n : ℕ} {bs : List (Bool × ℕ)} {c : Cfg} {i : ℕ} :
    (childCfg n bs c i).cur = some (bs.getI i) := rfl

/-- **The tail of a method program with a non-empty body.** -/
theorem mem_wpP_tail {n : ℕ} {h : Option (Bool × ℕ)} {bs : List (Bool × ℕ)} {Ψ : Set Cfg}
    {c : Cfg} (hcur : c.cur = h) :
    c ∈ wpP ([pickI fSel bs.length] ++
        (List.range bs.length).flatMap (fun i =>
          (childPairs n i).map fun q => ccpI (fSel i) q.1 q.2) ++
        (List.range bs.length).map fun i => ccurI (fSel i) h (some (bs.getI i))) Ψ ↔
      ∀ i < bs.length, childCfg n bs c i ∈ Ψ := by
  rw [wpP_append, wpP_append, wpP_cons, wpP_nil, mem_wpI_pick]
  refine forall₂_congr fun i hi => ?_
  have hsel : ∀ i' ∈ List.range bs.length, (c.pick fSel bs.length i).val (fSel i') =
      decide (i' = i) := fun i' hi' => Cfg.pick_val_sel fSel_injective (List.mem_range.1 hi')
  rw [mem_wpP_ccpBlocks (P := fun i => childPairs n i) (childPairs_tgt n) List.nodup_range hsel,
    if_pos (List.mem_range.2 hi), mem_wpP_ccurBlocks List.nodup_range
      (fun i' hi' => by rw [cps_val_sel _ (childPairs_tgt n i)]; exact hsel i' hi'),
    if_pos (List.mem_range.2 hi)]
  simp only [Cfg.cps_cur, Cfg.pick_cur, hcur, true_and]
  rfl

/-- The configuration after the guesses of a method program. -/
def guessCfg (n k : ℕ) (c : Cfg) (g : ℕ → Bool) : Cfg :=
  c.sets (slotFields n ((List.range (k + 1)).map (· + 2))) g

theorem guessCfg_val_lo {n k : ℕ} {c : Cfg} {g : ℕ → Bool} {x : ℕ}
    (hx : ∀ k' ≥ 2, ∀ j, x ≠ fSlot k' j) : (guessCfg n k c g).val x = c.val x := by
  rw [guessCfg, Cfg.sets_val, if_neg]
  rw [mem_slotFields]
  rintro ⟨k', hk', j, -, rfl⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hk'
  exact hx _ (by omega) j rfl

theorem guessCfg_val_hi {n k : ℕ} {c : Cfg} {g : ℕ → Bool} {i j : ℕ} (hi : i ≤ k) (hj : j < n) :
    (guessCfg n k c g).val (fSlot (i + 2) j) = g (fSlot (i + 2) j) := by
  rw [guessCfg, Cfg.sets_val, if_pos]
  rw [mem_slotFields]
  exact ⟨i + 2, List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩, j, hj, rfl⟩

@[simp] theorem guessCfg_cur {n k : ℕ} {c : Cfg} {g : ℕ → Bool} : (guessCfg n k c g).cur = c.cur :=
  Cfg.sets_cur _ _ _

theorem mem_wpP_progM {n : ℕ} {h : Option (Bool × ℕ)} {bs : List (Bool × ℕ)} {Ψ : Set Cfg}
    {c : Cfg} : c ∈ wpP (progM n h bs) Ψ ↔ c.cur = h ∧ ∃ g,
      (∀ j < n, (guessCfg n bs.length c g).val (fSlot 0 j) =
        (guessCfg n bs.length c g).val (fSlot 2 j)) ∧
      (∀ j < n, (guessCfg n bs.length c g).val (fSlot (bs.length + 2) j) =
        (guessCfg n bs.length c g).val (fSlot 1 j)) ∧
      (if bs = [] then (guessCfg n bs.length c g).set fDone true ∈ Ψ
        else ∀ i < bs.length, childCfg n bs (guessCfg n bs.length c g) i ∈ Ψ) := by
  unfold progM
  simp only [wpP_append, wpP_cons, wpP_nil, mem_wpI_chk, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, List.mem_singleton, forall_eq, true_and]
  by_cases hcur : c.cur = h
  swap
  · simp only [hcur, false_and]
  simp only [hcur, true_and]
  rw [mem_wpP_guess (slotFields_nodup n ((List.nodup_range).map fun a b h => by omega))]
  refine exists_congr fun g => ?_
  rw [mem_wpP_eq, mem_wpP_eq]
  simp only [cpPairs, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  cases hb : bs.isEmpty
  · have hne : bs ≠ [] := by simpa using hb
    simp only [cond_false, if_neg hne]
    exact mem_wpP_tail (by simp [hcur])
  · have he : bs = [] := by simpa using hb
    simp only [cond_true, if_pos he, wpP_cons, wpP_nil, mem_wpI_set]
    rfl

/-- **Soundness of a method program.** -/
theorem progM_sound {n : ℕ} {h : Option (Bool × ℕ)} {bs : List (Bool × ℕ)} {Ψ : Set Cfg}
    {c : Cfg} (hc : c ∈ wpP (progM n h bs) Ψ) :
    c.cur = h ∧ ∃ u : ℕ → List Bool, (∀ i, (u i).length = n) ∧ u 0 = vecC n c 0 ∧
      u bs.length = vecC n c 1 ∧
      ∀ i < bs.length, ∃ c' ∈ Ψ, c'.cur = some (bs.getI i) ∧ vecC n c' 0 = u i ∧
        vecC n c' 1 = u (i + 1) ∧ c'.val fDone = c.val fDone := by
  obtain ⟨hcur, g, h0, hk, ht⟩ := mem_wpP_progM.1 hc
  set c1 := guessCfg n bs.length c g
  have hlo : ∀ k < 2, ∀ j, c1.val (fSlot k j) = c.val (fSlot k j) := fun k hk j =>
    guessCfg_val_lo fun k' hk' j' he => by simp only [fSlot_inj] at he; omega
  refine ⟨hcur, fun i => vecC n c1 (i + 2), fun i => length_vecC _ _ _, ?_, ?_, fun i hi => ?_⟩
  · exact vecC_congr fun j hj => ((h0 j hj).symm.trans (hlo 0 (by omega) j))
  · exact vecC_congr fun j hj => ((hk j hj).trans (hlo 1 (by omega) j))
  · have hne : bs ≠ [] := by rintro rfl; simp at hi
    rw [if_neg hne] at ht
    refine ⟨_, ht i hi, rfl, childCfg_vecC0, childCfg_vecC1, ?_⟩
    rw [childCfg_done]
    exact guessCfg_val_lo fun k' _ j he => fDone_ne_fSlot _ _ he

/-- The guess realising given vectors. -/
def guessOf (u : ℕ → List Bool) (x : ℕ) : Bool :=
  (u ((Nat.unpair ((x - 2) / 2)).1 - 2)).getI (Nat.unpair ((x - 2) / 2)).2

theorem guessOf_fSlot (u : ℕ → List Bool) (i j : ℕ) : guessOf u (fSlot (i + 2) j) = (u i).getI j := by
  simp only [guessOf, fSlot]
  rw [show (2 * Nat.pair (i + 2) j + 2 - 2) / 2 = Nat.pair (i + 2) j by omega, Nat.unpair_pair]
  simp

/-- **Completeness of a method program.** -/
theorem progM_complete {n : ℕ} {h : Option (Bool × ℕ)} {bs : List (Bool × ℕ)} {Ψ : Set Cfg}
    {c : Cfg} (hcur : c.cur = h) (u : ℕ → List Bool) (hu : ∀ i, (u i).length = n)
    (hu0 : u 0 = vecC n c 0) (huk : u bs.length = vecC n c 1)
    (hdone : bs = [] → ∀ c' : Cfg, c'.val fDone = true → c' ∈ Ψ)
    (hch : ∀ i < bs.length, ∀ c' : Cfg, c'.cur = some (bs.getI i) → vecC n c' 0 = u i →
      vecC n c' 1 = u (i + 1) → c'.val fDone = c.val fDone → c' ∈ Ψ) :
    c ∈ wpP (progM n h bs) Ψ := by
  set c1 := guessCfg n bs.length c (guessOf u)
  have hlo : ∀ k < 2, ∀ j, c1.val (fSlot k j) = c.val (fSlot k j) := fun k hk j =>
    guessCfg_val_lo fun k' hk' j' he => by simp only [fSlot_inj] at he; omega
  have hhi : ∀ i ≤ bs.length, vecC n c1 (i + 2) = u i := by
    intro i hi
    have : vecC n c1 (i + 2) = (List.range n).map (u i).getI :=
      List.map_congr_left fun j hj => by
        rw [guessCfg_val_hi hi (List.mem_range.1 hj), guessOf_fSlot]
    rw [this, HTN.Syn.PolyDom.range_map_getI _ (hu i).le, hu i, Nat.sub_self, List.replicate_zero,
      List.append_nil]
  have hbit : ∀ i ≤ bs.length, ∀ j < n, c1.val (fSlot (i + 2) j) = (u i).getI j := by
    intro i hi j hj
    rw [← hhi i hi, getI_vecC hj]
  refine mem_wpP_progM.2 ⟨hcur, guessOf u, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [hlo 0 (by omega), hbit 0 (by omega) j hj, hu0, getI_vecC hj]
  · rw [hlo 1 (by omega), hbit _ le_rfl j hj, huk, getI_vecC hj]
  · split_ifs with hb
    · exact hdone hb _ (Cfg.set_val_self _ _ _)
    · intro i hi
      refine hch i hi _ rfl ?_ ?_ ?_
      · rw [childCfg_vecC0, hhi i hi.le]
      · rw [childCfg_vecC1, show i + 3 = (i + 1) + 2 by omega, hhi (i + 1) hi]
      · rw [childCfg_done]
        exact guessCfg_val_lo fun k' _ j he => fDone_ne_fSlot _ _ he

/-! ## Semantics of the action programs -/

theorem mem_wpI_bit {V : List ℕ} {act : ActDesc} {j : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (bitI V act j) Ψ ↔
      c.val (fSlot 1 j) = ((c.val (fSlot 0 j) && !decide (V.getI j ∈ act.2.2.2.2)) ||
        decide (V.getI j ∈ act.2.2.2.1)) ∧ c ∈ Ψ := by
  unfold bitI
  by_cases ha : V.getI j ∈ act.2.2.2.1
  · simp only [ha, decide_true, cond_true, mem_wpI_chk, List.mem_singleton, forall_eq,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true, Bool.or_true]
  · by_cases hd : V.getI j ∈ act.2.2.2.2
    · simp only [ha, hd, decide_true, decide_false, cond_true, cond_false, mem_wpI_chk,
        List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        and_true, true_and, Bool.not_true, Bool.and_false, Bool.or_false]
    · simp only [ha, hd, decide_false, cond_false, mem_wpI_eq, Bool.not_false, Bool.and_true,
        Bool.or_false]
      rw [eq_comm]

theorem mem_wpP_bits {V : List ℕ} {act : ActDesc} {Ψ : Set Cfg} {c : Cfg} :
    ∀ js : List ℕ, c ∈ wpP (js.map (bitI V act)) Ψ ↔
      (∀ j ∈ js, c.val (fSlot 1 j) = ((c.val (fSlot 0 j) && !decide (V.getI j ∈ act.2.2.2.2)) ||
        decide (V.getI j ∈ act.2.2.2.1))) ∧ c ∈ Ψ
  | [] => by simp
  | j :: js => by
    rw [List.map_cons, wpP_cons, mem_wpI_bit, mem_wpP_bits js]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_wpI_chkA {V : List ℕ} {act : ActDesc} {a : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpI (chkA V act a) Ψ ↔
      (∀ f ∈ act.2.1, f ∈ V) ∧ (∀ j < V.length, V.getI j ∈ act.2.1 → c.val (fSlot 0 j) = true) ∧
      (∀ j < V.length, V.getI j ∈ act.2.2.1 → c.val (fSlot 0 j) = false) ∧
      c.cur = some (false, a) ∧ c.set fDone true ∈ Ψ := by
  unfold chkA
  cases hall : act.2.1.all (fun f => decide (f ∈ V))
  · have : ¬ ∀ f ∈ act.2.1, f ∈ V := by simpa using hall
    simp [wpI, this]
  · have : ∀ f ∈ act.2.1, f ∈ V := by simpa using hall
    rw [mem_wpI_iff]
    simp only [cond_true, List.mem_singleton, exists_eq_left, app_iff, List.mem_map,
      List.mem_filter, List.mem_range, decide_eq_true_eq, forall_exists_index, and_imp,
      forall_eq, ASpec.effs, eff_add']
    exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨this, fun j hj hm => h1 _ j hj hm rfl,
      fun j hj hm => h2 _ j hj hm rfl, h3, h4⟩, fun ⟨_, h1, h2, h3, h4⟩ =>
      ⟨⟨fun f j hj hm he => he ▸ h1 j hj hm, fun f j hj hm he => he ▸ h2 j hj hm, h3⟩, h4⟩⟩

/-- The bits of `sv V v` for a vector read from a slot. -/
theorem mem_sv_vecC {V : List ℕ} (hV : V.Nodup) {c : Cfg} {k j : ℕ} (hj : j < V.length) :
    V.getI j ∈ sv V (vecC V.length c k) ↔ c.val (fSlot k j) = true := by
  rw [HTN.Article.sv_eq]
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hv⟩, he⟩
    have : i = j := by
      rw [← List.getD_default_eq_getI, ← List.getD_default_eq_getI,
        List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at he
      exact (hV.getElem_inj_iff).1 he
    subst this
    rwa [getI_vecC hi] at hv
  · intro h
    exact ⟨j, ⟨hj, by rwa [getI_vecC hj]⟩, rfl⟩

theorem mem_sv_vecC' {V : List ℕ} (hV : V.Nodup) {c : Cfg} {k : ℕ} {f : ℕ} :
    f ∈ sv V (vecC V.length c k) ↔ f ∈ V ∧ c.val (fSlot k (V.idxOf f)) = true := by
  constructor
  · intro h
    have hf := sv_sub h
    refine ⟨hf, ?_⟩
    have hj := List.idxOf_lt_length_of_mem hf
    rw [← mem_sv_vecC hV hj, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj,
      List.getElem_idxOf]
    exact h
  · rintro ⟨hf, h⟩
    have hj := List.idxOf_lt_length_of_mem hf
    have := (mem_sv_vecC hV hj).2 h
    rwa [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj, List.getElem_idxOf] at this

theorem getI_of_lt {V : List ℕ} {j : ℕ} (hj : j < V.length) : V.getI j = V[j] := by
  rw [← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hj]

@[simp] theorem getElem_vecC {n : ℕ} {c : Cfg} {k j : ℕ} (hj : j < (vecC n c k).length) :
    (vecC n c k)[j] = c.val (fSlot k j) := by
  simp [vecC]

theorem mem_runStep {p : ProbDesc} {a : ℕ} {s : List ℕ} {f : ℕ} :
    f ∈ (runStep p (true, s) a).2 ↔
      (f ∈ s ∧ f ∉ (actDescOf p a).2.2.2.2) ∨ f ∈ (actDescOf p a).2.2.2.1 := by
  simp [runStep]

/-- **The action check is the rule of the dynamic program.** -/
theorem progA_iff {p : ProbDesc} {a : ℕ} {Ψ : Set Cfg} {c : Cfg} :
    c ∈ wpP (progA p a) Ψ ↔
      (okV p a (vecC (pfacts p).length c 0) = true ∧
        apV p a (vecC (pfacts p).length c 0) = vecC (pfacts p).length c 1) ∧
      c.cur = some (false, a) ∧ c.set fDone true ∈ Ψ := by
  have hV : (pfacts p).Nodup := List.nodup_dedup _
  unfold progA
  rw [wpP_append, mem_wpP_bits, wpP_cons, wpP_nil, mem_wpI_chkA]
  have hok : okV p a (vecC (pfacts p).length c 0) = true ↔ (∀ f ∈ (actDescOf p a).2.1, f ∈ pfacts p) ∧
      (∀ j < (pfacts p).length, (pfacts p).getI j ∈ (actDescOf p a).2.1 → c.val (fSlot 0 j) = true) ∧
      (∀ j < (pfacts p).length, (pfacts p).getI j ∈ (actDescOf p a).2.2.1 →
        c.val (fSlot 0 j) = false) := by
    simp only [okV, runStep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => sv_sub (h1 f hf), fun j hj hm => (mem_sv_vecC hV hj).1 (h1 _ hm),
        fun j hj hm => ?_⟩
      have := h2 _ hm
      rw [mem_sv_vecC hV hj] at this
      simpa using this
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun f hf => (mem_sv_vecC' hV).2 ⟨h0 f hf, ?_⟩, fun f hf hm => ?_⟩
      · have hj := List.idxOf_lt_length_of_mem (h0 f hf)
        refine h1 _ hj ?_
        rwa [getI_of_lt hj, List.getElem_idxOf]
      · obtain ⟨hfV, hc⟩ := (mem_sv_vecC' hV).1 hm
        have hj := List.idxOf_lt_length_of_mem hfV
        have := h2 _ hj (by rwa [getI_of_lt hj, List.getElem_idxOf])
        rw [this] at hc
        exact Bool.false_ne_true hc
  have hap : apV p a (vecC (pfacts p).length c 0) = vecC (pfacts p).length c 1 ↔
      ∀ j ∈ List.range (pfacts p).length, c.val (fSlot 1 j) =
        ((c.val (fSlot 0 j) && !decide ((pfacts p).getI j ∈ (actDescOf p a).2.2.2.2)) ||
          decide ((pfacts p).getI j ∈ (actDescOf p a).2.2.2.1)) := by
    have hlen : (apV p a (vecC (pfacts p).length c 0)).length = (pfacts p).length := by
      simp [apV, length_vecOf]
    rw [List.ext_getElem_iff]
    simp only [hlen, length_vecC, true_and, List.mem_range]
    have key : ∀ j (hj : j < (pfacts p).length),
        (apV p a (vecC (pfacts p).length c 0))[j]'(by rw [hlen]; exact hj) =
          ((c.val (fSlot 0 j) && !decide ((pfacts p).getI j ∈ (actDescOf p a).2.2.2.2)) ||
            decide ((pfacts p).getI j ∈ (actDescOf p a).2.2.2.1)) := by
      intro j hj
      simp only [apV, vecOf, List.getElem_map]
      rw [← getI_of_lt hj]
      have hm := mem_sv_vecC (c := c) (k := 0) hV hj
      cases hc : c.val (fSlot 0 j) <;> rw [hc] at hm <;>
        by_cases h1 : (pfacts p).getI j ∈ (actDescOf p a).2.2.2.2 <;>
        by_cases h2 : (pfacts p).getI j ∈ (actDescOf p a).2.2.2.1 <;>
        simp_all [mem_runStep]
    refine forall_congr' fun j => ⟨fun h hj => ?_, fun h hj _ => ?_⟩
    · rw [← key j hj, h hj (by simpa using hj), getElem_vecC]
    · rw [key j hj, getElem_vecC, h hj]
  rw [hok, hap]
  tauto

/-! ## Chains of the table as functions -/

theorem chainX_of_fun {X : List Trip} {allV : List (List Bool)} {lab : ℕ → Bool × ℕ} :
    ∀ (l : List ℕ) (u : ℕ → List Bool),
      (∀ i < l.length, (u i, lab (l.getI i), u (i + 1)) ∈ X ∧ u (i + 1) ∈ allV) →
        ChainX X allV lab l (u 0) (u l.length)
  | [], u, _ => .nil _
  | x :: l, u, h => by
    have h0 := h 0 (by simp)
    refine .cons (u₁ := u 1) (by simpa using h0.1) h0.2 ?_
    have := chainX_of_fun l (fun i => u (i + 1)) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc] using this
    simpa [Nat.add_comm] using this

theorem fun_of_chainX {X : List Trip} {allV : List (List Bool)} {lab : ℕ → Bool × ℕ}
    {l : List ℕ} {v w : List Bool} (h : ChainX X allV lab l v w) :
    ∃ u : ℕ → List Bool, u 0 = v ∧ u l.length = w ∧
      ∀ i < l.length, (u i, lab (l.getI i), u (i + 1)) ∈ X ∧ u (i + 1) ∈ allV := by
  induction h with
  | nil u => exact ⟨fun _ => u, rfl, rfl, fun i hi => absurd hi (by simp)⟩
  | @cons x l u u₁ w hx h₁ _ ih =>
    obtain ⟨f, hf0, hfl, hf⟩ := ih
    refine ⟨fun i => if i = 0 then u else f (i - 1), by simp, by simpa using hfl, fun i hi => ?_⟩
    rcases i with _ | i
    · simp only [if_true, List.getI_cons_zero, zero_add, Nat.one_ne_zero, if_false,
        Nat.sub_self, hf0]
      exact ⟨hx, h₁⟩
    · have := hf i (by simpa using hi)
      simpa using this

theorem getI_map_lt {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {i : ℕ}
    (hi : i < l.length) : (l.map f).getI i = f (l.getI i) := by
  rw [← List.getD_default_eq_getI, ← List.getD_default_eq_getI, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

/-! ## The invariant and the soundness of a round -/

section Sound

variable (p : ProbDesc) (allV : List (List Bool))

/-- **The invariant**: done, or the current triple is in the table (for the root: the end
vector is reached by the initial task network). -/
def Good (c : Cfg) : Prop :=
  c.val fDone = true ∨
    (c.cur = none ∧ vecC (pfacts p).length c 1 ∈
      chainSet allV (dpTab p allV) p.tnI [vecC (pfacts p).length c 0]) ∨
    ∃ x, c.cur = some x ∧
      (vecC (pfacts p).length c 0, x, vecC (pfacts p).length c 1) ∈ dpTab p allV

variable {p allV}

/-- The children of a method program give a chain of the table. -/
theorem chain_of_progM {t : TnDesc} {Ψ : Set Cfg} (hΨ : ∀ c' ∈ Ψ, Good p allV c')
    (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) {h : Option (Bool × ℕ)} {c : Cfg}
    (hc : c ∈ wpP (progM (pfacts p).length h (bodyOf t)) Ψ) (hd : c.val fDone = false) :
    c.cur = h ∧ vecC (pfacts p).length c 1 ∈
      chainSet allV (dpTab p allV) t [vecC (pfacts p).length c 0] := by
  obtain ⟨hcur, u, hu, hu0, huk, hch⟩ := progM_sound hc
  refine ⟨hcur, mem_chainSet.2 ⟨_, List.mem_singleton_self _, ?_⟩⟩
  have hlen : (bodyOf t).length = (TnDesc.lin t).length := by simp [bodyOf]
  rw [← hu0, ← huk, hlen]
  refine chainX_of_fun _ u fun i hi => ?_
  obtain ⟨c', hc', hcur', h0, h1, hd'⟩ := hch i (by rwa [hlen])
  rcases hΨ c' hc' with hdn | ⟨hn, -⟩ | ⟨x, hx, hm⟩
  · rw [hd', hd] at hdn; exact absurd hdn (by simp)
  · rw [hcur'] at hn; exact absurd hn (by simp)
  · rw [hcur'] at hx
    cases hx
    rw [h0, h1, bodyOf, getI_map_lt _ hi] at hm
    exact ⟨hm, (hall _).2 (hu _)⟩

theorem mem_dpTab_of_rule' {q : Trip} (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length)
    (hn : q.2.1.2 ∈ numsOf p) (h1 : q.1.length = (pfacts p).length)
    (h2 : q.2.2.length = (pfacts p).length) (hr : ruleB p allV (dpTab p allV) q = true) :
    q ∈ dpTab p allV := by
  refine (dpStep_dpTab q).1 (List.mem_filter.2 ⟨?_, hr⟩)
  obtain ⟨v, n, v'⟩ := q
  exact mem_cand ((hall _).2 h1) ((hall _).2 h2) hn

/-- **Soundness of one round.** -/
theorem round_sound (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) {Ψ : Set Cfg}
    (hΨ : ∀ c' ∈ Ψ, Good p allV c') {r : List (List ASpec)} (hr : r ∈ rules p) {c : Cfg}
    (hc : c ∈ wpP r Ψ) : Good p allV c := by
  by_cases hd : c.val fDone = true
  · exact Or.inl hd
  replace hd : c.val fDone = false := by simpa using hd
  unfold rules at hr
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [progNoop, wpP_cons, wpP_nil, mem_wpI_chk, List.mem_singleton, forall_eq] at hc
        exact Or.inl hc.1.1
      · obtain ⟨hcur, hch⟩ := chain_of_progM hΨ hall hc hd
        exact Or.inr (Or.inl ⟨hcur, hch⟩)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
      obtain ⟨hcur, hch⟩ := chain_of_progM hΨ hall hc hd
      refine Or.inr (Or.inr ⟨_, hcur, mem_dpTab_of_rule' hall
        (mem_numsOf_method he (List.mem_cons_self ..)) (by simp) (by simp) ?_⟩)
      simp only [ruleB, cond_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      exact ⟨e, he, rfl, hch⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    obtain ⟨⟨hok, hap⟩, hcur, -⟩ := progA_iff.1 hc
    refine Or.inr (Or.inr ⟨_, hcur, mem_dpTab_of_rule' hall ha (by simp) (by simp) ?_⟩)
    simp only [ruleB, cond_false, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hok, hap⟩

end Sound

/-! ## Completeness of a round -/

section Complete

variable (p : ProbDesc) (allV : List (List Bool))

/-- The `m`-th iterate of the table. -/
def dpIt (m : ℕ) : List Trip := (dpStep p allV)^[m] []

/-- **The graded invariant**: done, or the current triple is in the `m`-th iterate of the table
(for the root: the children are in the `m - 1`-th). -/
def GoodK (m : ℕ) (c : Cfg) : Prop :=
  c.val fDone = true ∨
    (∃ m', m = m' + 1 ∧ c.cur = none ∧ vecC (pfacts p).length c 1 ∈
      chainSet allV (dpIt p allV m') p.tnI [vecC (pfacts p).length c 0]) ∨
    ∃ x, c.cur = some x ∧
      (vecC (pfacts p).length c 0, x, vecC (pfacts p).length c 1) ∈ dpIt p allV m

variable {p allV}

theorem goodK_zero {c : Cfg} (h : GoodK p allV 0 c) : c.val fDone = true := by
  rcases h with h | ⟨m', hm, -⟩ | ⟨x, -, hx⟩
  · exact h
  · omega
  · simp [dpIt] at hx

/-- A chain of the `m`-th iterate gives a method program into the `m`-th invariant. -/
theorem progM_of_chain (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) {m : ℕ}
    {t : TnDesc} {h : Option (Bool × ℕ)} {c : Cfg} (hcur : c.cur = h)
    (hch : vecC (pfacts p).length c 1 ∈ chainSet allV (dpIt p allV m) t
      [vecC (pfacts p).length c 0]) :
    c ∈ wpP (progM (pfacts p).length h (bodyOf t)) {c' | GoodK p allV m c'} := by
  obtain ⟨u₀, hu₀, hcx⟩ := mem_chainSet.1 hch
  rw [List.mem_singleton] at hu₀
  subst hu₀
  obtain ⟨u, hu0, hul, hu⟩ := fun_of_chainX hcx
  have hlen : (bodyOf t).length = (TnDesc.lin t).length := by simp [bodyOf]
  set k := (TnDesc.lin t).length
  let u' : ℕ → List Bool := fun i => if i ≤ k then u i else u 0
  have hu'len : ∀ i, (u' i).length = (pfacts p).length := by
    intro i
    simp only [u']
    split_ifs with hi
    · rcases i with _ | i
      · rw [hu0]; simp
      · exact (hall _).1 (hu i (by omega)).2
    · rw [hu0]; simp
  refine progM_complete hcur u' hu'len (by simp [u', hu0]) (by simp [u', hlen, hul])
    (fun _ c' hc' => Or.inl hc') fun i hi c' hc' h0 h1 _ => Or.inr (Or.inr ⟨_, hc', ?_⟩)
  rw [hlen] at hi
  rw [h0, h1]
  simp only [u', if_pos hi.le, if_pos (show i + 1 ≤ k by omega)]
  rw [bodyOf, getI_map_lt _ hi]
  exact (hu i hi).1

theorem numsOf_of_mem_dpIt {m : ℕ} {q : Trip} (h : q ∈ dpIt p allV m) : q.2.1.2 ∈ numsOf p := by
  have hc := iterate_sub (p := p) (allV := allV) m q h
  simp only [cand, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨v, -, n, hn, v', -, rfl⟩ := hc
  simp only [namesB, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hn
  obtain ⟨x, hx, rfl | rfl⟩ := hn <;> exact hx

/-- **Completeness of one round.** -/
theorem round_complete (hall : ∀ v, v ∈ allV ↔ v.length = (pfacts p).length) {m : ℕ} {c : Cfg}
    (hc : GoodK p allV (m + 1) c) : ∃ r ∈ rules p, c ∈ wpP r {c' | GoodK p allV m c'} := by
  rcases hc with hd | ⟨m', hm, hcur, hch⟩ | ⟨x, hcur, hx⟩
  · refine ⟨progNoop, by simp [rules], ?_⟩
    simp only [progNoop, wpP_cons, wpP_nil, mem_wpI_chk, List.mem_singleton, forall_eq,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨hd, Or.inl hd⟩
  · obtain rfl : m = m' := by omega
    exact ⟨_, by simp [rules], progM_of_chain hall hcur hch⟩
  · have hx' := hx
    rw [dpIt, Function.iterate_succ_apply'] at hx'
    obtain ⟨-, hr⟩ := List.mem_filter.1 hx'
    obtain ⟨b, a⟩ := x
    cases b
    · simp only [ruleB, cond_false, Bool.and_eq_true, beq_iff_eq] at hr
      have ha : a ∈ numsOf p := numsOf_of_mem_dpIt hx
      exact ⟨progA p a, List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩),
        progA_iff.2 ⟨hr, hcur, Or.inl (by simp)⟩⟩
    · simp only [ruleB, cond_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hr
      obtain ⟨e, he, rfl, hch⟩ := hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩)),
        progM_of_chain hall hcur hch⟩

end Complete

end HardMP

end FOND
